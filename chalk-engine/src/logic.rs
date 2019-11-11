use crate::context::{prelude::*, Floundered, UnificationOps};
use crate::fallible::NoSolution;
use crate::forest::Forest;
use crate::hh::HhGoal;
use crate::stack::StackIndex;
use crate::strand::{SelectedSubgoal, Strand};
use crate::table::AnswerIndex;
use crate::Answer;
use crate::{
    DepthFirstNumber, ExClause, FlounderedSubgoal, Literal, Minimums, TableIndex, TimeStamp,
};
use std::mem;

type RootSearchResult<T> = Result<T, RootSearchFail>;

/// The different ways that a *root* search (which potentially pursues
/// many strands) can fail. A root search is one that begins with an
/// empty stack.
///
/// (This is different from `RecursiveSearchFail` because nothing can
/// be on the stack, so cycles are ruled out.)
#[derive(Debug)]
pub(super) enum RootSearchFail {
    /// The subgoal we were trying to solve cannot succeed.
    NoMoreSolutions,

    /// The subgoal cannot be solved without more type information.
    Floundered,

    /// We did not find a solution, but we still have things to try.
    /// Repeat the request, and we'll give one of those a spin.
    ///
    /// (In a purely depth-first-based solver, like Prolog, this
    /// doesn't appear.)
    QuantumExceeded,

    /// A negative cycle was found. This is fail-fast, so even if there was
    /// possibly a solution (ambiguous or not), it may not have been found.
    NegativeCycle,
}

type RecursiveSearchResult<T> = Result<T, RecursiveSearchFail>;

/// The different ways that a recursive search (which potentially
/// pursues many strands) can fail -- a "recursive" search is one that
/// did not start with an empty stack.
#[derive(Debug)]
enum RecursiveSearchFail {
    /// The subgoal we were trying to solve cannot succeed.
    NoMoreSolutions,

    /// The subgoal cannot be solved without more type information.
    Floundered,

    /// A negative cycle was found. This is fail-fast, so even if there was
    /// possibly a solution (ambiguous or not), it may not have been found.
    NegativeCycle,

    /// **All** avenues to solve the subgoal we were trying solve
    /// encountered a cyclic dependency on something higher up in the
    /// stack. The `Minimums` encodes how high up (and whether
    /// positive or negative).
    PositiveCycle(Minimums),

    /// We did not find a solution, but we still have things to try.
    /// Repeat the request, and we'll give one of those a spin.
    ///
    /// (In a purely depth-first-based solver, like Prolog, this
    /// doesn't appear.)
    QuantumExceeded,
}

#[allow(type_alias_bounds)]
type StrandResult<C: Context, T> = Result<T, StrandFail<C>>;

/// Possible failures from pursuing a particular strand.
#[derive(Debug)]
pub(super) enum StrandFail<C: Context> {
    /// The strand has no solution.
    NoSolution,

    /// The strand got stuck and the table requires more type information.
    Floundered,

    /// We did not yet figure out a solution; the strand will have
    /// been rescheduled for later.
    QuantumExceeded,

    /// A negative cycle was found. This is fail-fast, so even if there was
    /// possibly a solution (ambiguous or not), it may not have been found.
    NegativeCycle,

    /// The strand hit a cyclic dependency. In this case,
    /// we return the strand, as well as a `Minimums` struct.
    PositiveCycle(Strand<C>, Minimums),
}

#[derive(Debug)]
enum EnsureSuccess {
    AnswerAvailable,
    Coinductive,
}

impl<C: Context> Forest<C> {
    /// Ensures that answer with the given index is available from the
    /// given table. This may require activating a strand. Returns
    /// `Ok(())` if the answer is available and otherwise a
    /// `RootSearchFail` result.
    pub(super) fn ensure_root_answer(
        &mut self,
        context: &impl ContextOps<C>,
        table: TableIndex,
        answer: AnswerIndex,
    ) -> RootSearchResult<()> {
        assert!(self.stack.is_empty());

        match self.ensure_answer_recursively(context, table, answer) {
            Ok(EnsureSuccess::AnswerAvailable) => Ok(()),
            Err(RecursiveSearchFail::Floundered) => Err(RootSearchFail::Floundered),
            Err(RecursiveSearchFail::NoMoreSolutions) => Err(RootSearchFail::NoMoreSolutions),
            Err(RecursiveSearchFail::QuantumExceeded) => Err(RootSearchFail::QuantumExceeded),
            Err(RecursiveSearchFail::NegativeCycle) => Err(RootSearchFail::NegativeCycle),

            // Things involving cycles should be impossible since our
            // stack was empty on entry:
            Ok(EnsureSuccess::Coinductive) | Err(RecursiveSearchFail::PositiveCycle(..)) => {
                panic!("ensure_root_answer: nothing on the stack but cyclic result")
            }
        }
    }

    pub(super) fn any_future_answer(
        &mut self,
        table: TableIndex,
        answer: AnswerIndex,
        mut test: impl FnMut(&C::Substitution) -> bool,
    ) -> bool {
        if let Some(answer) = self.tables[table].answer(answer) {
            info!("answer cached = {:?}", answer);
            return test(C::subst_from_canonical_subst(&answer.subst));
        }

        self.tables[table].strands_mut().any(|strand| {
            let subst = strand.infer.normalize_subst(&strand.ex_clause.subst);
            test(&subst)
        })
    }

    /// Ensures that answer with the given index is available from the
    /// given table. Returns `Ok` if there is an answer:
    ///
    /// - `EnsureSuccess::AnswerAvailable` means that the answer is
    ///   cached in the table (and can be fetched with e.g. `self.answer()`).
    /// - `EnsureSuccess::Coinductive` means that this was a cyclic
    ///   request of a coinductive goal and is thus considered true;
    ///   in this case, the answer is not cached in the table (it is
    ///   only true in this cyclic context).
    ///
    /// This function first attempts to fetch answer that is cached in
    /// the table. If none is found, then we will if the table is on
    /// the stack; if so, that constitutes a cycle (producing a new
    /// result for the table X required producing a new result for the
    /// table X), and we return a suitable result. Otherwise, we can
    /// push the table onto the stack and select the next available
    /// strand -- if none are available, then no more answers are
    /// possible.
    fn ensure_answer_recursively(
        &mut self,
        context: &impl ContextOps<C>,
        table: TableIndex,
        answer: AnswerIndex,
    ) -> RecursiveSearchResult<EnsureSuccess> {
        info_heading!(
            "ensure_answer_recursively(table={:?}, answer={:?})",
            table,
            answer
        );
        info!("table goal = {:#?}", self.tables[table].table_goal);

        // First, check if this table has floundered.
        if self.tables[table].is_floundered() {
            return Err(RecursiveSearchFail::Floundered);
        }

        // Next, check for a tabled answer.
        if self.tables[table].answer(answer).is_some() {
            info!("answer cached = {:?}", self.tables[table].answer(answer));
            return Ok(EnsureSuccess::AnswerAvailable);
        }

        // If no tabled answer is present, we ought to be requesting
        // the next available index.
        assert_eq!(self.tables[table].next_answer_index(), answer);

        // Next, check if the table is already active. If so, then we
        // have a recursive attempt.
        if let Some(depth) = self.stack.is_active(table) {
            info!("ensure_answer: cycle detected at depth {:?}", depth);

            if self.top_of_stack_is_coinductive_from(depth) {
                return Ok(EnsureSuccess::Coinductive);
            }

            return Err(RecursiveSearchFail::PositiveCycle(Minimums {
                positive: self.stack[depth].dfn,
                negative: DepthFirstNumber::MAX,
            }));
        }

        let dfn = self.next_dfn();
        let depth = self.stack.push(table, dfn);
        let result = crate::maybe_grow_stack(|| self.pursue_next_strand(context, depth));
        self.stack.pop(table, depth);
        info!("ensure_answer: result = {:?}", result);
        result.map(|()| EnsureSuccess::AnswerAvailable)
    }

    pub(crate) fn answer(&self, table: TableIndex, answer: AnswerIndex) -> &Answer<C> {
        self.tables[table].answer(answer).unwrap()
    }

    /// Selects the next eligible strand from the table at depth
    /// `depth` and pursues it. If that strand encounters a cycle,
    /// then this function will loop and keep trying strands until it
    /// reaches one that did not encounter a cycle; that result is
    /// propagated.  If all strands return a cycle, then the entire
    /// subtree is "completed" by invoking `cycle`.
    fn pursue_next_strand(
        &mut self,
        context: &impl ContextOps<C>,
        depth: StackIndex,
    ) -> RecursiveSearchResult<()> {
        // This is a bit complicated because this is where we handle cycles.
        let table = self.stack[depth].table;

        // Strands that encountered a cyclic error.
        let mut cyclic_strands = vec![];

        // The minimum of all cyclic strands.
        let mut cyclic_minimums = Minimums::MAX;

        loop {
            match self.tables[table].pop_next_strand() {
                Some(strand) => {
                    let result: StrandResult<C, ()> = self.pursue_strand(context, depth, strand);
                    match result {
                        Ok(answer) => {
                            // Now that we produced an answer, these
                            // cyclic strands need to be retried.
                            self.tables[table].extend_strands(cyclic_strands);
                            return Ok(answer);
                        }

                        Err(StrandFail::Floundered) => {
                            debug!("Marking table {:?} as floundered!", table);
                            self.tables[table].mark_floundered();
                            return Err(RecursiveSearchFail::Floundered);
                        }

                        Err(StrandFail::NoSolution) | Err(StrandFail::QuantumExceeded) => {
                            // This strand did not produce an answer,
                            // but either it (or some other, pending
                            // strands) may do so in the
                            // future. Enqueue the cyclic strands to
                            // be retried after that point.
                            self.tables[table].extend_strands(cyclic_strands);
                            return Err(RecursiveSearchFail::QuantumExceeded);
                        }

                        Err(StrandFail::NegativeCycle) => {
                            return Err(RecursiveSearchFail::NegativeCycle);
                        }

                        Err(StrandFail::PositiveCycle(strand, strand_minimums)) => {
                            // This strand encountered a cycle. Stash
                            // it for later and try the next one until
                            // we know that *all* available strands
                            // are hitting a cycle.
                            cyclic_strands.push(strand);
                            cyclic_minimums.take_minimums(&strand_minimums);
                        }
                    }
                }

                None => {
                    // No more strands left to try! That means either we started
                    // with no strands, or all available strands encountered a cycle.

                    if cyclic_strands.is_empty() {
                        // We started with no strands!
                        return Err(RecursiveSearchFail::NoMoreSolutions);
                    } else {
                        let c = mem::replace(&mut cyclic_strands, vec![]);
                        if let Some(err) = self.cycle(depth, c, cyclic_minimums) {
                            return Err(err);
                        }
                    }
                }
            }
        }
    }

    /// Invoked when all available strands for a table have
    /// encountered a cycle. In this case, the vector `strands` are
    /// the set of strands that encountered cycles, and `minimums` is
    /// the minimum stack depths that they were dependent on.
    ///
    /// Returns `None` if we have resolved the cycle and should try to
    /// pick a strand again. Returns `Some(_)` if the cycle indicates
    /// an error that we can propagate higher up.
    fn cycle(
        &mut self,
        depth: StackIndex,
        strands: Vec<Strand<C>>,
        minimums: Minimums,
    ) -> Option<RecursiveSearchFail> {
        let table = self.stack[depth].table;
        assert!(self.tables[table].pop_next_strand().is_none());

        let dfn = self.stack[depth].dfn;
        if minimums.positive == dfn && minimums.negative == DepthFirstNumber::MAX {
            // If all the things that we recursively depend on have
            // positive dependencies on things below us in the stack,
            // then no more answers are forthcoming. We can clear all
            // the strands for those things recursively.
            self.clear_strands_after_cycle(table, strands);
            Some(RecursiveSearchFail::NoMoreSolutions)
        } else if minimums.positive >= dfn && minimums.negative >= dfn {
            Some(RecursiveSearchFail::NegativeCycle)
        } else {
            self.tables[table].extend_strands(strands);
            Some(RecursiveSearchFail::PositiveCycle(minimums))
        }
    }

    /// Invoked after we have determined that every strand in `table`
    /// encounters a cycle; `strands` is the set of strands (which
    /// have been moved out of the table). This method then
    /// recursively clears the active strands from the tables
    /// referenced in `strands`, since all of them must encounter
    /// cycles too.
    fn clear_strands_after_cycle(
        &mut self,
        table: TableIndex,
        strands: impl IntoIterator<Item = Strand<C>>,
    ) {
        assert!(self.tables[table].pop_next_strand().is_none());
        for strand in strands {
            let Strand {
                mut infer,
                ex_clause,
                selected_subgoal,
            } = strand;
            let selected_subgoal = selected_subgoal.unwrap_or_else(|| {
                panic!(
                    "clear_strands_after_cycle invoked on strand in table {:?} \
                     without a selected subgoal: {:?}",
                    table,
                    infer.debug_ex_clause(&ex_clause),
                )
            });

            let strand_table = selected_subgoal.subgoal_table;
            let strands = self.tables[strand_table].take_strands();
            self.clear_strands_after_cycle(strand_table, strands);
        }
    }

    /// Pursues `strand` to see if it leads us to a new answer, either
    /// by selecting a new subgoal or by checking to see if the
    /// selected subgoal has an answer. `strand` is associated with
    /// the table on the stack at the given `depth`.
    fn pursue_strand(
        &mut self,
        context: &impl ContextOps<C>,
        depth: StackIndex,
        mut strand: Strand<C>,
    ) -> StrandResult<C, ()> {
        loop {
            info_heading!(
                "pursue_strand(table={:?}, depth={:?}, ex_clause={:#?}, selected_subgoal={:?})",
                self.stack[depth].table,
                depth,
                strand.infer.debug_ex_clause(&strand.ex_clause),
                strand.selected_subgoal,
            );

            // If no subgoal has yet been selected, select one.
            while strand.selected_subgoal.is_none() {
                if strand.ex_clause.subgoals.len() == 0 {
                    if strand.ex_clause.floundered_subgoals.is_empty() {
                        return self.pursue_answer(depth, strand);
                    }

                    self.reconsider_floundered_subgoals(&mut strand.ex_clause);

                    if strand.ex_clause.subgoals.is_empty() {
                        assert!(!strand.ex_clause.floundered_subgoals.is_empty());
                        return Err(StrandFail::Floundered);
                    }

                    continue;
                }

                let subgoal_index = strand.infer.next_subgoal_index(&strand.ex_clause);

                // Get or create table for this subgoal.
                match self.get_or_create_table_for_subgoal(
                    context,
                    &mut strand.infer,
                    &strand.ex_clause.subgoals[subgoal_index],
                ) {
                    Some((subgoal_table, universe_map)) => {
                        strand.selected_subgoal = Some(SelectedSubgoal {
                            subgoal_index,
                            subgoal_table,
                            universe_map,
                            answer_index: AnswerIndex::ZERO,
                        });
                    }

                    None => {
                        // If we failed to create a table for the subgoal,
                        // that is because we have a floundered negative
                        // literal.
                        self.flounder_subgoal(&mut strand.ex_clause, subgoal_index);
                        continue;
                    }
                }
            }

            // Find the selected subgoal and ask it for the next answer.
            let SelectedSubgoal {
                subgoal_index: _,
                subgoal_table,
                answer_index,
                universe_map: _,
            } = *strand.selected_subgoal.as_ref().unwrap();
            let recursive_search_result =
                self.ensure_answer_recursively(context, subgoal_table, answer_index);
            let incorporate_result = match strand.ex_clause.subgoals
                [strand.selected_subgoal.as_ref().unwrap().subgoal_index]
            {
                Literal::Positive(_) => self.incorporate_result_from_positive_subgoal(
                    depth,
                    &mut strand,
                    recursive_search_result,
                ),
                Literal::Negative(_) => self.incorporate_result_from_negative_subgoal(
                    depth,
                    &mut strand,
                    recursive_search_result,
                ),
            };

            match incorporate_result {
                Ok(_) => {}
                Err(RecursiveSearchFail::NoMoreSolutions) => {
                    return Err(StrandFail::NoSolution);
                }
                Err(RecursiveSearchFail::Floundered) => {
                    return Err(StrandFail::Floundered);
                }
                Err(RecursiveSearchFail::QuantumExceeded) => {
                    let table = self.stack[depth].table;
                    self.tables[table].push_strand(strand);
                    return Err(StrandFail::QuantumExceeded);
                }
                Err(RecursiveSearchFail::NegativeCycle) => {
                    return Err(StrandFail::NegativeCycle);
                }
                Err(RecursiveSearchFail::PositiveCycle(minimums)) => {
                    return Err(StrandFail::PositiveCycle(strand, minimums));
                }
            }
        }
    }

    /// Invoked when a strand represents an **answer**. This means
    /// that the strand has no subgoals left. There are two possibilities:
    ///
    /// - the strand may represent an answer we have already found; in
    ///   that case, we can return `StrandFail::NoSolution`, as this
    ///   strand led nowhere of interest.
    /// - the strand may represent a new answer, in which case it is
    ///   added to the table and `Ok` is returned.
    fn pursue_answer(&mut self, depth: StackIndex, strand: Strand<C>) -> StrandResult<C, ()> {
        let table = self.stack[depth].table;
        let Strand {
            mut infer,
            ex_clause:
                ExClause {
                    subst,
                    constraints,
                    ambiguous,
                    subgoals,
                    current_time: _,
                    floundered_subgoals,
                },
            selected_subgoal: _,
        } = strand;
        assert!(subgoals.is_empty());
        assert!(floundered_subgoals.is_empty());

        let answer_subst = infer.canonicalize_constrained_subst(subst, constraints);
        debug!("answer: table={:?}, answer_subst={:?}", table, answer_subst);

        let answer = Answer {
            subst: answer_subst,
            ambiguous: ambiguous,
        };

        // A "trivial" answer is one that is 'just true for all cases'
        // -- in other words, it gives no information back to the
        // caller. For example, `Vec<u32>: Sized` is "just true".
        // Such answers are important because they are the most
        // general case, and after we provide a trivial answer, no
        // further answers are useful -- therefore we can clear any
        // further pending strands (this is a "green cut", in
        // Prolog parlance).
        //
        // This optimization is *crucial* for performance: for
        // example, `projection_from_env_slow` fails miserably without
        // it. The reason is that we wind up (thanks to implied bounds)
        // with a clause like this:
        //
        // ```ignore
        // forall<T> { (<T as SliceExt>::Item: Clone) :- WF(T: SliceExt) }
        // ```
        //
        // we then apply that clause to `!1: Clone`, resulting in the
        // table goal `!1: Clone :- <?0 as SliceExt>::Item = !1,
        // WF(?0: SliceExt)`.  This causes us to **enumerate all types
        // `?0` that where `Slice<?0>` normalizes to `!1` -- this is
        // an infinite set of types, effectively. Interestingly,
        // though, we only need one and we are done, because (if you
        // look) our goal (`!1: Clone`) doesn't have any output
        // parameters.
        //
        // This is actually a kind of general case. Due to Rust's rule
        // about constrained impl type parameters, generally speaking
        // when we have some free inference variable (like `?0`)
        // within our clause, it must appear in the head of the
        // clause. This means that the values we create for it will
        // propagate up to the caller, and they will quickly surmise
        // that there is ambiguity and stop requesting more answers.
        // Indeed, the only exception to this rule about constrained
        // type parameters if with associated type projections, as in
        // the case above!
        //
        // (Actually, because of the trivial answer cut off rule, we
        // never even get to the point of asking the query above in
        // `projection_from_env_slow`.)
        //
        // However, there is one fly in the ointment: answers include
        // region constraints, and you might imagine that we could
        // find future answers that are also trivial but with distinct
        // sets of region constraints. **For this reason, we only
        // apply this green cut rule if the set of generated
        // constraints is empty.**
        //
        // The limitation on region constraints is quite a drag! We
        // can probably do better, though: for example, coherence
        // guarantees that, for any given set of types, only a single
        // impl ought to be applicable, and that impl can only impose
        // one set of region constraints. However, it's not quite that
        // simple, thanks to specialization as well as the possibility
        // of proving things from the environment (though the latter
        // is a *bit* suspect; e.g., those things in the environment
        // must be backed by an impl *eventually*).
        let is_trivial_answer = {
            !answer.ambiguous
                && C::is_trivial_substitution(&self.tables[table].table_goal, &answer.subst)
                && C::empty_constraints(&answer.subst)
        };

        if self.tables[table].push_answer(answer) {
            if is_trivial_answer {
                self.tables[table].take_strands();
            }

            Ok(())
        } else {
            info!("answer: not a new answer, returning StrandFail::NoSolution");
            Err(StrandFail::NoSolution)
        }
    }

    fn reconsider_floundered_subgoals(&mut self, ex_clause: &mut ExClause<impl Context>) {
        info!("reconsider_floundered_subgoals(ex_clause={:#?})", ex_clause,);
        let ExClause {
            current_time,
            subgoals,
            floundered_subgoals,
            ..
        } = ex_clause;
        for i in (0..floundered_subgoals.len()).rev() {
            if floundered_subgoals[i].floundered_time < *current_time {
                let floundered_subgoal = floundered_subgoals.swap_remove(i);
                subgoals.push(floundered_subgoal.floundered_literal);
            }
        }
    }

    /// Given a subgoal, converts the literal into u-canonical form
    /// and searches for an existing table. If one is found, it is
    /// returned, but otherwise a new table is created (and populated
    /// with its initial set of strands).
    ///
    /// Returns `None` if the literal cannot be converted into a table
    /// -- for example, this can occur when we have selected a
    /// negative literal with free existential variables, in which
    /// case the execution is said to "flounder".
    ///
    /// In terms of the NFTD paper, creating a new table corresponds
    /// to the *New Subgoal* step as well as the *Program Clause
    /// Resolution* steps.
    fn get_or_create_table_for_subgoal(
        &mut self,
        context: &impl ContextOps<C>,
        infer: &mut dyn InferenceTable<C>,
        subgoal: &Literal<C>,
    ) -> Option<(TableIndex, C::UniverseMap)> {
        debug_heading!("get_or_create_table_for_subgoal(subgoal={:?})", subgoal);

        // Subgoal abstraction:
        let (ucanonical_subgoal, universe_map) = match subgoal {
            Literal::Positive(subgoal) => self.abstract_positive_literal(infer, subgoal),
            Literal::Negative(subgoal) => self.abstract_negative_literal(infer, subgoal)?,
        };

        debug!("ucanonical_subgoal={:?}", ucanonical_subgoal);
        debug!("universe_map={:?}", universe_map);

        let table = self.get_or_create_table_for_ucanonical_goal(context, ucanonical_subgoal);

        Some((table, universe_map))
    }

    /// Given a u-canonical goal, searches for an existing table. If
    /// one is found, it is returned, but otherwise a new table is
    /// created (and populated with its initial set of strands).
    ///
    /// In terms of the NFTD paper, creating a new table corresponds
    /// to the *New Subgoal* step as well as the *Program Clause
    /// Resolution* steps.
    pub(crate) fn get_or_create_table_for_ucanonical_goal(
        &mut self,
        context: &impl ContextOps<C>,
        goal: C::UCanonicalGoalInEnvironment,
    ) -> TableIndex {
        debug_heading!("get_or_create_table_for_ucanonical_goal({:?})", goal);

        if let Some(table) = self.tables.index_of(&goal) {
            debug!("found existing table {:?}", table);
            return table;
        }

        info_heading!(
            "creating new table {:?} and goal {:#?}",
            self.tables.next_index(),
            goal
        );
        let coinductive_goal = context.is_coinductive(&goal);
        let table = self.tables.insert(goal, coinductive_goal);
        self.push_initial_strands(context, table);
        table
    }

    /// When a table is first created, this function is invoked to
    /// create the initial set of strands. If the table represents a
    /// domain goal, these strands are created from the program
    /// clauses as well as the clauses found in the environment.  If
    /// the table represents a non-domain goal, such as `for<T> G`
    /// etc, then `simplify_hh_goal` is invoked to create a strand
    /// that breaks the goal down.
    ///
    /// In terms of the NFTD paper, this corresponds to the *Program
    /// Clause Resolution* step being applied eagerly, as many times
    /// as possible.
    fn push_initial_strands(&mut self, context: &impl ContextOps<C>, table: TableIndex) {
        // Instantiate the table goal with fresh inference variables.
        let table_goal = self.tables[table].table_goal.clone();
        context.instantiate_ucanonical_goal(&table_goal, |infer, subst, environment, goal| {
            self.push_initial_strands_instantiated(context, table, infer, subst, environment, goal);
        });
    }

    fn push_initial_strands_instantiated(
        &mut self,
        context: &impl ContextOps<C>,
        table: TableIndex,
        mut infer: C::InferenceTable,
        subst: C::Substitution,
        environment: C::Environment,
        goal: C::Goal,
    ) {
        let table_ref = &mut self.tables[table];
        match infer.into_hh_goal(goal) {
            HhGoal::DomainGoal(domain_goal) => {
                match context.program_clauses(&environment, &domain_goal, &mut infer) {
                    Ok(clauses) => {
                        for clause in clauses {
                            info!("program clause = {:#?}", clause);
                            let mut infer = infer.clone();
                            if let Ok(resolvent) =
                                infer.resolvent_clause(&environment, &domain_goal, &subst, &clause)
                            {
                                info!("pushing initial strand with ex-clause: {:#?}", &resolvent,);
                                let strand = Strand {
                                    infer,
                                    ex_clause: resolvent,
                                    selected_subgoal: None,
                                };
                                table_ref.push_strand(strand);
                            }
                        }
                    }
                    Err(Floundered) => {
                        debug!("Marking table {:?} as floundered!", table);
                        table_ref.mark_floundered();
                    }
                }
            }

            hh_goal => {
                // `canonical_goal` is an HH goal. We can simplify it
                // into a series of *literals*, all of which must be
                // true. Thus, in EWFS terms, we are effectively
                // creating a single child of the `A :- A` goal that
                // is like `A :- B, C, D` where B, C, and D are the
                // simplified subgoals. You can think of this as
                // applying built-in "meta program clauses" that
                // reduce HH goals into Domain goals.
                if let Ok(ex_clause) =
                    Self::simplify_hh_goal(&mut infer, subst, environment, hh_goal)
                {
                    info!(
                        "pushing initial strand with ex-clause: {:#?}",
                        infer.debug_ex_clause(&ex_clause),
                    );
                    let strand = Strand {
                        infer,
                        ex_clause,
                        selected_subgoal: None,
                    };
                    table_ref.push_strand(strand);
                }
            }
        }
    }

    /// Given a selected positive subgoal, applies the subgoal
    /// abstraction function to yield the canonical form that will be
    /// used to pick a table. Typically, this abstraction has no
    /// effect, and hence we are simply returning the canonical form
    /// of `subgoal`, but if the subgoal is getting too big, we may
    /// truncate the goal to ensure termination.
    ///
    /// This technique is described in the SA paper.
    fn abstract_positive_literal(
        &mut self,
        infer: &mut dyn InferenceTable<C>,
        subgoal: &C::GoalInEnvironment,
    ) -> (C::UCanonicalGoalInEnvironment, C::UniverseMap) {
        // Subgoal abstraction: Rather than looking up the table for
        // `selected_goal` directly, first apply the truncation
        // function. This may introduce fresh variables, making the
        // goal that we are looking up more general, and forcing us to
        // reuse an existing table. For example, if we had a selected
        // goal of
        //
        //     // Vec<Vec<Vec<Vec<i32>>>>: Sized
        //
        // we might now produce a truncated goal of
        //
        //     // Vec<Vec<?T>>: Sized
        //
        // Obviously, the answer we are looking for -- if it exists -- will be
        // found amongst the answers of this new, truncated goal.
        //
        // Subtle point: Note that the **selected goal** remains
        // unchanged and will be carried over into the "pending
        // clause" for the positive link on the new subgoal. This
        // means that if our new, truncated subgoal produces
        // irrelevant answers (e.g., `Vec<Vec<u32>>: Sized`), they
        // will fail to unify with our selected goal, producing no
        // resolvent.
        match infer.truncate_goal(subgoal) {
            None => infer.fully_canonicalize_goal(subgoal),
            Some(truncated_subgoal) => {
                debug!("truncated={:?}", truncated_subgoal);
                infer.fully_canonicalize_goal(&truncated_subgoal)
            }
        }
    }

    /// Given a selected negative subgoal, the subgoal is "inverted"
    /// (see `InferenceTable<C>::invert`) and then potentially truncated
    /// (see `abstract_positive_literal`). The result subgoal is
    /// canonicalized. In some cases, this may return `None` and hence
    /// fail to yield a useful result, for example if free existential
    /// variables appear in `subgoal` (in which case the execution is
    /// said to "flounder").
    fn abstract_negative_literal(
        &mut self,
        infer: &mut dyn InferenceTable<C>,
        subgoal: &C::GoalInEnvironment,
    ) -> Option<(C::UCanonicalGoalInEnvironment, C::UniverseMap)> {
        // First, we have to check that the selected negative literal
        // is ground, and invert any universally quantified variables.
        //
        // DIVERGENCE -- In the RR paper, to ensure completeness, they
        // permit non-ground negative literals, but only consider
        // them to succeed when the target table has no answers at
        // all. This is equivalent inverting those free existentials
        // into universals, as discussed in the comments of
        // `invert`. This is clearly *sound*, but the completeness is
        // a subtle point. In particular, it can cause **us** to reach
        // false conclusions, because e.g. given a program like
        // (selected left-to-right):
        //
        //     not { ?T: Copy }, ?T = Vec<u32>
        //
        // we would select `not { ?T: Copy }` first. For this goal to
        // succeed we would require that -- effectively -- `forall<T>
        // { not { T: Copy } }`, which clearly doesn't hold. (In the
        // terms of RR, we would require that the table for `?T: Copy`
        // has failed before we can continue.)
        //
        // In the RR paper, this is acceptable because they assume all
        // of their input programs are both **normal** (negative
        // literals are selected after positive ones) and **safe**
        // (all free variables in negative literals occur in positive
        // literals). It is plausible for us to guarantee "normal"
        // form, we can reorder clauses as we need. I suspect we can
        // guarantee safety too, but I have to think about it.
        //
        // For now, we opt for the safer route of terming such
        // executions as floundering, because I think our use of
        // negative goals is sufficiently limited we can get away with
        // it. The practical effect is that we will judge more
        // executions as floundering than we ought to (i.e., where we
        // could instead generate an (imprecise) result). As you can
        // see a bit later, we also diverge in some other aspects that
        // affect completeness when it comes to subgoal abstraction.
        let inverted_subgoal = infer.invert_goal(subgoal)?;

        // DIVERGENCE
        //
        // If the negative subgoal has grown so large that we would have
        // to truncate it, we currently just abort the computation
        // entirely. This is not necessary -- the SA paper makes no
        // such distinction, for example, and applies truncation equally
        // for positive/negative literals. However, there are some complications
        // that arise that I do not wish to deal with right now.
        //
        // Let's work through an example to show you what I
        // mean. Imagine we have this (negative) selected literal;
        // hence `selected_subgoal` will just be the inner part:
        //
        //     // not { Vec<Vec<Vec<Vec<i32>>>>: Sized }
        //     //       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        //     //       `selected_goal`
        //
        // (In this case, the `inverted_subgoal` would be the same,
        // since there are no free universal variables.)
        //
        // If truncation **doesn't apply**, we would go and lookup the
        // table for the selected goal (`Vec<Vec<..>>: Sized`) and see
        // whether it has any answers. If it does, and they are
        // definite, then this negative literal is false. We don't
        // really care even how many answers there are and so forth
        // (if the goal is ground, as in this case, there can be at
        // most one definite answer, but if there are universals, then
        // the inverted goal would have variables; even so, a single
        // definite answer suffices to show that the `not { .. }` goal
        // is false).
        //
        // Truncation muddies the water, because the table may
        // generate answers that are not relevant to our original,
        // untruncated literal.  Suppose that we truncate the selected
        // goal to:
        //
        //     // Vec<Vec<T>: Sized
        //
        // Clearly this table will have some solutions that don't
        // apply to us.  e.g., `Vec<Vec<u32>>: Sized` is a solution to
        // this table, but that doesn't imply that `not {
        // Vec<Vec<Vec<..>>>: Sized }` is false.
        //
        // This can be made to work -- we carry along the original
        // selected goal when we establish links between tables, and
        // we could use that to screen the resulting answers. (There
        // are some further complications around the fact that
        // selected goal may contain universally quantified free
        // variables that have been inverted, as discussed in the
        // prior paragraph above.) I just didn't feel like dealing
        // with it yet.
        match infer.truncate_goal(&inverted_subgoal) {
            Some(_) => None,
            None => Some(infer.fully_canonicalize_goal(&inverted_subgoal)),
        }
    }

    /// Invoked when we have selected a positive literal, created its
    /// table, and selected a particular answer index N we are looking
    /// for. Searches for that answer. If we find one, we can do two things:
    ///
    /// - create a new strand with the same selected subgoal, but searching for the
    ///   answer with index N+1
    /// - use the answer to resolve our selected literal and select the next subgoal
    ///   in this strand to pursue
    ///
    /// When an answer is found, that corresponds to *Positive Return*
    /// from the NFTD paper.
    fn incorporate_result_from_positive_subgoal(
        &mut self,
        depth: StackIndex,
        strand: &mut Strand<C>,
        recursive_search_result: RecursiveSearchResult<EnsureSuccess>,
    ) -> RecursiveSearchResult<()> {
        let selected_subgoal = strand.selected_subgoal.as_ref().unwrap();
        let SelectedSubgoal {
            subgoal_index,
            subgoal_table,
            answer_index,
            ref universe_map,
        } = *selected_subgoal;

        match recursive_search_result {
            Ok(EnsureSuccess::AnswerAvailable) => {
                // Whichever way this particular answer turns out, there may
                // yet be *more* answers. Enqueue that alternative for later.
                let mut next_subgoal = selected_subgoal.clone();
                next_subgoal.answer_index.increment();
                let table = self.stack[depth].table;
                let next_strand = Strand {
                    infer: strand.infer.clone(),
                    ex_clause: strand.ex_clause.clone(),
                    selected_subgoal: Some(next_subgoal),
                };
                self.tables[table].push_strand(next_strand);

                // OK, let's follow *this* answer and see where it leads.
                let subgoal = match strand.ex_clause.subgoals.remove(subgoal_index) {
                    Literal::Positive(g) => g,
                    Literal::Negative(g) => panic!(
                        "incorporate_result_from_positive_subgoal invoked with negative selected literal: {:?}",
                        g
                    ),
                };

                let table_goal = &C::map_goal_from_canonical(
                    &universe_map,
                    &C::canonical(&self.tables[subgoal_table].table_goal),
                );
                let answer_subst = &C::map_subst_from_canonical(
                    &universe_map,
                    &self.answer(subgoal_table, answer_index).subst,
                );
                match strand.infer.apply_answer_subst(
                    &mut strand.ex_clause,
                    &subgoal,
                    table_goal,
                    answer_subst,
                ) {
                    Ok(()) => {
                        let Strand {
                            infer,
                            ex_clause,
                            selected_subgoal: _,
                        } = strand;

                        // If the answer had delayed literals, we have to
                        // ensure that `ex_clause` is also delayed. This is
                        // the SLG FACTOR operation, though NFTD just makes it
                        // part of computing the SLG resolvent.
                        {
                            let answer = self.answer(subgoal_table, answer_index);
                            if answer.ambiguous {
                                ex_clause.ambiguous = true;
                            }
                        }

                        // Increment time counter because we received a new answer.
                        ex_clause.current_time.increment();

                        // Apply answer abstraction.
                        self.truncate_returned(ex_clause, infer);

                        strand.selected_subgoal = None;
                        return Ok(());
                    }

                    // This answer led nowhere. Give up for now, but of course
                    // there may still be other strands to pursue, so return
                    // `QuantumExceeded`.
                    Err(NoSolution) => {
                        info!("incorporate_result_from_positive_subgoal: answer not unifiable -> NoSolution");
                        Err(RecursiveSearchFail::NoMoreSolutions)
                    }
                }
            }
            Ok(EnsureSuccess::Coinductive) => {
                // This is a co-inductive cycle. That is, this table
                // appears somewhere higher on the stack, and has now
                // recursively requested an answer for itself. That
                // means that our subgoal is unconditionally true, so
                // we can drop it and pursue the next thing.
                let table = self.stack[depth].table;
                assert!(
                    self.tables[table].coinductive_goal
                        && self.tables[subgoal_table].coinductive_goal
                );
                strand.ex_clause.subgoals.remove(subgoal_index);
                strand.selected_subgoal = None;
                return Ok(());
            }
            Err(RecursiveSearchFail::NoMoreSolutions) => {
                info!("incorporate_result_from_positive_subgoal: no more solutions");
                return Err(RecursiveSearchFail::NoMoreSolutions);
            }
            Err(RecursiveSearchFail::Floundered) => {
                // If this subgoal floundered, push it onto the
                // floundered list, along with the time that it
                // floundered. We'll try to solve some other subgoals
                // and maybe come back to it.
                info!("incorporate_result_from_positive_subgoal: floundered");
                self.flounder_subgoal(&mut strand.ex_clause, subgoal_index);
                strand.selected_subgoal = None;
                return Err(RecursiveSearchFail::QuantumExceeded);
            }
            Err(RecursiveSearchFail::QuantumExceeded) => {
                // We'll have to revisit this strand later
                info!("incorporate_result_from_positive_subgoal: quantum exceeded");
                return Err(RecursiveSearchFail::QuantumExceeded);
            }
            Err(RecursiveSearchFail::NegativeCycle) => {
                info!("negative cycle detected");
                return Err(RecursiveSearchFail::NegativeCycle);
            }
            Err(RecursiveSearchFail::PositiveCycle(minimums)) => {
                info!(
                    "incorporate_result_from_positive_subgoal: cycle with minimums {:?}",
                    minimums
                );
                return Err(RecursiveSearchFail::PositiveCycle(minimums));
            }
        }
    }

    fn incorporate_result_from_negative_subgoal(
        &mut self,
        depth: StackIndex,
        strand: &mut Strand<C>,
        recursive_search_result: RecursiveSearchResult<EnsureSuccess>,
    ) -> RecursiveSearchResult<()> {
        let selected_subgoal = strand.selected_subgoal.as_ref().unwrap();
        let SelectedSubgoal {
            subgoal_index: _,
            subgoal_table,
            answer_index,
            universe_map: _,
        } = *selected_subgoal;

        // In the match below, we will either (a) return early with an
        // error or some kind or (b) continue on to pursue this strand
        // further. We continue onward in the case where we either
        // proved that `answer_index` does not exist (in which case
        // the negative literal is true) or if we found an ambiguous answer.
        match recursive_search_result {
            Ok(EnsureSuccess::AnswerAvailable) => {
                if self.answer(subgoal_table, answer_index).is_unconditional() {
                    // We want to disproval the subgoal, but we
                    // have an unconditional answer for the subgoal,
                    // therefore we have failed to disprove it.
                    info!("incorporate_result_from_negative_subgoal: found unconditional answer to neg literal -> NoSolution");
                    return Err(RecursiveSearchFail::NoMoreSolutions);
                }

                // Got back a conditional answer. We neither succeed
                // nor fail yet, so just mark as ambiguous.
                //
                // This corresponds to the Delaying action in NFTD.
                // It also interesting to compare this with the EWFS
                // paper; there, when we encounter a delayed cached
                // answer in `negative_subgoal`, we do not immediately
                // convert to a delayed literal, but instead simply
                // stop. However, in EWFS, we *do* add the strand to
                // the table as a negative pending subgoal, and also
                // update the link to depend negatively on the
                // table. Then later, when all pending work from that
                // table is completed, all negative links are
                // converted to delays.
                //
                // Previously, this introduced a `delayed_literal` that
                // we could follow and potentially resolve later. However,
                // for simplicity, we now just mark the strand as ambiguous.
                strand
                    .ex_clause
                    .subgoals
                    .remove(selected_subgoal.subgoal_index);
                strand.selected_subgoal = None;
                strand.ex_clause.ambiguous = true;
                return Ok(());
            }

            Ok(EnsureSuccess::Coinductive) => {
                // This is a co-inductive cycle. That is, this table
                // appears somewhere higher on the stack, and has now
                // recursively requested an answer for itself. That
                // means that our subgoal is unconditionally true, so
                // our negative goal fails.
                info!("incorporate_result_from_negative_subgoal: found coinductive answer to neg literal -> NoSolution");
                return Err(RecursiveSearchFail::NoMoreSolutions);
            }

            Err(RecursiveSearchFail::Floundered) => {
                // Floundering on a negative literal isn't like a
                // positive search: we only pursue negative literals
                // when we already know precisely the type we are
                // looking for. So there's no point waiting for other
                // subgoals, we'll never recover more information.
                //
                // In fact, floundering on negative searches shouldn't
                // normally happen, since there are no uninferred
                // variables in the goal, but it can with forall
                // goals:
                //
                //     forall<T> { not { T: Debug } }
                //
                // Here, the table we will be searching for answers is
                // `?T: Debug`, so it could well flounder.
                return Err(RecursiveSearchFail::Floundered);
            }

            Err(RecursiveSearchFail::NegativeCycle) => {
                return Err(RecursiveSearchFail::NegativeCycle);
            }

            Err(RecursiveSearchFail::PositiveCycle(minimums)) => {
                // We depend on `not(subgoal)`. For us to continue,
                // `subgoal` must be completely evaluated. Therefore,
                // we depend (negatively) on the minimum link of
                // `subgoal` as a whole -- it doesn't matter whether
                // it's pos or neg.
                let min = minimums.minimum_of_pos_and_neg();
                info!(
                    "incorporate_result_from_negative_subgoal: found neg cycle at depth {:?}",
                    min
                );
                return Err(RecursiveSearchFail::PositiveCycle(Minimums {
                    positive: self.stack[depth].dfn,
                    negative: min,
                }));
            }

            Err(RecursiveSearchFail::NoMoreSolutions) => {
                // This answer does not exist. Huzzah, happy days are
                // here again! =) We can just remove this subgoal and continue
                // with no need for a delayed literal.
                strand
                    .ex_clause
                    .subgoals
                    .remove(selected_subgoal.subgoal_index);
                strand.selected_subgoal = None;
                return Ok(());
            }

            // Learned nothing yet. Have to try again some other time.
            Err(RecursiveSearchFail::QuantumExceeded) => {
                info!("incorporate_result_from_negative_subgoal: quantum exceeded");
                return Err(RecursiveSearchFail::QuantumExceeded);
            }
        }
    }

    /// Removes the subgoal at `subgoal_index` from the strand's
    /// subgoal list and adds it to the strand's floundered subgoal
    /// list.
    fn flounder_subgoal(&self, ex_clause: &mut ExClause<impl Context>, subgoal_index: usize) {
        info_heading!(
            "flounder_subgoal(current_time={:?}, subgoal={:?})",
            ex_clause.current_time,
            ex_clause.subgoals[subgoal_index],
        );
        let floundered_time = ex_clause.current_time;
        let floundered_literal = ex_clause.subgoals.remove(subgoal_index);
        ex_clause.floundered_subgoals.push(FlounderedSubgoal {
            floundered_literal,
            floundered_time,
        });
        debug!("flounder_subgoal: ex_clause={:#?}", ex_clause);
    }

    /// Used whenever we process an answer (whether new or cached) on
    /// a positive edge (the SLG POSITIVE RETURN operation). Truncates
    /// the resolvent (or factor) if it has grown too large.
    fn truncate_returned(&self, ex_clause: &mut ExClause<C>, infer: &mut dyn InferenceTable<C>) {
        // DIVERGENCE
        //
        // In the original RR paper, truncation is only applied
        // when the result of resolution is a new answer (i.e.,
        // `ex_clause.subgoals.is_empty()`).  I've chosen to be
        // more aggressive here, precisely because or our extended
        // semantics for unification. In particular, unification
        // can insert new goals, so I fear that positive feedback
        // loops could still run indefinitely in the original
        // formulation. I would like to revise our unification
        // mechanism to avoid that problem, in which case this could
        // be tightened up to be more like the original RR paper.
        //
        // Still, I *believe* this more aggressive approx. should
        // not interfere with any of the properties of the
        // original paper. In particular, applying truncation only
        // when the resolvent has no subgoals seems like it is
        // aimed at giving us more times to eliminate this
        // ambiguous answer.

        match infer.truncate_answer(&ex_clause.subst) {
            // No need to truncate
            None => {}

            // Resolvent got too large. Have to introduce approximation.
            Some(truncated_subst) => {
                mem::replace(
                    ex_clause,
                    ExClause {
                        subst: truncated_subst,
                        ambiguous: true,
                        constraints: vec![],
                        subgoals: vec![],
                        current_time: TimeStamp::default(),
                        floundered_subgoals: vec![],
                    },
                );
            }
        }
    }
}
