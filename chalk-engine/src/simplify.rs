use crate::context::{Context, ContextOps, UnificationOps};
use crate::strand::Strand;
use crate::fallible::Fallible;
use crate::forest::Forest;
use crate::hh::HhGoal;
use crate::{ExClause, Literal, TimeStamp};

impl<C: Context> Forest<C> {
    /// Simplifies an HH goal into a series of positive domain goals
    /// and negative HH goals. This operation may fail if the HH goal
    /// includes unifications that cannot be completed.
    pub(super) fn simplify_hh_goal(
        context: &impl ContextOps<C>,
        mut infer: C::InferenceTable,
        subst: C::Substitution,
        initial_environment: C::Environment,
        initial_hh_goal: HhGoal<C>,
    ) -> Fallible<Strand<C>> {
        let mut ex_clause = ExClause {
            subst,
            ambiguous: false,
            constraints: vec![],
            subgoals: vec![],
            delayed_subgoals: vec![],
            answer_time: TimeStamp::default(),
            floundered_subgoals: vec![],
        };

        // A stack of higher-level goals to process.
        let mut pending_goals = vec![(initial_environment, initial_hh_goal)];

        while let Some((environment, hh_goal)) = pending_goals.pop() {
            match hh_goal {
                HhGoal::ForAll(subgoal) => {
                    let subgoal =
                        infer.instantiate_binders_universally(context.interner(), &subgoal);
                    pending_goals.push((environment, context.into_hh_goal(subgoal)));
                }
                HhGoal::Exists(subgoal) => {
                    let subgoal =
                        infer.instantiate_binders_existentially(context.interner(), &subgoal);
                    pending_goals.push((environment, context.into_hh_goal(subgoal)))
                }
                HhGoal::Implies(wc, subgoal) => {
                    let new_environment = context.add_clauses(&environment, wc);
                    pending_goals.push((new_environment, context.into_hh_goal(subgoal)));
                }
                HhGoal::All(subgoals) => {
                    for subgoal in subgoals {
                        pending_goals.push((environment.clone(), context.into_hh_goal(subgoal)));
                    }
                }
                HhGoal::Not(subgoal) => {
                    ex_clause
                        .subgoals
                        .push(Literal::Negative(C::goal_in_environment(
                            &environment,
                            subgoal,
                        )));
                }
                HhGoal::Unify(variance, a, b) => infer.unify_parameters_into_ex_clause(
                    context.interner(),
                    &environment,
                    variance,
                    &a,
                    &b,
                    &mut ex_clause,
                )?,
                HhGoal::DomainGoal(domain_goal) => {
                    /*
                    match context.program_clauses(&environment, &domain_goal, &mut infer) {
                        Ok(clauses) => {
                            for clause in clauses {
                                info!("program clause = {:#?}", clause);
                                let mut infer = infer.clone();
                                if let Ok(resolvent) = infer.resolvent_clause(
                                    context.interner(),
                                    &environment,
                                    &domain_goal,
                                    &subst,
                                    &clause,
                                ) {
                                    info!("pushing initial strand with ex-clause: {:#?}", &resolvent,);
                                    let strand = Strand {
                                        infer,
                                        ex_clause: resolvent,
                                        selected_subgoal: None,
                                        last_pursued_time: TimeStamp::default(),
                                    };
                                    let canonical_strand = Self::canonicalize_strand(context, strand);
                                    table_ref.enqueue_strand(canonical_strand);
                                }
                            }
                        }
                        Err(Floundered) => {
                            debug!("Marking table {:?} as floundered!", table);
                            table_ref.mark_floundered();
                        }
                    }
                    */

                    context.add_goal_to_ex_clause(&mut ex_clause, &environment, domain_goal);
                }
                HhGoal::CannotProve => {
                    ex_clause.ambiguous = true;
                }
            }
        }

        let strand = Strand {
            infer,
            ex_clause,
            selected_subgoal: None,
            last_pursued_time: TimeStamp::default(),
        };

        Ok(strand)
    }
}
