use crate::context::{self, AnswerResult};
use crate::slg::SlgContextOps;
use crate::slg::SubstitutionExt;
use crate::CompleteAnswer;
use chalk_ir::cast::Cast;
use chalk_ir::interner::Interner;
use chalk_ir::*;
use chalk_solve::ext::*;
use chalk_solve::infer::{InferenceTable, alias_egraph};
use chalk_solve::infer::alias_egraph::Egraph;
use chalk_solve::solve::{Guidance, Solution};
use rustc_hash::FxHashMap;

use ena::unify::{UnifyKey, UnifyValue};
use std::fmt::Debug;
use std::marker::PhantomData;

/// Methods for combining solutions to yield an aggregate solution.
pub trait AggregateOps<I: Interner> {
    fn make_solution(
        &self,
        root_goal: &UCanonical<InEnvironment<Goal<I>>>,
        answers: impl context::AnswerStream<I>,
        should_continue: impl std::ops::Fn() -> bool,
    ) -> Option<Solution<I>>;
}

/// Draws as many answers as it needs from `answers` (but
/// no more!) in order to come up with a solution.
impl<I: Interner> AggregateOps<I> for SlgContextOps<'_, I> {
    fn make_solution(
        &self,
        root_goal: &UCanonical<InEnvironment<Goal<I>>>,
        mut answers: impl context::AnswerStream<I>,
        should_continue: impl std::ops::Fn() -> bool,
    ) -> Option<Solution<I>> {
        let interner = self.program.interner();
        let CompleteAnswer {
            mut subst,
            ambiguous,
        } = match answers.next_answer(&should_continue) {
            AnswerResult::NoMoreSolutions => {
                // No answers at all
                return None;
            }
            AnswerResult::Floundered => return Some(Solution::Ambig(Guidance::Unknown)),
            AnswerResult::QuantumExceeded => {
                return Some(Solution::Ambig(Guidance::Unknown));
            }
            AnswerResult::Answer(answer) => answer,
        };

        // Otherwise, we either have >1 answer, or else we have
        // ambiguity.  Either way, we are only going to be giving back
        // **guidance**, and with guidance, the caller doesn't get
        // back any region constraints. So drop them from our `subst`
        // variable.
        //
        // FIXME-- there is actually a 3rd possibility. We could have
        // >1 answer where all the answers have the same substitution,
        // but different region constraints. We should collapse those
        // cases into an `OR` region constraint at some point, but I
        // leave that for future work. This is basically
        // rust-lang/rust#21974.
        //let mut subst = subst.clone().map(interner, |cs| cs.subst);

        // Extract answers and merge them into `subst`. Stop once we have
        // a trivial subst (or run out of answers).

        // Track the number of answers and the number of solutions separately.
        // Answers may be different but ultimately result in a single solution.
        // This currently only applies for aliases, but may apply for e.g.
        // region constraints in the future.
        let mut num_answers = 1;
        let mut num_solutions = 1;
        let solution = loop {
            dbg!(&subst);
            if num_solutions > 1
                && is_trivial(interner, &subst)
            {
                break Some(Solution::Ambig(Guidance::Unknown));
            }

            let next_answer = answers.peek_answer(&should_continue);
            dbg!(&next_answer);
            match next_answer {
                AnswerResult::QuantumExceeded => {
                    break if subst.value.subst.is_identity_subst(interner) {
                        Some(Solution::Ambig(Guidance::Unknown))
                    } else {
                        Some(Solution::Ambig(Guidance::Suggested(
                            subst.clone().map(interner, |cs| cs.subst),
                        )))
                    };
                }
                AnswerResult::Floundered => return Some(Solution::Ambig(Guidance::Unknown)),
                AnswerResult::NoMoreSolutions => {
                    //dbg!(num_answers, num_solutions, ambiguous);
                    break if num_solutions == 1 && !ambiguous {
                        Some(Solution::Unique(subst))
                    } else {
                        Some(Solution::Ambig(Guidance::Definite(
                            subst.clone().map(interner, |cs| cs.subst),
                        )))
                    };
                }
                AnswerResult::Answer(next_answer) => {
                    num_answers += 1;
                    if let Some(expected_answers) = self.expected_answers {
                        if num_answers >= expected_answers {
                            panic!("Too many answers for solution.");
                        }
                    }

                    let new_solution;
                    (subst, new_solution) = merge_into_guidance(
                        interner,
                        &root_goal.canonical,
                        subst,
                        &next_answer.subst,
                    );

                    dbg!(&subst, &new_solution);

                    if new_solution {
                        num_solutions += 1;
                        if !answers.any_future_answer(|new_subst, alias_egraph | {
                            new_subst.may_invalidate(
                                interner,
                                &subst.clone().map(interner, |cs| cs.subst),
                                alias_egraph,
                            )
                        }) {
                            break Some(Solution::Ambig(Guidance::Definite(
                                subst.clone().map(interner, |cs| cs.subst),
                            )));
                        }
                    }
                }
            }
        };

        /*
                // Exactly 1 unconditional answer?
                let next_answer = answers.peek_answer(&should_continue);
                if next_answer.is_quantum_exceeded() {
                    return if subst.value.subst.is_identity_subst(interner) {
                        Some(Solution::Ambig(Guidance::Unknown))
                    } else {
                        Some(Solution::Ambig(Guidance::Suggested(
                            subst.clone().map(interner, |cs| cs.subst),
                        )))
                    };
                }
                if next_answer.is_no_more_solutions() && !ambiguous {
                    return Some(Solution::Unique(subst));
                }

                // Extract answers and merge them into `subst`. Stop once we have
                // a trivial subst (or run out of answers).
                let mut num_answers = 1;
                let guidance = loop {
                    if is_trivial(interner, &subst) {
                        break Guidance::Unknown;
                    }

                    if !answers
                        .any_future_answer(|ref mut new_subst| new_subst.may_invalidate(interner, &subst))
                    {
                        break Guidance::Definite(subst);
                    }

                    if let Some(expected_answers) = self.expected_answers {
                        if num_answers >= expected_answers {
                            panic!("Too many answers for solution.");
                        }
                    }

                    let new_subst = match answers.next_answer(&should_continue) {
                        AnswerResult::Answer(answer1) => answer1.subst,
                        AnswerResult::Floundered => return Some(Solution::Ambig(Guidance::Unknown)),
                        AnswerResult::NoMoreSolutions => {
                            break Guidance::Definite(subst);
                        }
                        AnswerResult::QuantumExceeded => {
                            break Guidance::Suggested(subst);
                        }
                    };
                    subst = merge_into_guidance(interner, &root_goal.canonical, subst, &new_subst);
                    num_answers += 1;
                };
        */

        if let Some(expected_answers) = self.expected_answers {
            assert_eq!(
                expected_answers, num_answers,
                "Not enough answers for solution."
            );
        }

        solution
    }
}

/// Given a current substitution used as guidance for `root_goal`, and
/// a new possible answer to `root_goal`, returns a new set of
/// guidance that encompasses both of them. This is often more general
/// than the old guidance. For example, if we had a guidance of `?0 =
/// u32` and the new answer is `?0 = i32`, then the guidance would
/// become `?0 = ?X` (where `?X` is some fresh variable).
fn merge_into_guidance<I: Interner>(
    interner: I,
    root_goal: &Canonical<InEnvironment<Goal<I>>>,
    guidance: Canonical<ConstrainedSubst<I>>,
    answer: &Canonical<ConstrainedSubst<I>>,
) -> (Canonical<ConstrainedSubst<I>>, bool) {
    let (mut infer, _, guidance_) = InferenceTable::from_canonical(interner, 1, guidance.clone());
    let (_, _, answer) = InferenceTable::from_canonical(interner, 1, answer.clone());
    let ConstrainedSubst {
        subst: subst1,
        constraints: _,
        alias_egraph,
    } = answer;

    let mut egraph = Egraph::from_constraints(interner, &mut infer, guidance_.alias_egraph).unwrap();

    // Collect the types that the two substitutions have in
    // common.
    let aggr_generic_args: Vec<_> = guidance
        .value
        .subst
        .iter(interner)
        .zip(subst1.iter(interner))
        .enumerate()
        .map(|(index, (p1, p2))| {
            // We have two values for some variable X that
            // appears in the root goal. Find out the universe
            // of X.
            let universe = *root_goal.binders.as_slice(interner)[index].skip_kind();

            match p1.data(interner) {
                GenericArgData::Ty(_) => (),
                GenericArgData::Lifetime(_) => {
                    // Ignore the lifetimes from the substitution: we're just
                    // creating guidance here anyway.
                    return infer
                        .new_variable(universe)
                        .to_lifetime(interner)
                        .cast(interner);
                }
                GenericArgData::Const(_) => (),
            };

            // Combine the two types into a new type.
            let mut aggr = AntiUnifier {
                infer: &mut infer,
                universe,
                interner,
                egraph: &mut egraph,
            };
            aggr.aggregate_generic_args(p1, p2)
        })
        .collect();

    let aggr_subst = Substitution::from_iter(interner, aggr_generic_args);

    egraph.register_egraph(interner, &mut infer, alias_egraph.clone()).unwrap();
    let alias_egraph = egraph.alias_egraph(interner);
    let aggr_subst = ConstrainedSubst {
        subst: aggr_subst,
        // FIXME: if this is one solution, we need to keep the existing constraints
        constraints: Constraints::empty(interner),
        alias_egraph,
    };
    dbg!(&aggr_subst);
    (infer.canonicalize(interner, aggr_subst).quantified, true)
}

fn is_trivial<I: Interner>(interner: I, subst: &Canonical<ConstrainedSubst<I>>) -> bool {
    // The subst is trivial if...

    // ...for the substition...
    let trivial_substition = subst
        .value
        .subst
        .iter(interner)
        .enumerate()
        .all(|(index, parameter)| {
            let is_trivial = |b: Option<BoundVar>| match b {
                None => false,
                Some(bound_var) => {
                    if let Some(index1) = bound_var.index_if_innermost() {
                        index == index1
                    } else {
                        false
                    }
                }
            };

            match parameter.data(interner) {
                // All types and consts are mapped to distinct variables. Since this
                // has been canonicalized, those will also be the first N
                // variables.
                GenericArgData::Ty(t) => is_trivial(t.bound_var(interner)),
                GenericArgData::Const(t) => is_trivial(t.bound_var(interner)),

                // And no lifetime mappings. (This is too strict, but we never
                // product substs with lifetimes.)
                GenericArgData::Lifetime(_) => false,
            }
        });

    if !trivial_substition {
        return false;
    }

    // ...and the alias egraph is empty...
    subst.value.alias_egraph.is_empty()
}

/// [Anti-unification] is the act of taking two things that do not
/// unify and finding a minimal generalization of them. So for
/// example `Vec<u32>` anti-unified with `Vec<i32>` might be
/// `Vec<?X>`. This is a **very simplistic** anti-unifier.
///
/// NOTE: The values here are canonicalized, but output is not, this means
/// that any escaping bound variables that we see have to be replaced with
/// inference variables.
///
/// [Anti-unification]: https://en.wikipedia.org/wiki/Anti-unification_(computer_science)
struct AntiUnifier<'infer, I: Interner> {
    infer: &'infer mut InferenceTable<I>,
    universe: UniverseIndex,
    interner: I,
    egraph: &'infer mut Egraph<I>,
}

impl<I: Interner> AntiUnifier<'_, I> {
    fn aggregate_tys(&mut self, ty0: &Ty<I>, ty1: &Ty<I>) -> Ty<I> {
        let interner = self.interner;
        match (ty0.kind(interner), ty1.kind(interner)) {
            // If we see bound things on either side, just drop in a
            // fresh variable. This means we will sometimes
            // overgeneralize.  So for example if we have two
            // solutions that are both `(X, X)`, we just produce `(Y,
            // Z)` in all cases.
            (TyKind::InferenceVar(var, _), _) => {
                if self.egraph.is_alias_var(*var) {
                    panic!()
                } else {
                    self.new_ty_variable()
                }
            }
            (_, TyKind::InferenceVar(_, _)) => self.new_ty_variable(),

            // Ugh. Aggregating two types like `for<'a> fn(&'a u32,
            // &'a u32)` and `for<'a, 'b> fn(&'a u32, &'b u32)` seems
            // kinda hard. Don't try to be smart for now, just plop a
            // variable in there and be done with it.
            // This also ensures that any bound variables we do see
            // were bound by `Canonical`.
            (TyKind::BoundVar(_), TyKind::BoundVar(_))
            | (TyKind::Function(_), TyKind::Function(_))
            | (TyKind::Dyn(_), TyKind::Dyn(_)) => self.new_ty_variable(),

            (
                TyKind::Alias(alias_a),
                TyKind::Alias(alias_b),
            ) => {
                match self.egraph.register_alias_alias_constraint(self.infer, alias_a.clone(), alias_b.clone()) {
                    Ok(()) => ty0.clone(),
                    Err(_) => self.new_ty_variable(),
                }
            }

            (TyKind::Alias(alias), _) => {
                match self.egraph.register_alias_rigid_constraint(self.interner, self.infer, alias.clone(), ty1.clone()) {
                    Ok(()) => ty1.clone(),
                    Err(_) => self.new_ty_variable(),
                }
            }

            (_, TyKind::Alias(alias)) => {
                match self.egraph.register_alias_rigid_constraint(self.interner, self.infer, alias.clone(), ty0.clone()) {
                    Ok(()) => ty0.clone(),
                    Err(_) => self.new_ty_variable(),
                }
            }

            (
                TyKind::Alias(AliasTy::Opaque(opaque_ty1)),
                TyKind::Alias(AliasTy::Opaque(opaque_ty2)),
            ) => self.aggregate_opaque_ty_tys(opaque_ty1, opaque_ty2),

            (
                TyKind::Alias(AliasTy::Projection(proj1)),
                TyKind::Alias(AliasTy::Projection(proj2)),
            ) => self.aggregate_projection_tys(proj1, proj2),

            (
                TyKind::Alias(AliasTy::Opaque(opaque_ty1)),
                TyKind::Alias(AliasTy::Opaque(opaque_ty2)),
            ) => self.aggregate_opaque_ty_tys(opaque_ty1, opaque_ty2),

            (TyKind::Placeholder(placeholder1), TyKind::Placeholder(placeholder2)) => {
                self.aggregate_placeholder_tys(placeholder1, placeholder2)
            }

            (TyKind::Adt(id_a, substitution_a), TyKind::Adt(id_b, substitution_b)) => self
                .aggregate_name_and_substs(id_a, substitution_a, id_b, substitution_b)
                .map(|(&name, substitution)| TyKind::Adt(name, substitution).intern(interner))
                .unwrap_or_else(|| self.new_ty_variable()),
            (TyKind::Scalar(scalar_a), TyKind::Scalar(scalar_b)) => {
                if scalar_a == scalar_b {
                    TyKind::Scalar(*scalar_a).intern(interner)
                } else {
                    self.new_ty_variable()
                }
            }
            (TyKind::Str, TyKind::Str) => TyKind::Str.intern(interner),
            (TyKind::Tuple(arity_a, substitution_a), TyKind::Tuple(arity_b, substitution_b)) => {
                self.aggregate_name_and_substs(arity_a, substitution_a, arity_b, substitution_b)
                    .map(|(&name, substitution)| TyKind::Tuple(name, substitution).intern(interner))
                    .unwrap_or_else(|| self.new_ty_variable())
            }
            (
                TyKind::OpaqueType(id_a, substitution_a),
                TyKind::OpaqueType(id_b, substitution_b),
            ) => self
                .aggregate_name_and_substs(id_a, substitution_a, id_b, substitution_b)
                .map(|(&name, substitution)| {
                    TyKind::OpaqueType(name, substitution).intern(interner)
                })
                .unwrap_or_else(|| self.new_ty_variable()),
            (TyKind::Slice(ty_a), TyKind::Slice(ty_b)) => {
                TyKind::Slice(self.aggregate_tys(ty_a, ty_b)).intern(interner)
            }
            (TyKind::FnDef(id_a, substitution_a), TyKind::FnDef(id_b, substitution_b)) => self
                .aggregate_name_and_substs(id_a, substitution_a, id_b, substitution_b)
                .map(|(&name, substitution)| TyKind::FnDef(name, substitution).intern(interner))
                .unwrap_or_else(|| self.new_ty_variable()),
            (TyKind::Ref(id_a, lifetime_a, ty_a), TyKind::Ref(id_b, lifetime_b, ty_b)) => {
                if id_a == id_b {
                    TyKind::Ref(
                        *id_a,
                        self.aggregate_lifetimes(lifetime_a, lifetime_b),
                        self.aggregate_tys(ty_a, ty_b),
                    )
                    .intern(interner)
                } else {
                    self.new_ty_variable()
                }
            }
            (TyKind::Raw(id_a, ty_a), TyKind::Raw(id_b, ty_b)) => {
                if id_a == id_b {
                    TyKind::Raw(*id_a, self.aggregate_tys(ty_a, ty_b)).intern(interner)
                } else {
                    self.new_ty_variable()
                }
            }
            (TyKind::Never, TyKind::Never) => TyKind::Never.intern(interner),
            (TyKind::Array(ty_a, const_a), TyKind::Array(ty_b, const_b)) => TyKind::Array(
                self.aggregate_tys(ty_a, ty_b),
                self.aggregate_consts(const_a, const_b),
            )
            .intern(interner),
            (TyKind::Closure(id_a, substitution_a), TyKind::Closure(id_b, substitution_b)) => self
                .aggregate_name_and_substs(id_a, substitution_a, id_b, substitution_b)
                .map(|(&name, substitution)| TyKind::Closure(name, substitution).intern(interner))
                .unwrap_or_else(|| self.new_ty_variable()),
            (TyKind::Generator(id_a, substitution_a), TyKind::Generator(id_b, substitution_b)) => {
                self.aggregate_name_and_substs(id_a, substitution_a, id_b, substitution_b)
                    .map(|(&name, substitution)| {
                        TyKind::Generator(name, substitution).intern(interner)
                    })
                    .unwrap_or_else(|| self.new_ty_variable())
            }
            (
                TyKind::GeneratorWitness(id_a, substitution_a),
                TyKind::GeneratorWitness(id_b, substitution_b),
            ) => self
                .aggregate_name_and_substs(id_a, substitution_a, id_b, substitution_b)
                .map(|(&name, substitution)| {
                    TyKind::GeneratorWitness(name, substitution).intern(interner)
                })
                .unwrap_or_else(|| self.new_ty_variable()),
            (TyKind::Foreign(id_a), TyKind::Foreign(id_b)) => {
                if id_a == id_b {
                    TyKind::Foreign(*id_a).intern(interner)
                } else {
                    self.new_ty_variable()
                }
            }
            (TyKind::Error, TyKind::Error) => TyKind::Error.intern(interner),

            (TyKind::BoundVar(..), _) => {
                panic!()
            }
            (_, _) => self.new_ty_variable(),
        }
    }

    fn aggregate_placeholder_tys(
        &mut self,
        index1: &PlaceholderIndex,
        index2: &PlaceholderIndex,
    ) -> Ty<I> {
        let interner = self.interner;
        if index1 != index2 {
            self.new_ty_variable()
        } else {
            TyKind::Placeholder(*index1).intern(interner)
        }
    }

    fn aggregate_projection_tys(
        &mut self,
        proj1: &ProjectionTy<I>,
        proj2: &ProjectionTy<I>,
    ) -> Ty<I> {
        let interner = self.interner;
        let ProjectionTy {
            associated_ty_id: name1,
            substitution: substitution1,
        } = proj1;
        let ProjectionTy {
            associated_ty_id: name2,
            substitution: substitution2,
        } = proj2;

        self.aggregate_name_and_substs(name1, substitution1, name2, substitution2)
            .map(|(&associated_ty_id, substitution)| {
                TyKind::Alias(AliasTy::Projection(ProjectionTy {
                    associated_ty_id,
                    substitution,
                }))
                .intern(interner)
            })
            .unwrap_or_else(|| self.new_ty_variable())
    }

    fn aggregate_opaque_ty_tys(
        &mut self,
        opaque_ty1: &OpaqueTy<I>,
        opaque_ty2: &OpaqueTy<I>,
    ) -> Ty<I> {
        let OpaqueTy {
            opaque_ty_id: name1,
            substitution: substitution1,
        } = opaque_ty1;
        let OpaqueTy {
            opaque_ty_id: name2,
            substitution: substitution2,
        } = opaque_ty2;

        self.aggregate_name_and_substs(name1, substitution1, name2, substitution2)
            .map(|(&opaque_ty_id, substitution)| {
                TyKind::Alias(AliasTy::Opaque(OpaqueTy {
                    opaque_ty_id,
                    substitution,
                }))
                .intern(self.interner)
            })
            .unwrap_or_else(|| self.new_ty_variable())
    }

    fn aggregate_name_and_substs<N>(
        &mut self,
        name1: N,
        substitution1: &Substitution<I>,
        name2: N,
        substitution2: &Substitution<I>,
    ) -> Option<(N, Substitution<I>)>
    where
        N: Copy + Eq + Debug,
    {
        let interner = self.interner;
        if name1 != name2 {
            return None;
        }

        let name = name1;

        assert_eq!(
            substitution1.len(interner),
            substitution2.len(interner),
            "does {:?} take {} substitution or {}? can't both be right",
            name,
            substitution1.len(interner),
            substitution2.len(interner)
        );

        let substitution = Substitution::from_iter(
            interner,
            substitution1
                .iter(interner)
                .zip(substitution2.iter(interner))
                .map(|(p1, p2)| self.aggregate_generic_args(p1, p2)),
        );

        Some((name, substitution))
    }

    fn aggregate_generic_args(&mut self, p1: &GenericArg<I>, p2: &GenericArg<I>) -> GenericArg<I> {
        let interner = self.interner;
        match (p1.data(interner), p2.data(interner)) {
            (GenericArgData::Ty(ty1), GenericArgData::Ty(ty2)) => {
                self.aggregate_tys(ty1, ty2).cast(interner)
            }
            (GenericArgData::Lifetime(l1), GenericArgData::Lifetime(l2)) => {
                self.aggregate_lifetimes(l1, l2).cast(interner)
            }
            (GenericArgData::Const(c1), GenericArgData::Const(c2)) => {
                self.aggregate_consts(c1, c2).cast(interner)
            }
            (GenericArgData::Ty(_), _)
            | (GenericArgData::Lifetime(_), _)
            | (GenericArgData::Const(_), _) => {
                panic!("mismatched parameter kinds: p1={:?} p2={:?}", p1, p2)
            }
        }
    }

    fn aggregate_lifetimes(&mut self, l1: &Lifetime<I>, l2: &Lifetime<I>) -> Lifetime<I> {
        let interner = self.interner;
        match (l1.data(interner), l2.data(interner)) {
            (LifetimeData::Phantom(void, ..), _) | (_, LifetimeData::Phantom(void, ..)) => {
                match *void {}
            }
            (LifetimeData::BoundVar(..), _) | (_, LifetimeData::BoundVar(..)) => {
                self.new_lifetime_variable()
            }
            _ => {
                if l1 == l2 {
                    l1.clone()
                } else {
                    self.new_lifetime_variable()
                }
            }
        }
    }

    fn aggregate_consts(&mut self, c1: &Const<I>, c2: &Const<I>) -> Const<I> {
        let interner = self.interner;

        // It would be nice to check that c1 and c2 have the same type, even though
        // on this stage of solving they should already have the same type.

        let ConstData {
            ty: c1_ty,
            value: c1_value,
        } = c1.data(interner);
        let ConstData {
            ty: _c2_ty,
            value: c2_value,
        } = c2.data(interner);

        let ty = c1_ty.clone();

        match (c1_value, c2_value) {
            (ConstValue::InferenceVar(_), _) | (_, ConstValue::InferenceVar(_)) => {
                self.new_const_variable(ty)
            }

            (ConstValue::BoundVar(_), _) | (_, ConstValue::BoundVar(_)) => {
                self.new_const_variable(ty)
            }

            (ConstValue::Placeholder(_), ConstValue::Placeholder(_)) => {
                if c1 == c2 {
                    c1.clone()
                } else {
                    self.new_const_variable(ty)
                }
            }
            (ConstValue::Concrete(e1), ConstValue::Concrete(e2)) => {
                if e1.const_eq(&ty, e2, interner) {
                    c1.clone()
                } else {
                    self.new_const_variable(ty)
                }
            }

            (ConstValue::Placeholder(_), _) | (_, ConstValue::Placeholder(_)) => {
                self.new_const_variable(ty)
            }
        }
    }

    fn new_ty_variable(&mut self) -> Ty<I> {
        let interner = self.interner;
        self.infer.new_variable(self.universe).to_ty(interner)
    }

    fn new_lifetime_variable(&mut self) -> Lifetime<I> {
        let interner = self.interner;
        self.infer.new_variable(self.universe).to_lifetime(interner)
    }

    fn new_const_variable(&mut self, ty: Ty<I>) -> Const<I> {
        let interner = self.interner;
        self.infer
            .new_variable(self.universe)
            .to_const(interner, ty)
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AliasVarTy<I: Interner> {
    index: u32,
    phantom: PhantomData<I>,
}

impl<I: Interner> UnifyKey for AliasVarTy<I> {
    type Value = AliasValue<I>;

    fn index(&self) -> u32 {
        self.index
    }

    fn from_index(index: u32) -> Self {
        AliasVarTy {
            index,
            phantom: PhantomData,
        }
    }

    fn tag() -> &'static str {
        "AliasVarTy"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AliasValue<I: Interner> {
    Unbound,
    Bound(Ty<I>),
}

impl<I: Interner> UnifyValue for AliasValue<I> {
    type Error = ();

    fn unify_values(a: &Self, b: &Self) -> Result<Self, Self::Error> {
        match (a, b) {
            (&AliasValue::Unbound, &AliasValue::Unbound) => Ok(AliasValue::Unbound),
            (bound @ &AliasValue::Bound(_), &AliasValue::Unbound)
            | (&AliasValue::Unbound, bound @ &AliasValue::Bound(_)) => Ok(bound.clone()),
            (&AliasValue::Bound(_), &AliasValue::Bound(_)) => Err(()),
        }
    }
}

#[cfg(test)]
mod test {
    use crate::slg::aggregate::AntiUnifier;
    use chalk_integration::{arg, ty};
    use chalk_ir::UniverseIndex;
    use chalk_solve::infer::InferenceTable;

    /// Test the equivalent of `Vec<i32>` vs `Vec<u32>`
    #[test]
    fn vec_i32_vs_vec_u32() {
        use chalk_integration::interner::ChalkIr;
        let mut infer: InferenceTable<ChalkIr> = InferenceTable::new();
        let mut anti_unifier = AntiUnifier {
            infer: &mut infer,
            universe: UniverseIndex::root(),
            interner: ChalkIr,
        };

        let ty = anti_unifier.aggregate_tys(
            &ty!(apply (item 0) (apply (item 1))),
            &ty!(apply (item 0) (apply (item 2))),
        );
        assert_eq!(ty!(apply (item 0) (infer 0)), ty);
    }

    /// Test the equivalent of `Vec<i32>` vs `Vec<i32>`
    #[test]
    fn vec_i32_vs_vec_i32() {
        use chalk_integration::interner::ChalkIr;
        let interner = ChalkIr;
        let mut infer: InferenceTable<ChalkIr> = InferenceTable::new();
        let mut anti_unifier = AntiUnifier {
            interner,
            infer: &mut infer,
            universe: UniverseIndex::root(),
        };

        let ty = anti_unifier.aggregate_tys(
            &ty!(apply (item 0) (apply (item 1))),
            &ty!(apply (item 0) (apply (item 1))),
        );
        assert_eq!(ty!(apply (item 0) (apply (item 1))), ty);
    }

    /// Test the equivalent of `Vec<X>` vs `Vec<Y>`
    #[test]
    fn vec_x_vs_vec_y() {
        use chalk_integration::interner::ChalkIr;
        let interner = ChalkIr;
        let mut infer: InferenceTable<ChalkIr> = InferenceTable::new();
        let mut anti_unifier = AntiUnifier {
            interner,
            infer: &mut infer,
            universe: UniverseIndex::root(),
        };

        // Note that the `var 0` and `var 1` in these types would be
        // referring to canonicalized free variables, not variables in
        // `infer`.
        let ty = anti_unifier.aggregate_tys(
            &ty!(apply (item 0) (infer 0)),
            &ty!(apply (item 0) (infer 1)),
        );

        // But this `var 0` is from `infer.
        assert_eq!(ty!(apply (item 0) (infer 0)), ty);
    }
}
