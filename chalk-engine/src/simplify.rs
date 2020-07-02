use crate::context::{Context, ContextOps, UnificationOps};
use crate::forest::Forest;
use crate::{ExClause, Literal, TimeStamp};

use chalk_ir::interner::Interner;
use chalk_ir::{
    Environment, Fallible, Goal, GoalData, InEnvironment, QuantifierKind, Substitution, Variance,
};
use tracing::debug;

impl<I: Interner, C: Context<I>> Forest<I, C> {
    /// Simplifies a goal into a series of positive domain goals
    /// and negative goals. This operation may fail if the goal
    /// includes unifications that cannot be completed.
    pub(super) fn simplify_goal(
        context: &impl ContextOps<I, C>,
        infer: &mut dyn UnificationOps<I, C>,
        subst: Substitution<I>,
        initial_environment: Environment<I>,
        initial_goal: Goal<I>,
    ) -> Fallible<ExClause<I>> {
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
        let mut pending_goals = vec![(initial_environment, initial_goal)];

        while let Some((environment, goal)) = pending_goals.pop() {
            match goal.data(context.interner()) {
                GoalData::Quantified(QuantifierKind::ForAll, subgoal) => {
                    let subgoal =
                        infer.instantiate_binders_universally(context.interner(), &subgoal);
                    pending_goals.push((environment, subgoal.clone()));
                }
                GoalData::Quantified(QuantifierKind::Exists, subgoal) => {
                    let subgoal =
                        infer.instantiate_binders_existentially(context.interner(), &subgoal);
                    pending_goals.push((environment, subgoal.clone()));
                }
                GoalData::Implies(wc, subgoal) => {
                    let new_environment = context.add_clauses(&environment, wc.clone());
                    pending_goals.push((new_environment, subgoal.clone()));
                }
                GoalData::All(subgoals) => {
                    for subgoal in subgoals.iter(context.interner()) {
                        pending_goals.push((environment.clone(), subgoal.clone()));
                    }
                }
                GoalData::Not(subgoal) => {
                    ex_clause
                        .subgoals
                        .push(Literal::Negative(InEnvironment::new(
                            &environment,
                            subgoal.clone(),
                        )));
                }
                GoalData::EqGoal(goal) => infer.relate_generic_args_into_ex_clause(
                    context.interner(),
                    context.unification_database(),
                    &environment,
                    Variance::Invariant,
                    &goal.a,
                    &goal.b,
                    &mut ex_clause,
                )?,
                GoalData::SubtypeGoal(goal) => infer.relate_generic_args_into_ex_clause(
                    context.interner(),
                    context.unification_database(),
                    &environment,
                    Variance::Covariant,
                    &goal.a,
                    &goal.b,
                    &mut ex_clause,
                )?,
                GoalData::DomainGoal(domain_goal) => {
                    ex_clause
                        .subgoals
                        .push(Literal::Positive(InEnvironment::new(
                            &environment,
                            context.into_goal(domain_goal.clone()),
                        )));
                }
                GoalData::CannotProve(()) => {
                    debug!("Marking Strand as ambiguous because of a `CannotProve` subgoal");
                    ex_clause.ambiguous = true;
                }
            }
        }

        Ok(ex_clause)
    }
}
