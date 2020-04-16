use std::{iter, mem::replace};

use chalk_engine::fallible::Fallible;
use chalk_ir::{
    fold::{shift::Shift, Fold, Folder, SuperFold},
    interner::Interner,
    Binders, BoundVar, DebruijnIndex, EqGoal, Goal, GoalData, Goals, Parameter, ProgramClause,
    ProgramClauseData, ProgramClauseImplication, QuantifierKind, Ty, TyData, ParameterKind, ApplicationTy, TypeName,
    ParameterKinds,
};

pub fn syn_eq_lower<I: Interner>(interner: &I, clause: &ProgramClause<I>) -> ProgramClause<I> {
    let mut folder = SynEqFolder {
        interner,
        new_params: vec![],
        binders_len: 0,
    };

    clause.fold_with(&mut folder, DebruijnIndex::INNERMOST).unwrap()
}

struct SynEqFolder<'i, I: Interner> {
    interner: &'i I,
    new_params: Vec<Parameter<I>>,
    binders_len: usize,
}

impl<'i, I: Interner> SynEqFolder<'i, I>
where
    I: 'i,
{
    fn to_eq_goals(&self, new_params: Vec<Parameter<I>>, old_len: usize) -> impl Iterator<Item = Goal<I>> + 'i {
        let interner = self.interner;
        new_params.into_iter().enumerate().map(move |(i, p)| {
            let var = BoundVar {
                debruijn: DebruijnIndex::INNERMOST,
                index: i + old_len,
            };
            GoalData::EqGoal(EqGoal {
                a: p.replace_bound(var, interner),
                b: p,
            })
            .intern(interner)
        })
    }
}

impl<'i, I: Interner> Folder<'i, I> for SynEqFolder<'i, I> {
    fn as_dyn(&mut self) -> &mut dyn Folder<'i, I> {
        self
    }

    fn fold_ty(&mut self, ty: &Ty<I>, outer_binder: DebruijnIndex) -> Fallible<Ty<I>> {
        let interner = self.interner;
        let bound_var = BoundVar::new(DebruijnIndex::INNERMOST, self.binders_len);

        let folded = ty.super_fold_with(self, outer_binder)?;
        match folded.data(interner) {
            TyData::Apply(ApplicationTy { name: TypeName::AssociatedType(_), .. }) => {
                self.new_params.push(ParameterKind::Ty(ty.clone()).intern(interner));
                self.binders_len += 1;
                Ok(TyData::BoundVar(bound_var).intern(interner))
            }
            _ => ty.super_fold_with(self, outer_binder),
        }
    }

    fn fold_program_clause(
        &mut self,
        clause: &ProgramClause<I>,
        outer_binder: DebruijnIndex,
    ) -> Fallible<ProgramClause<I>> {
        let interner = self.interner;

        let ((binders, implication), in_binders) = match clause.data(interner) {
            ProgramClauseData::ForAll(for_all) => {
                (for_all.clone().into(), true)
            }
            // introduce a dummy binder and shift implication through it
            ProgramClauseData::Implies(implication) => ((ParameterKinds::new(interner), implication.shifted_in(interner)), false),
        };
        let mut binders: Vec<_> = binders.as_slice(interner).clone().into();
        
        let outer_binder = outer_binder.shifted_in();

        self.binders_len = binders.len();
        let consequence = implication.consequence.fold_with(self, outer_binder)?;
        // Immediately move `new_params` out of of the folder struct so it's safe
        // to call `.fold_with` again
        let new_params = replace(&mut self.new_params, vec![]);
        
        let mut conditions = implication.conditions.fold_with(self, outer_binder)?;
        if new_params.is_empty() && !in_binders {
            // shift the clause out since we didn't use the dummy binder
            return Ok(ProgramClauseData::Implies(ProgramClauseImplication {
                consequence,
                conditions,
                priority: implication.priority,
            }.shifted_out(interner)?)
            .intern(interner));
        }

        let old_len = binders.len();
        binders.extend(new_params.iter().map(|p| p.data(interner).anonymize()));

        conditions = Goals::from(
            interner,
            conditions
                .iter(interner)
                .cloned()
                .chain(self.to_eq_goals(new_params, old_len)),
        );

        Ok(ProgramClauseData::ForAll(Binders::new(
            ParameterKinds::from(interner, binders),
            ProgramClauseImplication {
                consequence,
                conditions,
                priority: implication.priority,
            },
        ))
        .intern(interner))
    }

    fn fold_goal(&mut self, goal: &Goal<I>, outer_binder: DebruijnIndex) -> Fallible<Goal<I>> {
        assert!(self.new_params.is_empty(), true);

        let interner = self.interner;
        let domain_goal = match goal.data(interner) {
            GoalData::DomainGoal(dg) => dg,
            _ => return goal.super_fold_with(self, outer_binder),
        };

        self.binders_len = 0;
        // shifted in because we introduce a new binder
        let outer_binder = outer_binder.shifted_in();
        let domain_goal =
            GoalData::DomainGoal(domain_goal.shifted_in(interner).fold_with(self, outer_binder)?).intern(interner);
        let new_params = replace(&mut self.new_params, vec![]);

        let binders: Vec<_> = new_params
            .iter()
            .map(|p| p.data(interner).anonymize())
            .collect();

        if binders.is_empty() {
            return Ok(goal.clone());
        }

        let goal = GoalData::All(Goals::from(
            interner,
            iter::once(domain_goal).chain(self.to_eq_goals(new_params, 0)),
        ))
        .intern(interner);

        Ok(
            GoalData::Quantified(QuantifierKind::Exists, Binders::new(ParameterKinds::from(interner, binders), goal))
                .intern(interner),
        )
    }

    fn interner(&self) -> &'i I {
        self.interner
    }

    fn target_interner(&self) -> &'i I {
        self.interner
    }
}
