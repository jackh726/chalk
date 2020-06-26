use crate::coherence::CoherenceError;
use crate::ext::GoalExt;
use crate::solve::Solver;
use crate::RustIrDatabase;
use chalk_ir::cast::*;
use chalk_ir::interner::Interner;
use chalk_ir::*;
use tracing::{debug, instrument};

// Test if a local impl violates the orphan rules.
//
// For `impl<T> Trait for MyType<T>` we generate:
//
//     forall<T> { LocalImplAllowed(MyType<T>: Trait) }
//
// This must be provable in order to pass the orphan check.
#[instrument(level = "debug", skip(db, solver_choice))]
pub fn perform_orphan_check<I: Interner, S: Solver<I>, SC: Into<S>>(
    db: &dyn RustIrDatabase<I>,
    solver_choice: SC,
    impl_id: ImplId<I>,
) -> Result<(), CoherenceError<I>> {
    let impl_datum = db.impl_datum(impl_id);
    debug!("impl_datum={:#?}", impl_datum);

    let impl_allowed: Goal<I> = impl_datum
        .binders
        .map_ref(|bound_impl| {
            // Ignoring the polarization of the impl's polarized trait ref
            DomainGoal::LocalImplAllowed(bound_impl.trait_ref.clone())
        })
        .cast(db.interner());

    let canonical_goal = &impl_allowed.into_closed_goal(db.interner());
    let is_allowed = solver_choice.into().solve(db, canonical_goal).is_some();
    debug!("overlaps = {:?}", is_allowed);

    if !is_allowed {
        let trait_id = impl_datum.trait_id();
        Err(CoherenceError::FailedOrphanCheck(trait_id))?;
    }

    Ok(())
}
