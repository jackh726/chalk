use chalk_ir::{Goal, InEnvironment, Canonical};

pub type UCanonicalGoal<I> = Canonical<InEnvironment<Goal<I>>>;

mod combine;
mod fixed_point;
mod fulfill;
mod recursive;
pub mod solve;

pub use fixed_point::Cache;
pub use recursive::RecursiveSolver;
