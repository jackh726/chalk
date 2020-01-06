//! An alternative solver based around the SLG algorithm, which
//! implements the well-formed semantics. For an overview of how the solver
//! works, see [The On-Demand SLG Solver][guide] in the rustc guide.
//!
//! [guide]: https://rust-lang.github.io/rustc-guide/traits/slg.html
//!
//! This algorithm is very closed based on the description found in the
//! following paper, which I will refer to in the comments as EWFS:
//!
//! > Efficient Top-Down Computation of Queries Under the Well-founded Semantics
//! > (Chen, Swift, and Warren; Journal of Logic Programming '95)
//!
//! However, to understand that paper, I would recommend first
//! starting with the following paper, which I will refer to in the
//! comments as NFTD:
//!
//! > A New Formulation of Tabled resolution With Delay
//! > (Swift; EPIA '99)
//!
//! In addition, I incorporated extensions from the following papers,
//! which I will refer to as SA and RR respectively, that
//! describes how to do introduce approximation when processing
//! subgoals and so forth:
//!
//! > Terminating Evaluation of Logic Programs with Finite Three-Valued Models
//! > Riguzzi and Swift; ACM Transactions on Computational Logic 2013
//! > (Introduces "subgoal abstraction", hence the name SA)
//! >
//! > Radial Restraint
//! > Grosof and Swift; 2013
//!
//! Another useful paper that gives a kind of high-level overview of
//! concepts at play is the following, which I will refer to as XSB:
//!
//! > XSB: Extending Prolog with Tabled Logic Programming
//! > (Swift and Warren; Theory and Practice of Logic Programming '10)
//!
//! While this code is adapted from the algorithms described in those
//! papers, it is not the same. For one thing, the approaches there
//! had to be extended to our context, and in particular to coping
//! with hereditary harrop predicates and our version of unification
//! (which produces subgoals). I believe those to be largely faithful
//! extensions. However, there are some other places where I
//! intentionally diverged from the semantics as described in the
//! papers -- e.g. by more aggressively approximating -- which I
//! marked them with a comment DIVERGENCE. Those places may want to be
//! evaluated in the future.
//!
//! Glossary of other terms:
//!
//! - WAM: Warren abstract machine, an efficient way to evaluate Prolog programs.
//!   See <http://wambook.sourceforge.net/>.
//! - HH: Hereditary harrop predicates. What Chalk deals in.
//!   Popularized by Lambda Prolog.

#[macro_use]
extern crate chalk_macros;

#[cfg(feature = "stack_protection")]
extern crate stacker;

extern crate rustc_hash;

use crate::context::Context;
use std::cmp::min;
use std::usize;

pub mod context;
mod derived;
pub mod fallible;
pub mod forest;
pub mod hh;
mod logic;
mod simplify;
mod stack;
mod strand;
mod table;
mod tables;

index_struct! {
    pub struct TableIndex { // FIXME: pub b/c Fold
        value: usize,
    }
}

index_struct! {
    /// The StackIndex identifies the position of a table's goal in the
    /// stack of goals that are actively being processed. Note that once a
    /// table is completely evaluated, it may be popped from the stack,
    /// and hence no longer have a stack index.
    struct StackIndex {
        value: usize,
    }
}

/// The paper describes these as `A :- D | G`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ExClause<C: Context> {
    /// The substitution which, applied to the goal of our table,
    /// would yield A.
    pub subst: C::Substitution,

    /// Region constraints we have accumulated.
    pub constraints: Vec<C::RegionConstraint>,

    /// Subgoals: literals that must be proven
    pub subgoals: Vec<Literal<C>>,

    /// We assume that negative literals cannot have coinductive cycles.
    pub delayed_subgoals: Vec<C::GoalInEnvironment>,

    /// Time stamp that is incremented each time we find an answer to
    /// some subgoal. This is used to figure out whether any of the
    /// floundered subgoals may no longer be floundered: we record the
    /// current time when we add something to the list of floundered
    /// subgoals, and then we can compare whether its value has
    /// changed since then. This is not the same `TimeStamp` of
    /// `Forest`'s clock.
    pub answer_time: TimeStamp,

    /// List of subgoals that have floundered. See `FlounderedSubgoal`
    /// for more information.
    pub floundered_subgoals: Vec<FlounderedSubgoal<C>>,
}

/// The "time stamp" is a simple clock that gets incremented each time
/// we encounter a positive answer in processing a particular
/// strand. This is used as an optimization to help us figure out when
/// we *may* have changed inference variables.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TimeStamp {
    clock: u64,
}

impl TimeStamp {
    const MAX: TimeStamp = TimeStamp {
        clock: ::std::u64::MAX,
    };

    fn increment(&mut self) {
        self.clock += 1;
    }
}

/// A "floundered" subgoal is one that contains unbound existential
/// variables for which it cannot produce a value. The classic example
/// of floundering is a negative subgoal:
///
/// ```notrust
/// not { Implemented(?T: Foo) }
/// ```
///
/// The way the prolog solver works, it basically enumerates all the
/// ways that a given goal can be *true*. But we can't use this
/// technique to find all the ways that `?T: Foo` can be *false* -- so
/// we call it floundered. In other words, we can evaluate a negative
/// goal, but only if we know what `?T` is -- we can't use the
/// negative goal to help us figuring out `?T`.
///
/// In addition to negative goals, we use floundering to prevent the
/// trait solver from trying to enumerate very large goals with tons
/// of answers. For example, we consider a goal like `?T: Sized` to
/// "flounder", since we can't hope to enumerate all types that are
/// `Sized`. The same is true for other special traits like `Clone`.
///
/// Floundering can also occur indirectly. For example:
///
/// ```notrust
/// trait Foo { }
/// impl<T> Foo for T { }
/// ```
///
/// trying to solve `?T: Foo` would immediately require solving `?T:
/// Sized`, and hence would flounder.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FlounderedSubgoal<C: Context> {
    /// Literal that floundered.
    pub floundered_literal: Literal<C>,

    /// Current value of the strand's clock at the time of
    /// floundering.
    pub floundered_time: TimeStamp,
}

/// An "answer" in the on-demand solver corresponds to a fully solved
/// goal for a particular table (modulo delayed literals). It contains
/// a substitution
#[derive(Clone, Debug)]
pub struct Answer<C: Context> {
    /// Contains values for the unbound inference variables for which
    /// the table is true, along with any delayed subgoals (Which must
    /// still be proven) and region constrained (which must still be
    /// proven, but not by chalk).
    pub subst: C::CanonicalAnswerSubst,

    /// If this flag is set, then the answer could be neither proven
    /// nor disproven. This could be the size of the answer exceeded
    /// `max_size` or because of a negative loop (e.g., `P :- not { P }`).
    pub ambiguous: bool,
}

#[derive(Clone, Debug)]
pub struct CompleteAnswer<C: Context> {
    /// Contains values for the unbound inference variables for which
    /// the table is true, along with any region constrained (which must still be
    /// proven, but not by chalk).
    pub subst: C::CanonicalConstrainedSubst,

    /// If this flag is set, then the answer could be neither proven
    /// nor disproven. This could be the size of the answer exceeded
    /// `max_size` or because of a negative loop (e.g., `P :- not { P }`).
    pub ambiguous: bool,
}

/// Either `A` or `~A`, where `A` is a `Env |- Goal`.
#[derive(Clone, Debug)]
pub enum Literal<C: Context> {
    // FIXME: pub b/c fold
    Positive(C::GoalInEnvironment),
    Negative(C::GoalInEnvironment),
}

/// The `Minimums` structure is used to track the dependencies between
/// some item E on the evaluation stack. In particular, it tracks
/// cases where the success of E depends (or may depend) on items
/// deeper in the stack than E (i.e., with lower DFNs).
///
/// `positive` tracks the lowest index on the stack to which we had a
/// POSITIVE dependency (e.g. `foo(X) :- bar(X)`) -- meaning that in
/// order for E to succeed, the dependency must succeed. It is
/// initialized with the index of the predicate on the stack. So
/// imagine we have a stack like this:
///
/// ```notrust
///     // 0 foo(X)   <-- bottom of stack
///     // 1 bar(X)
///     // 2 baz(X)   <-- top of stack
/// ```
///
/// In this case, `positive` would be initially 0, 1, and 2 for `foo`,
/// `bar`, and `baz` respectively. This reflects the fact that the
/// answers for `foo(X)` depend on the answers for `foo(X)`. =)
///
/// Now imagine that we had a clause `baz(X) :- foo(X)`, inducing a
/// cycle. In this case, we would update `positive` for `baz(X)` to be
/// 0, reflecting the fact that its answers depend on the answers for
/// `foo(X)`. Similarly, the minimum for `bar` would (eventually) be
/// updated, since it too transitively depends on `foo`. `foo` is
/// unaffected.
///
/// `negative` tracks the lowest index on the stack to which we had a
/// NEGATIVE dependency (e.g., `foo(X) :- not { bar(X) }`) -- meaning
/// that for E to succeed, the dependency must fail. This is initially
/// `usize::MAX`, reflecting the fact that the answers for `foo(X)` do
/// not depend on `not(foo(X))`. When negative cycles are encountered,
/// however, this value must be updated.
#[derive(Copy, Clone, Debug)]
struct Minimums {
    positive: TimeStamp,
    negative: TimeStamp,
}

impl Minimums {
    const MAX: Minimums = Minimums {
        positive: TimeStamp::MAX,
        negative: TimeStamp::MAX,
    };

    /// Update our fields to be the minimum of our current value
    /// and the values from other.
    fn take_minimums(&mut self, other: &Minimums) {
        self.positive = min(self.positive, other.positive);
        self.negative = min(self.negative, other.negative);
    }

    fn minimum_of_pos_and_neg(&self) -> TimeStamp {
        min(self.positive, self.negative)
    }
}
