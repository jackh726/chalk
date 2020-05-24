use chalk_ir::interner::{HasInterner, Interner};
use chalk_ir::*;
use chalk_ir::{cast::Cast, fold::Fold};

pub(crate) mod canonicalize;
pub(crate) mod instantiate;
mod invert;
mod normalize_deep;
mod test;
pub(crate) mod ucanonicalize;
pub(crate) mod unify;
pub(crate) mod var;

use self::var::*;

#[derive(Clone)]
pub(crate) struct InferenceTable<I: Interner> {
    unify: ena::unify::InPlaceUnificationTable<EnaVariable<I>>,
    vars: Vec<EnaVariable<I>>,
    max_universe: UniverseIndex,
}

pub(crate) struct InferenceSnapshot<I: Interner> {
    unify_snapshot: ena::unify::Snapshot<ena::unify::InPlace<EnaVariable<I>>>,
    max_universe: UniverseIndex,
    vars: Vec<EnaVariable<I>>,
}

#[allow(type_alias_bounds)]
pub(crate) type ParameterEnaVariable<I: Interner> = WithKind<I, EnaVariable<I>>;

impl<I: Interner> InferenceTable<I> {
    /// Create an empty inference table with no variables.
    pub(crate) fn new() -> Self {
        InferenceTable {
            unify: ena::unify::UnificationTable::new(),
            vars: vec![],
            max_universe: UniverseIndex::root(),
        }
    }

    /// Creates a new inference table, pre-populated with
    /// `num_universes` fresh universes. Instantiates the canonical
    /// value `canonical` within those universes (which must not
    /// reference any universe greater than `num_universes`). Returns
    /// the substitution mapping from each canonical binder to its
    /// corresponding existential variable, along with the
    /// instantiated result.
    pub(crate) fn from_canonical<T>(
        interner: &I,
        num_universes: usize,
        canonical: &Canonical<T>,
    ) -> (Self, Substitution<I>, T)
    where
        T: HasInterner<Interner = I> + Fold<I, Result = T> + Clone,
    {
        let mut table = InferenceTable::new();

        assert!(num_universes >= 1); // always have U0
        for _ in 1..num_universes {
            table.new_universe();
        }

        let subst = table.fresh_subst(interner, canonical.binders.as_slice(interner));
        let value = subst.apply(&canonical.value, interner);
        // let value = canonical.value.fold_with(&mut &subst, 0).unwrap();

        (table, subst, value)
    }

    /// Creates and returns a fresh universe that is distinct from all
    /// others created within this inference table. This universe is
    /// able to see all previously created universes (though hopefully
    /// it is only brought into contact with its logical *parents*).
    pub(crate) fn new_universe(&mut self) -> UniverseIndex {
        let u = self.max_universe.next();
        self.max_universe = u;
        debug!("new_universe: {:?}", u);
        u
    }

    /// Creates a new inference variable and returns its index. The
    /// kind of the variable should be known by the caller, but is not
    /// tracked directly by the inference table.
    pub(crate) fn new_variable(&mut self, ui: UniverseIndex) -> EnaVariable<I> {
        let var = self.unify.new_key(InferenceValue::Unbound(ui));
        self.vars.push(var);
        debug!("new_variable: var={:?} ui={:?}", var, ui);
        var
    }

    /// Takes a "snapshot" of the current state of the inference
    /// table.  Later, you must invoke either `rollback_to` or
    /// `commit` with that snapshot.  Snapshots can be nested, but you
    /// must respect a stack discipline (i.e., rollback or commit
    /// snapshots in reverse order of that with which they were
    /// created).
    pub(crate) fn snapshot(&mut self) -> InferenceSnapshot<I> {
        let unify_snapshot = self.unify.snapshot();
        let vars = self.vars.clone();
        let max_universe = self.max_universe;
        InferenceSnapshot {
            unify_snapshot,
            max_universe,
            vars,
        }
    }

    /// Restore the table to the state it had when the snapshot was taken.
    pub(crate) fn rollback_to(&mut self, snapshot: InferenceSnapshot<I>) {
        self.unify.rollback_to(snapshot.unify_snapshot);
        self.vars = snapshot.vars;
        self.max_universe = snapshot.max_universe;
    }

    /// Make permanent the changes made since the snapshot was taken.
    pub(crate) fn commit(&mut self, snapshot: InferenceSnapshot<I>) {
        self.unify.commit(snapshot.unify_snapshot);
    }

    pub(crate) fn normalize_ty_shallow(&mut self, interner: &I, leaf: &Ty<I>) -> Option<Ty<I>> {
        self.probe_var(leaf.inference_var(interner)?)
            .map(|p| p.assert_ty_ref(interner).clone())
    }

    pub(crate) fn normalize_lifetime_shallow(
        &mut self,
        interner: &I,
        leaf: &Lifetime<I>,
    ) -> Option<Lifetime<I>> {
        self.probe_var(leaf.inference_var(interner)?)
            .map(|p| p.assert_lifetime_ref(interner).clone())
    }

    pub(crate) fn normalize_const_shallow(
        &mut self,
        interner: &I,
        leaf: &Const<I>,
    ) -> Option<Const<I>> {
        self.probe_var(leaf.inference_var(interner)?)
            .map(|p| p.assert_const_ref(interner).clone())
    }

    /// If type `leaf` is a free inference variable, and that variable has been
    /// bound, returns `Some(P)` where `P` is the parameter to which it has been bound.
    pub(crate) fn probe_var(&mut self, leaf: InferenceVar) -> Option<GenericArg<I>> {
        match self.unify.probe_value(EnaVariable::from(leaf)) {
            InferenceValue::Unbound(_) => None,
            InferenceValue::Bound(val) => Some(val),
        }
    }

    /// Given an unbound variable, returns its universe.
    ///
    /// # Panics
    ///
    /// Panics if the variable is bound.
    fn universe_of_unbound_var(&mut self, var: EnaVariable<I>) -> UniverseIndex {
        match self.unify.probe_value(var) {
            InferenceValue::Unbound(ui) => ui,
            InferenceValue::Bound(_) => panic!("var_universe invoked on bound variable"),
        }
    }
}

pub(crate) trait ParameterEnaVariableExt<I: Interner> {
    fn to_generic_arg(&self, interner: &I) -> GenericArg<I>;
}

impl<I: Interner> ParameterEnaVariableExt<I> for ParameterEnaVariable<I> {
    fn to_generic_arg(&self, interner: &I) -> GenericArg<I> {
        // we are matching on kind, so skipping it is fine
        let ena_variable = self.skip_kind();
        match &self.kind {
            VariableKind::Ty => ena_variable.to_ty(interner).cast(interner),
            VariableKind::Lifetime => ena_variable.to_lifetime(interner).cast(interner),
            VariableKind::Const(ty) => ena_variable.to_const(interner, ty.clone()).cast(interner),
        }
    }
}
