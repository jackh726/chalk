use chalk_ir::interner::{HasInterner, Interner};
use chalk_ir::*;
use chalk_ir::{cast::Cast, fold::TypeFoldable};
use ena::unify::UnifyKey;
use rustc_hash::{FxHashMap, FxHashSet};
use tracing::debug;

mod alias_egraph;
mod canonicalize;
pub(crate) mod instantiate;
mod invert;
mod test;
pub mod ucanonicalize;
pub mod unify;
mod var;

use self::var::*;
use self::alias_egraph::*;

// Some special things to note about alias:
// Whenever we encounter an alias and relate it to something, we always replace
// that with a new inference variable, registering that relations into a map.
//
// These can be thought after as a set of AliasEq clauses from the alias to the
// common inference variable.

#[derive(Clone)]
pub struct InferenceTable<I: Interner> {
    unify: ena::unify::InPlaceUnificationTable<EnaVariable<I>>,
    vars: Vec<EnaVariable<I>>,
    max_universe: UniverseIndex,
    alias_map: FxHashMap<AliasVar<I>, FxHashSet<AliasTy<I>>>,
    inverse_alias_map: FxHashMap<AliasTy<I>, AliasVar<I>>,
    inference_alias_map: FxHashMap<EnaVariable<I>, AliasVar<I>>,
    alias_var_to_inference_var_map: FxHashMap<AliasVar<I>, EnaVariable<I>>,
    next_alias_var_index: u32,
}

pub struct InferenceSnapshot<I: Interner> {
    unify_snapshot: ena::unify::Snapshot<ena::unify::InPlace<EnaVariable<I>>>,
    max_universe: UniverseIndex,
    vars: Vec<EnaVariable<I>>,
    alias_map: FxHashMap<AliasVar<I>, FxHashSet<AliasTy<I>>>,
    inverse_alias_map: FxHashMap<AliasTy<I>, AliasVar<I>>,
    inference_alias_map: FxHashMap<EnaVariable<I>, AliasVar<I>>,
    alias_var_to_inference_var_map: FxHashMap<AliasVar<I>, EnaVariable<I>>,
    next_alias_var_index: u32,
}

#[allow(type_alias_bounds)]
pub type ParameterEnaVariable<I: Interner> = WithKind<I, EnaVariable<I>>;

impl<I: Interner> InferenceTable<I> {
    /// Create an empty inference table with no variables.
    pub fn new() -> Self {
        InferenceTable {
            unify: ena::unify::UnificationTable::new(),
            vars: vec![],
            max_universe: UniverseIndex::root(),
            alias_map: FxHashMap::default(),
            inverse_alias_map: FxHashMap::default(),
            inference_alias_map: FxHashMap::default(),
            alias_var_to_inference_var_map: FxHashMap::default(),
            next_alias_var_index: 0,
        }
    }

    /// Creates a new inference table, pre-populated with
    /// `num_universes` fresh universes. Instantiates the canonical
    /// value `canonical` within those universes (which must not
    /// reference any universe greater than `num_universes`). Returns
    /// the substitution mapping from each canonical binder to its
    /// corresponding existential variable, along with the
    /// instantiated result.
    pub fn from_canonical<T>(
        interner: I,
        num_universes: usize,
        canonical: Canonical<T>,
    ) -> (Self, Substitution<I>, T)
    where
        T: HasInterner<Interner = I> + TypeFoldable<I> + Clone,
    {
        let mut table = InferenceTable::new();

        assert!(num_universes >= 1); // always have U0
        for _ in 1..num_universes {
            table.new_universe();
        }

        let subst = table.fresh_subst(interner, canonical.binders.as_slice(interner));
        let value = subst.apply(canonical.value, interner);
        // let value = canonical.value.fold_with(&mut &subst, 0).unwrap();

        (table, subst, value)
    }

    /// Creates and returns a fresh universe that is distinct from all
    /// others created within this inference table. This universe is
    /// able to see all previously created universes (though hopefully
    /// it is only brought into contact with its logical *parents*).
    pub fn new_universe(&mut self) -> UniverseIndex {
        let u = self.max_universe.next();
        self.max_universe = u;
        debug!("created new universe: {:?}", u);
        u
    }

    /// Creates a new inference variable and returns its index. The
    /// kind of the variable should be known by the caller, but is not
    /// tracked directly by the inference table.
    pub fn new_variable(&mut self, ui: UniverseIndex) -> EnaVariable<I> {
        let var = self.unify.new_key(InferenceValue::Unbound(ui));
        self.vars.push(var);
        debug!(?var, ?ui, "created new variable");
        var
    }

    /// Takes a "snapshot" of the current state of the inference
    /// table.  Later, you must invoke either `rollback_to` or
    /// `commit` with that snapshot.  Snapshots can be nested, but you
    /// must respect a stack discipline (i.e., rollback or commit
    /// snapshots in reverse order of that with which they were
    /// created).
    pub fn snapshot(&mut self) -> InferenceSnapshot<I> {
        let unify_snapshot = self.unify.snapshot();
        let max_universe = self.max_universe;
        let vars = self.vars.clone();
        let alias_map = self.alias_map.clone();
        let inverse_alias_map = self.inverse_alias_map.clone();
        let inference_alias_map = self.inference_alias_map.clone();
        let alias_var_to_inference_var_map = self.alias_var_to_inference_var_map.clone();
        let next_alias_var_index = self.next_alias_var_index;
        InferenceSnapshot {
            unify_snapshot,
            max_universe,
            vars,
            alias_map,
            inverse_alias_map,
            inference_alias_map,
            alias_var_to_inference_var_map,
            next_alias_var_index,
        }
    }

    /// Restore the table to the state it had when the snapshot was taken.
    pub fn rollback_to(&mut self, snapshot: InferenceSnapshot<I>) {
        self.unify.rollback_to(snapshot.unify_snapshot);
        self.vars = snapshot.vars;
        self.max_universe = snapshot.max_universe;
        self.alias_map = snapshot.alias_map;
        self.inverse_alias_map = snapshot.inverse_alias_map;
        self.inference_alias_map = snapshot.inference_alias_map;
        self.alias_var_to_inference_var_map = snapshot.alias_var_to_inference_var_map;
        self.next_alias_var_index = snapshot.next_alias_var_index;
    }

    /// Make permanent the changes made since the snapshot was taken.
    pub fn commit(&mut self, snapshot: InferenceSnapshot<I>) {
        self.unify.commit(snapshot.unify_snapshot);
    }

    pub fn normalize_ty_shallow(&mut self, interner: I, leaf: &Ty<I>) -> Option<Ty<I>> {
        // An integer/float type variable will never normalize to another
        // variable; but a general type variable might normalize to an
        // integer/float variable. So we potentially need to normalize twice to
        // get at the actual value.
        let ty = self.normalize_ty_shallow_inner(interner, leaf)?;
        Some(self.normalize_ty_shallow_inner(interner, &ty).unwrap_or(ty))
    }

    fn normalize_ty_shallow_inner(&mut self, interner: I, leaf: &Ty<I>) -> Option<Ty<I>> {
        let var = leaf.inference_var(interner)?;
        let p = self.probe_var(var)?;
        Some(p.assert_ty_ref(interner).clone())
    }

    pub fn normalize_lifetime_shallow(
        &mut self,
        interner: I,
        leaf: &Lifetime<I>,
    ) -> Option<Lifetime<I>> {
        let var = leaf.inference_var(interner)?;
        let p = self.probe_var(var)?;
        Some(p.assert_lifetime_ref(interner).clone())
    }

    pub fn normalize_const_shallow(&mut self, interner: I, leaf: &Const<I>) -> Option<Const<I>> {
        let var = leaf.inference_var(interner)?;
        let p = self.probe_var(var)?;
        Some(p.assert_const_ref(interner).clone())
    }

    pub fn ty_root(&mut self, interner: I, leaf: &Ty<I>) -> Option<Ty<I>> {
        Some(
            self.unify
                .find(leaf.inference_var(interner)?)
                .to_ty(interner),
        )
    }

    pub fn lifetime_root(&mut self, interner: I, leaf: &Lifetime<I>) -> Option<Lifetime<I>> {
        Some(
            self.unify
                .find(leaf.inference_var(interner)?)
                .to_lifetime(interner),
        )
    }

    /// Finds the root inference var for the given variable.
    ///
    /// The returned variable will be exactly equivalent to the given
    /// variable except in name. All variables which have been unified to
    /// eachother (but don't yet have a value) have the same "root".
    ///
    /// This is useful for `DeepNormalizer`.
    pub fn inference_var_root(&mut self, var: InferenceVar) -> InferenceVar {
        self.unify.find(var).into()
    }

    /// If type `leaf` is a free inference variable, and that variable has been
    /// bound, returns `Some(P)` where `P` is the parameter to which it has been bound.
    pub fn probe_var(&mut self, leaf: InferenceVar) -> Option<GenericArg<I>> {
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

    fn unify_var_var(&mut self, var1: EnaVariable<I>, var2: EnaVariable<I>) -> Fallible<()> {
        if let Err(_) = self.unify.unify_var_var(var1, var2) {
            return Err(NoSolution);
        }
        Ok(())
    }

    pub fn register_alias_var_constraint(&mut self, var: EnaVariable<I>, alias_ty: AliasTy<I>) -> Fallible<()> {
        // Make sure we're only handling the root var; this simplifies things
        let var = self.unify.find(var);

        // If the var itself is bound, that is a separate function
        assert!(matches!(self.unify.probe_value(var), InferenceValue::Unbound(_)));

        let existing_alias_var_a = self.inverse_alias_map.get(&alias_ty).copied();
        let existing_alias_var_b = self.inference_alias_map.get(&var).copied();
        match (existing_alias_var_a, existing_alias_var_b) {
            (Some(a), Some(b)) if a == b => {
                // Nothing to do, we've already registered this constraint before
            }
            (Some(a), Some(b)) => {
                // First, we need to unify the two inference variables
                let alias_inference_var = self.alias_var_to_inference_var_map.get(&b).unwrap();
                // (and they shouldn't be the same)
                assert_ne!(var, *alias_inference_var);
                if let Err(_) = self.unify.unify_var_var(var, *alias_inference_var) {
                    return Err(NoSolution);
                }
                // Then, we want to cleanup the existing maps, because we only
                // keep around info for root vars.
                let new_root = self.unify.find(var);
                if new_root == *alias_inference_var {
                    let new_aliases = self.alias_map.remove(&b).unwrap();
                    let aliases = self.alias_map.get_mut(&a).unwrap();
                    aliases.extend(new_aliases.into_iter());

                    for (_, val) in self.inverse_alias_map.iter_mut() {
                        if val == &b {
                            *val = a;
                        }
                    }
                    for (_, val) in self.inference_alias_map.iter_mut() {
                        if val == &b {
                            *val = a;
                        }
                    }
                    self.alias_var_to_inference_var_map.remove(&b);
                } else if new_root == var {
                    let new_aliases = self.alias_map.remove(&a).unwrap();
                    let aliases = self.alias_map.get_mut(&b).unwrap();
                    aliases.extend(new_aliases.into_iter());

                    for (_, val) in self.inverse_alias_map.iter_mut() {
                        if val == &a {
                            *val = b;
                        }
                    }
                    for (_, val) in self.inference_alias_map.iter_mut() {
                        if val == &a {
                            *val = b;
                        }
                    }
                    self.alias_var_to_inference_var_map.remove(&a);
                } else {
                    panic!();
                };
            }
            (Some(a), None) => {
                // If we've never seen the alias before, this is simple: just
                // add the alias to the existing set.
                self.inverse_alias_map.insert(alias_ty.clone(), a);
                let aliases = self.alias_map.get_mut(&a).unwrap();
                aliases.insert(alias_ty);
            }
            (None, Some(b)) => {
                // We've already seen the alias, which means that there is an
                // inference variable associated with it
                let alias_inference_var = self.alias_var_to_inference_var_map.get(&b).unwrap();
                // We have to unify them, but this *shouldn't* fail (because both
                // should be "unbound").
                if let Err(_) = self.unify.unify_var_var(var, *alias_inference_var) {
                    return Err(NoSolution);
                }
                // Make sure we register this mapping for the new inference var
                // Note: we're not removing the old key-value, even if the root
                // changes. We should be able to, I think. But it doesn't hurt.
                self.inference_alias_map.insert(var, b);
                // If the alias inference var is not the new root, then we need
                // to update the maps
                let new_root = self.unify.find(var);
                if new_root == var {
                    *self.alias_var_to_inference_var_map.get_mut(&b).unwrap() = var;
                }
            }
            (None, None) => {
                let alias_var_index = self.next_alias_var_index;
                self.next_alias_var_index += 1;
                let alias_var = AliasVar::from_index(alias_var_index);

                self.alias_map.insert(alias_var, Some(alias_ty.clone()).into_iter().collect());
                self.inverse_alias_map.insert(alias_ty, alias_var);
                self.inference_alias_map.insert(var, alias_var);
                self.alias_var_to_inference_var_map.insert(alias_var, var);
            }
        }
        Ok(())
    }

    pub fn register_alias_alias_constraint(&mut self, alias_a: AliasTy<I>, alias_b: AliasTy<I>) -> Fallible<()> {
        let existing_alias_var_a = self.inverse_alias_map.get(&alias_a).copied();
        let existing_alias_var_b = self.inverse_alias_map.get(&alias_b).copied();
        match (existing_alias_var_a, existing_alias_var_b) {
            (Some(a), Some(b)) if a == b => {
                // Nothing to do, we've already registered this constraint before
            }
            (Some(a), Some(b)) => {
                // First, we need to unify the two inference variables
                let alias_inference_var_a = self.alias_var_to_inference_var_map.get(&a).unwrap();
                let alias_inference_var_b = self.alias_var_to_inference_var_map.get(&b).unwrap();
                // (and they shouldn't be the same)
                assert_ne!(*alias_inference_var_a, *alias_inference_var_b);
                if let Err(_) = self.unify.unify_var_var(*alias_inference_var_a, *alias_inference_var_b) {
                    return Err(NoSolution);
                }
                // Then, we want to cleanup the existing maps, because we only
                // keep around info for root vars.
                let new_root = self.unify.find(*alias_inference_var_a);
                if new_root == *alias_inference_var_a {
                    let new_aliases = self.alias_map.remove(&b).unwrap();
                    let aliases = self.alias_map.get_mut(&a).unwrap();
                    aliases.extend(new_aliases.into_iter());

                    for (_, val) in self.inverse_alias_map.iter_mut() {
                        if val == &b {
                            *val = a;
                        }
                    }
                    for (_, val) in self.inference_alias_map.iter_mut() {
                        if val == &b {
                            *val = a;
                        }
                    }
                    self.alias_var_to_inference_var_map.remove(&b);
                } else if new_root == *alias_inference_var_b {
                    let new_aliases = self.alias_map.remove(&a).unwrap();
                    let aliases = self.alias_map.get_mut(&b).unwrap();
                    aliases.extend(new_aliases.into_iter());

                    for (_, val) in self.inverse_alias_map.iter_mut() {
                        if val == &a {
                            *val = b;
                        }
                    }
                    for (_, val) in self.inference_alias_map.iter_mut() {
                        if val == &a {
                            *val = b;
                        }
                    }
                    self.alias_var_to_inference_var_map.remove(&a);
                } else {
                    panic!();
                };
            }
            (Some(a), None) => {
                self.inverse_alias_map.insert(alias_b.clone(), a);
                let aliases = self.alias_map.get_mut(&a).unwrap();
                aliases.insert(alias_b);
            }
            (None, Some(b)) => {
                self.inverse_alias_map.insert(alias_a.clone(), b);
                let aliases = self.alias_map.get_mut(&b).unwrap();
                aliases.insert(alias_a);
            }
            (None, None) => {
                let alias_var_index = self.next_alias_var_index;
                self.next_alias_var_index += 1;
                let alias_var = AliasVar::from_index(alias_var_index);

                let mut set = FxHashSet::default();
                set.insert(alias_a.clone());
                set.insert(alias_b.clone());
                self.alias_map.insert(alias_var, set);
                self.inverse_alias_map.insert(alias_a, alias_var);
                self.inverse_alias_map.insert(alias_b, alias_var);

                let alias_inference_variable = self.new_variable(UniverseIndex::root());
                self.inference_alias_map.insert(alias_inference_variable, alias_var);
                self.alias_var_to_inference_var_map.insert(alias_var, alias_inference_variable);
            }
        }
        Ok(())
    }

    pub fn register_alias_rigid_constraint(&mut self, interner: I, alias: AliasTy<I>, ty: Ty<I>) -> Fallible<()> {
        let existing_alias_var = self.inverse_alias_map.get(&alias).copied();
        match existing_alias_var {
            // We've seen this alias before
            Some(var) => {
                // Have we unified this inference variable before?
                let alias_inference_var = *self.alias_var_to_inference_var_map.get(&var).unwrap();
                match self.probe_var(InferenceVar::from(alias_inference_var)) {
                    // Yes, so that value must equal the passed ty
                    Some(val) => {
                        if let Some(val_ty) = val.ty(interner) {
                            if val_ty == &ty {
                                return Ok(());
                            }
                        }
                        return Err(NoSolution);
                    }
                    None => {
                        self.unify
                            .unify_var_value(
                                alias_inference_var,
                                InferenceValue::from_ty(interner, ty),
                            ).unwrap();
                    }
                }
            }
            None => {
                // First need to make an alias
                let alias_var_index = self.next_alias_var_index;
                self.next_alias_var_index += 1;
                let alias_var = AliasVar::from_index(alias_var_index);

                let mut set = FxHashSet::default();
                set.insert(alias.clone());
                self.alias_map.insert(alias_var, set);
                self.inverse_alias_map.insert(alias, alias_var);

                // Then we need to make an inference var
                let alias_inference_variable = self.new_variable(UniverseIndex::root());
                self.inference_alias_map.insert(alias_inference_variable, alias_var);
                self.alias_var_to_inference_var_map.insert(alias_var, alias_inference_variable);

                // And finally, just set the inference variable to the given ty
                self.unify
                    .unify_var_value(
                        alias_inference_variable,
                        InferenceValue::from_ty(interner, ty),
                    ).unwrap();
            }
        }
        Ok(())
    }
}

pub trait ParameterEnaVariableExt<I: Interner> {
    fn to_generic_arg(&self, interner: I) -> GenericArg<I>;
}

impl<I: Interner> ParameterEnaVariableExt<I> for ParameterEnaVariable<I> {
    fn to_generic_arg(&self, interner: I) -> GenericArg<I> {
        // we are matching on kind, so skipping it is fine
        let ena_variable = self.skip_kind();
        match &self.kind {
            VariableKind::Ty(kind) => ena_variable.to_ty_with_kind(interner, *kind).cast(interner),
            VariableKind::Lifetime => ena_variable.to_lifetime(interner).cast(interner),
            VariableKind::Const(ty) => ena_variable.to_const(interner, ty.clone()).cast(interner),
        }
    }
}
