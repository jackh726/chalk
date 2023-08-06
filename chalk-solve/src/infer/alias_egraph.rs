use chalk_ir::interner::Interner;
use chalk_ir::*;
use ena::unify::{UnifyKey, UnifyValue};
use rustc_hash::{FxHashMap, FxHashSet};
use std::marker::PhantomData;
use std::u32;
use tracing::debug;

use super::InferenceTable;
use super::var::{EnaVariable, InferenceValue};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AliasVar<I: Interner> {
    index: u32,
    phantom: PhantomData<I>,
}

impl<I: Interner> UnifyKey for AliasVar<I> {
    type Value = AliasValue<I>;

    fn index(&self) -> u32 {
        self.index
    }

    fn from_index(u: u32) -> Self {
        AliasVar {
            index: u,
            phantom: PhantomData,
        }
        
    }

    fn tag() -> &'static str {
        "AliasVar"
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AliasValue<I: Interner> {
    aliases: Vec<AliasTy<I>>,
    value: Option<Ty<I>>,
}

impl<I: Interner> UnifyValue for AliasValue<I> {
    type Error = ();

    fn unify_values(
        a: &AliasValue<I>,
        b: &AliasValue<I>,
    ) -> Result<Self, Self::Error> {
        todo!()
    }
}

// Some special things to note about aliases:
// Whenever we encounter an alias and relate it to something, we always replace
// that with a new inference variable, registering that relations into a map.
//
// These can be thought after as a set of AliasEq clauses from the alias to the
// common inference variable.
#[derive(Debug)]
pub struct Egraph<I: Interner> {
    alias_map: FxHashMap<AliasVar<I>, FxHashSet<AliasTy<I>>>,
    inverse_alias_map: FxHashMap<AliasTy<I>, AliasVar<I>>,
    inference_alias_map: FxHashMap<EnaVariable<I>, AliasVar<I>>,
    alias_var_to_inference_var_map: FxHashMap<AliasVar<I>, EnaVariable<I>>,
    next_alias_var_index: u32,
}

impl<I: Interner> Egraph<I> {
    pub fn new() -> Self {
        Egraph {
            alias_map: FxHashMap::default(),
            inverse_alias_map: FxHashMap::default(),
            inference_alias_map: FxHashMap::default(),
            alias_var_to_inference_var_map: FxHashMap::default(),
            next_alias_var_index: 0,
        }
    }

    pub fn from_constraints(interner: I, table: &mut InferenceTable<I>, egraph: Vec<(AliasTy<I>, Ty<I>)>) -> Fallible<Self> {
        let mut this = Self::new();
        this.register_egraph(interner, table, egraph)?;
        Ok(this)
    }

    #[tracing::instrument(level = "debug", skip(self, interner, table))]
    pub fn register_alias_var_constraint(&mut self, interner: I, table: &mut InferenceTable<I>, var: EnaVariable<I>, alias_ty: AliasTy<I>) -> Fallible<()> {
        // Make sure we're only handling the root var; this simplifies things
        let var = table.unify.find(var);

        // If the var itself is bound, that is a separate function
        if let InferenceValue::Bound(ty) = table.unify.probe_value(var) {
            return self.register_alias_rigid_constraint(interner, table, alias_ty, ty.ty(interner).unwrap().clone());
        }

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
                if let Err(_) = table.unify.unify_var_var(var, *alias_inference_var) {
                    return Err(NoSolution);
                }
                // Then, we want to cleanup the existing maps, because we only
                // keep around info for root vars.
                let new_root = table.unify.find(var);
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
                if let Err(_) = table.unify.unify_var_var(var, *alias_inference_var) {
                    return Err(NoSolution);
                }
                // Make sure we register this mapping for the new inference var
                // Note: we're not removing the old key-value, even if the root
                // changes. We should be able to, I think. But it doesn't hurt.
                self.inference_alias_map.insert(var, b);
                // If the alias inference var is not the new root, then we need
                // to update the maps
                let new_root = table.unify.find(var);
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

    #[tracing::instrument(level = "debug", skip(self, table))]
    pub fn register_alias_alias_constraint(&mut self, table: &mut InferenceTable<I>, alias_a: AliasTy<I>, alias_b: AliasTy<I>) -> Fallible<()> {
        let existing_alias_var_a = self.inverse_alias_map.get(&alias_a).copied();
        let existing_alias_var_b = self.inverse_alias_map.get(&alias_b).copied();
        dbg!(&existing_alias_var_a, &existing_alias_var_b);
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
                if let Err(_) = table.unify.unify_var_var(*alias_inference_var_a, *alias_inference_var_b) {
                    return Err(NoSolution);
                }
                // Then, we want to cleanup the existing maps, because we only
                // keep around info for root vars.
                let new_root = table.unify.find(*alias_inference_var_a);
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

                let alias_inference_variable = table.new_variable(UniverseIndex::root());
                self.inference_alias_map.insert(alias_inference_variable, alias_var);
                self.alias_var_to_inference_var_map.insert(alias_var, alias_inference_variable);
                dbg!(&self);
            }
        }
        Ok(())
    }

    #[tracing::instrument(level = "debug", skip(self, interner, table))]
    pub fn register_alias_rigid_constraint(&mut self, interner: I, table: &mut InferenceTable<I>, alias: AliasTy<I>, ty: Ty<I>) -> Fallible<()> {
        let existing_alias_var = self.inverse_alias_map.get(&alias).copied();
        match existing_alias_var {
            // We've seen this alias before
            Some(var) => {
                // Have we unified this inference variable before?
                let alias_inference_var = *self.alias_var_to_inference_var_map.get(&var).unwrap();
                match table.probe_var(InferenceVar::from(alias_inference_var)) {
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
                        table.unify
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
                let alias_inference_variable = table.new_variable(UniverseIndex::root());
                self.inference_alias_map.insert(alias_inference_variable, alias_var);
                self.alias_var_to_inference_var_map.insert(alias_var, alias_inference_variable);

                // And finally, just set the inference variable to the given ty
                table.unify
                    .unify_var_value(
                        alias_inference_variable,
                        InferenceValue::from_ty(interner, ty),
                    ).unwrap();
            }
        }
        Ok(())
    }

    pub fn alias_egraph(&self, interner: I) -> Vec<(AliasTy<I>, Ty<I>)> {
        self.inverse_alias_map
            .iter()
            .map(|(alias_ty, alias_var)| {
                let ena_var = self.alias_var_to_inference_var_map.get(alias_var).unwrap();
                let inference_var = ena_var.to_ty(interner);
                (alias_ty.clone(), inference_var)
            })
            .collect()
    }

    pub fn register_egraph(&mut self, interner: I, table: &mut InferenceTable<I>, egraph: Vec<(AliasTy<I>, Ty<I>)>) -> Fallible<()> {
        debug!(?egraph);
        for (alias_ty, ty) in egraph {
            match ty.inference_var(interner) {
                Some(var) => self.register_alias_var_constraint(interner, table, var.into(), alias_ty)?,
                None => self.register_alias_rigid_constraint(interner, table, alias_ty, ty)?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod test {
    #[test]
    fn test_alias_unification() {
        let table: ena::unify::InPlaceUnificationTable<EnaVariable<I>> = ena::unify::UnificationTable::new();
    }
}
