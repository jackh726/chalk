use chalk_ir::cast::Cast;
use chalk_ir::interner::Interner;
use chalk_ir::*;
use ena::unify::{UnifyKey, UnifyValue};
use std::cmp::min;
use std::fmt;
use std::marker::PhantomData;
use std::u32;

use super::var::EnaVariable;

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

#[cfg(test)]
mod test {
    #[test]
    fn test_alias_unification() {
        let table: ena::unify::InPlaceUnificationTable<EnaVariable<I>> = ena::unify::UnificationTable::new();
    }
}