use crate::clauses::builtin_traits::needs_impl_for_tys;
use crate::clauses::ClauseBuilder;
use crate::{Interner, RustIrDatabase, TraitRef};
use chalk_ir::{ApplicationTy, Substitution, TyData, TypeName};
use std::iter;

fn push_tuple_copy_conditions<I: Interner>(
    db: &dyn RustIrDatabase<I>,
    builder: &mut ClauseBuilder<'_, I>,
    trait_ref: &TraitRef<I>,
    arity: usize,
    substitution: &Substitution<I>,
) {
    // Empty tuples are always Copy
    if arity == 0 {
        builder.push_fact(trait_ref.clone());
        return;
    }

    let interner = db.interner();

    needs_impl_for_tys(
        db,
        builder,
        trait_ref,
        substitution
            .iter(interner)
            .map(|param| param.assert_ty_ref(interner).clone()),
    );
}

pub fn add_copy_program_clauses<I: Interner>(
    db: &dyn RustIrDatabase<I>,
    builder: &mut ClauseBuilder<'_, I>,
    trait_ref: &TraitRef<I>,
    ty: &TyData<I>,
) {
    let _interner = db.interner();

    match ty {
        TyData::Apply(ApplicationTy { name, substitution }) => match name {
            TypeName::Tuple(arity) => {
                push_tuple_copy_conditions(db, builder, trait_ref, *arity, substitution)
            }
            TypeName::Array => {
                let interner = db.interner();
                needs_impl_for_tys(
                    db,
                    builder,
                    trait_ref,
                    iter::once(substitution.at(interner, 0).assert_ty_ref(interner).clone()),
                );
            }
            TypeName::FnDef(_) => {
                builder.push_fact(trait_ref.clone());
            }
            TypeName::Closure(_) => {
                let interner = db.interner();
                match substitution
                    .parameters(interner)
                    .last()
                    .unwrap()
                    .assert_ty_ref(interner)
                    .data(interner)
                {
                    TyData::Apply(ApplicationTy { name, substitution }) => match name {
                        TypeName::Tuple(arity) => {
                            push_tuple_copy_conditions(db, builder, trait_ref, *arity, substitution)
                        }
                        _ => panic!("Expected tuple for upvars."),
                    },
                    _ => panic!("Expected tuple for upvars."),
                }
            }
            _ => return,
        },
        TyData::Function(_) => builder.push_fact(trait_ref.clone()),
        // TODO(areredify)
        // when #368 lands, extend this to handle everything accordingly
        _ => return,
    };
}
