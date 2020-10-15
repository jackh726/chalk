//! Useful macros for writing unit tests. They let you gin up dummy types and things.

#[macro_export]
macro_rules! ty {
    (apply $n:tt $($arg:tt)*) => {
        chalk_ir::TyData::Apply(chalk_ir::ApplicationTy {
            name: ty_name!($n),
            substitution: chalk_ir::Substitution::from_iter(
                &chalk_integration::interner::ChalkIr,
                vec![$(arg!($arg)),*] as Vec<chalk_ir::GenericArg<_>>
            ),
        }).intern(&chalk_integration::interner::ChalkIr)
    };

    (function $n:tt $($arg:tt)*) => {
        chalk_ir::TyData::Function(chalk_ir::FnPointer {
            num_binders: $n,
            substitution: chalk_ir::Substitution::from_iter(
                &chalk_integration::interner::ChalkIr,
                vec![$(arg!($arg)),*] as Vec<chalk_ir::GenericArg<_>>
            ),
            sig: chalk_ir::FnSig {
                safety: chalk_ir::Safety::Safe,
                abi: <chalk_integration::interner::ChalkIr as chalk_ir::interner::Interner>::FnAbi::Rust,
                variadic: false,
            }
        }).intern(&chalk_integration::interner::ChalkIr)
    };

    (placeholder $n:expr) => {
        chalk_ir::TyData::Placeholder(PlaceholderIndex {
            ui: UniverseIndex { counter: $n },
            idx: 0,
        }).intern(&chalk_integration::interner::ChalkIr)
    };

    (projection (item $n:tt) $($arg:tt)*) => {
        chalk_ir::AliasTy::Projection(chalk_ir::ProjectionTy  {
            associated_ty_id: chalk_ir::AssocTypeId(chalk_integration::interner::RawId { index: $n }),
            substitution: chalk_ir::Substitution::from_iter(
                &chalk_integration::interner::ChalkIr,
                vec![$(arg!($arg)),*] as Vec<chalk_ir::GenericArg<_>>
            ),
        }).intern(&chalk_integration::interner::ChalkIr)
    };

    (infer $b:expr) => {
        chalk_ir::TyData::InferenceVar(chalk_ir::InferenceVar::from($b), chalk_ir::TyKind::General)
            .intern(&chalk_integration::interner::ChalkIr)
    };

    (bound $d:tt $b:tt) => {
        chalk_ir::TyData::BoundVar(chalk_ir::BoundVar::new(chalk_ir::DebruijnIndex::new($d), $b))
            .intern(&chalk_integration::interner::ChalkIr)
    };

    (bound $b:expr) => {
        chalk_ir::TyData::BoundVar(chalk_ir::BoundVar::new(chalk_ir::DebruijnIndex::INNERMOST, $b))
            .intern(&chalk_integration::interner::ChalkIr)
    };

    (expr $b:expr) => {
        $b.clone()
    };

    (($($b:tt)*)) => {
        ty!($($b)*)
    };
}

#[macro_export]
macro_rules! arg {
    ((lifetime $b:tt)) => {
        chalk_ir::GenericArg::new(
            &chalk_integration::interner::ChalkIr,
            chalk_ir::GenericArgData::Lifetime(lifetime!($b)),
        )
    };

    ($arg:tt) => {
        chalk_ir::GenericArg::new(
            &chalk_integration::interner::ChalkIr,
            chalk_ir::GenericArgData::Ty(ty!($arg)),
        )
    };
}

#[macro_export]
macro_rules! lifetime {
    (infer $b:expr) => {
        chalk_ir::LifetimeData::InferenceVar(chalk_ir::InferenceVar::from($b))
            .intern(&chalk_integration::interner::ChalkIr)
    };

    (bound $d:tt $b:tt) => {
        chalk_ir::LifetimeData::BoundVar(chalk_ir::BoundVar::new(chalk_ir::DebruijnIndex::new($d), $b))
            .intern(&chalk_integration::interner::ChalkIr)
    };

    (bound $b:expr) => {
        chalk_ir::LifetimeData::BoundVar(chalk_ir::BoundVar::new(chalk_ir::DebruijnIndex::INNERMOST, $b))
            .intern(&chalk_integration::interner::ChalkIr)
    };

    (placeholder $b:expr) => {
        chalk_ir::LifetimeData::Placeholder(PlaceholderIndex { ui: UniverseIndex { counter: $b }, idx: 0})
            .intern(&chalk_integration::interner::ChalkIr)
    };

    (expr $b:expr) => {
        $b.clone()
    };

    (($($b:tt)*)) => {
        lifetime!($($b)*)
    };
}

#[macro_export]
macro_rules! ty_name {
    ((item $n:expr)) => {
        chalk_ir::TypeName::Adt(chalk_ir::AdtId(chalk_integration::interner::RawId {
            index: $n,
        }))
    };
}

#[macro_export]
macro_rules! trait_name {
    ($n:expr) => {
        chalk_ir::TraitId(chalk_integration::interner::RawId { index: $n })
    };
}

#[macro_export]
macro_rules! domain_goal {
    (holds implemented $n:tt $($arg:tt)*) => {
        chalk_ir::DomainGoal::Holds(
            chalk_ir::WhereClause::Implemented(
                chalk_ir::TraitRef {
                    trait_id: trait_name!($n),
                    substitution: chalk_ir::Substitution::from_iter(
                        &chalk_integration::interner::ChalkIr,
                        vec![$(arg!($arg)),*] as Vec<chalk_ir::GenericArg<_>>
                    ),
                },
            ),
        )
    }
}
