use std::fmt::{Debug, Display, Error, Formatter};

use super::*;

impl Debug for RawId {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "#{}", self.index)
    }
}

impl<TF: TypeFamily> Debug for TraitId<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        TF::debug_trait_id(*self, fmt).unwrap_or_else(|| write!(fmt, "TraitId({:?})", self.0))
    }
}

impl<TF: TypeFamily> Debug for StructId<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        TF::debug_struct_id(*self, fmt).unwrap_or_else(|| write!(fmt, "StructId({:?})", self.0))
    }
}

impl<TF: TypeFamily> Debug for AssocTypeId<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        TF::debug_assoc_type_id(*self, fmt)
            .unwrap_or_else(|| write!(fmt, "AssocTypeId({:?})", self.0))
    }
}

impl Display for UniverseIndex {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "U{}", self.counter)
    }
}

impl Debug for UniverseIndex {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "U{}", self.counter)
    }
}

impl<TF: TypeFamily> Debug for TypeName<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            TypeName::Struct(id) => write!(fmt, "{:?}", id),
            TypeName::AssociatedType(assoc_ty) => write!(fmt, "{:?}", assoc_ty),
            TypeName::Error => write!(fmt, "{{error}}"),
        }
    }
}
impl<TF: TypeFamily> Debug for Ty<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "{:?}", self.data())
    }
}

impl<TF: TypeFamily> Debug for TyData<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            TyData::BoundVar(depth) => write!(fmt, "^{}", depth),
            TyData::Dyn(clauses) => write!(fmt, "{:?}", clauses),
            TyData::InferenceVar(var) => write!(fmt, "{:?}", var),
            TyData::Apply(apply) => write!(fmt, "{:?}", apply),
            TyData::Projection(proj) => write!(fmt, "{:?}", proj),
            TyData::Placeholder(index) => write!(fmt, "{:?}", index),
            TyData::Function(function) => write!(fmt, "{:?}", function),
        }
    }
}

impl<TF: TypeFamily> Debug for DynTy<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        let DynTy { bounds } = self;
        write!(fmt, "dyn {:?}", bounds)
    }
}

impl Debug for InferenceVar {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "?{}", self.index)
    }
}

impl<TF: TypeFamily> Debug for Fn<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        // FIXME -- we should introduce some names or something here
        let Fn {
            num_binders,
            parameters,
        } = self;
        write!(fmt, "for<{}> {:?}", num_binders, parameters)
    }
}

impl<TF: TypeFamily> Debug for Lifetime<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "{:?}", self.data())
    }
}

impl<TF: TypeFamily> Debug for LifetimeData<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            LifetimeData::BoundVar(depth) => write!(fmt, "'^{}", depth),
            LifetimeData::InferenceVar(var) => write!(fmt, "'{:?}", var),
            LifetimeData::Placeholder(index) => write!(fmt, "'{:?}", index),
            LifetimeData::Phantom(..) => unreachable!(),
        }
    }
}

impl Debug for PlaceholderIndex {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        let PlaceholderIndex { ui, idx } = self;
        write!(fmt, "!{}_{}", ui.counter, idx)
    }
}

impl<TF: TypeFamily> Debug for ApplicationTy<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        let ApplicationTy { name, substitution } = self;
        write!(fmt, "{:?}{:?}", name, substitution.with_angle())
    }
}

impl<TF: TypeFamily> TraitRef<TF> {
    /// Returns a "Debuggable" type that prints like `P0 as Trait<P1..>`
    pub fn with_as(&self) -> impl std::fmt::Debug + '_ {
        SeparatorTraitRef {
            trait_ref: self,
            separator: " as ",
        }
    }

    /// Returns a "Debuggable" type that prints like `P0: Trait<P1..>`
    pub fn with_colon(&self) -> impl std::fmt::Debug + '_ {
        SeparatorTraitRef {
            trait_ref: self,
            separator: ": ",
        }
    }
}

impl<TF: TypeFamily> Debug for TraitRef<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        Debug::fmt(&self.with_as(), fmt)
    }
}

struct SeparatorTraitRef<'me, TF: TypeFamily> {
    trait_ref: &'me TraitRef<TF>,
    separator: &'me str,
}

impl<TF: TypeFamily> Debug for SeparatorTraitRef<'_, TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        let parameters = self.trait_ref.substitution.parameters();
        write!(
            fmt,
            "{:?}{}{:?}{:?}",
            parameters[0],
            self.separator,
            self.trait_ref.trait_id,
            Angle(&parameters[1..])
        )
    }
}

impl<TF: TypeFamily> Debug for ProjectionTy<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        TF::debug_projection(self, fmt).unwrap_or_else(|| {
            write!(
                fmt,
                "({:?}){:?}",
                self.associated_ty_id,
                self.substitution.with_angle()
            )
        })
    }
}

pub struct Angle<'a, T: 'a>(pub &'a [T]);

impl<'a, T: Debug> Debug for Angle<'a, T> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        if self.0.len() > 0 {
            write!(fmt, "<")?;
            for (index, elem) in self.0.iter().enumerate() {
                if index > 0 {
                    write!(fmt, ", {:?}", elem)?;
                } else {
                    write!(fmt, "{:?}", elem)?;
                }
            }
            write!(fmt, ">")?;
        }
        Ok(())
    }
}

impl<TF: TypeFamily> Debug for Normalize<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(
            fmt,
            "Normalize({:?}{:?} -> {:?})",
            self.associated_ty_id, self.substitution.with_angle(), self.ty
        )
    }
}

impl<TF: TypeFamily> Debug for ProjectionEq<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "ProjectionEq({:?} = {:?})", self.projection, self.ty)
    }
}

impl<TF: TypeFamily> Debug for WhereClause<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            WhereClause::Implemented(tr) => write!(fmt, "Implemented({:?})", tr.with_colon()),
            WhereClause::ProjectionEq(p) => write!(fmt, "{:?}", p),
            WhereClause::Normalize(n) => write!(fmt, "{:?}", n),
        }
    }
}

impl<TF: TypeFamily> Debug for FromEnv<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            FromEnv::Trait(t) => write!(fmt, "FromEnv({:?})", t.with_colon()),
            FromEnv::Ty(t) => write!(fmt, "FromEnv({:?})", t),
        }
    }
}

impl<TF: TypeFamily> Debug for WellFormed<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            WellFormed::Trait(t) => write!(fmt, "WellFormed({:?})", t.with_colon()),
            WellFormed::Ty(t) => write!(fmt, "WellFormed({:?})", t),
        }
    }
}

impl<TF: TypeFamily> Debug for DomainGoal<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            DomainGoal::Holds(n) => write!(fmt, "{:?}", n),
            DomainGoal::WellFormed(n) => write!(fmt, "{:?}", n),
            DomainGoal::FromEnv(n) => write!(fmt, "{:?}", n),
            DomainGoal::IsLocal(n) => write!(fmt, "IsLocal({:?})", n),
            DomainGoal::IsUpstream(n) => write!(fmt, "IsUpstream({:?})", n),
            DomainGoal::IsFullyVisible(n) => write!(fmt, "IsFullyVisible({:?})", n),
            DomainGoal::LocalImplAllowed(tr) => {
                write!(fmt, "LocalImplAllowed({:?})", tr.with_colon(),)
            }
            DomainGoal::Compatible(_) => write!(fmt, "Compatible"),
            DomainGoal::DownstreamType(n) => write!(fmt, "DownstreamType({:?})", n),
        }
    }
}

impl<TF: TypeFamily> Debug for EqGoal<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "({:?} = {:?})", self.a, self.b)
    }
}

impl<TF: TypeFamily> Debug for Goal<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self.data() {
            GoalData::Quantified(qkind, ref subgoal) => {
                write!(fmt, "{:?}<", qkind)?;
                for (index, binder) in subgoal.binders.iter().enumerate() {
                    if index > 0 {
                        write!(fmt, ", ")?;
                    }
                    match *binder {
                        ParameterKind::Ty(()) => write!(fmt, "type")?,
                        ParameterKind::Lifetime(()) => write!(fmt, "lifetime")?,
                    }
                }
                write!(fmt, "> {{ {:?} }}", subgoal.value)
            }
            GoalData::Implies(ref wc, ref g) => write!(fmt, "if ({:?}) {{ {:?} }}", wc, g),
            GoalData::All(ref goals) => {
                write!(fmt, "all(")?;
                for (goal, index) in goals.iter().zip(0..) {
                    if index > 0 {
                        write!(fmt, ", ")?;
                    }
                    write!(fmt, "{:?}", goal)?;
                }
                write!(fmt, ")")?;
                Ok(())
            }
            GoalData::Not(ref g) => write!(fmt, "not {{ {:?} }}", g),
            GoalData::EqGoal(ref wc) => write!(fmt, "{:?}", wc),
            GoalData::DomainGoal(ref wc) => write!(fmt, "{:?}", wc),
            GoalData::CannotProve(()) => write!(fmt, r"¯\_(ツ)_/¯"),
        }
    }
}

impl<T: Debug> Debug for Binders<T> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        let Binders {
            ref binders,
            ref value,
        } = *self;
        if !binders.is_empty() {
            write!(fmt, "for<")?;
            for (index, binder) in binders.iter().enumerate() {
                if index > 0 {
                    write!(fmt, ", ")?;
                }
                match *binder {
                    ParameterKind::Ty(()) => write!(fmt, "type")?,
                    ParameterKind::Lifetime(()) => write!(fmt, "lifetime")?,
                }
            }
            write!(fmt, "> ")?;
        }
        Debug::fmt(value, fmt)
    }
}

impl<TF: TypeFamily> Debug for ProgramClause<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            ProgramClause::Implies(pc) => write!(fmt, "Implies({:?})", pc),
            ProgramClause::ForAll(pc) => write!(fmt, "ForAll({:?})", pc),
        }
    }
}

impl<TF: TypeFamily> Debug for ProgramClauseImplication<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "{:?}", self.consequence)?;

        let conds = self.conditions.len();
        if conds == 0 {
            return Ok(());
        }

        write!(fmt, " :- ")?;
        for cond in &self.conditions[..conds - 1] {
            write!(fmt, "{:?}, ", cond)?;
        }
        write!(fmt, "{:?}", self.conditions[conds - 1])
    }
}

impl<TF: TypeFamily> Debug for Environment<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        write!(fmt, "Env({:?})", self.clauses)
    }
}

impl<T: Display> Display for Canonical<T> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let Canonical { binders, value } = self;

        if binders.is_empty() {
            write!(f, "{}", value)?;
        } else {
            write!(f, "for<")?;

            for (i, pk) in binders.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, "?{}", pk.into_inner())?;
            }

            write!(f, "> {{ {} }}", value)?;
        }

        Ok(())
    }
}

impl<T: Debug, L: Debug> Debug for ParameterKind<T, L> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match *self {
            ParameterKind::Ty(ref n) => write!(fmt, "Ty({:?})", n),
            ParameterKind::Lifetime(ref n) => write!(fmt, "Lifetime({:?})", n),
        }
    }
}

impl<TF: TypeFamily> Debug for Parameter<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self.data() {
            ParameterKind::Ty(n) => write!(fmt, "{:?}", n),
            ParameterKind::Lifetime(n) => write!(fmt, "{:?}", n),
        }
    }
}

impl<TF: TypeFamily> Debug for Constraint<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        match self {
            Constraint::LifetimeEq(a, b) => write!(fmt, "{:?} == {:?}", a, b),
        }
    }
}

impl<TF: TypeFamily> Display for ConstrainedSubst<TF> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let ConstrainedSubst { subst, constraints } = self;

        write!(
            f,
            "substitution {}, lifetime constraints {:?}",
            subst, constraints,
        )
    }
}

impl<TF: TypeFamily> Substitution<TF> {
    /// Displays the substitution in the form `< P0, .. Pn >`, or (if
    /// the substitution is empty) as an empty string.
    pub fn with_angle(&self) -> Angle<'_, Parameter<TF>> {
        Angle(self.parameters())
    }
}

impl<TF: TypeFamily> Debug for Substitution<TF> {
    fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
        Display::fmt(self, fmt)
    }
}

impl<TF: TypeFamily> Display for Substitution<TF> {
    fn fmt(&self, f: &mut Formatter) -> Result<(), Error> {
        let mut first = true;

        write!(f, "[")?;

        for (index, value) in self.iter().enumerate() {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }

            write!(f, "?{} := {:?}", index, value)?;
        }

        write!(f, "]")?;

        Ok(())
    }
}
