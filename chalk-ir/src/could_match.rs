use crate::family::HasTypeFamily;
use crate::zip::{Zip, Zipper};
use crate::*;

/// A fast check to see whether two things could ever possibly match.
pub trait CouldMatch<T: ?Sized> {
    fn could_match(&self, other: &T) -> bool;
}

impl<T, TF> CouldMatch<T> for T
where
    T: Zip<TF> + ?Sized + HasTypeFamily<TypeFamily = TF>,
    TF: TypeFamily,
{
    fn could_match(&self, other: &T) -> bool {
        dbg!(self, other);
        return dbg!(Zip::zip_with(&mut MatchZipper, self, other).is_ok());

        struct MatchZipper;

        impl<TF: TypeFamily> Zipper<TF> for MatchZipper {
            fn zip_tys(&mut self, a: &Ty<TF>, b: &Ty<TF>) -> Fallible<()> {
                dbg!(a, b);
                let could_match = match (a.data(), b.data()) {
                    (&TyData::Apply(ref app_a), &TyData::Apply(ref app_b)) => {
                        if app_a.name == app_b.name &&
                            app_a.parameters
                                .iter()
                                .zip(&app_b.parameters)
                                .all(|(p_a, p_b)| p_a.could_match(p_b))
                        {
                            true
                        } else {
                            match (app_a.normalized_to.as_ref(), app_b.normalized_to.as_ref()) {
                                (Some(a), Some(b)) => {
                                    unimplemented!();
                                }
                                (Some(norm), None) => {
                                    self.zip_tys(&*norm, b)?;
                                    true
                                }
                                (None, Some(norm))=> {
                                    self.zip_tys(a, &*norm)?;
                                    true
                                }
                                (None, None) => false,
                            }
                        }
                    }

                    _ => true,
                };

                if dbg!(could_match) {
                    Ok(())
                } else {
                    Err(NoSolution)
                }
            }

            fn zip_lifetimes(&mut self, _: &Lifetime<TF>, _: &Lifetime<TF>) -> Fallible<()> {
                Ok(())
            }

            fn zip_binders<T>(&mut self, a: &Binders<T>, b: &Binders<T>) -> Fallible<()>
            where
                T: Zip<TF>,
            {
                Zip::zip_with(self, &a.value, &b.value)
            }
        }
    }
}

impl<TF: TypeFamily> CouldMatch<DomainGoal<TF>> for ProgramClause<TF> {
    fn could_match(&self, other: &DomainGoal<TF>) -> bool {
        match self {
            ProgramClause::Implies(implication) => implication.consequence.could_match(other),

            ProgramClause::ForAll(clause) => clause.value.consequence.could_match(other),
        }
    }
}
