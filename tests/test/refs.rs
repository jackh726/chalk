use super::*;

#[test]
fn immut_refs_are_well_formed() {
    test! {
        program { }

        goal {
            forall<'a, T> { WellFormed(&'a T) }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}

#[test]
fn immut_refs_are_sized() {
    test! {
        program {
            #[lang(sized)]
            trait Sized { }
        }

        goal {
            forall<'a, T> { &'a T: Sized }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}

#[test]
fn mut_refs_are_well_formed() {
    test! {
        program { }

        goal {
            forall<'a, T> { WellFormed(&'a mut T) }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}

#[test]
fn mut_refs_are_sized() {
    test! {
        program {
            #[lang(sized)]
            trait Sized { }
        }

        goal {
            forall<'a, T> { &'a mut T: Sized }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}

#[test]
fn immut_refs_are_copy() {
    test! {
        program {
            #[lang(copy)]
            trait Copy { }
        }

        goal {
            forall<'a, T> { &'a T: Copy }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}

#[test]
fn immut_refs_are_clone() {
    test! {
        program {
            #[lang(clone)]
            trait Clone { }
        }

        goal {
            forall<'a, T> { &'a T: Clone }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}

#[test]
fn mut_refs_are_not_copy() {
    test! {
        program {
            #[lang(copy)]
            trait Copy { }
        }

        goal {
            forall<'a, T> { not { &'a mut T: Copy } }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}

#[test]
fn mut_refs_are_not_clone() {
    test! {
        program {
            #[lang(clone)]
            trait Clone { }
        }

        goal {
            forall<'a, T> { not { &'a mut T: Clone } }
        } yields {
            "Unique; substitution [], lifetime constraints []"
        }
    }
}
