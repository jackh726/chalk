use super::*;

#[test]
fn scalar_in_tuple_trait_impl() {
    test! {
        program {
            trait Foo { }
            impl Foo for usize { }
            impl Foo for isize { }
            impl<T1, T2> Foo for (T1, T2) where T1: Foo, T2: Foo { }
            impl<T> Foo for (T,T,T) where T: Foo { }
        }

        goal {
            (usize, usize): Foo
        } yields {
            "Unique"
        }

        goal {
            (usize, isize): Foo
        } yields {
            "Unique"
        }

        goal {
            (usize, bool): Foo
        } yields {
            "No possible solution"
        }

        goal {
            (usize, usize, usize): Foo
        } yields {
            "Unique"
        }

        goal {
            (char, u8, i8): Foo
        } yields {
            "No possible solution"
        }
    }
}

#[test]
fn scalar_trait_impl() {
    test! {
        program {
            trait Foo { }

            impl Foo for i8 { }
            impl Foo for i16 { }
            impl Foo for i32 { }
            impl Foo for i64 { }
            impl Foo for i128 { }
            impl Foo for isize { }
            impl Foo for u8 { }
            impl Foo for u16 { }
            impl Foo for u32 { }
            impl Foo for u64 { }
            impl Foo for u128 { }
            impl Foo for usize { }
            impl Foo for f32 { }
            impl Foo for f64 { }
            impl Foo for bool { }
            impl Foo for char { }
        }

        goal { i8: Foo } yields { "Unique" }
        goal { i16: Foo } yields { "Unique" }
        goal { i32: Foo } yields { "Unique" }
        goal { i64: Foo } yields { "Unique" }
        goal { i128: Foo } yields { "Unique" }
        goal { isize: Foo } yields { "Unique" }
        goal { u8: Foo } yields { "Unique" }
        goal { u16: Foo } yields { "Unique" }
        goal { u32: Foo } yields { "Unique" }
        goal { u64: Foo } yields { "Unique" }
        goal { u128: Foo } yields { "Unique" }
        goal { usize: Foo } yields { "Unique" }
        goal { f32: Foo } yields { "Unique" }
        goal { f64: Foo } yields { "Unique" }
        goal { bool: Foo } yields { "Unique" }
        goal { char: Foo } yields { "Unique" }
    }
}
