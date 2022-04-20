//! This crate is aiming to make work with [variance][var] easier.
//! The crate exposes 3 types - [`Invariant<T>`][inv], [`Covariant<T>`][cov] and
//! [`Contravariant<T>`][cnt] with corresponding variance over `T` those work
//! in a very similar way to [`PhantomData<_>`][phd].
//!
//! [var]: https://doc.rust-lang.org/nomicon/subtyping.html
//! [inv]: crate::Invariant#type
//! [cov]: crate::Covariant#type
//! [cnt]: crate::Contravariant#type
//! [phd]: core::marker::PhantomData
//!
//! ## motivation
//!
//! In rust it's an error to have an unused generic param in struct:
//! ```compile_fail
//! struct Slice<'a, T> {
//!     start: *const T,
//!     end: *const T,
//! }
//! ```
//! ```text
//! error[E0392]: parameter `'a` is never used
//!  --> src/lib.rs:16:14
//!   |
//! 3 | struct Slice<'a, T> {
//!   |              ^^ unused parameter
//!   |
//!   = help: consider removing `'a`, referring to it in a field, or using a marker such as `std::marker::PhantomData`
//! ```
//! This is an error because rust compiler doesn't know should `Slice` be
//! covariant, contravariant or invariant over `'a`. What this means is that
//! rustc doesn't know if `Slice<'static, _>` should be a subtype of `Slice<'a,
//! _>` or vice versa or neither. See [Subtyping and Variance][nom] nomicon
//! chapter for better explanation
//!
//! To mitigate this issue and control the variance there is a type called
//! [`marker::PhantomData<T>`][phd]. [`PhantomData<T>`][phd] is a
//! zero-sized type that acts like it owns `T`.
//!
//! However, [`PhantomData`][phd] comes with a number of issues:
//! 1. Variance is a hard thing to understand by itself, but
//!    [`PhantomData`][phd] makes it    even harder to understand. It's not
//!    straightforward to understand what    statement like `PhantomData<fn(A,
//!    B) -> B>` does (contravariant over `A` and invariant over `B`)
//! 2. Sometimes it works badly in `const` context (see next
//!    [paragraph](#function-pointers-in-const-fn-are-unstable))
//!
//! `phantasm`'s naming helps with the first issue by making the original
//! intention clearer (though variance still is a hard-to-understand thing) and
//! with the second by doing some _hacks under the hood_.
//!
//! [nom]: https://doc.rust-lang.org/nomicon/subtyping.html#subtyping-and-variance
//!
//! ## function pointers in `const fn` are unstable
//!
//! It's common practice to make a type invariant over `T` with
//! `PhantomData<fn(T) -> T>`. However, if you've ever tried to use it in a
//! `const fn`, you know that it's painful (see [rust-lang/69459][my_issue] and
//! [rust-lang/67649][or_issue]) because before Rust `1.61.0` function pointers
//! in `const fn` were unstable, see [stabilization PR] for more. This crate
//! helps with this problem:
//!
//! ```
//! use phantasm::Invariant;
//!
//! pub struct Test<T>(Invariant<T>);
//!
//! impl<T> Test<T> {
//!     pub const fn new() -> Self {
//!         Self(Invariant) // just works (even on old rust)
//!     }
//! }
//! ```
//! [my_issue]: https://github.com/rust-lang/rust/issues/69459
//! [or_issue]: https://github.com/rust-lang/rust/issues/67649
//! [stabilization PR]: https://github.com/rust-lang/rust/pull/93827
//!
//! ## life
//!
//! For variance over lifetimes, use `&'l ()`:
//! ```
//! use phantasm::{Contravariant, Covariant, Invariant};
//!
//! # // yep, I just don't want to copy&paste everything yet again
//! struct Test<'a, 'b, 'c>(Invariant<&'a ()>, Covariant<&'b ()>, Contravariant<&'c ()>);
//! ```
//!
//! ## comparison operators cannot be chained
//!
//! Note: you can't use `Invariant<Ty>` as a value (just as
//! [`PhantomData`][phd]). To create `Invariant<Ty>` value use turbofish:
//! `Invariant::<Ty>` (same goes for both [`Covariant<T>`][cov] and
//! [`Contravariant<T>`][cnt])
//!
//! ```compile_fail
//! // won't compile
//! let _ = phantasm::Invariant<i32>;
//! ```
//!
//! ```
//! use phantasm::Invariant;
//!
//! // ok
//! let _ = Invariant::<i32>;
//!
//! // Both forms are acceptable in type position
//! struct NoFish<T>(Invariant<T>);
//! struct Turbofish<T>(Invariant<T>);
//! ```
//!
//! ## many types
//!
//! When you need to set variance of many types at once, just use a tuple:
//! ```
//! struct Test<A, B>(phantasm::Covariant<(A, B)>);
//! ```
#![cfg_attr(not(test), no_std)] // `format!` is used in tests
#![allow(type_alias_bounds)] // for :?Sized bound to appear in docs
#![deny(missing_docs)]
#![forbid(unsafe_code)]

/// Marker zero-sized type that is invariant over `T`.
///
/// "Invariant" means that given `F<_>`, `Super` and `Sub` (where `Sub` is a
/// subtype of `Super`), `F<Sub>` is **not** a subtype of `F<Super>` and vice
/// versa - `F<Super>` is **not** a subtype of `F<Sub>`
///
/// ## Examples
///
/// ```
/// use phantasm::Invariant;
///
/// // This struct is invariant over `T`
/// struct Test<T>(Invariant<T> /* ... */);
///
/// let _: Test<i32> = Test(Invariant /* ... */);
/// let _ = Test::<i32>(Invariant /* ... */);
/// let _ = Test(Invariant::<i32> /* ... */);
/// ```
///
/// ```compile_fail,E0308
/// use phantasm::Invariant;
///
/// // `F<Sub>` is **not** a subtype of `F<Super>`
/// fn covariant_fail<'l>(with_sub: Invariant<&'static ()>) {
///     let with_super: Invariant<&'l ()> = with_sub; // mismatched types
/// }
/// ```
///
/// ```compile_fail,E0308
/// use phantasm::Invariant;
///
/// // `F<Super>` is **not** a subtype of `F<Sub>`
/// fn contravariant_fail<'l>(with_super: Invariant<&'l ()>) {
///     let with_sub: Invariant<&'static ()> = with_super; // mismatched types
/// }
/// ```
///
/// ## See also
///
/// - [crate docs](crate)
/// - [`PhantomData`](core::marker::PhantomData)
/// - [Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html)
///   nomicon chapter
pub type Invariant<T: ?Sized> = r#impl::Invariant<T>;

/// Marker zero-sized type that is covariant over `T`.
///
/// "Covariant" means that given `F<_>`, `Super` and `Sub` (where `Sub` is a
/// subtype of `Super`), `F<Sub>` **is** a subtype of `F<Super>` (but `F<Super>`
/// is **not** a subtype of `F<Sub>`)
///
/// ## Examples
///
/// ```
/// use phantasm::Covariant;
///
/// // This struct is covariant over `T`
/// struct Test<T>(Covariant<T> /* ... */);
///
/// let _: Test<i32> = Test(Covariant /* ... */);
/// let _ = Test::<i32>(Covariant /* ... */);
/// let _ = Test(Covariant::<i32> /* ... */);
/// ```
///
/// ```
/// use phantasm::Covariant;
///
/// // `F<Sub>` **is** a subtype of `F<Super>`
/// fn covariant_pass<'l>(with_sub: Covariant<&'static ()>) {
///     let with_super: Covariant<&'l ()> = with_sub;
/// }
/// ```
///
/// ```compile_fail,E0308
/// use phantasm::Covariant;
///
/// // `F<Super>` is **not** a subtype of `F<Sub>`
/// fn contravariant_fail<'l>(with_super: Covariant<&'l ()>) {
///     let with_sub: Covariant<&'static ()> = with_super; // mismatched types
/// }
/// ```
///
/// ## See also
///
/// - [crate docs](crate)
/// - [`PhantomData`](core::marker::PhantomData)
/// - [Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html)
///   nomicon chapter
pub type Covariant<T: ?Sized> = r#impl::Covariant<T>;

/// Marker zero-sized type that is contravariant over `T`.
///
/// "Contravariant" means that given `F<_>`, `Super` and `Sub` (where `Sub` is a
/// subtype of `Super`), `F<Super>` **is** a subtype of `F<Sub>` (but `F<Sub>`
/// is **not** a subtype of `F<Super>`)
///
/// ## Examples
///
/// ```
/// use phantasm::Contravariant;
///
/// // This struct is covariant over `T`
/// struct Test<T>(Contravariant<T> /* ... */);
///
/// let _: Test<i32> = Test(Contravariant /* ... */);
/// let _ = Test::<i32>(Contravariant /* ... */);
/// let _ = Test(Contravariant::<i32> /* ... */);
/// ```
///
/// ```compile_fail,E0308
/// use phantasm::Contravariant;
///
/// // `F<Sub>` is **not** a subtype of `F<Super>`
/// fn covariant_fail<'l>(with_sub: Contravariant<&'static ()>) {
///     let with_super: Contravariant<&'l ()> = with_sub; // mismatched types
/// }
/// ```
///
/// ```
/// use phantasm::Contravariant;
///
/// // `F<Super>` **is** a subtype of `F<Sub>`
/// fn contravariant_pass<'l>(with_super: Contravariant<&'l ()>) {
///     let with_sub: Contravariant<&'static ()> = with_super;
/// }
/// ```
///
/// ## See also
///
/// - [crate docs](crate)
/// - [`PhantomData`](core::marker::PhantomData)
/// - [Subtyping and Variance](https://doc.rust-lang.org/nomicon/subtyping.html)
///   nomicon chapter
pub type Contravariant<T: ?Sized> = r#impl::Contravariant<T>;

/// Brings `Invariant`/`Covariant`/`Contravariant` values to scope (in addition
/// to types)
#[doc(hidden)]
pub use crate::r#impl::reexport_hack::*;

/// Implementation of the types in the crate.
///
/// This is a private module to hide ugly enum implementation details and make
/// doc cleaner.
mod r#impl {
    // Note: the idea of the implementation is actually copy-pasted from
    // dtolnay's ghost <https://docs.rs/ghost/> (I haven't used it to be 0-dep, yep, I'm a bad guy)

    /// A hack to have both type and variant in the same namespace.
    ///
    /// This allows to do the following:
    ///
    /// ```
    /// use phantasm::Invariant;
    ///
    /// let _: Invariant<i32> = Invariant::<i32>; // (same goes for `Covariant` and `Contravariant`)
    /// //    |^^^^^^^^^^^^^^   ^^^^^^^^^^^^^^^^\
    /// //    *--- type                          value (variant)
    /// ```
    ///
    /// (idk how it works, but it works)
    pub mod reexport_hack {
        pub use super::{Contravariant::Contravariant, Covariant::Covariant, Invariant::Invariant};
    }

    /// Replacement for `!` aka never that will never be stabilized.
    #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
    pub enum Never {}

    /// For documentation see [`Invariant`](crate::Invariant#type)'s docs.
    pub enum Invariant<T: ?Sized> {
        /// The only possible [`Invariant<_>`][inv] value. For type see
        /// [`Invariant`][inv] docs.
        ///
        /// [inv]: crate::Invariant#type
        Invariant,

        /// Uninhabited variant that uses `T`.
        #[doc(hidden)]
        #[deprecated(
            since = "0.1.0",
            note = "you shouldn't use `Invariant` as a enum and/or use `__Phantom` variant of it. \
                    This variant is only used to use the generic parameter. It's implementation \
                    detail and may change at any time."
        )]
        __Phantom(core::marker::PhantomData<fn(T) -> T>, Never),
        //                                 /^^^^^^^^^^
        // `fn(T) -> U` is **contra**variant
        // over `T` and covariant over `U`, so
        // `fn(T) -> T` is invariant over `T`
    }

    /// For documentation see [`Covariant`](crate::Covariant#type)'s docs.
    pub enum Covariant<T: ?Sized> {
        /// The only possible [`Covariant<_>`][cov] value. For type see
        /// [`Covariant`][cov] docs.
        ///
        /// [cov]: crate::Covariant#type
        Covariant,

        /// Uninhabited variant that uses `T`.
        #[doc(hidden)]
        #[deprecated(
            since = "0.1.0",
            note = "you shouldn't use `Covariant` as a enum and/or use `__Phantom` variant of it. \
                    This variant is only used to use the generic parameter. It's implementation \
                    detail and may change at any time."
        )]
        __Phantom(core::marker::PhantomData<fn(()) -> T>, Never),
        //                                 /^^^^^^^^^^^
        //  `fn(_) -> U` is covariant over `U`
    }

    /// For documentation, see [`Contravariant`](crate::Contravariant#type)'s
    /// docs.
    pub enum Contravariant<T: ?Sized> {
        /// The only possible [`Contravariant<_>`][cnt] value. For type see
        /// [`Contravariant`][cnt] docs.
        ///
        /// [cnt]: crate::Contravariant#type
        Contravariant,

        /// Uninhibited variant that uses `T`.
        #[doc(hidden)]
        #[deprecated(
            since = "0.1.0",
            note = "you shouldn't use `Contravariant` as a enum and/or use `__Phantom` variant of \
                    it. This variant is only used to use the generic parameter. It's \
                    implementation detail and may change at any time."
        )]
        __Phantom(core::marker::PhantomData<fn(T) -> ()>, Never),
        //                                 /^^^^^^^^^^^
        // `fn(T) -> _` is **contra**variant
        // over `T`
    }

    // #[derive] doesn't work for us since it adds unnecessary bounds to generics
    macro_rules! impls {
        (for $T:ident) => {
            impl<T: ?Sized> Copy for $T<T> {}

            impl<T: ?Sized> Clone for $T<T> {
                fn clone(&self) -> Self {
                    crate::$T
                }
            }

            impl<T: ?Sized> Default for $T<T> {
                fn default() -> Self {
                    crate::$T
                }
            }

            impl<T: ?Sized> core::fmt::Debug for $T<T> {
                fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
                    f.write_str(stringify!($T))
                }
            }

            impl<T: ?Sized> Ord for $T<T> {
                fn cmp(&self, _: &Self) -> core::cmp::Ordering {
                    // There is only one possible value, so it's always equal to itself
                    core::cmp::Ordering::Equal
                }
            }

            impl<T: ?Sized> PartialOrd for $T<T> {
                fn partial_cmp(&self, _: &Self) -> Option<core::cmp::Ordering> {
                    // There is only one possible value, so it's always equal to itself
                    Some(core::cmp::Ordering::Equal)
                }
            }

            impl<T: ?Sized> Eq for $T<T> {}

            impl<T: ?Sized> PartialEq for $T<T> {
                fn eq(&self, _: &Self) -> bool {
                    // There is only one possible value, so it's always equal to itself
                    true
                }
            }

            impl<T: ?Sized> core::hash::Hash for $T<T> {
                fn hash<H: core::hash::Hasher>(&self, _: &mut H) {}
            }
        };
    }

    impls!(for Invariant);
    impls!(for Covariant);
    impls!(for Contravariant);
}

#[cfg(any(test, doctest /* needed for compile_fail tests */))]
mod tests {
    use crate::{Contravariant, Covariant, Invariant};
    use core::mem::size_of;

    type T = [u8]; // Just an example type. Can be any type actually.

    /// Tests that `Invariant` can be created in const context.
    const _: Invariant<T> = Invariant::<T>;
    /// Tests that `Covariant` can be created in const context.
    const _: Covariant<T> = Covariant::<T>;
    /// Tests that `Contravariant` can be created in const context.
    const _: Contravariant<T> = Contravariant::<T>;

    #[test]
    fn zstness() {
        assert_eq!(size_of::<Invariant<T>>(), 0);
        assert_eq!(size_of::<Covariant<T>>(), 0);
        assert_eq!(size_of::<Contravariant<T>>(), 0);
    }

    #[test]
    fn debug() {
        assert_eq!(format!("{:?}", Invariant::<T>), "Invariant");
        assert_eq!(format!("{:?}", Covariant::<T>), "Covariant");
        assert_eq!(format!("{:?}", Contravariant::<T>), "Contravariant");
    }

    /// ```compile_fail,E0308
    /// use phantasm::Invariant;
    /// fn contravariant_fail<'l>(arg: Invariant<&'l ()>) -> Invariant<&'static ()> {
    ///     arg
    /// }
    /// ```
    /// ```compile_fail,E0308
    /// use phantasm::Invariant;
    /// fn covariant_fail<'l>(arg: Invariant<&'static ()>) -> Invariant<&'l ()> {
    ///     arg
    /// }
    /// ```
    #[allow(dead_code)]
    fn invariance() {}

    /// ```compile_fail,E0308
    /// use phantasm::Covariant;
    /// fn contravariant_fail<'l>(arg: Covariant<&'l ()>) -> Covariant<&'static ()> {
    ///     arg
    /// }
    /// ```
    #[allow(dead_code)]
    fn covariance<'l>(arg: Covariant<&'static ()>) -> Covariant<&'l ()> {
        // This coercion is only legal because the lifetime parameter is
        // covariant. If it were contravariant or invariant,
        // this would not compile.
        arg
    }

    /// ```compile_fail,E0308
    /// use phantasm::Contravariant;
    /// fn covariant_fail<'l>(arg: Contravariant<&'static ()>) -> Contravariant<&'l ()> {
    ///     arg
    /// }
    /// ```
    #[allow(dead_code)]
    fn contravariance<'l>(arg: Contravariant<&'l ()>) -> Contravariant<&'static ()> {
        // This coercion is only legal because the lifetime parameter is
        // contravariant. If it were covariant or invariant,
        // this would not compile.
        arg
    }
}
