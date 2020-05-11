//! This crate is aiming to make work with [variance][var] easier.
//! The crate exposes 3 types - [`Invariant<T>`][inv], [`Covariant<T>`][cov] and
//! [`Contravariant<T>`][cnt] with corresponding variance over `T` those work
//! very similar to [`PhantomData<_>`][phd].
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
//! covariant, contravariant or invariant over `'a`. (What it means is that
//! rustc doesn't know if `Slice<'static, _>` should be `Slice<'a, _>` or vice
//! versa or none of this. See [Subtyping and Variance][nom] nomicon chapter for
//! better explanation)
//!
//! To mitigate this issue and control the variance there is a type called
//! [`core::marker::PhantomData<T>`][phd]. [`PhantomData<T>`][phd] is a zst type
//! that acts like it owns `T`.
//!
//! However [`PhantomData`][phd] come with a number of issues
//! 1. Variance is a hard thing itself, but [`PhantomData`][phd] makes it even
//!    harder to understand. It's not so clear to understand what does smt like
//!    `PhantomData<fn(A, B) -> B>` (contravariant over `A` and invariant over
//!    `B`)
//! 2. Sometimes it works badly in const context (see next
//!    [paragraph](#function-pointers-in-const-fn-are-unstable))
//!
//! `phantasm`'s naming somehow helps woth `1.` making code clearer (though
//! variance still is a hard-to-understand thing)
//!
//! [nom]: https://doc.rust-lang.org/nomicon/subtyping.html#subtyping-and-variance
//!
//! ## function pointers in const fn are unstable
//!
//! It's common to make a type invariant over `T` with `PhantomData<fn(T) -> T>`
//! however, if you've ever tryed to use it in `const fn`, you know that it's
//! painfull (see [rust-lang/69459][my_issue] and [rust-lang/67649][or_issue]).
//! This crate helps mitigate this issue:
//!
//! ```
//! use phantasm::Invariant;
//!
//! pub struct Test<T>(Invariant<T>);
//!
//! impl<T> Test<T> {
//!     pub const fn new() -> Self {
//!         Self(Invariant) // just works
//!     }
//! }
//! ```
//! [my_issue]: https://github.com/rust-lang/rust/issues/69459
//! [or_issue]: https://github.com/rust-lang/rust/issues/67649
//!
//! ## life
//!
//! For variance over lifetimes, use `&'l ()`:
//! ```
//! use phantasm::{Contravariant, Covariant, Invariant};
//!
//! # // yep, I just don't want to copy-paste everything yet another time
//! struct Test<'a, 'b, 'c>(Invariant<&'a ()>, Covariant<&'b ()>, Contravariant<&'c ()>);
//! ```
//!
//! ## comparison operators cannot be chained
//!
//! Note: you can't use `Invariant<Ty>` as a value (just as
//! [`PhantomData`][phd]). To create `Invariant<Ty>` value use `Invariant::<Ty>`
//! (same goes for both [`Covariant<T>`][cov] and [`Contravariant<T>`][cnt])
//!
//! ```compile_fail
//! // won't compile
//! let _ = phantasm::Invariant<i32>;
//! ```
//! ```
//! use phantasm::Invariant;
//! // ok
//! let _ = Invariant::<i32>;
//! // Both forms are acceptable in type possition
//! struct A<T>(Invariant<T>);
//! struct B<T>(Invariant<T>);
//! ```
//!
//! ## many types
//!
//! When you need to set variance of many types at once, just use typle:
//! ```
//! struct Test<A, B>(phantasm::Covariant<(A, B)>);
//! ```
#![cfg_attr(not(test), no_std)] // `format!` is used in tests
#![allow(type_alias_bounds)] // for :?Sized bound
#![deny(missing_docs)]
#![forbid(unsafe_code)]

/// Marker zst type that is invariant over `T`.
///
/// "Invariant" means that given `F<_>`, `Super` and `Sub` (where `Sub` is a
/// subtype of `Super`), `F<Sub>` is **not** a subtype of `F<Super>` and vice
/// versa - `F<Super>` is **not** a subtype of `F<Sub>`
///
/// ## Examples
///
/// ```
/// // This struct is invariant over `T`
/// struct Test<T>(phantasm::Invariant<T> /* ... */);
///
/// let _: Test<i32> = Test(phantasm::Invariant);
/// let _ = Test(phantasm::Invariant::<i32>);
/// ```
///
/// ```compile_fail
/// // `F<Super>` is **not** a subtype of `F<Sub>`
/// fn fail<'l>(arg: Invariant<&'l ()>) -> Invariant<&'static ()> {
///     arg
/// }
/// ```
/// ```compile_fail
/// // `F<Sub>` is **not** a subtype of `F<Super>`
/// fn fail<'l>(arg: Invariant<&'static ()>) -> Invariant<&'l ()> {
///     arg
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

/// Marker zst type that is covariant over `T`.
///
/// "Covariant" means that given `F<_>`, `Super` and `Sub` (where `Sub` is a
/// subtype of `Super`), `F<Sub>` **is** a subtype of `F<Super>` (but `F<Super>`
/// is **not** a subtype of `F<Sub>`)
///
/// ## Examples
///
/// ```
/// // This struct is covariant over `T`
/// struct Test<T>(phantasm::Covariant<T> /* ... */);
///
/// let _: Test<i32> = Test(phantasm::Covariant);
/// let _ = Test(phantasm::Covariant::<i32>);
/// ```
///
/// ```compile_fail
/// use phantasm::Covariant;
/// // `F<Super>` is **not** a subtype of `F<Sub>`
/// fn fail<'l>(arg: Covariant<&'l ()>) -> Covariant<&'static ()> {
///     arg
/// }
/// ```
/// ```
/// use phantasm::Covariant;
/// // `F<Sub>` **is** a subtype of `F<Super>`
/// fn pass<'l>(arg: Covariant<&'static ()>) -> Covariant<&'l ()> {
///     arg
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

/// Marker zst type that is contravariant over `T`.
///
/// "Contravariant" means that given `F<_>`, `Super` and `Sub` (where `Sub` is a
/// subtype of `Super`), `F<Super>` **is** a subtype of `F<Sub>` (but `F<Sub>`
/// is **not** a subtype of `F<Super>`)
///
/// ## Examples
///
/// ```
/// // This struct is covariant over `T`
/// struct Test<T>(phantasm::Contravariant<T> /* ... */);
///
/// let _: Test<i32> = Test(phantasm::Contravariant);
/// let _ = Test(phantasm::Contravariant::<i32>);
/// ```
///
/// ```compile_fail
/// use phantasm::Contravariant;
/// // `F<Sub>` is **not** a subtype of `F<Super>`
/// fn fail<'l>(arg: Contravariant<&'static ()>) -> Contravariant<&'l ()> {
///     arg
/// }
/// ```
/// ```
/// use phantasm::Contravariant;
/// // `F<Super>` **is** a subtype of `F<Sub>`
/// fn pass<'l>(arg: Contravariant<&'l ()>) -> Contravariant<&'static ()> {
///     arg
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
/// This is a private module to hide ugly enum  implementation details and make
/// doc cleaner.
mod r#impl {
    // Note: the idea of the implementation is actually copy-pasted from
    // dtolnay's ghost <https://docs.rs/ghost/> (I haven't used it to be 0-dep, yep I'am a bad guy)

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
    #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
    pub enum Invariant<T: ?Sized> {
        /// Uninhibited variant that uses `T`.
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
        /// The only possible [`Invariant<_>`][inv] value. For type see
        /// [`Invariant`][inv] docs.
        ///
        /// [inv]: crate::Invariant#type
        Invariant,
    }

    /// For documentation see [`Covariant`](crate::Covariant#type)'s docs.
    #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
    pub enum Covariant<T: ?Sized> {
        /// Uninhibited variant that uses `T`.
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
        /// The only possible [`Covariant<_>`][cov] value. For type see
        /// [`Covariant`][cov] docs.
        ///
        /// [cov]: crate::Covariant#type
        Covariant,
    }

    /// For documentation see [`Contravariant`](crate::Contravariant#type)'s
    /// docs.
    #[derive(Copy, Clone, Debug, Ord, PartialOrd, Eq, PartialEq, Hash)]
    pub enum Contravariant<T: ?Sized> {
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
        /// The only possible [`Contravariant<_>`][cnt] value. For type see
        /// [`Contravariant`][cnt] docs.
        ///
        /// [cnt]: crate::Contravariant#type
        Contravariant,
    }
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

    /// ```compile_fail
    /// use phantasm::Invariant;
    /// fn fail<'l>(arg: Invariant<&'l ()>) -> Invariant<&'static ()> {
    ///     arg
    /// }
    /// ```
    /// ```compile_fail
    /// use phantasm::Invariant;
    /// fn fail<'l>(arg: Invariant<&'static ()>) -> Invariant<&'l ()> {
    ///     arg
    /// }
    /// ```
    #[allow(dead_code)]
    fn invariance() {}

    /// ```compile_fail
    /// use phantasm::Covariant;
    /// fn fail<'l>(arg: Covariant<&'l ()>) -> Covariant<&'static ()> {
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

    /// ```compile_fail
    /// use phantasm::Contravariant;
    /// fn fail<'l>(arg: Contravariant<&'static ()>) -> Contravariant<&'l ()> {
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
