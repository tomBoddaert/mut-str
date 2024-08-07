//! # `mut-str`
//!
//! A toolkit for working with mutable string slices (`&mut str`), and immutable ones too!
//!
//! Pretty much all you can do safely in the standard library with mutable string slices is make them lower or upper case.
//! This package allows for splitting and slicing by character index (rather than byte index), replacing strings and using references to characters.
//!
//! All functions on string slices are available either at the package root or as methods on the `StrExt` trait.
//!
//! ```
//! use mut_str::StrExt;
//!
//! let mut welcome = Box::<str>::from("Hello, World!");
//!
//! // Split by character index
//! let (l, r) = welcome.char_split_at_mut(7).unwrap();
//! assert_eq!(l, "Hello, ");
//! assert_eq!(r, "World!");
//!
//! // Replace string slices
//! l.replace_with("mut-str").unwrap();
//! assert_eq!(l, "mut-str");
//!
//! // Replace with padding
//! let sub = r.replace_with_pad_left_char("👑!", ' ').unwrap();
//! assert_eq!(sub, "👑!");
//! assert_eq!(r, " 👑!");
//!
//! assert_eq!(&*welcome, "mut-str 👑!");
//!
//! // Get character references
//! let crown = welcome.get_char_mut(8).unwrap();
//! assert_eq!(crown, '👑');
//!
//! // Mutate characters
//! crown.replace('🌍').unwrap();
//! assert_eq!(crown, '🌍');
//!
//! // Slice by character index
//! let l = welcome.char_slice_mut(..7).unwrap();
//! l.replace_with_pad_left_space("👋").unwrap();
//!
//! assert_eq!(&*welcome, "   👋 🌍!");
//! ```
//!
//! ## Links
//! [Latest version of `mut-str` on crates.io](https://crates.io/crates/mut-str)  
#![doc = concat!("[This version of `mut-str` on crates.io](https://crates.io/crates/mut-str/", env!("CARGO_PKG_VERSION"), ")  ")]
//! [`mut-str` on GitHub](https://github.com/tomBoddaert/mut-str)
//!
//! # Features
#![doc = concat!("[Features on docs.rs](https://docs.rs/crate/mut-str/", env!("CARGO_PKG_VERSION"), "/features)  ")]
//! - `alloc` (enabled by default) adds implementations that require the `alloc` library.
//! - `std` (enabled by default, requires `alloc`) adds implementations specific to the standard library.
//! - `nightly` (requires rust [nightly](https://rust-lang.github.io/rustup/concepts/channels.html)) see [below](#nightly-changes).
//!
//! To make this package `no-std` compatible, disable the `std` feature.  
//! ```sh
//! cargo add mut-str --no-default-features
//! ```
//! ```sh
//! cargo add mut-str --no-default-features --features=alloc
//! ```
//!
//! ## Nightly Changes
//! - Uses the [`extern_types`](https://rust-lang.github.io/rfcs/1861-extern-types.html) feature to fix pointer provenance issues.
//! - Implements [`Error`](https://doc.rust-lang.org/stable/core/error/trait.Error.html) for errors without [`std`](#features) being enabled.
//!
//! ## License
//!
//! [`mut-str`](https://github.com/tomBoddaert/mut-str) is dual-licensed under either the Apache License Version 2.0 or MIT license at your option.

#![cfg_attr(feature = "nightly", feature(extern_types))]
#![warn(
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::perf,
    clippy::cargo,
    clippy::alloc_instead_of_core,
    clippy::std_instead_of_alloc,
    clippy::std_instead_of_core,
    clippy::get_unwrap,
    clippy::panic_in_result_fn,
    clippy::todo,
    clippy::undocumented_unsafe_blocks
)]
#![cfg_attr(not(test), warn(clippy::unwrap_used, clippy::expect_used))]
#![allow(clippy::module_name_repetitions)]
#![cfg_attr(not(feature = "std"), no_std)]

use core::{mem::transmute, str};

mod char_owned;
mod char_ref;
/// Errors.
pub mod errors;
mod get;
/// Iterators over UTF-8 character references.
pub mod iter;
mod replace;
mod slice;
mod split;
mod traits;

pub use char_owned::*;
pub use char_ref::*;
pub use get::*;
pub use replace::*;
pub use slice::*;
pub use split::*;
pub use traits::*;

#[inline]
/// Copy the [`prim@str`] to a byte buffer and get the new [`prim@str`] containing the inserted character.
/// Returns `None` if `buffer` is shorter than the string slice.
///
/// ```
/// use mut_str::copy_to;
///
/// let s = "Hello, World!";
/// let mut buffer = [0; 50];
/// let new_s = copy_to(s, &mut buffer).unwrap();
///
/// assert_eq!(new_s, s);
/// ```
pub fn copy_to<'a>(s: &str, buffer: &'a mut [u8]) -> Option<&'a mut str> {
    if s.len() > buffer.len() {
        None
    } else {
        let exact_buffer = &mut buffer[..s.len()];
        exact_buffer.copy_from_slice(s.as_bytes());

        // SAFETY:
        // This is valid as a utf8 string slice of the same length was just
        // copied to the slice.
        Some(unsafe { str::from_utf8_unchecked_mut(exact_buffer) })
    }
}

#[must_use]
#[inline]
/// Extend the lifetime of a mutable reference.
///
/// # Safety
/// This should only be used when a slice is split and the original
/// reference is 'forgotten' and replaced with one half.
unsafe fn extend_lifetime_mut<'to, T: ?Sized>(value: &mut T) -> &'to mut T {
    transmute(value)
}

#[cfg(test)]
#[allow(clippy::module_name_repetitions)]
mod test {
    pub static TEST_STR: &str = "oΦ⏣🌑";

    pub fn test_str_owned() -> Box<str> {
        Box::from(TEST_STR)
    }
}
