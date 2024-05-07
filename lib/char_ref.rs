// Clippy recommends using `ptr::cast`, which does not work with unsized types,
// like the future implementation of `Char`
#![cfg_attr(not(feature = "future"), allow(clippy::ptr_as_ptr))]

use core::{
    borrow::{Borrow, BorrowMut},
    cmp,
    fmt::{self, Display},
    hash, ptr, slice,
    str::{self, FromStr},
};
#[cfg(feature = "alloc")]
extern crate alloc;
// `ToOwned` is in the std prelude, so ignore unused import
#[allow(unused_imports)]
#[cfg(feature = "alloc")]
use alloc::borrow::ToOwned;

use crate::{
    errors::{
        LenNotEqual, ReplaceWithPadCharError, ReplaceWithPadError, ReplacementTooLong,
        TryFromBytesError, TryFromStrError,
    },
    OwnedChar,
};

mod char_internal {
    #[cfg(feature = "future")]
    extern "Rust" {
        pub type Char;
    }

    #[cfg(not(feature = "future"))]
    pub struct Char {
        _c: u8,
    }
}

/// A UTF-8 encoded character.
///
/// This type can only be obtained as a reference or mutable reference similarly to [`prim@str`].
///
/// ```
/// use mut_str::Char;
///
/// let s = "Hello, World!";
/// let c = Char::get(s, 1).unwrap();
///
/// assert_eq!(c, 'e');
/// ```
pub use char_internal::Char;

impl Char {
    #[must_use]
    #[inline]
    /// Create a new character reference from a pointer to a character.
    ///
    /// # Safety
    /// `p` must be a pointer to the first byte of a valid UTF-8 character.
    pub const unsafe fn new_unchecked(p: *const u8) -> *const Self {
        p as *const Self
    }

    #[must_use]
    #[inline]
    /// Create a new mutable character reference from a mutable pointer to a character.
    ///
    /// # Safety
    /// `p` must be a mutable pointer to the first byte of a valid UTF-8 character that
    /// can be mutated. String literals cannot be mutated.
    pub const unsafe fn new_unchecked_mut(p: *mut u8) -> *mut Self {
        p as *mut Self
    }

    #[must_use]
    #[inline]
    /// Read the first byte of the character.
    const fn first_byte(&self) -> u8 {
        // SAFETY:
        // The character that `&self` points to must be at least 1 byte
        // long, so reading the first byte is valid.
        unsafe { *ptr::from_ref::<Self>(self).cast() }
    }

    #[must_use]
    #[inline]
    /// Get a mutable reference to the first byte of the character.
    ///
    /// # Safety
    /// The caller must only mutate the value if it is an ASCII character, and the byte must remain valid ASCII.
    unsafe fn first_byte_mut(&mut self) -> &mut u8 {
        &mut *ptr::from_mut::<Self>(self).cast()
    }

    #[must_use]
    /// Get a character reference from a [`prim@str`] and an index.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let s = "Hello, World!";
    /// let c = Char::get(s, 1).unwrap();
    ///
    /// assert_eq!(c, 'e');
    /// ```
    pub fn get(s: &str, i: usize) -> Option<&Self> {
        let (start, _) = s.char_indices().nth(i)?;

        // SAFETY:
        // `start` is an offset obtained from `CharIndices` and is
        // therefore within the bounds of the string.
        let p = unsafe { s.as_ptr().add(start) };

        // SAFETY:
        // As the offset is from `CharIndices`, `p` points to the first
        // byte of a utf8 character.
        Some(unsafe { &*Self::new_unchecked(p) })
    }

    #[must_use]
    /// Get a mutable character reference from a mutable [`prim@str`] and an index.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("Hello, World!");
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    ///
    /// assert_eq!(c, 'e');
    /// ```
    pub fn get_mut(s: &mut str, i: usize) -> Option<&mut Self> {
        let (start, _) = s.char_indices().nth(i)?;

        // SAFETY:
        // `start` is an offset obtained from `CharIndices` and is
        // therefore within the bounds of the string.
        // `Self` also maintains utf8 validity.
        let p = unsafe { s.as_mut_ptr().add(start) };

        // SAFETY:
        // As the offset is from `CharIndices`, `p` points to the first
        // byte of a utf8 character, and the string is mutable.
        Some(unsafe { &mut *Self::new_unchecked_mut(p) })
    }

    #[must_use]
    #[inline]
    // This can never be empty.
    #[allow(clippy::len_without_is_empty)]
    /// Get the length of the character in bytes.
    ///
    /// This will be in the range `1..=4`.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let s = "oΦ⏣🌑";
    ///
    /// assert_eq!(Char::get(s, 0).unwrap().len(), 1);
    /// assert_eq!(Char::get(s, 1).unwrap().len(), 2);
    /// assert_eq!(Char::get(s, 2).unwrap().len(), 3);
    /// assert_eq!(Char::get(s, 3).unwrap().len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        match self.first_byte().leading_ones() {
            0 => 1,
            l @ 2..=4 => l as usize,
            _ => unreachable!("invalid char pointer"),
        }
    }

    #[must_use]
    #[inline]
    /// Get a pointer to the character ([`prim@pointer`]).
    pub const fn as_ptr(&self) -> *const u8 {
        ptr::from_ref::<Self>(self).cast()
    }

    #[must_use]
    #[inline]
    /// Get a mutable pointer to the character ([`prim@pointer`]).
    pub fn as_mut_ptr(&mut self) -> *mut u8 {
        ptr::from_mut::<Self>(self).cast()
    }

    #[must_use]
    #[inline]
    /// Get the character as a byte slice ([`prim@slice`]).
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let s = "Hello, 🌍!";
    ///
    /// let c = Char::get(s, 1).unwrap();
    /// assert_eq!(c.as_bytes(), &[101]);
    ///
    /// let c = Char::get(s, 7).unwrap();
    /// assert_eq!(c.as_bytes(), &[240, 159, 140, 141]);
    /// ```
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY:
        // The pointer is to the start of the character in the utf8 string.
        // There is guaranteed to be `self.len()` bytes after (and including)
        // the pointer.
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    #[must_use]
    #[inline]
    /// Get the character as a mutable byte slice ([`prim@slice`]).
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::from("Hello, 🌍!");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// let b = unsafe { c.as_bytes_mut() };
    /// assert_eq!(b, &[101]);
    /// b[0] = b'E';
    ///
    /// assert_eq!(&*s, "HEllo, 🌍!");
    /// ```
    ///
    /// # Safety
    /// See [`str::as_bytes_mut`].
    pub unsafe fn as_bytes_mut(&mut self) -> &mut [u8] {
        slice::from_raw_parts_mut(self.as_mut_ptr(), self.len())
    }

    #[must_use]
    #[inline]
    /// Get the character as a [`prim@str`].
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let s = "Hello, 🌍!";
    ///
    /// let c = Char::get(s, 1).unwrap();
    /// assert_eq!(c.as_str(), "e");
    ///
    /// let c = Char::get(s, 7).unwrap();
    /// assert_eq!(c.as_str(), "🌍");
    /// ```
    pub fn as_str(&self) -> &str {
        // SAFETY:
        // `&self` points to a valid utf8 character,
        // so it is also a valid utf8 string.
        unsafe { str::from_utf8_unchecked(self.as_bytes()) }
    }

    #[must_use]
    #[inline]
    /// Get the character as a mutable [`prim@str`].
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("Hello, 🌍!");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// assert_eq!(c.as_str_mut(), "e");
    ///
    /// let c = Char::get_mut(&mut *s, 7).unwrap();
    /// assert_eq!(c.as_str_mut(), "🌍");
    /// ```
    pub fn as_str_mut(&mut self) -> &mut str {
        // SAFETY:
        // `&self` points to a valid utf8 character,
        // so it is also a valid utf8 string.
        unsafe { str::from_utf8_unchecked_mut(self.as_bytes_mut()) }
    }

    #[must_use]
    /// Get the character as a [`char`].
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let s = "Hello, 🌍!";
    ///
    /// let c = Char::get(s, 1).unwrap();
    /// assert_eq!(c.as_char(), 'e');
    ///
    /// let c = Char::get(s, 7).unwrap();
    /// assert_eq!(c.as_char(), '🌍');
    /// ```
    pub fn as_char(&self) -> char {
        // SAFETY:
        // `self` is guaranteed to contain exactly one character, so calling`
        // `next for the first time on the `Chars` iterator will yield an
        // `Option::Some`.
        unsafe { self.as_str().chars().next().unwrap_unchecked() }
    }

    #[must_use]
    #[inline]
    /// Creates an [`OwnedChar`] from a borrowed [`Char`].
    ///
    /// ```
    /// use mut_str::{Char, OwnedChar};
    ///
    /// let s = "Hello, 🌍!";
    ///
    /// let c = Char::get(s, 1).unwrap();
    /// assert_eq!(c.as_owned(), OwnedChar::from('e'));
    ///
    /// let c = Char::get(s, 7).unwrap();
    /// assert_eq!(c.as_owned(), OwnedChar::from('🌍'));
    /// ```
    pub fn as_owned(&self) -> OwnedChar {
        let bytes = self.as_bytes();

        // SAFETY:
        // `bytes` is guaranteed be to a valid UTF-8 character.
        unsafe { OwnedChar::from_bytes_unchecked(bytes) }
    }

    #[inline]
    /// Copy the character to a byte buffer and get a mutable reference to the inserted character.
    /// Returns `None` if `buffer` is shorter than `self`.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let s = "Hello, World!";
    /// let c = Char::get(s, 1).unwrap();
    ///
    /// let mut buffer = [0; 4];
    /// let c2 = c.copy_to(&mut buffer).unwrap();
    ///
    /// assert_eq!(c2, c);
    /// ```
    pub fn copy_to<'a>(&self, buffer: &'a mut [u8]) -> Option<&'a mut Self> {
        let len = self.len();
        if len > buffer.len() {
            None
        } else {
            buffer[..len].copy_from_slice(self.as_bytes());

            // SAFETY:
            // This is valid as a utf8 character was just copied to the buffer.
            Some(unsafe { &mut *Self::new_unchecked_mut(buffer.as_mut_ptr()) })
        }
    }

    /// Replace the character with another of the same length.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// assert!(c.replace('e').is_ok());
    /// assert_eq!(&*s, "eΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// assert!(c.replace('a').is_err());
    /// ```
    ///
    /// # Errors
    /// - If `r`, when utf8 encoded, does not have the same length as `self`, [`LenNotEqual`] will be returned.
    pub fn replace<C>(&mut self, r: C) -> Result<(), LenNotEqual>
    where
        C: Into<char>,
    {
        let r = r.into();

        if self.len() != r.len_utf8() {
            return Err(LenNotEqual);
        }

        // SAFETY:
        // Replacing the character with a valid utf8 character of the same
        // length is valid.
        r.encode_utf8(unsafe { self.as_bytes_mut() });
        Ok(())
    }

    /// Replace the character with another of the same length or shorter.
    /// The remaining bytes will be filled with spaces.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// assert!(c.replace_with_pad_space('e').is_ok());
    /// assert_eq!(&*s, "eΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// assert!(c.replace_with_pad_space('a').is_ok());
    /// assert_eq!(&*s, "ea ⏣🌑");
    /// ```
    ///
    /// # Errors
    /// - If `r`, when utf8 encoded, is longer than `self`, [`ReplacementTooLong`] will be returned.
    pub fn replace_with_pad_space<C>(&mut self, r: C) -> Result<(), ReplacementTooLong>
    where
        C: Into<char>,
    {
        let r = r.into();

        if self.len() < r.len_utf8() {
            return Err(ReplacementTooLong);
        }

        // SAFETY:
        // `Self` maintains utf8 validity.
        let (char_slice, remaining) = unsafe { self.as_bytes_mut().split_at_mut(r.len_utf8()) };

        r.encode_utf8(char_slice);
        remaining.fill(b' ');

        Ok(())
    }

    /// Replace the character with another of the same length or shorter.
    /// The remaining bytes will be filled with `pad`.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// assert!(c.replace_with_pad('e', b'b').is_ok());
    /// assert_eq!(&*s, "eΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// assert!(c.replace_with_pad('a', b'b').is_ok());
    /// assert_eq!(&*s, "eab⏣🌑");
    /// ```
    ///
    /// # Errors
    /// - If `pad` is not valid utf8, [`ReplaceWithPadError::InvalidPad`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `self`, [`ReplaceWithPadError::ReplacementLen`] will be returned.
    pub fn replace_with_pad<C>(&mut self, r: C, pad: u8) -> Result<(), ReplaceWithPadError>
    where
        C: Into<char>,
    {
        let r = r.into();

        if self.len() < r.len_utf8() {
            return Err(ReplaceWithPadError::CHAR_LEN);
        }

        str::from_utf8(&[pad]).map_err(ReplaceWithPadError::InvalidPad)?;

        // SAFETY:
        // `Self` maintains utf8 validity.
        let (char_slice, remaining) = unsafe { self.as_bytes_mut().split_at_mut(r.len_utf8()) };

        r.encode_utf8(char_slice);
        remaining.fill(pad);

        Ok(())
    }

    /// Replace the character with another of the same length or shorter.
    /// The remaining bytes will be filled with `pad`, which must be one byte long.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// assert!(c.replace_with_pad_char('e', 'b').is_ok());
    /// assert_eq!(&*s, "eΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// assert!(c.replace_with_pad_char('a', 'b').is_ok());
    /// assert_eq!(&*s, "eab⏣🌑");
    /// ```
    ///
    /// # Errors
    /// - If `pad_char`, when utf8 encoded, is longer than `Self`, [`ReplaceWithPadCharError::PadCharTooLong`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `self`, [`ReplaceWithPadCharError::ReplacementLen`] will be returned.
    pub fn replace_with_pad_char<C1, C2>(
        &mut self,
        r: C1,
        pad_char: C2,
    ) -> Result<(), ReplaceWithPadCharError>
    where
        C1: Into<char>,
        C2: Into<char>,
    {
        let (r, pad_char) = (r.into(), pad_char.into());

        if pad_char.len_utf8() != 1 {
            return Err(ReplaceWithPadCharError::PadCharTooLong);
        }

        if self.len() < r.len_utf8() {
            return Err(ReplaceWithPadCharError::CHAR_LEN);
        }

        let mut pad: u8 = 0;
        pad_char.encode_utf8(slice::from_mut(&mut pad));

        // SAFETY:
        // `Self` maintains utf8 validity.
        let (char_slice, remaining) = unsafe { self.as_bytes_mut().split_at_mut(r.len_utf8()) };

        r.encode_utf8(char_slice);
        remaining.fill(pad);

        Ok(())
    }

    /// Replace the character with another of the same length or shorter, right aligned.
    /// The remaining bytes before the character will be filled with spaces.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// assert!(c.replace_with_pad_left_space('e').is_ok());
    /// assert_eq!(&*s, "eΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// let c2 = c.replace_with_pad_left_space('a').unwrap();
    /// assert_eq!(c2, 'a');
    /// assert_eq!(c, ' ');
    /// assert_eq!(&*s, "e a⏣🌑");
    /// ```
    ///
    /// # Errors
    /// - If `r`, when utf8 encoded, is longer than `self`, [`ReplacementTooLong`] will be returned.
    pub fn replace_with_pad_left_space<C>(&mut self, r: C) -> Result<&mut Self, ReplacementTooLong>
    where
        C: Into<char>,
    {
        let r = r.into();
        let len = self.len();

        if len < r.len_utf8() {
            return Err(ReplacementTooLong);
        }

        let (remaining, char_slice) =
            // SAFETY:
            // `Self` maintains utf8 validity.
            unsafe { self.as_bytes_mut().split_at_mut(len - r.len_utf8()) };

        r.encode_utf8(char_slice);
        remaining.fill(b' ');

        // SAFETY:
        // The pointer is directly after a char boundary.
        Ok(unsafe { &mut *Self::new_unchecked_mut(char_slice.as_mut_ptr()) })
    }

    /// Replace the character with another of the same length or shorter, right aligned.
    /// The remaining bytes before the character will be filled with `pad`.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// assert!(c.replace_with_pad_left('e', b'b').is_ok());
    /// assert_eq!(&*s, "eΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// let c2 = c.replace_with_pad_left('a', b'b').unwrap();
    /// assert_eq!(c2, 'a');
    /// assert_eq!(c, 'b');
    /// assert_eq!(&*s, "eba⏣🌑");
    /// ```
    ///
    /// # Errors
    /// - If `pad` is not valid utf8, [`ReplaceWithPadError::InvalidPad`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `self`, [`ReplaceWithPadError::ReplacementLen`] will be returned.
    pub fn replace_with_pad_left<C>(
        &mut self,
        r: C,
        pad: u8,
    ) -> Result<&mut Self, ReplaceWithPadError>
    where
        C: Into<char>,
    {
        let r = r.into();
        let len = self.len();

        if len < r.len_utf8() {
            return Err(ReplaceWithPadError::CHAR_LEN);
        }

        str::from_utf8(&[pad]).map_err(ReplaceWithPadError::InvalidPad)?;

        let (remaining, char_slice) =
            // SAFETY:
            // `Self` maintains utf8 validity.
            unsafe { self.as_bytes_mut().split_at_mut(len - r.len_utf8()) };

        r.encode_utf8(char_slice);
        remaining.fill(pad);

        // SAFETY:
        // The pointer is directly after a char boundary.
        Ok(unsafe { &mut *Self::new_unchecked_mut(char_slice.as_mut_ptr()) })
    }

    /// Replace the character with another of the same length or shorter, right aligned.
    /// The remaining bytes before the character will be filled with `char`, which must be one byte long.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// assert!(c.replace_with_pad_left_char('e', 'b').is_ok());
    /// assert_eq!(&*s, "eΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// let c2 = c.replace_with_pad_left_char('a', 'b').unwrap();
    /// assert_eq!(c2, 'a');
    /// assert_eq!(c, 'b');
    /// assert_eq!(&*s, "eba⏣🌑");
    /// ```
    ///
    /// # Errors
    /// - If `pad_char`, when utf8 encoded, is longer than `Self`, [`ReplaceWithPadCharError::PadCharTooLong`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `self`, [`ReplaceWithPadCharError::ReplacementLen`] will be returned.
    pub fn replace_with_pad_left_char<C1, C2>(
        &mut self,
        r: C1,
        pad_char: C2,
    ) -> Result<&mut Self, ReplaceWithPadCharError>
    where
        C1: Into<char>,
        C2: Into<char>,
    {
        let (r, pad_char) = (r.into(), pad_char.into());
        let len = self.len();

        if pad_char.len_utf8() != 1 {
            return Err(ReplaceWithPadCharError::PadCharTooLong);
        }

        if len < r.len_utf8() {
            return Err(ReplaceWithPadCharError::CHAR_LEN);
        }

        let mut pad: u8 = 0;
        pad_char.encode_utf8(slice::from_mut(&mut pad));

        let (remaining, char_slice) =
            // SAFETY:
            // `Self` maintains utf8 validity.
            unsafe { self.as_bytes_mut().split_at_mut(len - r.len_utf8()) };

        r.encode_utf8(char_slice);
        remaining.fill(pad);

        // SAFETY:
        // The pointer is directly after a char boundary.
        Ok(unsafe { &mut *Self::new_unchecked_mut(char_slice.as_mut_ptr()) })
    }

    #[must_use]
    #[inline]
    /// Checks if the value is within ASCII range.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let s = "oΦ⏣🌑";
    ///
    /// let c = Char::get(s, 0).unwrap();
    /// assert!(c.is_ascii());
    ///
    /// let c = Char::get(s, 1).unwrap();
    /// assert!(!c.is_ascii());
    /// ```
    pub const fn is_ascii(&self) -> bool {
        self.first_byte().is_ascii()
    }

    #[inline]
    /// Converts this type to its ASCII upper case equivalent in-place.
    ///
    /// ASCII letters ‘a’ to ‘z’ are mapped to 'A' to 'Z', but non-ASCII letters are unchanged.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oφ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// c.make_ascii_uppercase();
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// c.make_ascii_uppercase();
    ///
    /// assert_eq!(&*s, "Oφ⏣🌑");
    /// ```
    pub fn make_ascii_uppercase(&mut self) {
        // SAFETY:
        // `make_ascii_uppercase` only mutates the value if it is ASCII
        // and maintains ASCII validity.
        unsafe { self.first_byte_mut() }.make_ascii_uppercase();
    }

    #[inline]
    /// Converts this type to its ASCII lower case equivalent in-place.
    ///
    /// ASCII letters 'A' to 'Z' are mapped to 'a' to 'z', but non-ASCII letters are unchanged.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("OΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// c.make_ascii_lowercase();
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// c.make_ascii_lowercase();
    ///
    /// assert_eq!(&*s, "oΦ⏣🌑");
    /// ```
    pub fn make_ascii_lowercase(&mut self) {
        // SAFETY:
        // `make_ascii_lowercase` only mutates the value if it is ASCII
        // and maintains ASCII validity.
        unsafe { self.first_byte_mut() }.make_ascii_lowercase();
    }

    /// Converts this type to its Unicode upper case equivalent in-place.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("oß⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// c.try_make_uppercase().unwrap();
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// c.try_make_uppercase().unwrap();
    ///
    /// assert_eq!(&*s, "OSS⏣🌑");
    /// ```
    ///
    /// # Errors
    /// If the character and its uppercase version is not the same length when utf8 encoded, [`LenNotEqual`] will be returned.
    pub fn try_make_uppercase(&mut self) -> Result<(), LenNotEqual> {
        let chars = self.as_char().to_uppercase();

        let mut buffer = [0; 4];
        let mut index = 0;

        let self_len = self.len();

        for char in chars {
            let len = char.len_utf8();
            if index + len > self_len {
                return Err(LenNotEqual);
            }

            char.encode_utf8(&mut buffer[index..]);
            index += len;
        }

        if index != self_len {
            return Err(LenNotEqual);
        }

        // SAFETY:
        // Replacing the character with a valid utf8 string of the same
        // byte length is valid.
        unsafe { self.as_bytes_mut() }.copy_from_slice(&buffer[..index]);
        Ok(())
    }

    /// Converts this type to its Unicode lower case equivalent in-place.
    ///
    /// ```
    /// use mut_str::Char;
    ///
    /// let mut s = Box::<str>::from("OΦ⏣🌑");
    ///
    /// let c = Char::get_mut(&mut *s, 0).unwrap();
    /// c.try_make_lowercase().unwrap();
    ///
    /// let c = Char::get_mut(&mut *s, 1).unwrap();
    /// c.try_make_lowercase().unwrap();
    ///
    /// assert_eq!(&*s, "oφ⏣🌑");
    /// ```
    ///
    /// # Errors
    /// If the character and its lowercase version is not the same length when utf8 encoded, [`LenNotEqual`] will be returned.
    pub fn try_make_lowercase(&mut self) -> Result<(), LenNotEqual> {
        let chars = self.as_char().to_lowercase();

        let mut buffer = [0; 4];
        let mut index = 0;

        let self_len = self.len();

        for char in chars {
            let len = char.len_utf8();
            if index + len > self_len {
                return Err(LenNotEqual);
            }

            char.encode_utf8(&mut buffer[index..]);
            index += len;
        }

        if index != self_len {
            return Err(LenNotEqual);
        }

        // SAFETY:
        // Replacing the character with a valid utf8 string of the same
        // byte length is valid.
        unsafe { self.as_bytes_mut() }.copy_from_slice(&buffer[..index]);
        Ok(())
    }
}

impl fmt::Display for Char {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_str().fmt(f)
    }
}

impl fmt::Debug for Char {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut b = [b'\''; 6];
        b[1..=self.len()].copy_from_slice(self.as_bytes());

        // SAFETY:
        // `self` is valid utf8, so when embedded in a string of single-byte
        // utf8 characters, the resulting string will be valid.
        let s = unsafe { str::from_utf8_unchecked(&b[..self.len() + 2]) };
        Display::fmt(s, f)
    }
}

impl PartialEq for Char {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_bytes().eq(other.as_bytes())
    }
}

impl PartialEq<OwnedChar> for Char {
    #[inline]
    fn eq(&self, other: &OwnedChar) -> bool {
        self.eq(other.as_ref())
    }
}

impl PartialEq<str> for Char {
    #[inline]
    fn eq(&self, other: &str) -> bool {
        self.as_bytes().eq(other.as_bytes())
    }
}

impl PartialEq<Char> for str {
    #[inline]
    fn eq(&self, other: &Char) -> bool {
        self.as_bytes().eq(other.as_bytes())
    }
}

impl PartialEq<char> for Char {
    #[inline]
    fn eq(&self, other: &char) -> bool {
        self.as_char().eq(other)
    }
}

impl PartialEq<Char> for char {
    #[inline]
    fn eq(&self, other: &Char) -> bool {
        self.eq(&other.as_char())
    }
}

impl PartialEq<char> for &Char {
    #[inline]
    fn eq(&self, other: &char) -> bool {
        self.as_char().eq(other)
    }
}

impl PartialEq<char> for &mut Char {
    #[inline]
    fn eq(&self, other: &char) -> bool {
        self.as_char().eq(other)
    }
}

impl Eq for Char {}

impl Ord for Char {
    #[inline]
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.as_bytes().cmp(other.as_bytes())
    }
}

impl PartialOrd for Char {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialOrd<OwnedChar> for Char {
    #[inline]
    fn partial_cmp(&self, other: &OwnedChar) -> Option<cmp::Ordering> {
        self.partial_cmp(other.as_ref())
    }
}

impl PartialOrd<str> for Char {
    #[inline]
    fn partial_cmp(&self, other: &str) -> Option<cmp::Ordering> {
        Some(self.as_bytes().cmp(other.as_bytes()))
    }
}

impl PartialOrd<Char> for str {
    #[inline]
    fn partial_cmp(&self, other: &Char) -> Option<cmp::Ordering> {
        Some(self.as_bytes().cmp(other.as_bytes()))
    }
}

impl PartialOrd<char> for Char {
    #[inline]
    fn partial_cmp(&self, other: &char) -> Option<cmp::Ordering> {
        Some(self.as_char().cmp(other))
    }
}

impl PartialOrd<Char> for char {
    #[inline]
    fn partial_cmp(&self, other: &Char) -> Option<cmp::Ordering> {
        Some(self.cmp(&other.as_char()))
    }
}

impl hash::Hash for &Char {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_bytes().hash(state);
    }
}

impl AsRef<str> for Char {
    #[inline]
    fn as_ref(&self) -> &str {
        self.as_str()
    }
}

impl AsMut<str> for Char {
    #[inline]
    fn as_mut(&mut self) -> &mut str {
        self.as_str_mut()
    }
}

impl Borrow<str> for Char {
    #[inline]
    fn borrow(&self) -> &str {
        self.as_str()
    }
}

impl BorrowMut<str> for Char {
    #[inline]
    fn borrow_mut(&mut self) -> &mut str {
        self.as_str_mut()
    }
}

#[cfg(feature = "alloc")]
impl ToOwned for Char {
    type Owned = OwnedChar;

    #[inline]
    fn to_owned(&self) -> Self::Owned {
        self.as_owned()
    }

    #[inline]
    fn clone_into(&self, target: &mut Self::Owned) {
        let bytes = self.as_bytes();

        // SAFETY:
        // `bytes` is guaranteed to be a valid UTF-8 character. The succeeding
        // bytes do not have to be zeroed as they will not be read.
        unsafe { target.buffer_mut()[..bytes.len()].copy_from_slice(bytes) }
    }
}

impl From<&Char> for char {
    #[inline]
    fn from(value: &Char) -> Self {
        value.as_char()
    }
}

impl TryFrom<&str> for &Char {
    type Error = TryFromStrError;

    #[inline]
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        if value.is_empty() {
            return Err(TryFromStrError::Empty);
        }

        // SAFETY:
        // `value` is a `str` with at least one character, so its pointer must
        // point to a valid utf8 character.
        let c = unsafe { &*Char::new_unchecked(value.as_ptr()) };

        if value.len() == c.len() {
            Ok(c)
        } else {
            Err(TryFromStrError::MultipleChars)
        }
    }
}

impl TryFrom<&mut str> for &mut Char {
    type Error = TryFromStrError;

    #[inline]
    fn try_from(value: &mut str) -> Result<Self, Self::Error> {
        if value.is_empty() {
            return Err(TryFromStrError::Empty);
        }

        // SAFETY:
        // `value` is a `str` with at least one character, so its pointer must
        // point to a valid character.
        let c = unsafe { &mut *Char::new_unchecked_mut(value.as_mut_ptr()) };

        if value.len() == c.len() {
            Ok(c)
        } else {
            Err(TryFromStrError::MultipleChars)
        }
    }
}

impl FromStr for &Char {
    type Err = TryFromStrError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::try_from(s)
    }
}

impl TryFrom<&[u8]> for &Char {
    type Error = TryFromBytesError;

    #[inline]
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        if value.len() > 4 {
            return Err(TryFromStrError::MultipleChars.into());
        }

        let s = str::from_utf8(value)?;
        Self::try_from(s).map_err(TryFromBytesError::Length)
    }
}

impl TryFrom<&mut [u8]> for &mut Char {
    type Error = TryFromBytesError;

    #[inline]
    fn try_from(value: &mut [u8]) -> Result<Self, Self::Error> {
        if value.len() > 4 {
            return Err(TryFromStrError::MultipleChars.into());
        }

        let s = str::from_utf8_mut(value)?;
        Self::try_from(s).map_err(TryFromBytesError::Length)
    }
}

#[cfg(test)]
mod test {
    use core::str;

    use crate::{
        iter::{CharMutRefs, CharRefs},
        test::{test_str_owned, TEST_STR},
        Char,
    };

    #[test]
    fn test_len() {
        for (expected_char, char) in TEST_STR.chars().zip(CharRefs::from(TEST_STR)) {
            assert_eq!(char.len(), expected_char.len_utf8());
        }
    }

    #[test]
    fn test_get() {
        for (i, expected) in TEST_STR.chars().enumerate() {
            let actual = Char::get(TEST_STR, i).expect("expected a character reference");
            assert_eq!(actual.as_char(), expected);
        }

        let mut s = test_str_owned();

        for (i, expected) in TEST_STR.chars().enumerate() {
            let actual = Char::get_mut(&mut s, i).expect("expected a character reference");
            assert_eq!(actual.as_char(), expected);
        }

        assert_eq!(
            &*s, TEST_STR,
            "`Char::get_mut` mutated the mutable string slice"
        );
    }

    #[test]
    fn test_as() {
        let pr = TEST_STR.as_bytes().as_ptr_range();

        for (c, actual) in TEST_STR.chars().zip(CharRefs::from(TEST_STR)) {
            assert_eq!(actual.as_char(), c);

            let mut buffer = [0; 4];

            let s = c.encode_utf8(&mut buffer);
            let len = s.len();
            assert_eq!(actual.as_str(), s);

            let b = &buffer[..len];
            assert_eq!(actual.as_bytes(), b);

            assert!(pr.contains(&actual.as_ptr()));
        }

        let mut s = test_str_owned();
        let pr2 = s.as_bytes().as_ptr_range();

        for (c, actual) in TEST_STR.chars().zip(CharMutRefs::from(&mut *s)) {
            assert_eq!(actual.as_char(), c);

            let mut buffer = [0; 4];

            let s2 = c.encode_utf8(&mut buffer);
            let len = s2.len();
            assert_eq!(actual.as_str_mut(), s2);

            let b = &buffer[..len];
            // SAFETY:
            // Not mutating.
            assert_eq!(unsafe { actual.as_bytes_mut() }, b);

            assert!(pr2.contains(&actual.as_ptr()));
        }

        assert_eq!(
            &*s, TEST_STR,
            "`Char` as methods mutated the mutable string slice"
        );
    }

    macro_rules! replace {
        ( ($fn:path)($c:expr $(, $arg:expr)*) <- $c2:expr, $expected:ident => $cfg:block ) => {
            let mut buffer = [0; 6];
            let s = $c2.encode_utf8(&mut buffer[1..]);
            let c2 = <&mut Char>::try_from(s).unwrap();

            $fn(c2, $c $(, $arg)*).expect(concat!(stringify!($fn), " returned an error"));

            let mut $expected = [0; 6];
            $cfg

            assert_eq!(buffer, $expected, concat!(stringify!($fn), " failed a replace"));
        };
    }

    #[test]
    fn test_replace() {
        let test_chars = ['a', 'à', 'ḁ', '🔤'];

        for (i, c) in TEST_STR.chars().enumerate() {
            replace!((Char::replace)(c) <- test_chars[i], expected_buffer => {
                c.encode_utf8(&mut expected_buffer[1..=4]);
            });

            for test_char in &test_chars[i..] {
                let test_char_len = test_char.len_utf8();

                replace!(
                    (Char::replace_with_pad_space)(c) <- test_char,
                    expected_buffer => {
                        let len = c.encode_utf8(&mut expected_buffer[1..]).len();
                        expected_buffer[(len + 1)..=test_char_len].fill(b' ');
                    }
                );

                replace!(
                    (Char::replace_with_pad)(c, b'a') <- test_char,
                    expected_buffer => {
                        let len = c.encode_utf8(&mut expected_buffer[1..]).len();
                        expected_buffer[(len + 1)..=test_char_len].fill(b'a');
                    }
                );

                replace!(
                    (Char::replace_with_pad_char)(c, 'a') <- test_char,
                    expected_buffer => {
                        let len = c.encode_utf8(&mut expected_buffer[1..]).len();
                        expected_buffer[(len + 1)..=test_char_len].fill(b'a');
                    }
                );

                replace!(
                    (Char::replace_with_pad_left_space)(c) <- test_char,
                    expected_buffer => {
                        let i = test_char_len + 1 - c.len_utf8();
                        c.encode_utf8(&mut expected_buffer[i..]);
                    expected_buffer[1..i].fill(b' ');
                    }
                );

                replace!(
                    (Char::replace_with_pad_left)(c, b'a') <- test_char,
                    expected_buffer => {
                        let i = test_char_len + 1 - c.len_utf8();
                        c.encode_utf8(&mut expected_buffer[i..]);
                    expected_buffer[1..i].fill(b'a');
                    }
                );

                replace!(
                    (Char::replace_with_pad_left_char)(c, 'a') <- test_char,
                    expected_buffer => {
                        let i = test_char_len + 1 - c.len_utf8();
                        c.encode_utf8(&mut expected_buffer[i..]);
                    expected_buffer[1..i].fill(b'a');
                    }
                );
            }
        }
    }

    #[test]
    fn test_eq() {
        for c in CharRefs::from(TEST_STR) {
            assert_eq!(c, c.as_str());
            assert_eq!(c, c.as_char());

            {
                // Make sure that the character with a suffix does not equal it.
                let mut buffer = [b' '; 5];
                c.copy_to(&mut buffer).unwrap();

                // SAFETY:
                // This is valid as the buffer was full of single-byte utf8
                // encoded characters and then had another embedded into it.
                let s = unsafe { str::from_utf8_unchecked(&buffer) };

                assert_ne!(c, s);
            }
            assert_ne!(c, "b");
            assert_ne!(c, 'b');
        }
    }
}
