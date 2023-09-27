use core::ops::RangeBounds;

use crate::{
    char_slice, char_slice_mut, char_split_at, char_split_at_mut, copy_to,
    errors::{LenNotEqual, ReplaceWithPadCharError, ReplaceWithPadError, ReplacementTooLong},
    iter::{CharMutRefs, CharRefs},
    replace, replace_with_pad, replace_with_pad_char, replace_with_pad_left,
    replace_with_pad_left_char, replace_with_pad_left_space, replace_with_pad_space, Char,
};

/// The `StrExt` trait adds some methods to string types, many of which operate on character indexes and with character references.
///
/// To use its methods, import it with a use statement.
/// ```
/// use mut_str::StrExt;
/// ```
pub trait StrExt {
    type Output: ?Sized;
    type Iter<'a>: Iterator<Item = &'a Char>
    where
        Self: 'a;
    type IterMut<'a>: Iterator<Item = &'a mut Char>
    where
        Self: 'a;

    #[must_use]
    /// Get a character reference from the string and an index.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let s = "Hello, World!";
    /// let c = s.get_char(1).unwrap();
    ///
    /// assert_eq!(c, 'e');
    /// ```
    fn get_char(&self, i: usize) -> Option<&Char>;
    #[must_use]
    /// Get a mutable character reference from the mutable string and an index.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("Hello, World!");
    /// let c = owned_s.get_char_mut(1).unwrap();
    ///
    /// assert_eq!(c, 'e');
    /// ```
    fn get_char_mut(&mut self, i: usize) -> Option<&mut Char>;

    #[must_use]
    /// Slice the string in units of UTF-8 characters.
    /// If `range` is out of bounds, `None` will be returned.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let s = "Hello, World!";
    ///
    /// let hello = s.char_slice(..5).unwrap();
    /// assert_eq!(hello, "Hello");
    ///
    /// let world = s.char_slice(7..12).unwrap();
    /// assert_eq!(world, "World");
    /// ```
    fn char_slice<R: RangeBounds<usize>>(&self, range: R) -> Option<&Self::Output>;
    #[must_use]
    /// Slice the mutable string in units of UTF-8 characters.
    /// If `range` is out of bounds, `None` will be returned.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("Hello, World!");
    ///
    /// let hello = owned_s.char_slice_mut(..5).unwrap();
    /// assert_eq!(hello, "Hello");
    ///
    /// let world = owned_s.char_slice_mut(7..12).unwrap();
    /// assert_eq!(world, "World");
    /// ```
    fn char_slice_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<&mut Self::Output>;

    #[must_use]
    /// Divide the string into two at an index in units of UTF-8 characters.
    /// If `mid` is out of bounds, `None` will be returned.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let s = "Hello, World!";
    ///
    /// let (l, r) = s.char_split_at(6).unwrap();
    /// assert_eq!(l, "Hello,");
    /// assert_eq!(r, " World!");
    /// ```
    fn char_split_at(&self, mid: usize) -> Option<(&Self::Output, &Self::Output)>;
    #[must_use]
    /// Divide the mutable string into two at an index in units of UTF-8 characters.
    /// If `mid` is out of bounds, `None` will be returned.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("Hello, World!");
    ///
    /// let (l, r) = owned_s.char_split_at_mut(6).unwrap();
    /// assert_eq!(l, "Hello,");
    /// assert_eq!(r, " World!");
    /// ```
    fn char_split_at_mut(&mut self, mid: usize) -> Option<(&mut Self::Output, &mut Self::Output)>;

    #[must_use]
    /// Get an iterator over character references in the string.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let s = "Hello, World!";
    ///
    /// s.ref_iter()
    ///     .zip(s.chars())
    ///     .for_each(|(x, y)| assert_eq!(x, y));
    /// ```
    fn ref_iter(&self) -> Self::Iter<'_>;
    #[must_use]
    /// Get an iterator over mutable character references in the string.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let s = "Hello, World!";
    /// let mut owned_s = Box::<str>::from(s);
    ///
    /// owned_s.mut_iter()
    ///     .zip(s.chars())
    ///     .for_each(|(x, y)| assert_eq!(x, y));
    /// ```
    fn mut_iter(&mut self) -> Self::IterMut<'_>;

    /// Copy the string to a byte buffer and get the new string containing the inserted character.
    /// Returns `None` if `buffer` is shorter than the string.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let s = "Hello, World!";
    /// let mut buffer = [0; 50];
    /// let new_s = s.copy_to(&mut buffer).unwrap();
    ///
    /// assert_eq!(new_s, s);
    /// ```
    fn copy_to<'a>(&self, buffer: &'a mut [u8]) -> Option<&'a mut Self::Output>;

    /// Replace the mutable string with another of the same length.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("World!");
    ///
    /// owned_s.replace_with("🌍!!").unwrap();
    /// assert_eq!(&*owned_s, "🌍!!");
    ///
    /// owned_s.replace_with("aaaaaa").unwrap();
    /// assert_eq!(&*owned_s, "aaaaaa");
    /// ```
    ///
    /// # Errors
    /// - If `s` and `r`, when utf8 encoded, do not have the same length, [`LenNotEqual`] will be returned.
    fn replace_with<'a>(&'a mut self, r: &str) -> Result<&'a mut str, LenNotEqual>;
    /// Replace the mutable string with another of the same length or shorter.
    /// The remaining bytes will be filled with spaces.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("World!");
    ///
    /// owned_s.replace_with_pad_space("🌍").unwrap();
    /// assert_eq!(&*owned_s, "🌍  ");
    ///
    /// owned_s.replace_with_pad_space("aaaa").unwrap();
    /// assert_eq!(&*owned_s, "aaaa  ");
    /// ```
    ///
    /// # Errors
    /// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplacementTooLong`] will be returned.
    fn replace_with_pad_space<'a>(&'a mut self, r: &str)
        -> Result<&'a mut str, ReplacementTooLong>;
    /// Replace the mutable string with another of the same length or shorter.
    /// The remaining bytes will be filled with `pad`.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("World!");
    ///
    /// owned_s.replace_with_pad("🌍", b'!').unwrap();
    /// assert_eq!(&*owned_s, "🌍!!");
    ///
    /// owned_s.replace_with_pad("aaaa", b'b').unwrap();
    /// assert_eq!(&*owned_s, "aaaabb");
    /// ```
    ///
    /// # Errors
    /// - If `pad` is not valid utf8, [`ReplaceWithPadError::InvalidPad`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadError::ReplacementLen`] will be returned.
    fn replace_with_pad<'a>(
        &'a mut self,
        r: &str,
        pad: u8,
    ) -> Result<&'a mut str, ReplaceWithPadError>;
    /// Replace the mutable string with another of the same length or shorter.
    /// The remaining bytes will be filled with `pad`, which must be one byte long.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("World!");
    ///
    /// owned_s.replace_with_pad_char("🌍", '!').unwrap();
    /// assert_eq!(&*owned_s, "🌍!!");
    ///
    /// owned_s.replace_with_pad_char("aaaa", 'b').unwrap();
    /// assert_eq!(&*owned_s, "aaaabb");
    /// ```
    ///
    /// # Errors
    /// - If `pad_char`, when utf8 encoded, is longer than `Self`, [`ReplaceWithPadCharError::PadCharTooLong`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadCharError::ReplacementLen`] will be returned.
    fn replace_with_pad_char<'a, C>(
        &'a mut self,
        r: &str,
        pad_char: C,
    ) -> Result<&'a mut str, ReplaceWithPadCharError>
    where
        C: Into<char>;
    /// Replace the mutable string with another of the same length or shorter, right aligned.
    /// The remaining bytes before the string will be filled with spaces.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("World!");
    ///
    /// owned_s.replace_with_pad_left_space("🌍").unwrap();
    /// assert_eq!(&*owned_s, "  🌍");
    ///
    /// owned_s.replace_with_pad_left_space("aaaa").unwrap();
    /// assert_eq!(&*owned_s, "  aaaa");
    /// ```
    ///
    /// # Errors
    /// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplacementTooLong`] will be returned.
    fn replace_with_pad_left_space<'a>(
        &'a mut self,
        r: &str,
    ) -> Result<&'a mut Self::Output, ReplacementTooLong>;
    /// Replace the mutable string with another of the same length or shorter, right aligned.
    /// The remaining bytes before the string will be filled with `pad`.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("World!");
    ///
    /// owned_s.replace_with_pad_left("🌍", b'!').unwrap();
    /// assert_eq!(&*owned_s, "!!🌍");
    ///
    /// owned_s.replace_with_pad_left("aaaa", b'b').unwrap();
    /// assert_eq!(&*owned_s, "bbaaaa");
    /// ```
    ///
    /// # Errors
    /// - If `pad` is not valid utf8, [`ReplaceWithPadError::InvalidPad`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadError::ReplacementLen`] will be returned.
    fn replace_with_pad_left<'a>(
        &'a mut self,
        r: &str,
        pad: u8,
    ) -> Result<&'a mut Self::Output, ReplaceWithPadError>;
    /// Replace the mutable string with another of the same length or shorter, right aligned.
    /// The remaining bytes before the string will be filled with `char`, which must be one byte long.
    ///
    /// ```
    /// use mut_str::StrExt;
    ///
    /// let mut owned_s = Box::<str>::from("World!");
    ///
    /// owned_s.replace_with_pad_left_char("🌍", '!').unwrap();
    /// assert_eq!(&*owned_s, "!!🌍");
    ///
    /// owned_s.replace_with_pad_left_char("aaaa", 'b').unwrap();
    /// assert_eq!(&*owned_s, "bbaaaa");
    /// ```
    ///
    /// # Errors
    /// - If `pad_char`, when utf8 encoded, is longer than `Self`, [`ReplaceWithPadCharError::PadCharTooLong`] will be returned.
    /// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadCharError::ReplacementLen`] will be returned.
    fn replace_with_pad_left_char<'a, C>(
        &'a mut self,
        r: &str,
        pad_char: C,
    ) -> Result<&'a mut Self::Output, ReplaceWithPadCharError>
    where
        C: Into<char>;
}

impl StrExt for str {
    type Output = Self;
    type Iter<'a> = CharRefs<'a>;
    type IterMut<'a> = CharMutRefs<'a>;

    #[inline]
    fn get_char(&self, i: usize) -> Option<&Char> {
        Char::get(self, i)
    }

    #[inline]
    fn get_char_mut(&mut self, i: usize) -> Option<&mut Char> {
        Char::get_mut(self, i)
    }

    #[inline]
    fn char_slice<R: RangeBounds<usize>>(&self, range: R) -> Option<&Self::Output> {
        char_slice(self, range)
    }

    #[inline]
    fn char_slice_mut<R: RangeBounds<usize>>(&mut self, range: R) -> Option<&mut Self::Output> {
        char_slice_mut(self, range)
    }

    #[inline]
    fn char_split_at(&self, mid: usize) -> Option<(&Self::Output, &Self::Output)> {
        char_split_at(self, mid)
    }

    #[inline]
    fn char_split_at_mut(&mut self, mid: usize) -> Option<(&mut Self::Output, &mut Self::Output)> {
        char_split_at_mut(self, mid)
    }

    #[inline]
    fn ref_iter(&self) -> Self::Iter<'_> {
        CharRefs::from(self)
    }

    #[inline]
    fn mut_iter(&mut self) -> Self::IterMut<'_> {
        CharMutRefs::from(self)
    }

    #[inline]
    fn copy_to<'a>(&self, buffer: &'a mut [u8]) -> Option<&'a mut Self::Output> {
        copy_to(self, buffer)
    }

    #[inline]
    fn replace_with<'a>(&'a mut self, r: &str) -> Result<&'a mut str, LenNotEqual> {
        replace(self, r)
    }

    #[inline]
    fn replace_with_pad_space<'a>(
        &'a mut self,
        r: &str,
    ) -> Result<&'a mut str, ReplacementTooLong> {
        replace_with_pad_space(self, r)
    }

    #[inline]
    fn replace_with_pad<'a>(
        &'a mut self,
        r: &str,
        pad: u8,
    ) -> Result<&'a mut str, ReplaceWithPadError> {
        replace_with_pad(self, r, pad)
    }

    #[inline]
    fn replace_with_pad_char<'a, C>(
        &'a mut self,
        r: &str,
        pad_char: C,
    ) -> Result<&'a mut str, ReplaceWithPadCharError>
    where
        C: Into<char>,
    {
        replace_with_pad_char(self, r, pad_char)
    }

    #[inline]
    fn replace_with_pad_left_space(
        &mut self,
        r: &str,
    ) -> Result<&mut Self::Output, ReplacementTooLong> {
        replace_with_pad_left_space(self, r)
    }

    #[inline]
    fn replace_with_pad_left(
        &mut self,
        r: &str,
        pad: u8,
    ) -> Result<&mut Self::Output, ReplaceWithPadError> {
        replace_with_pad_left(self, r, pad)
    }

    #[inline]
    fn replace_with_pad_left_char<C>(
        &mut self,
        r: &str,
        pad_char: C,
    ) -> Result<&mut Self::Output, ReplaceWithPadCharError>
    where
        C: Into<char>,
    {
        replace_with_pad_left_char(self, r, pad_char)
    }
}
