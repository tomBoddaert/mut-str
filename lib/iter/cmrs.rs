use core::{iter::FusedIterator, mem::transmute, str};

use crate::{Char, OwnedChar};

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
/// An iterator over mutable references to the UTF-8 encoded characters of a mutable [`prim@str`].
///
/// This is created by [`Self::from()`].
///
/// ```
/// use mut_str::iter::CharMutRefs;
///
/// let s = "Hello, World!";
/// let mut owned_s = Box::<str>::from(s);
///
/// CharMutRefs::from(&mut *owned_s)
///     .zip(s.chars())
///     .for_each(|(x, y)| assert_eq!(x, y));
/// ```
pub struct CharMutRefs<'a> {
    s: &'a mut [u8],
}

#[allow(clippy::needless_lifetimes)]
impl<'a> CharMutRefs<'a> {
    #[must_use]
    #[inline]
    /// Get the remaining string to be iterated over.
    pub const fn as_str<'b>(&'b self) -> &'b str {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        unsafe { str::from_utf8_unchecked(self.s) }
    }

    #[must_use]
    #[inline]
    /// Get the remaining mutable string to be iterated over.
    pub fn as_str_mut<'b>(&'b mut self) -> &'b str {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        unsafe { str::from_utf8_unchecked_mut(self.s) }
    }

    #[inline]
    /// Map the iterator to [`OwnedChar`] values.
    pub fn owned(self) -> core::iter::Map<Self, fn(&mut Char) -> OwnedChar> {
        self.map(|x| x.as_owned())
    }
}

impl<'a> From<&'a mut str> for CharMutRefs<'a> {
    #[inline]
    fn from(value: &'a mut str) -> Self {
        Self {
            // SAFETY:
            // `Self` ensures that the string remains valid utf8.
            s: unsafe { value.as_bytes_mut() },
        }
    }
}

impl<'a> Iterator for CharMutRefs<'a> {
    type Item = &'a mut Char;

    fn next<'b>(&'b mut self) -> Option<Self::Item> {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        let char = unsafe { str::from_utf8_unchecked(self.s) }.chars().next()?;

        // SAFETY:
        // As the string slice is split each time, this iterator will not hand out
        // multiple mutable references to the same data, so extending its lifetime
        // to `'a` is valid.
        let (char_slice, remaining) = unsafe {
            transmute::<(&'b mut [u8], &'b mut [u8]), (&'a mut [u8], &'a mut [u8])>(
                self.s.split_at_mut(char.len_utf8()),
            )
        };

        self.s = remaining;

        // SAFETY:
        // `char_slice` is guaranteed to be a valid utf8 string containing
        // exactly one character.
        Some(unsafe { &mut *Char::new_unchecked_mut(char_slice.as_mut_ptr()) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = self.s.len();
        ((len + 3) / 4, Some(len))
    }

    #[inline]
    fn count(self) -> usize
    where
        Self: Sized,
    {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        unsafe { str::from_utf8_unchecked(self.s) }.chars().count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }
}

impl<'a> DoubleEndedIterator for CharMutRefs<'a> {
    fn next_back<'b>(&'b mut self) -> Option<Self::Item> {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        let char = unsafe { str::from_utf8_unchecked(self.s) }
            .chars()
            .next_back()?;

        // SAFETY:
        // As the string slice is split each time, this iterator will not hand out
        // multiple mutable references to the same data, so extending its lifetime
        // to `'a` is valid.
        let (remaining, char_slice) = unsafe {
            transmute::<(&'b mut [u8], &'b mut [u8]), (&'a mut [u8], &'a mut [u8])>(
                self.s.split_at_mut(self.s.len() - char.len_utf8()),
            )
        };

        self.s = remaining;

        // SAFETY:
        // `char_slice` is guaranteed to be a valid utf8 string containing
        // exactly one character.
        Some(unsafe { &mut *Char::new_unchecked_mut(char_slice.as_mut_ptr()) })
    }
}

impl<'a> FusedIterator for CharMutRefs<'a> {}

#[cfg(test)]
mod test {
    use crate::{
        test::{test_str_owned, TEST_STR},
        StrExt,
    };

    use super::CharMutRefs;

    #[test]
    fn test_forwards() {
        let mut s = test_str_owned();
        let mut iter = CharMutRefs::from(&mut *s);

        for expected in TEST_STR.chars() {
            let actual = iter.next().expect("expected a character ref");

            assert_eq!(actual.len(), expected.len_utf8());
            assert_eq!(actual.as_char(), expected);
        }

        assert!(iter.next().is_none(), "expected no more character refs");

        let size_hint = iter.size_hint();
        assert_eq!(size_hint.0, 0);
        assert_eq!(size_hint.1, Some(0));
    }

    #[test]
    fn test_backwards() {
        let mut s = test_str_owned();
        let mut iter = CharMutRefs::from(&mut *s);

        for expected in TEST_STR.chars().rev() {
            let actual = iter.next_back().expect("expected a character ref");

            assert_eq!(actual.len(), expected.len_utf8());
            assert_eq!(actual.as_char(), expected);
        }

        assert!(
            iter.next_back().is_none(),
            "expected no more character refs"
        );

        let size_hint = iter.size_hint();
        assert_eq!(size_hint.0, 0);
        assert_eq!(size_hint.1, Some(0));
    }

    #[test]
    fn test_mut() {
        let s = "abcd";
        let mut s2 = Box::<str>::from(s);

        for char in s2.mut_iter() {
            char.make_ascii_uppercase();
        }

        assert_eq!(&*s2, s.to_ascii_uppercase());
    }
}
