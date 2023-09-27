use core::{iter::FusedIterator, str};

use crate::{Char, OwnedChar};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
/// An iterator over references to the UTF-8 encoded characters of a string slice.
///
/// This is created by [`Self::from()`].
///
/// ```
/// use mut_str::iter::CharRefs;
///
/// let s = "Hello, World!";
///
/// CharRefs::from(s)
///     .zip(s.chars())
///     .for_each(|(x, y)| assert_eq!(x, y));
/// ```
pub struct CharRefs<'a> {
    s: &'a [u8],
}

impl<'a> CharRefs<'a> {
    #[must_use]
    #[inline]
    /// Get the remaining string to be iterated over.
    pub const fn as_str(&self) -> &'a str {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        unsafe { str::from_utf8_unchecked(self.s) }
    }

    #[inline]
    /// Map the iterator to [`OwnedChar`] values.
    pub fn owned(self) -> core::iter::Map<Self, fn(&Char) -> OwnedChar> {
        self.map(Char::as_owned)
    }
}

impl<'a> From<&'a str> for CharRefs<'a> {
    #[inline]
    fn from(value: &'a str) -> Self {
        Self {
            s: value.as_bytes(),
        }
    }
}

impl<'a> Iterator for CharRefs<'a> {
    type Item = &'a Char;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        let char = unsafe { str::from_utf8_unchecked(self.s) }.chars().next()?;

        let (char_slice, remaining) = self.s.split_at(char.len_utf8());
        self.s = remaining;

        // SAFETY:
        // `char_slice` is guaranteed to be a valid utf8 string containing
        // exactly one character.
        Some(unsafe { &*Char::new_unchecked(char_slice.as_ptr()) })
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

impl<'a> DoubleEndedIterator for CharRefs<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        // SAFETY:
        // `self.s` is guaranteed to be the bytes of a valid utf8 string.
        let char = unsafe { str::from_utf8_unchecked(self.s) }
            .chars()
            .next_back()?;

        let (remaining, char_slice) = self.s.split_at(self.s.len() - char.len_utf8());
        self.s = remaining;

        // SAFETY:
        // `char_slice` is guaranteed to be a valid utf8 string containing
        // exactly one character.
        Some(unsafe { &*Char::new_unchecked(char_slice.as_ptr()) })
    }
}

impl<'a> FusedIterator for CharRefs<'a> {}

#[cfg(test)]
mod test {
    use crate::test::TEST_STR;

    use super::CharRefs;

    #[test]
    fn test_forwards() {
        let mut iter = CharRefs::from(TEST_STR);

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
        let mut iter = CharRefs::from(TEST_STR);

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
}
