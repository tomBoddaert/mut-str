use core::{iter::FusedIterator, str};

use crate::{char_rsplit_at, char_split_at, Char, OwnedChar};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
/// An iterator over references to the UTF-8 encoded characters of a [`prim@str`].
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
    s: &'a str,
}

impl<'a> CharRefs<'a> {
    #[must_use]
    #[inline]
    /// Get the remaining string to be iterated over.
    pub const fn as_str(&self) -> &'a str {
        self.s
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
        Self { s: value }
    }
}

impl<'a> Iterator for CharRefs<'a> {
    type Item = &'a Char;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let (c, remaining) = char_split_at(self.s, 1)?;
        self.s = remaining;

        // SAFETY:
        // `c` is a utf8 string with 1 character in, as returned by
        // `char_split_at`, so `c.as_ptr()` points to the start of a
        // utf8 character.
        Some(unsafe { &*Char::new_unchecked(c.as_ptr()) })
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
        self.s.chars().count()
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item>
    where
        Self: Sized,
    {
        self.next_back()
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        let Some((head, remaining)) = n.checked_add(1).and_then(|mid| char_split_at(self.s, mid))
        else {
            self.s = "";
            return None;
        };
        self.s = remaining;

        // SAFETY:
        // `head` must contain at least one character, as `mid >= 1`, therefore
        // `char_indices.last()` will return a `Some` value.
        let (index, _) = unsafe { head.char_indices().last().unwrap_unchecked() };
        // SAFETY:
        // `index` is obtained from `CharIndices`, so it is within the bounds
        // of `head` and must be on a character boundry.
        let ptr = unsafe { head.as_ptr().add(index) };

        // SAFETY:
        // `ptr` is a pointer to the start of a utf8 character.
        Some(unsafe { &*Char::new_unchecked(ptr) })
    }
}

impl<'a> DoubleEndedIterator for CharRefs<'a> {
    #[inline]
    fn next_back(&mut self) -> Option<Self::Item> {
        let (remaining, c) = char_rsplit_at(self.s, 1)?;
        self.s = remaining;

        // SAFETY:
        // `c` is a utf8 string with 1 character in, as returned by
        // `char_split_at`, so `c.as_ptr()` points to the start of a
        // utf8 character.
        Some(unsafe { &*Char::new_unchecked(c.as_ptr()) })
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let Some((remaining, tail)) = n.checked_add(1).and_then(|mid| char_rsplit_at(self.s, mid))
        else {
            self.s = "";
            return None;
        };
        self.s = remaining;

        let ptr = tail.as_ptr();

        // SAFETY:
        // `ptr` is a pointer to the start of a utf8 string (`tail`)
        // with at least one character as `mid >= 1`.
        Some(unsafe { &*Char::new_unchecked(ptr) })
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
    fn test_nth() {
        for step in 0..4 {
            let mut iter = CharRefs::from(TEST_STR);
            let mut expected_chars = TEST_STR.chars();

            while let Some(expected) = expected_chars.nth(step) {
                let actual = iter.nth(step).expect("expected a character ref");

                assert_eq!(actual.len(), expected.len_utf8());
                assert_eq!(actual.as_char(), expected);
            }

            assert!(iter.nth(step).is_none(), "expected no more character refs");
        }

        assert!(CharRefs::from(TEST_STR).nth(4).is_none());
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

    #[test]
    fn test_nth_backwards() {
        for step in 0..4 {
            let mut iter = CharRefs::from(TEST_STR);
            let mut expected_chars = TEST_STR.chars();

            while let Some(expected) = expected_chars.nth_back(step) {
                let actual = iter.nth_back(step).expect("expected a character ref");

                assert_eq!(actual.len(), expected.len_utf8());
                assert_eq!(actual.as_char(), expected);
            }

            assert!(
                iter.nth_back(step).is_none(),
                "expected no more character refs"
            );
        }

        assert!(CharRefs::from(TEST_STR).nth_back(4).is_none());
    }
}
