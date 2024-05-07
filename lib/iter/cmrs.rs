use core::{iter::FusedIterator, str};

use crate::{char_rsplit_at_mut, char_split_at_mut, extend_lifetime_mut, Char, OwnedChar};

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
    s: &'a mut str,
}

// #[allow(clippy::needless_lifetimes)]
impl<'a> CharMutRefs<'a> {
    #[must_use]
    #[inline]
    /// Get the remaining string to be iterated over.
    pub const fn as_str(&self) -> &str {
        self.s
    }

    #[must_use]
    #[inline]
    /// Get the remaining mutable string to be iterated over.
    pub fn as_str_mut(&mut self) -> &mut str {
        self.s
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
        Self { s: value }
    }
}

impl<'a> Iterator for CharMutRefs<'a> {
    type Item = &'a mut Char;

    fn next(&mut self) -> Option<Self::Item> {
        let (c, remaining) = char_split_at_mut(self.s, 1)?;
        // SAFETY:
        // The subslice is created from `self.s` and immediately replaces
        // it, so the lifetime can be extended.
        self.s = unsafe { extend_lifetime_mut(remaining) };

        // SAFETY:
        // `c` is a utf8 string with 1 character in, as returned by
        // `char_split_at`, so `c.as_ptr()` points to the start of a
        // utf8 character.
        Some(unsafe { &mut *Char::new_unchecked_mut(c.as_mut_ptr()) })
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
        let Some(mid) = n.checked_add(1) else {
            // SAFETY:
            // `0..0` is always a valid subslice.
            // The subslice is created from `self.s` and immediately replaces
            // it, so the lifetime can be extended.
            self.s = unsafe { extend_lifetime_mut(self.s.get_unchecked_mut(0..0)) };
            return None;
        };

        let Some((head, remaining)) = char_split_at_mut(self.s, mid) else {
            // SAFETY:
            // `0..0` is always a valid subslice.
            // The subslice is created from `self.s` and immediately replaces
            // it, so the lifetime can be extended.
            self.s = unsafe { extend_lifetime_mut(self.s.get_unchecked_mut(0..0)) };
            return None;
        };

        // SAFETY:
        // `remaining` and `tail` were created from `self.s` with lifetime 'a.
        // `self.s` is now replaced with one half, so both lifetimes can be extended.
        self.s = unsafe { extend_lifetime_mut(remaining) };

        // SAFETY:
        // `head` must contain at least one character, as `mid >= 1`, therefore
        // `char_indices.last()` will return a `Some` value.
        let (index, _) = unsafe { head.char_indices().last().unwrap_unchecked() };
        // SAFETY:
        // `index` is obtained from `CharIndices`, so it is within the bounds
        // of `head` and must be on a character boundry.
        let ptr = unsafe { head.as_mut_ptr().add(index) };

        // SAFETY:
        // `ptr` is a pointer to the start of a utf8 character.
        Some(unsafe { &mut *Char::new_unchecked_mut(ptr) })
    }
}

impl<'a> DoubleEndedIterator for CharMutRefs<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let (remaining, c) = char_rsplit_at_mut(self.s, 1)?;
        // SAFETY:
        // The subslice is created from `self.s` and immediately replaces
        // it, so the lifetime can be extended.
        self.s = unsafe { extend_lifetime_mut(remaining) };

        // SAFETY:
        // `c` is a utf8 string with 1 character in, as returned by
        // `char_split_at`, so `c.as_ptr()` points to the start of a
        // utf8 character.
        Some(unsafe { &mut *Char::new_unchecked_mut(c.as_mut_ptr()) })
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        let Some(mid) = n.checked_add(1) else {
            // SAFETY:
            // `0..0` is always a valid subslice.
            // The subslice is created from `self.s` and immediately replaces
            // it, so the lifetime can be extended.
            self.s = unsafe { extend_lifetime_mut(self.s.get_unchecked_mut(0..0)) };
            return None;
        };

        let Some((remaining, tail)) = char_rsplit_at_mut(self.s, mid) else {
            // SAFETY:
            // `0..0` is always a valid subslice.
            // The subslice is created from `self.s` and immediately replaces
            // it, so the lifetime can be extended.
            self.s = unsafe { extend_lifetime_mut(self.s.get_unchecked_mut(0..0)) };
            return None;
        };

        // SAFETY:
        // `remaining` and `tail` were created from `self.s` with lifetime 'a.
        // `self.s` is now replaced with one half, so both lifetimes can be extended.
        self.s = unsafe { extend_lifetime_mut(remaining) };

        let ptr = tail.as_mut_ptr();

        // SAFETY:
        // `ptr` is a pointer to the start of a utf8 string (`tail`)
        // with at least one character as `mid >= 1`.
        Some(unsafe { &mut *Char::new_unchecked_mut(ptr) })
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
    fn test_nth() {
        let mut s = test_str_owned();

        for step in 0..4 {
            let mut iter = CharMutRefs::from(&mut *s);
            let mut expected_chars = TEST_STR.chars();

            while let Some(expected) = expected_chars.nth(step) {
                let actual = iter.nth(step).expect("expected a character ref");

                assert_eq!(actual.len(), expected.len_utf8());
                assert_eq!(actual.as_char(), expected);
            }

            assert!(iter.nth(step).is_none(), "expected no more character refs");
        }

        assert!(CharMutRefs::from(&mut *s).nth(4).is_none());
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
    fn test_nth_backwards() {
        let mut s = test_str_owned();

        for step in 0..4 {
            let mut iter = CharMutRefs::from(&mut *s);
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

        assert!(CharMutRefs::from(&mut *s).nth_back(4).is_none());
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
