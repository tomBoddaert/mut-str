use core::ops::{Bound, RangeBounds};

#[must_use]
/// Slice a [`prim@str`] in units of UTF-8 characters.
///
/// ```
/// use mut_str::char_slice;
///
/// let s = "Hello, World!";
///
/// let hello = char_slice(s, ..5).unwrap();
/// assert_eq!(hello, "Hello");
///
/// let world = char_slice(s, 7..12).unwrap();
/// assert_eq!(world, "World");
/// ```
pub fn char_slice<R: RangeBounds<usize>>(s: &str, range: R) -> Option<&str> {
    let start_inclusive = match range.start_bound() {
        Bound::Included(&i) => i,
        Bound::Excluded(i) => i.checked_add(1)?,
        Bound::Unbounded => 0,
    };

    // This will not exclude all out of bounds ranges but is a quick
    // check that will eliminate extreme bounds.
    if start_inclusive > s.len() {
        return None;
    }

    let mut iter = s.char_indices();

    // Get the position of the first character in the subslice.
    let start = if let Some(n) = start_inclusive.checked_sub(1) {
        let (i, c) = iter.nth(n)?;
        i + c.len_utf8()
    } else {
        0
    };

    let Some(end_exclusive) = (match range.end_bound() {
        Bound::Included(i) => Some(i.checked_add(1)?),
        Bound::Excluded(&i) => Some(i),
        Bound::Unbounded => None,
    }) else {
        return Some(
            // SAFETY:
            // `start_index` is from a `CharIndices` iterator, so its position
            // is valid.
            unsafe { s.get_unchecked(start..) },
        );
    };

    // This will not exclude all out of bounds ranges but is a quick
    // check that will eliminate extreme bounds.
    if end_exclusive > s.len() {
        return None;
    }

    // Get the number of characters in the subslice.
    let char_len = end_exclusive.checked_sub(start_inclusive)?;

    // Get the position of the byte after the last character in the subslice.
    let end = if let Some(n) = char_len.checked_sub(1) {
        let (i, c) = iter.nth(n)?;
        i + c.len_utf8()
    } else {
        start
    };

    Some(
        // SAFETY:
        // `start` is either 0 or a character index + its byte length.
        // `end` is either `start` or a character index + its byte length.
        // Both are therefore upperbounded by the byte length of the string and
        // are character boundries.
        unsafe { s.get_unchecked(start..end) },
    )
}

#[must_use]
/// Slice a mutable [`prim@str`] in units of UTF-8 characters.
///
/// ```
/// use mut_str::char_slice_mut;
///
/// let mut owned_s = Box::<str>::from("Hello, World!");
///
/// let hello = char_slice_mut(&mut *owned_s, ..5).unwrap();
/// assert_eq!(hello, "Hello");
///
/// let world = char_slice_mut(&mut *owned_s, 7..12).unwrap();
/// assert_eq!(world, "World");
/// ```
pub fn char_slice_mut<R: RangeBounds<usize>>(s: &mut str, range: R) -> Option<&mut str> {
    let start_inclusive = match range.start_bound() {
        Bound::Included(&i) => i,
        Bound::Excluded(i) => i.checked_add(1)?,
        Bound::Unbounded => 0,
    };

    // This will not exclude all out of bounds ranges but is a quick
    // check that will eliminate extreme bounds.
    if start_inclusive > s.len() {
        return None;
    }

    let mut iter = s.char_indices();

    // Get the position of the first character in the subslice.
    let start = if let Some(n) = start_inclusive.checked_sub(1) {
        let (i, c) = iter.nth(n)?;
        i + c.len_utf8()
    } else {
        0
    };

    let Some(end_exclusive) = (match range.end_bound() {
        Bound::Included(i) => Some(i.checked_add(1)?),
        Bound::Excluded(&i) => Some(i),
        Bound::Unbounded => None,
    }) else {
        return Some(
            // SAFETY:
            // `start_index` is from a `CharIndices` iterator, so its position
            // is valid.
            unsafe { s.get_unchecked_mut(start..) },
        );
    };

    // This will not exclude all out of bounds ranges but is a quick
    // check that will eliminate extreme bounds.
    if end_exclusive > s.len() {
        return None;
    }

    // Get the number of characters in the subslice.
    let char_len = end_exclusive.checked_sub(start_inclusive)?;

    // Get the position of the byte after the last character in the subslice.
    let end = if let Some(n) = char_len.checked_sub(1) {
        let (i, c) = iter.nth(n)?;
        i + c.len_utf8()
    } else {
        start
    };

    Some(
        // SAFETY:
        // `start` is either 0 or a character index + its byte length.
        // `end` is either `start` or a character index + its byte length.
        // Both are therefore upperbounded by the byte length of the string and
        // are character boundries.
        unsafe { s.get_unchecked_mut(start..end) },
    )
}

#[cfg(test)]
mod test {
    use crate::{
        char_slice, char_slice_mut,
        test::{test_str_owned, TEST_STR},
    };

    #[test]
    fn slice_empty_at_bounds() {
        let slice =
            char_slice(TEST_STR, ..0).expect("failed to slice string at character bound ..0");
        assert!(slice.is_empty());

        let slice =
            char_slice(TEST_STR, 0..0).expect("failed to slice string at character bound 0..0");
        assert!(slice.is_empty());

        let char_len = TEST_STR.chars().count();
        let slice = char_slice(TEST_STR, char_len..char_len).unwrap_or_else(|| {
            panic!("failed to slice string at character bound {char_len}..{char_len}")
        });
        assert!(slice.is_empty());

        let slice = char_slice(TEST_STR, char_len..)
            .unwrap_or_else(|| panic!("failed to slice string at character bound {char_len}.."));
        assert!(slice.is_empty());
    }

    #[test]
    fn slice_full_at_bounds() {
        let slice =
            char_slice(TEST_STR, 0..).expect("failed to slice string at character bound 0..");
        assert_eq!(slice, TEST_STR);

        let char_len = TEST_STR.chars().count();
        let slice = char_slice(TEST_STR, 0..char_len)
            .unwrap_or_else(|| panic!("failed to slice string at character bound 0..{char_len}"));
        assert_eq!(slice, TEST_STR);

        #[allow(clippy::range_minus_one)]
        let slice = char_slice(TEST_STR, 0..=(char_len - 1))
            .unwrap_or_else(|| panic!("failed to slice string at character bound 0..{char_len}"));
        assert_eq!(slice, TEST_STR);

        let slice = char_slice(TEST_STR, ..char_len)
            .unwrap_or_else(|| panic!("failed to slice string at character bound ..{char_len}"));
        assert_eq!(slice, TEST_STR);

        #[allow(clippy::range_minus_one)]
        let slice = char_slice(TEST_STR, ..=(char_len - 1))
            .unwrap_or_else(|| panic!("failed to slice string at character bound ..{char_len}"));
        assert_eq!(slice, TEST_STR);
    }

    #[test]
    fn slice_empty_at_bounds_mut() {
        let mut s = test_str_owned();

        let slice =
            char_slice_mut(&mut s, ..0).expect("failed to slice string at character bound ..0");
        assert!(slice.is_empty());

        let slice =
            char_slice_mut(&mut s, 0..0).expect("failed to slice string at character bound 0..0");
        assert!(slice.is_empty());

        let char_len = s.chars().count();
        let slice = char_slice_mut(&mut s, char_len..char_len).unwrap_or_else(|| {
            panic!("failed to slice string at character bound {char_len}..{char_len}")
        });
        assert!(slice.is_empty());

        let slice = char_slice_mut(&mut s, char_len..)
            .unwrap_or_else(|| panic!("failed to slice string at character bound {char_len}.."));
        assert!(slice.is_empty());
    }

    #[test]
    fn slice_full_at_bounds_mut() {
        let mut s = test_str_owned();

        let slice =
            char_slice_mut(&mut s, 0..).expect("failed to slice string at character bound 0..");
        assert_eq!(slice, TEST_STR);

        let char_len = s.chars().count();
        let slice = char_slice_mut(&mut s, 0..char_len)
            .unwrap_or_else(|| panic!("failed to slice string at character bound 0..{char_len}"));
        assert_eq!(slice, TEST_STR);

        #[allow(clippy::range_minus_one)]
        let slice = char_slice_mut(&mut s, 0..=(char_len - 1))
            .unwrap_or_else(|| panic!("failed to slice string at character bound 0..{char_len}"));
        assert_eq!(slice, TEST_STR);

        let slice = char_slice_mut(&mut s, ..char_len)
            .unwrap_or_else(|| panic!("failed to slice string at character bound ..{char_len}"));
        assert_eq!(slice, TEST_STR);

        #[allow(clippy::range_minus_one)]
        let slice = char_slice_mut(&mut s, ..=(char_len - 1))
            .unwrap_or_else(|| panic!("failed to slice string at character bound ..{char_len}"));
        assert_eq!(slice, TEST_STR);
    }
}
