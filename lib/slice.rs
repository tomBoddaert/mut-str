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
        Bound::Included(i) => *i,
        Bound::Excluded(i) => i.checked_add(1)?,
        Bound::Unbounded => 0,
    };

    // This will not exclude all out of bounds ranges but is a quick
    // check that will eliminate extreme bounds.
    if start_inclusive >= s.len() {
        return None;
    }

    let mut iter = s.char_indices();

    // Get the first char in the slice and its position.
    let start_char = iter.nth(start_inclusive)?;
    let start_index = start_char.0;

    Some(
        if let Some(end_inclusive) = match range.end_bound() {
            Bound::Included(i) => Some(*i),
            Bound::Excluded(i) => {
                if let Some(index) = i.checked_sub(1) {
                    Some(index)
                } else {
                    return (start_inclusive == 0).then(||
                        // SAFETY:
                        // 0 is guaranteed to be a char boundary and cannot exceed
                        // the length.
                        unsafe { s.get_unchecked(0..0) });
                }
            }
            Bound::Unbounded => None,
        } {
            // This will not exclude all out of bounds ranges but is a quick
            // check that will eliminate extreme bounds.
            if end_inclusive >= s.len() {
                return None;
            }

            // Get the number of characters the last character is after the
            // first character.
            let offset = end_inclusive.checked_sub(start_inclusive)?;

            // Get the last character and its position.
            let end_char = if let Some(n) = offset.checked_sub(1) {
                iter.nth(n)?
            } else {
                start_char
            };
            let end_index = end_char.0 + end_char.1.len_utf8();

            // SAFETY:
            // `start_index` is from a `CharIndices` iterator, so its position
            // is valid. `end_index` is from `CharIndices` + the char length, so
            // `end_index` is a byte after a char boundary.
            unsafe { s.get_unchecked(start_index..end_index) }
        } else {
            // SAFETY:
            // `start_index` is from a `CharIndices` iterator, so its position
            // is valid.
            unsafe { s.get_unchecked(start_index..) }
        },
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
        Bound::Included(i) => *i,
        Bound::Excluded(i) => i.checked_add(1)?,
        Bound::Unbounded => 0,
    };

    // This will not exclude all out of bounds ranges but is a quick
    // check that will eliminate extreme bounds.
    if start_inclusive >= s.len() {
        return None;
    }

    let mut iter = s.char_indices();

    // Get the first char in the slice and its position.
    let start_char = iter.nth(start_inclusive)?;
    let start_index = start_char.0;

    Some(
        if let Some(end_inclusive) = match range.end_bound() {
            Bound::Included(i) => Some(*i),
            Bound::Excluded(i) => {
                if let Some(index) = i.checked_sub(1) {
                    Some(index)
                } else {
                    return (start_inclusive == 0).then(||
                        // SAFETY:
                        // 0 is guaranteed to be a char boundary and cannot exceed
                        // the length.
                        unsafe { s.get_unchecked_mut(0..0) });
                }
            }
            Bound::Unbounded => None,
        } {
            // This will not exclude all out of bounds ranges but is a quick
            // check that will eliminate extreme bounds.
            if end_inclusive >= s.len() {
                return None;
            }

            // Get the number of characters the last character is after the
            // first character.
            let offset = end_inclusive.checked_sub(start_inclusive)?;

            // Get the last character and its position.
            let end_char = if let Some(n) = offset.checked_sub(1) {
                iter.nth(n)?
            } else {
                start_char
            };
            let end_index = end_char.0 + end_char.1.len_utf8();

            // SAFETY:
            // `start_index` is from a `CharIndices` iterator, so its position
            // is valid. `end_index` is from `CharIndices` + the char length, so
            // `end_index` is a byte after a char boundary.
            unsafe { s.get_unchecked_mut(start_index..end_index) }
        } else {
            // SAFETY:
            // `start_index` is from a `CharIndices` iterator, so its position
            // is valid.
            unsafe { s.get_unchecked_mut(start_index..) }
        },
    )
}
