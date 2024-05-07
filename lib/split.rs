use core::{slice, str};

#[must_use]
/// Split a [`prim@str`] in units of UTF-8 characters.
///
/// The first string will contain `mid` characters.
/// Returns [`None`] if `mid` is out of bounds.
///
/// ```
/// use mut_str::char_split_at;
///
/// let s = "Hello, World!";
///
/// let (l, r) = char_split_at(s, 6).unwrap();
/// assert_eq!(l, "Hello,");
/// assert_eq!(r, " World!");
/// ```
pub fn char_split_at(s: &str, mid: usize) -> Option<(&str, &str)> {
    let mid_index = if let Some(last) = mid.checked_sub(1) {
        let (i, c) = s.char_indices().nth(last)?;
        i + c.len_utf8()
    } else {
        0
    };

    let second_len = s.len() - mid_index;
    let first = s.as_ptr();
    // SAFETY:
    // `mid_index` is an offset from `CharIndices`, so `first + mid_index` is within the bounds of `s`.
    let second = unsafe { first.add(mid_index) };

    Some((
        // SAFETY:
        // `first` is the pointer to the start of the string. As `mid_index - 1` is a valid index,
        // `mid_index <= string length`.
        unsafe { str::from_utf8_unchecked(slice::from_raw_parts(first, mid_index)) },
        // SAFETY:
        // `second` is `ptr + index` and `second_len` is `length - index`, where `index <= length`.
        unsafe { str::from_utf8_unchecked(slice::from_raw_parts(second, second_len)) },
    ))
}

#[must_use]
/// Split a mutable [`prim@str`] in units of UTF-8 characters.
///
/// The first string will contain `mid` characters.
/// Returns [`None`] if `mid` is out of bounds.
///
/// ```
/// use mut_str::char_split_at_mut;
///
/// let mut owned_s = Box::<str>::from("Hello, World!");
///
/// let (l, r) = char_split_at_mut(&mut *owned_s, 6).unwrap();
/// assert_eq!(l, "Hello,");
/// assert_eq!(r, " World!");
/// ```
pub fn char_split_at_mut(s: &mut str, mid: usize) -> Option<(&mut str, &mut str)> {
    let mid_index = if let Some(last) = mid.checked_sub(1) {
        let (i, c) = s.char_indices().nth(last)?;
        i + c.len_utf8()
    } else {
        0
    };

    let second_len = s.len() - mid_index;
    let first = s.as_mut_ptr();
    // SAFETY:
    // `mid_index` is an offset from `CharIndices`, so `first + mid_index` is within the bounds of `s`.
    let second = unsafe { first.add(mid_index) };

    Some((
        // SAFETY:
        // `first` is the pointer to the start of the string. As `mid_index - 1` is a valid index,
        // `mid_index <= string length`.
        unsafe { str::from_utf8_unchecked_mut(slice::from_raw_parts_mut(first, mid_index)) },
        // SAFETY:
        // `second` is `ptr + index` and `second_len` is `length - index`, where `index <= length`.
        unsafe { str::from_utf8_unchecked_mut(slice::from_raw_parts_mut(second, second_len)) },
    ))
}

#[must_use]
/// Split a [`prim@str`] in units of UTF-8 characters from the end.
///
/// The second string will contain `mid` characters.
/// Returns [`None`] if `mid` is out of bounds.
///
/// ```
/// use mut_str::char_rsplit_at;
///
/// let s = "Hello, World!";
///
/// let (l, r) = char_rsplit_at(s, 6).unwrap();
/// assert_eq!(l, "Hello, ");
/// assert_eq!(r, "World!");
/// ```
pub fn char_rsplit_at(s: &str, mid: usize) -> Option<(&str, &str)> {
    let mid_index = if let Some(first) = mid.checked_sub(1) {
        let (i, _) = s.char_indices().nth_back(first)?;
        i
    } else {
        s.len()
    };

    let second_len = s.len() - mid_index;
    let first = s.as_ptr();
    // SAFETY:
    // `mid_index` is an offset from `CharIndices`, so `first + mid_index` is within the bounds of `s`.
    let second = unsafe { first.add(mid_index) };

    Some((
        // SAFETY:
        // `first` is the pointer to the start of the string. As `mid_index - 1` is a valid index,
        // `mid_index <= string length`.
        unsafe { str::from_utf8_unchecked(slice::from_raw_parts(first, mid_index)) },
        // SAFETY:
        // `second` is `ptr + index` and `second_len` is `length - index`, where `index <= length`.
        unsafe { str::from_utf8_unchecked(slice::from_raw_parts(second, second_len)) },
    ))
}

#[must_use]
/// Split a mutable [`prim@str`] in units of UTF-8 characters from the end.
///
/// The second string will contain `mid` characters.
/// Returns [`None`] if `mid` is out of bounds.
///
/// ```
/// use mut_str::char_rsplit_at_mut;
///
/// let mut owned_s = Box::<str>::from("Hello, World!");
///
/// let (l, r) = char_rsplit_at_mut(&mut *owned_s, 6).unwrap();
/// assert_eq!(l, "Hello, ");
/// assert_eq!(r, "World!");
/// ```
pub fn char_rsplit_at_mut(s: &mut str, mid: usize) -> Option<(&mut str, &mut str)> {
    let mid_index = if let Some(last) = mid.checked_sub(1) {
        let (i, _) = s.char_indices().nth_back(last)?;
        i
    } else {
        s.len()
    };

    let second_len = s.len() - mid_index;
    let first = s.as_mut_ptr();
    // SAFETY:
    // `mid_index` is an offset from `CharIndices`, so `first + mid_index` is within the bounds of `s`.
    let second = unsafe { first.add(mid_index) };

    Some((
        // SAFETY:
        // `first` is the pointer to the start of the string. As `mid_index - 1` is a valid index,
        // `mid_index <= string length`.
        unsafe { str::from_utf8_unchecked_mut(slice::from_raw_parts_mut(first, mid_index)) },
        // SAFETY:
        // `second` is `ptr + index` and `second_len` is `length - index`, where `index <= length`.
        unsafe { str::from_utf8_unchecked_mut(slice::from_raw_parts_mut(second, second_len)) },
    ))
}

#[cfg(test)]
mod test {
    use crate::{
        char_rsplit_at, char_rsplit_at_mut, char_split_at, char_split_at_mut,
        test::{test_str_owned, TEST_STR},
    };

    #[test]
    fn split_at_bounds() {
        let (left, right) =
            char_split_at(TEST_STR, 0).expect("failed to split a string at character 0");
        assert!(left.is_empty());
        assert_eq!(right, TEST_STR);

        let char_len = TEST_STR.chars().count();
        let (left, right) = char_split_at(TEST_STR, char_len)
            .expect("failed to split a string at the last character");
        assert_eq!(left, TEST_STR);
        assert!(right.is_empty());
    }

    #[test]
    fn split_at_bounds_mut() {
        let mut s = test_str_owned();

        let (head, tail) =
            char_split_at_mut(&mut s, 0).expect("failed to split a string at character 0");
        assert!(head.is_empty());
        assert_eq!(tail, TEST_STR);

        let char_len = TEST_STR.chars().count();
        let (head, tail) = char_split_at_mut(&mut s, char_len)
            .expect("failed to split a string at the last character");
        assert_eq!(head, TEST_STR);
        assert!(tail.is_empty());
    }

    #[test]
    fn rsplit_at_bounds() {
        let (left, right) =
            char_rsplit_at(TEST_STR, 0).expect("failed to rsplit a string at character 0");
        assert_eq!(left, TEST_STR);
        assert!(right.is_empty());

        let char_len = TEST_STR.chars().count();
        let (left, right) = char_rsplit_at(TEST_STR, char_len)
            .expect("failed to rsplit a string at the last character");
        assert!(left.is_empty());
        assert_eq!(right, TEST_STR);
    }

    #[test]
    fn rsplit_at_bounds_mut() {
        let mut s = test_str_owned();

        let (left, right) =
            char_rsplit_at_mut(&mut s, 0).expect("failed to rsplit a string at character 0");
        assert_eq!(left, TEST_STR);
        assert!(right.is_empty());

        let char_len = TEST_STR.chars().count();
        let (left, right) = char_rsplit_at_mut(&mut s, char_len)
            .expect("failed to rsplit a string at the last character");
        assert!(left.is_empty());
        assert_eq!(right, TEST_STR);
    }
}
