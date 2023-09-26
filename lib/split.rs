use core::{slice, str};

#[must_use]
/// Split a [`prim@str`] in units of UTF-8 characters.
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
    let mut iter = s.char_indices();
    let mut last_char = (0, '\x00');

    for _ in 0..mid {
        last_char = iter.next()?;
    }

    let mid_index = last_char.0 + last_char.1.len_utf8();

    // SAFETY:
    // `mid` is guaranteed to be on a char boundary and a maximum of one byte
    // over the end of the slice.
    Some(unsafe { (s.get_unchecked(..mid_index), s.get_unchecked(mid_index..)) })
}

#[must_use]
/// Split a mutable [`prim@str`] in units of UTF-8 characters.
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
    let mut iter = s.char_indices();
    let mut last_char = (0, '\x00');

    for _ in 0..mid {
        last_char = iter.next()?;
    }

    let mid_index = last_char.0 + last_char.1.len_utf8();

    // SAFETY:
    // `mid` is guaranteed to be on a char boundary and a maximum of one byte
    // over the end of the slice.
    Some(unsafe {
        (
            str::from_utf8_unchecked_mut(slice::from_raw_parts_mut(s.as_mut_ptr(), mid_index)),
            s.get_unchecked_mut(mid_index..),
        )
    })
}
