use crate::Char;

#[must_use]
#[inline]
/// Get a character reference from a string slice and an index.
///
/// ```
/// use mut_str::get_char;
///
/// let s = "Hello, World!";
/// let c = get_char(s, 1).unwrap();
///
/// assert_eq!(c, &'e');
/// ```
pub fn get_char(s: &str, i: usize) -> Option<&Char> {
    Char::get(s, i)
}

#[must_use]
#[inline]
/// Get a mutable character reference from a mutable string slice and an index.
///
/// ```
/// use mut_str::get_char_mut;
///
/// let mut owned_s = Box::<str>::from("Hello, World!");
/// let c = get_char_mut(&mut *owned_s, 1).unwrap();
///
/// assert_eq!(c, &'e');
/// ```
pub fn get_char_mut(s: &mut str, i: usize) -> Option<&mut Char> {
    Char::get_mut(s, i)
}
