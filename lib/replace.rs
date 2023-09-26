use core::{slice, str};

use crate::errors::{
    LenNotEqual, ReplaceWithPadCharError, ReplaceWithPadError, ReplacementTooLong,
};

/// Replace the string slice with another of the same length.
///
/// ```
/// use mut_str::replace;
///
/// let mut owned_s = Box::<str>::from("World!");
///
/// replace(&mut *owned_s, "🌍!!").unwrap();
/// assert_eq!(&*owned_s, "🌍!!");
///
/// replace(&mut *owned_s, "aaaaaa").unwrap();
/// assert_eq!(&*owned_s, "aaaaaa");
/// ```
///
/// # Errors
/// - If `s` and `r`, when utf8 encoded, do not have the same length, [`LenNotEqual`] will be returned.
pub fn replace<'a>(s: &'a mut str, r: &str) -> Result<&'a mut str, LenNotEqual> {
    if r.len() != s.len() {
        return Err(LenNotEqual);
    }

    // SAFETY:
    // This is valid as it copies one valid string to another of the same
    // length.
    unsafe { s.as_bytes_mut() }.copy_from_slice(r.as_bytes());

    Ok(s)
}

/// Replace the string slice with another of the same length or shorter.
/// The remaining bytes will be filled with spaces.
///
/// ```
/// use mut_str::replace_with_pad_space;
///
/// let mut owned_s = Box::<str>::from("World!");
///
/// replace_with_pad_space(&mut *owned_s, "🌍").unwrap();
/// assert_eq!(&*owned_s, "🌍  ");
///
/// replace_with_pad_space(&mut *owned_s, "aaaa").unwrap();
/// assert_eq!(&*owned_s, "aaaa  ");
/// ```
///
/// # Errors
/// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplacementTooLong`] will be returned.
pub fn replace_with_pad_space<'a>(
    s: &'a mut str,
    r: &str,
) -> Result<&'a mut str, ReplacementTooLong> {
    if r.len() > s.len() {
        return Err(ReplacementTooLong);
    }

    // SAFETY:
    // This is valid as it copies one valid string to another of at least the
    // same length, replacing the remainder with one byte padding.
    let (slice, remaining) = unsafe { s.as_bytes_mut() }.split_at_mut(r.len());

    slice.copy_from_slice(r.as_bytes());
    remaining.fill(b' ');

    // SAFETY:
    // This is valid as`slice` comes from a `str` split on a char boundary.
    Ok(unsafe { str::from_utf8_unchecked_mut(slice) })
}

/// Replace the string slice with another of the same length or shorter.
/// The remaining bytes will be filled with `pad`.
///
/// ```
/// use mut_str::replace_with_pad;
///
/// let mut owned_s = Box::<str>::from("World!");
///
/// replace_with_pad(&mut *owned_s, "🌍", b'!').unwrap();
/// assert_eq!(&*owned_s, "🌍!!");
///
/// replace_with_pad(&mut *owned_s, "aaaa", b'b').unwrap();
/// assert_eq!(&*owned_s, "aaaabb");
/// ```
///
/// # Errors
/// - If `pad` is not valid utf8, [`ReplaceWithPadError::InvalidPad`] will be returned.
/// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadError::ReplacementLen`] will be returned.
pub fn replace_with_pad<'a>(
    s: &'a mut str,
    r: &str,
    pad: u8,
) -> Result<&'a mut str, ReplaceWithPadError> {
    if r.len() > s.len() {
        return Err(ReplaceWithPadError::CHAR_LEN);
    }

    str::from_utf8(&[pad])?;

    // SAFETY:
    // This is valid as it copies one valid string to another of at least the
    // same length, replacing the remainder with one byte padding.
    let (slice, remaining) = unsafe { s.as_bytes_mut() }.split_at_mut(r.len());

    slice.copy_from_slice(r.as_bytes());
    remaining.fill(pad);

    // SAFETY:
    // This is valid as`slice` comes from a `str` split on a char boundary.
    Ok(unsafe { str::from_utf8_unchecked_mut(slice) })
}

/// Replace the string slice with another of the same length or shorter.
/// The remaining bytes will be filled with `pad`, which must be one byte long.
///
/// ```
/// use mut_str::replace_with_pad_char;
///
/// let mut owned_s = Box::<str>::from("World!");
///
/// replace_with_pad_char(&mut *owned_s, "🌍", '!').unwrap();
/// assert_eq!(&*owned_s, "🌍!!");
///
/// replace_with_pad_char(&mut *owned_s, "aaaa", 'b').unwrap();
/// assert_eq!(&*owned_s, "aaaabb");
/// ```
///
/// # Errors
/// - If `pad_char`, when utf8 encoded, is longer than `Self`, [`ReplaceWithPadCharError::PadCharTooLong`] will be returned.
/// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadCharError::ReplacementLen`] will be returned.
pub fn replace_with_pad_char<'a, C>(
    s: &'a mut str,
    r: &str,
    pad_char: C,
) -> Result<&'a mut str, ReplaceWithPadCharError>
where
    C: Into<char>,
{
    let pad_char = pad_char.into();

    if r.len() > s.len() {
        return Err(ReplaceWithPadCharError::CHAR_LEN);
    }

    if pad_char.len_utf8() != 1 {
        return Err(ReplaceWithPadCharError::PadCharTooLong);
    }

    let mut pad: u8 = 0;
    pad_char.encode_utf8(slice::from_mut(&mut pad));

    // SAFETY:
    // This is valid as it copies one valid string to another of at least the
    // same length, replacing the remainder with one byte padding.
    let (slice, remaining) = unsafe { s.as_bytes_mut() }.split_at_mut(r.len());

    slice.copy_from_slice(r.as_bytes());
    remaining.fill(pad);

    // SAFETY:
    // This is valid as`slice` comes from a `str` split on a char boundary.
    Ok(unsafe { str::from_utf8_unchecked_mut(slice) })
}

/// Replace the string slice with another of the same length or shorter, right aligned.
/// The remaining bytes before the string slice will be filled with spaces.
///
/// ```
/// use mut_str::replace_with_pad_left_space;
///
/// let mut owned_s = Box::<str>::from("World!");
///
/// replace_with_pad_left_space(&mut *owned_s, "🌍").unwrap();
/// assert_eq!(&*owned_s, "  🌍");
///
/// replace_with_pad_left_space(&mut *owned_s, "aaaa").unwrap();
/// assert_eq!(&*owned_s, "  aaaa");
/// ```
///
/// # Errors
/// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplacementTooLong`] will be returned.
pub fn replace_with_pad_left_space<'a>(
    s: &'a mut str,
    r: &str,
) -> Result<&'a mut str, ReplacementTooLong> {
    if r.len() > s.len() {
        return Err(ReplacementTooLong);
    }

    let mid = s.len() - r.len();

    // SAFETY:
    // This is valid as it copies one valid string to another of at least the
    // same length, replacing the remainder with one byte padding.
    let (remaining, slice) = unsafe { s.as_bytes_mut() }.split_at_mut(mid);

    slice.copy_from_slice(r.as_bytes());
    remaining.fill(b' ');

    // SAFETY:
    // This is valid as`slice` comes from a `str` split on a char boundary.
    Ok(unsafe { str::from_utf8_unchecked_mut(slice) })
}

/// Replace the string slice with another of the same length or shorter, right aligned.
/// The remaining bytes before the character string slice will be filled with `pad`.
///
/// ```
/// use mut_str::replace_with_pad_left;
///
/// let mut owned_s = Box::<str>::from("World!");
///
/// replace_with_pad_left(&mut *owned_s, "🌍", b'!').unwrap();
/// assert_eq!(&*owned_s, "!!🌍");
///
/// replace_with_pad_left(&mut *owned_s, "aaaa", b'b').unwrap();
/// assert_eq!(&*owned_s, "bbaaaa");
/// ```
///
/// # Errors
/// - If `pad` is not valid utf8, [`ReplaceWithPadError::InvalidPad`] will be returned.
/// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadError::ReplacementLen`] will be returned.
pub fn replace_with_pad_left<'a>(
    s: &'a mut str,
    r: &str,
    pad: u8,
) -> Result<&'a mut str, ReplaceWithPadError> {
    if r.len() > s.len() {
        return Err(ReplaceWithPadError::CHAR_LEN);
    }

    str::from_utf8(&[pad])?;

    let mid = s.len() - r.len();

    // SAFETY:
    // This is valid as it copies one valid string to another of at least the
    // same length, replacing the remainder with one byte padding.
    let (remaining, slice) = unsafe { s.as_bytes_mut() }.split_at_mut(mid);

    slice.copy_from_slice(r.as_bytes());
    remaining.fill(pad);

    // SAFETY:
    // This is valid as`slice` comes from a `str` split on a char boundary.
    Ok(unsafe { str::from_utf8_unchecked_mut(slice) })
}

/// Replace the string slice with another of the same length or shorter, right aligned.
/// The remaining bytes before the string slice will be filled with `char`, which must be one byte long.
///
/// ```
/// use mut_str::replace_with_pad_left_char;
///
/// let mut owned_s = Box::<str>::from("World!");
///
/// replace_with_pad_left_char(&mut *owned_s, "🌍", '!').unwrap();
/// assert_eq!(&*owned_s, "!!🌍");
///
/// replace_with_pad_left_char(&mut *owned_s, "aaaa", 'b').unwrap();
/// assert_eq!(&*owned_s, "bbaaaa");
/// ```
///
/// # Errors
/// - If `pad_char`, when utf8 encoded, is longer than `Self`, [`ReplaceWithPadCharError::PadCharTooLong`] will be returned.
/// - If `r`, when utf8 encoded, is longer than `s`, when utf8 encoded, [`ReplaceWithPadCharError::ReplacementLen`] will be returned.
pub fn replace_with_pad_left_char<'a, C>(
    s: &'a mut str,
    r: &str,
    pad_char: C,
) -> Result<&'a mut str, ReplaceWithPadCharError>
where
    C: Into<char>,
{
    let pad_char = pad_char.into();
    if r.len() > s.len() {
        return Err(ReplaceWithPadCharError::CHAR_LEN);
    }

    if pad_char.len_utf8() != 1 {
        return Err(ReplaceWithPadCharError::PadCharTooLong);
    }

    let mut pad: u8 = 0;
    pad_char.encode_utf8(slice::from_mut(&mut pad));

    let mid = s.len() - r.len();

    // SAFETY:
    // This is valid as it copies one valid string to another of at least the
    // same length, replacing the remainder with one byte padding.
    let (remaining, slice) = unsafe { s.as_bytes_mut() }.split_at_mut(mid);

    slice.copy_from_slice(r.as_bytes());
    remaining.fill(pad);

    // SAFETY:
    // This is valid as`slice` comes from a `str` split on a char boundary.
    Ok(unsafe { str::from_utf8_unchecked_mut(slice) })
}
