use core::{
    borrow::{Borrow, BorrowMut},
    fmt,
    ops::{Deref, DerefMut},
};

use crate::{
    errors::{TryFromBytesError, TryFromStrError},
    Char,
};

#[derive(Clone)]
#[repr(transparent)]
/// An owned [`Char`].
///
/// Use [`Char::to_owned()`] to obtain this.
///
/// ```
/// use mut_str::get_char;
///
/// let s = "Hello, World!";
/// let c = get_char(s, 1).unwrap();
/// let owned_c = c.to_owned();
///
/// assert_eq!(owned_c, 'e');
/// ```
pub struct OwnedChar {
    b: [u8; 4],
}

impl OwnedChar {
    #[must_use]
    #[inline]
    /// Create a new [`OwnedChar`] without checking the validity of the buffer.
    ///
    /// For a safe version, see [`OwnedChar::try_from()`].
    ///
    /// # Safety
    /// There must be one valid UTF-8 encoded character at the start of the `b`.
    pub const unsafe fn new_unchecked(b: [u8; 4]) -> Self {
        Self { b }
    }

    #[must_use]
    #[inline]
    /// Create a new [`OwnedChar`] without checking the validity of the bytes.
    ///
    /// For a safe version, see [`OwnedChar::try_from()`].
    ///
    /// # Safety
    /// There must be one valid UTF-8 encoded character at the start of `bytes`, which must be no longer than 4 bytes long.
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> Self {
        let mut c = [0; 4];
        c[..bytes.len()].copy_from_slice(bytes);

        Self { b: c }
    }

    #[must_use]
    #[inline]
    /// Get the underlying buffer as a mutable array.
    ///
    /// # Safety
    /// The caller must ensure that when the mutable reference returned is dropped, there is a valid UTF-8 encoded character ath the start of the buffer.
    pub unsafe fn buffer_mut(&mut self) -> &mut [u8; 4] {
        &mut self.b
    }
}

impl AsRef<Char> for OwnedChar {
    #[inline]
    fn as_ref(&self) -> &Char {
        // SAFETY:
        // `self` is transparent bytes and contains a utf8 encoded character at
        // the start, so this cast is valid, as the pointer will be to the
        // start of a utf8 character.
        unsafe { &*(self as *const Self).cast() }
    }
}

impl AsMut<Char> for OwnedChar {
    #[inline]
    fn as_mut(&mut self) -> &mut Char {
        // SAFETY:
        // `self` is transparent bytes and contains a utf8 encoded character at
        // the start, so this cast is valid, as the pointer will be to the
        // start of a utf8 character.
        unsafe { &mut *(self as *mut Self).cast() }
    }
}

impl Borrow<Char> for OwnedChar {
    #[inline]
    fn borrow(&self) -> &Char {
        self.as_ref()
    }
}

impl BorrowMut<Char> for OwnedChar {
    #[inline]
    fn borrow_mut(&mut self) -> &mut Char {
        self.as_mut()
    }
}

impl Deref for OwnedChar {
    type Target = Char;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_ref()
    }
}

impl DerefMut for OwnedChar {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.as_mut()
    }
}

impl fmt::Debug for OwnedChar {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl fmt::Display for OwnedChar {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.as_ref().fmt(f)
    }
}

impl From<char> for OwnedChar {
    #[inline]
    fn from(value: char) -> Self {
        let mut c = [0; 4];
        value.encode_utf8(&mut c);
        Self { b: c }
    }
}

impl From<&Char> for OwnedChar {
    #[inline]
    fn from(value: &Char) -> Self {
        value.to_owned()
    }
}

impl TryFrom<&str> for OwnedChar {
    type Error = TryFromStrError;

    #[inline]
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        <&Char>::try_from(value)?;

        let mut c = [0; 4];
        c[..value.len()].copy_from_slice(value.as_bytes());

        Ok(Self { b: c })
    }
}

impl TryFrom<&[u8]> for OwnedChar {
    type Error = TryFromBytesError;

    #[inline]
    fn try_from(value: &[u8]) -> Result<Self, Self::Error> {
        <&Char>::try_from(value)?;

        let mut c = [0; 4];
        c[..value.len()].copy_from_slice(value);

        Ok(Self { b: c })
    }
}

impl TryFrom<[u8; 4]> for OwnedChar {
    type Error = TryFromBytesError;

    #[inline]
    fn try_from(value: [u8; 4]) -> Result<Self, Self::Error> {
        <&Char>::try_from(&value[..]).map(|_| Self { b: value })
    }
}

impl<T> PartialEq<T> for OwnedChar
where
    Char: PartialEq<T>,
{
    #[inline]
    fn eq(&self, other: &T) -> bool {
        self.as_ref().eq(other)
    }
}

impl Eq for OwnedChar {}

impl<T> PartialOrd<T> for OwnedChar
where
    Char: PartialOrd<T>,
{
    #[inline]
    fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
        self.as_ref().partial_cmp(other)
    }
}

impl Ord for OwnedChar {
    #[inline]
    fn cmp(&self, other: &Self) -> core::cmp::Ordering {
        self.as_ref().cmp(other)
    }
}
