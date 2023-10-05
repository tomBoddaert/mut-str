use core::{fmt, str::Utf8Error};
#[cfg(feature = "std")]
use std::error::Error;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Length not equal error can occur if replacing a string or a character with one of a different length without padding.
pub struct LenNotEqual;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Replacement too long error can occur if replacing a string or a character with a longer one.
pub struct ReplacementTooLong;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Replace with pad error can occur when replacing a string or a character with a byte pad.
pub enum ReplaceWithPadError {
    /// The given pad is not valid UTF-8.
    InvalidPad(Utf8Error),
    /// The replacement is longer than the original.
    ReplacementLen(ReplacementTooLong),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Replace with pad [`prim@char`] error can occur when replacing a string or a character with a [`prim@char`] pad.
pub enum ReplaceWithPadCharError {
    /// The given pad is more than one byte long when UTF-8 encoded.
    PadCharTooLong,
    /// The replacement is longer than the original.
    ReplacementLen(ReplacementTooLong),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Try from [`prim@str`] error can occur when trying to convert a [`prim@str`] to a [`crate::Char`].
pub enum TryFromStrError {
    /// The [`prim@str`] contains no characters.
    Empty,
    /// The [`prim@str`] contains multiple characters.
    MultipleChars,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// Try from bytes error can occur when trying to convert a byte slice (`[u8]`) to a [`crate::Char`].
pub enum TryFromBytesError {
    /// The bytes are not valid UTF-8. See [`Utf8Error`].
    Utf8(Utf8Error),
    /// The bytes do not contain exactly one UTF-8 encoded character. See [`TryFromStrError`].
    Length(TryFromStrError),
}

impl ReplaceWithPadError {
    pub(crate) const CHAR_LEN: Self = Self::ReplacementLen(ReplacementTooLong);
}

impl From<Utf8Error> for ReplaceWithPadError {
    #[inline]
    fn from(value: Utf8Error) -> Self {
        Self::InvalidPad(value)
    }
}

impl ReplaceWithPadCharError {
    pub(crate) const CHAR_LEN: Self = Self::ReplacementLen(ReplacementTooLong);
}

impl From<Utf8Error> for TryFromBytesError {
    #[inline]
    fn from(value: Utf8Error) -> Self {
        Self::Utf8(value)
    }
}

impl From<TryFromStrError> for TryFromBytesError {
    #[inline]
    fn from(value: TryFromStrError) -> Self {
        Self::Length(value)
    }
}

impl fmt::Display for LenNotEqual {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "Replacement character is not the same length as the character!".fmt(f)
    }
}

impl fmt::Display for ReplacementTooLong {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        "Replacement character longer than the character!".fmt(f)
    }
}

impl fmt::Display for ReplaceWithPadError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidPad(_) => "Pad character is not valid UTF-8!".fmt(f),
            Self::ReplacementLen(error) => error.fmt(f),
        }
    }
}

impl fmt::Display for ReplaceWithPadCharError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PadCharTooLong => "Pad character must be one byte long!".fmt(f),
            Self::ReplacementLen(error) => error.fmt(f),
        }
    }
}

impl fmt::Display for TryFromStrError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => "String slice is empty!",
            Self::MultipleChars => "String slice contains multiple characters!",
        }
        .fmt(f)
    }
}

impl fmt::Display for TryFromBytesError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Utf8(error) => error.fmt(f),
            Self::Length(error) => error.fmt(f),
        }
    }
}

#[cfg(feature = "std")]
impl Error for LenNotEqual {}

#[cfg(feature = "std")]
impl Error for ReplacementTooLong {}

#[cfg(feature = "std")]
impl Error for ReplaceWithPadError {
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(match self {
            Self::InvalidPad(error) => error,
            Self::ReplacementLen(error) => error,
        })
    }
}

#[cfg(feature = "std")]
impl Error for ReplaceWithPadCharError {
    #[inline]
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::PadCharTooLong => None,
            Self::ReplacementLen(error) => Some(error),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryFromBytesError {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(match self {
            Self::Utf8(error) => error,
            Self::Length(error) => error,
        })
    }
}

#[cfg(feature = "std")]
impl std::error::Error for TryFromStrError {}
