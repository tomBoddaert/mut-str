mod cmrs;
mod crs;

pub use cmrs::*;
pub use crs::*;

use crate::{Char, OwnedChar};

#[cfg(feature = "std")]
impl<'a> Extend<&'a Char> for String {
    fn extend<T: IntoIterator<Item = &'a Char>>(&mut self, iter: T) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push_str(c.as_str()));
    }
}

#[cfg(feature = "std")]
impl<'a> Extend<&'a mut Char> for String {
    #[inline]
    fn extend<T: IntoIterator<Item = &'a mut Char>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(|x| &*x));
    }
}

#[cfg(feature = "std")]
impl Extend<OwnedChar> for String {
    fn extend<T: IntoIterator<Item = OwnedChar>>(&mut self, iter: T) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push_str(c.as_str()));
    }
}

#[cfg(feature = "std")]
impl<'a> Extend<&'a OwnedChar> for String {
    #[inline]
    fn extend<T: IntoIterator<Item = &'a OwnedChar>>(&mut self, iter: T) {
        self.extend(iter.into_iter().map(AsRef::as_ref));
    }
}

#[cfg(feature = "std")]
impl<'a> Extend<&'a mut OwnedChar> for String {
    #[inline]
    fn extend<T: IntoIterator<Item = &'a mut OwnedChar>>(&mut self, iter: T) {
        let iterator = iter.into_iter();
        let (lower_bound, _) = iterator.size_hint();
        self.reserve(lower_bound);
        iterator.for_each(move |c| self.push_str(c.as_str()));
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a Char> for String {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a Char>>(iter: T) -> Self {
        let mut s = Self::new();
        s.extend(iter);
        s
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a mut Char> for String {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a mut Char>>(iter: T) -> Self {
        let mut s = Self::new();
        s.extend(iter);
        s
    }
}

#[cfg(feature = "std")]
impl FromIterator<OwnedChar> for String {
    #[inline]
    fn from_iter<T: IntoIterator<Item = OwnedChar>>(iter: T) -> Self {
        let mut s = Self::new();
        s.extend(iter);
        s
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a OwnedChar> for String {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a OwnedChar>>(iter: T) -> Self {
        let mut s = Self::new();
        s.extend(iter);
        s
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a mut OwnedChar> for String {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a mut OwnedChar>>(iter: T) -> Self {
        let mut s = Self::new();
        s.extend(iter);
        s
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a Char> for Box<str> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a Char>>(iter: T) -> Self {
        String::from_iter(iter).into_boxed_str()
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a mut Char> for Box<str> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a mut Char>>(iter: T) -> Self {
        String::from_iter(iter).into_boxed_str()
    }
}

#[cfg(feature = "std")]
impl FromIterator<OwnedChar> for Box<str> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = OwnedChar>>(iter: T) -> Self {
        String::from_iter(iter).into_boxed_str()
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a OwnedChar> for Box<str> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a OwnedChar>>(iter: T) -> Self {
        String::from_iter(iter).into_boxed_str()
    }
}

#[cfg(feature = "std")]
impl<'a> FromIterator<&'a mut OwnedChar> for Box<str> {
    #[inline]
    fn from_iter<T: IntoIterator<Item = &'a mut OwnedChar>>(iter: T) -> Self {
        String::from_iter(iter).into_boxed_str()
    }
}
