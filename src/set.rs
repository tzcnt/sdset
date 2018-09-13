//! All the methods and types associated to [`Set`]s.

use std::cmp::Ordering;
use std::borrow::Borrow;
use std::ops::{Deref, RangeBounds, Bound};
use std::{error, fmt, mem};
use ::exponential_search;

/// Represent a slice which contains types that are sorted and deduplicated (akin to [`str`]).
///
/// This is an *unsized* type, meaning that it must always be used behind a
/// pointer like `&` or [`Box`]. For an owned version of this type,
/// see [`SetBuf`].
#[repr(C)] // TODO replace by repr(transparent)
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Set<T>([T]);

impl<T> Set<T> {
    /// Construct a [`Set`] only if it is sorted and deduplicated.
    ///
    /// ```
    /// use sdset::{Set, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let slice = &[1, 2, 4, 6, 7];
    /// let set = Set::new(slice)?;
    ///
    /// // this slice is not sorted!
    /// let slice = &[1, 2, 4, 7, 6];
    /// let set = Set::new(slice);
    ///
    /// assert_eq!(set, Err(Error::NotSort));
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn new(slice: &[T]) -> Result<&Self, Error>
    where T: Ord
    {
        is_sort_dedup(slice).map(|_| Self::new_unchecked(slice))
    }

    /// Construct a [`Set`] without checking it.
    ///
    /// ```
    /// use sdset::{Set, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// // this slice is not sorted
    /// let slice = &[1, 2, 4, 7, 6];
    ///
    /// // but we can still create a Set, so be careful!
    /// let set = Set::new_unchecked(slice);
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn new_unchecked(slice: &[T]) -> &Self {
        unsafe { mem::transmute(slice) }
    }

    /// Returns a [`Set`] containing all the values in the given range.
    ///
    /// This function uses exponential searching internally
    /// because it is verified that the elements are ordered.
    ///
    /// ```
    /// use std::ops::Bound::{Excluded, Included};
    /// use sdset::{Set, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let set = Set::new(&[1, 2, 4, 6, 7])?;
    ///
    /// let subset = set.range(2..=6);
    /// assert_eq!(subset.as_slice(), &[2, 4, 6]);
    ///
    /// let subset = set.range(3..5);
    /// assert_eq!(subset.as_slice(), &[4]);
    ///
    /// let subset = set.range((Excluded(&2), Included(&7)));
    /// assert_eq!(subset.as_slice(), &[4, 6, 7]);
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn range<K, R>(&self, range: R) -> &Self
    where K: Ord + ?Sized,
          R: RangeBounds<K>,
          T: Borrow<K>,
    {
        let left = match range.start_bound() {
            Bound::Included(x) => match exponential_search(self, x) {
                Ok(index) => index,
                Err(index) => index,
            },
            Bound::Excluded(x) => match exponential_search(self, x) {
                Ok(index) => index + 1,
                Err(index) => index,
            },
            Bound::Unbounded => 0,
        };

        let right = match range.end_bound() {
            Bound::Included(x) => match exponential_search(self, x) {
                Ok(index) => index + 1,
                Err(index) => index,
            },
            Bound::Excluded(x) => match exponential_search(self, x) {
                Ok(index) => index,
                Err(index) => index,
            },
            Bound::Unbounded => self.len(),
        };

        Self::new_unchecked(&self[left..right])
    }

    /// Returns `true` if the set contains an element with the given value.
    ///
    /// This function uses exponential searching internally
    /// because it is verified that the elements are ordered.
    ///
    /// ```
    /// use sdset::{Set, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let slice = &[1, 2, 4, 6, 7];
    /// let set = Set::new(slice)?;
    ///
    /// assert!(set.contains(&4));
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn contains(&self, x: &T) -> bool
    where T: Ord
    {
        exponential_search(self.as_slice(), x).is_ok()
    }

    /// Construct the owning version of the [`Set`].
    ///
    /// ```
    /// use sdset::{Set, SetBuf, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let set = Set::new(&[1, 2, 4, 6, 7])?;
    /// let setbuf: SetBuf<_> = set.to_set_buf();
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn to_set_buf(&self) -> SetBuf<T>
    where T: Clone
    {
        SetBuf(self.0.to_vec())
    }

    /// Return the slice "inside" of this [`Set`].
    ///
    /// ```
    /// use sdset::{Set, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let slice = &[1, 2, 4, 6, 7];
    /// let set = Set::new(slice)?;
    ///
    /// assert_eq!(set.as_slice(), slice);
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn as_slice(&self) -> &[T] {
        &self.0
    }
}

impl<T> Deref for Set<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T> AsRef<[T]> for Set<T> {
    fn as_ref(&self) -> &[T] {
        &self.0
    }
}

impl<T> AsRef<Set<T>> for Set<T> {
    fn as_ref(&self) -> &Set<T> {
        self
    }
}

/// An owned, set (akin to [`String`]).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SetBuf<T>(Vec<T>);

impl<T> SetBuf<T> {
    /// Construct a [`SetBuf`] only if it is sorted and deduplicated.
    ///
    /// ```
    /// use sdset::{SetBuf, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let vec = vec![1, 2, 4, 6, 7];
    /// let setbuf = SetBuf::new(vec)?;
    ///
    /// // this vec is not sorted!
    /// let vec = vec![1, 2, 4, 7, 6];
    /// let setbuf = SetBuf::new(vec);
    ///
    /// assert_eq!(setbuf, Err(Error::NotSort));
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn new(vec: Vec<T>) -> Result<Self, Error>
    where T: Ord
    {
        is_sort_dedup(&vec).map(|_| SetBuf::new_unchecked(vec))
    }

    /// Construct a [`SetBuf`] without checking it.
    ///
    /// ```
    /// use sdset::{SetBuf, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// // this vec is not sorted
    /// let vec = vec![1, 2, 4, 7, 6];
    ///
    /// // but we can still create a SetBuf, so be careful!
    /// let setbuf = SetBuf::new_unchecked(vec);
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn new_unchecked(vec: Vec<T>) -> Self {
        SetBuf(vec)
    }

    /// Return the [`Set`] owned by this [`SetBuf`].
    ///
    /// ```
    /// use sdset::{Set, SetBuf, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let vec = vec![1, 2, 4, 6, 7];
    /// let setbuf = SetBuf::new(vec.clone())?;
    ///
    /// let set = Set::new(&vec)?;
    /// assert_eq!(setbuf.as_set(), set);
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn as_set(&self) -> &Set<T> {
        Set::new_unchecked(self.0.as_slice())
    }

    /// Return the [`Vec`] inside by this [`SetBuf`].
    ///
    /// ```
    /// use sdset::{SetBuf, Error};
    /// # fn try_main() -> Result<(), Error> {
    ///
    /// let vec = vec![1, 2, 4, 6, 7];
    /// let setbuf = SetBuf::new(vec)?;
    ///
    /// let vec = setbuf.into_vec();
    /// # Ok(()) }
    /// # try_main().unwrap();
    /// ```
    pub fn into_vec(self) -> Vec<T> {
        self.0
    }
}

impl<T> Deref for SetBuf<T> {
    type Target = Set<T>;

    fn deref(&self) -> &Self::Target {
        self.as_set()
    }
}

impl<T> AsRef<Set<T>> for SetBuf<T> {
    fn as_ref(&self) -> &Set<T> {
        self.as_set()
    }
}

impl<T> AsRef<[T]> for SetBuf<T> {
    fn as_ref(&self) -> &[T] {
        self.0.as_slice()
    }
}

/// Represent the possible errors when creating a [`Set`].
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Error {
    /// Define that a slice is not sorted.
    NotSort,
    /// Define that a slice is not deduplicated.
    NotDedup,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        let desc = match self {
            Error::NotSort => "the given slice is not sorted.",
            Error::NotDedup => "the given slice is not deduplicated.",
        };
        f.write_str(desc)
    }
}

impl error::Error for Error {}

/// The list of all [`Error`]s that can occur
/// while trying to convert a [`slice`](std::slice) to a [`Set`].
pub type Errors = Vec<Option<Error>>;

/// Construct a [`Vec`] of [`Set`]s only if all slices are sorted and deduplicated.
///
/// Otherwise returns the [`Vec`] given in parameter along with a [`Vec`] containing
/// the possible conversion errors of each slice.
///
/// # Examples
/// ```
/// use sdset::set::vec_slices_into_sets;
///
/// let a = &[1, 2, 3, 4][..];
/// let b = &[1, 4, 6, 7];
/// let slices = vec![a, b];
///
/// let sets = vec_slices_into_sets(slices).unwrap();
/// ```
pub fn vec_slices_into_sets<T: Ord>(vec: Vec<&[T]>) -> Result<Vec<&Set<T>>, (Vec<&[T]>, Errors)> {
    let mut has_error = false;
    let mut errors = Errors::with_capacity(vec.len());
    for slice in &vec {
        let res = is_sort_dedup(slice).err();
        has_error = res.is_some();
        errors.push(res);
    }

    if has_error {
        return Err((vec, errors))
    }

    Ok(vec_slices_into_sets_unchecked(vec))
}

/// Transmutes slices without checking them.
///
/// This is useful when you don't want to introduce another allocation to
/// your program and you are sure all these slices are valid [`Set`]s.
///
/// # Examples
/// ```
/// use sdset::set::vec_slices_into_sets_unchecked;
///
/// // these slices are not sorted!
/// let a = &[1, 6, 4][..];
/// let b = &[1, 6, 1];
/// let slices = vec![a, b];
///
/// // but we can still create a Vec of Sets, so be careful!
/// let sets = vec_slices_into_sets_unchecked(slices);
/// ```
pub fn vec_slices_into_sets_unchecked<T>(vec: Vec<&[T]>) -> Vec<&Set<T>> {
    unsafe { mem::transmute(vec) }
}

/// Safely transmute a [`Vec`] of [`Set`]s into a [`Vec`] of [`slice`](std::slice).
///
/// This is useful when you don't want to introduce another allocation to your program.
///
/// Note that the values that are parts of the returned
/// slices will be ordered and deduplicated.
pub fn vec_sets_into_slices<T>(vec: Vec<&Set<T>>) -> Vec<&[T]> {
    unsafe { mem::transmute(vec) }
}

/// Safely transmute a [`slice`](std::slice) of [`Set`]s into
/// a [`slice`](std::slice) of [`slice`](std::slice).
///
/// This is useful when you don't want to introduce another allocation to your program.
///
/// Note that the values that are parts of the returned
/// slices will be ordered and deduplicated.
pub fn slice_sets_into_slices<'a, T: 'a>(slice: &'a [&'a Set<T>]) -> &'a [&'a [T]] {
    unsafe { mem::transmute(slice) }
}

/// Sort and dedup the vec given in parameter.
pub fn sort_dedup_vec<T: Ord>(vec: &mut Vec<T>) {
    vec.sort_unstable();
    vec.dedup();
}

/// Returns an error if the slice is not sorted nor deduplicated, returns `()` if it is.
pub fn is_sort_dedup<T: Ord>(slice: &[T]) -> Result<(), Error> {
    for pair in slice.windows(2) {
        match pair[0].cmp(&pair[1]) {
            Ordering::Less => (),
            Ordering::Equal => return Err(Error::NotDedup),
            Ordering::Greater => return Err(Error::NotSort),
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::Bound::*;

    #[test]
    fn range_set() {
        let set = Set::new(&[1, 2, 4, 6, 7]).unwrap();

        let subset = set.range((Excluded(1), Unbounded));
        assert_eq!(subset.as_slice(), &[2, 4, 6, 7]);

        let subset = set.range((Excluded(1), Included(4)));
        assert_eq!(subset.as_slice(), &[2, 4]);

        let subset = set.range((Excluded(0), Included(4)));
        assert_eq!(subset.as_slice(), &[1, 2, 4]);

        let subset = set.range((Unbounded, Excluded(10)));
        assert_eq!(subset.as_slice(), &[1, 2, 4, 6, 7]);
    }
}
