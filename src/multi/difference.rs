use std::{cmp, mem};
use sort_dedup::SortDedup;
use ::offset_ge;

/// Represent the _difference_ set operation that will be applied to the slices.
///
/// Note that the difference is all the elements
/// that are in the first slice but not in all the others.
///
/// # Examples
/// ```
/// # use sdset::Error;
/// # fn try_main() -> Result<(), Error> {
/// use sdset::multi::OpBuilder;
/// use sdset::SortDedup;
///
/// let a = SortDedup::new(&[1, 2, 4])?;
/// let b = SortDedup::new(&[2, 3, 5, 7])?;
/// let c = SortDedup::new(&[4, 6, 7])?;
///
/// let op = OpBuilder::from_vec(vec![a, b, c]).difference();
///
/// let res = op.into_vec();
/// assert_eq!(&res, &[1]);
/// # Ok(()) }
/// # try_main().unwrap();
/// ```
#[derive(Clone)]
pub struct Difference<'a, T: 'a> {
    slices: Vec<&'a [T]>,
}

impl<'a, T> Difference<'a, T> {
    /// Construct one with slices checked to be sorted and deduplicated.
    pub fn new(slices: Vec<SortDedup<'a, T>>) -> Self {
        Self::new_unchecked(unsafe { mem::transmute(slices) })
    }

    /// Construct one with unchecked slices.
    pub fn new_unchecked(slices: Vec<&'a [T]>) -> Self {
        Self { slices }
    }
}

impl<'a, T: Ord + Clone> Difference<'a, T> {
    /// Extend a [`Vec`] with the cloned values of the slices using the set operation.
    pub fn extend_vec(mut self, output: &mut Vec<T>) {
        let (base, others) = match self.slices.split_first_mut() {
            Some(split) => split,
            None => return,
        };

        while let Some(first) = base.first() {

            let mut minimum = None;
            for slice in others.iter_mut() {
                *slice = offset_ge(slice, first);
                minimum = match (minimum, slice.first()) {
                    (Some(min), Some(first)) => Some(cmp::min(min, first)),
                    (None, Some(first)) => Some(first),
                    (min, _) => min,
                };
            }

            match minimum {
                Some(min) if min == first => *base = offset_ge(&base[1..], min),
                Some(min) => {
                    let off = base.iter().take_while(|&x| x < min).count();
                    output.extend_from_slice(&base[..off]);

                    *base = &base[off..];
                },
                None => {
                    output.extend_from_slice(base);
                    break;
                },
            }
        }
    }

    /// Populate a [`Vec`] with the cloned values of the slices using the set operation.
    pub fn into_vec(self) -> Vec<T> {
        let mut vec = Vec::new();
        self.extend_vec(&mut vec);
        vec
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn no_slice() {
        let union_: Vec<i32> = Difference::new_unchecked(vec![]).into_vec();
        assert_eq!(&union_[..], &[]);
    }

    #[test]
    fn one_empty_slice() {
        let a: &[i32] = &[];

        let intersection_ = Difference::new_unchecked(vec![a]).into_vec();
        assert_eq!(&intersection_[..], &[]);
    }

    #[test]
    fn one_slice() {
        let a = &[1, 2, 3];

        let union_ = Difference::new_unchecked(vec![a]).into_vec();
        assert_eq!(&union_[..], &[1, 2, 3]);
    }

    #[test]
    fn two_slices() {
        let a = &[1, 2, 3];
        let b = &[2, 4];

        let union_ = Difference::new_unchecked(vec![a, b]).into_vec();
        assert_eq!(&union_[..], &[1, 3]);
    }

    #[test]
    fn two_slices_special_case() {
        let a = &[1, 2, 3];
        let b = &[3];

        let union_ = Difference::new_unchecked(vec![a, b]).into_vec();
        assert_eq!(&union_[..], &[1, 2]);
    }

    #[test]
    fn three_slices() {
        let a = &[1, 2, 3, 6, 7];
        let b = &[2, 3, 4];
        let c = &[3, 4, 5, 7];

        let union_ = Difference::new_unchecked(vec![a, b, c]).into_vec();
        assert_eq!(&union_[..], &[1, 6]);
    }

    quickcheck! {
        fn qc_difference(xss: Vec<Vec<i32>>) -> bool {
            use std::collections::BTreeSet;
            use std::iter::FromIterator;

            // FIXME temporary hack (can have mutable parameters!)
            let mut xss = xss;

            for xs in &mut xss {
                ::sort_dedup_vec(xs);
            }

            let x = {
                let xss = xss.iter().map(|xs| xs.as_slice()).collect();
                Difference::new_unchecked(xss).into_vec()
            };

            let mut xss = xss.into_iter();
            let mut y = match xss.next() {
                Some(xs) => BTreeSet::from_iter(xs),
                None => BTreeSet::new(),
            };

            for v in xss {
                let x = BTreeSet::from_iter(v.iter().cloned());
                y = y.difference(&x).cloned().collect();
            }
            let y: Vec<_> = y.into_iter().collect();

            x.as_slice() == y.as_slice()
        }
    }
}

#[cfg(all(feature = "unstable", test))]
mod bench {
    extern crate test;
    use super::*;
        use self::test::Bencher;

    #[bench]
    fn two_slices_big(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (1..101).collect();

        bench.iter(|| {
            let union_ = Difference::new_unchecked(vec![&a, &b]).into_vec();
            test::black_box(|| union_);
        });
    }

    #[bench]
    fn two_slices_big2(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (51..151).collect();

        bench.iter(|| {
            let union_ = Difference::new_unchecked(vec![&a, &b]).into_vec();
            test::black_box(|| union_);
        });
    }

    #[bench]
    fn two_slices_big3(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (100..200).collect();

        bench.iter(|| {
            let union_ = Difference::new_unchecked(vec![&a, &b]).into_vec();
            test::black_box(|| union_);
        });
    }
}