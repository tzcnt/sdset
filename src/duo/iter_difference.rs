use crate::{SetOperation, Collection};
use std::cmp::Ordering;

/// Represent the _difference_ set operation that will be applied to two iterators.
///
/// # Examples
/// ```
/// # use sdset::Error;
/// # fn try_main() -> Result<(), Error> {
/// use sdset::duo::IterOpBuilder;
/// use sdset::{SetOperation, Set, SetBuf};
///
/// let a = Set::new(&[1, 2, 4, 6, 7])?;
/// let b = Set::new(&[2, 3, 4, 5, 6, 7])?;
///
/// let op = IterOpBuilder::new(a.iter(), b.iter()).difference();
///
/// let res: SetBuf<i32> = op.into_set_buf();
/// assert_eq!(&res[..], &[1]);
/// # Ok(()) }
/// # try_main().unwrap();
/// ```
pub struct IterDifference<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    iter: IterDifferenceIter<T, A, B>
}

impl<T, A, B> IterDifference<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    /// Construct one with slices checked to be sorted and deduplicated.
    pub fn new<AIn, BIn>(a: AIn, b: BIn) -> Self
    where 
    AIn: IntoIterator<IntoIter=A>,
    BIn: IntoIterator<IntoIter=B>
    {
        let a = a.into_iter();
        let mut b = b.into_iter();
        let next_b = b.next();
        Self {
            iter: IterDifferenceIter {
                a: a,
                b: b,
                next_b: next_b,
            }
        }
    }
}

impl<T, A, B> SetOperation<T> for IterDifference<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    fn extend_collection<C>(self, output: &mut C) -> Result<(), C::Error>
    where C: Collection<T>
    {
        for elem in self.iter {
            Collection::push(output, elem)?;
        }
        Ok(())
    }
}

impl<'a, T, A, B> SetOperation<T> for IterDifference<&'a T, A, B>
where
T: Ord + Clone,
A: Iterator<Item=&'a T>,
B: Iterator<Item=&'a T>
{
    fn extend_collection<C>(self, output: &mut C) -> Result<(), C::Error>
    where C: Collection<T>
    {
        for elem in self.iter {
            Collection::push(output, elem.clone())?;
        }
        Ok(())
    }
}

impl<T, A, B> IntoIterator for IterDifference<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    type Item = T;
    type IntoIter = IterDifferenceIter<T, A, B>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

pub struct IterDifferenceIter<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    a: A,
    b: B,
    next_b: Option<T>,
}

impl<T, A, B> Iterator for IterDifferenceIter<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let mut next_a = self.a.next();
            loop {
                if self.next_b.is_none() {
                    return next_a;
                }
                match next_a.as_ref().cmp(&self.next_b.as_ref()) {
                    Ordering::Greater => { // a > b
                        self.next_b = self.b.next();
                        continue;
                    },
                    Ordering::Equal => {
                        next_a = self.a.next();
                        if next_a.is_none() {
                            return None;
                        }
                        self.next_b = self.b.next();
                        continue;
                    },
                    Ordering::Less => { // b > a
                        return next_a;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    mod iter_to_set {
        use super::super::*;
        use crate::set::{sort_dedup_vec, SetBuf};
        #[test]
        fn two_slices() {
            let a = vec![1, 2, 3];
            let b = vec![2, 4];

            // test iter of references
            let diff: SetBuf<i32> = IterDifference::new(a.iter(), b.iter()).into_set_buf();
            assert_eq!(&diff[..], &[1, 3]);

            // test iter of values
            let diff: SetBuf<i32> = IterDifference::new(a, b).into_set_buf();
            assert_eq!(&diff[..], &[1, 3]);
        }

        #[test]
        fn two_slices_special_case() {
            let a = vec![1, 2, 3];
            let b = vec![3];

            // test iter of references
            let diff: SetBuf<i32> = IterDifference::new(a.iter(), b.iter()).into_set_buf();
            assert_eq!(&diff[..], &[1, 2]);

            // test iter of values
            let diff: SetBuf<i32> = IterDifference::new(a, b).into_set_buf();
            assert_eq!(&diff[..], &[1, 2]);
        }

        quickcheck! {
            fn qc_difference(a: Vec<i32>, b: Vec<i32>) -> bool {
                use std::collections::BTreeSet;
                use std::iter::FromIterator;

                let mut a = a;
                let mut b = b;

                sort_dedup_vec(&mut a);
                sort_dedup_vec(&mut b);

                let x: SetBuf<i32> = IterDifference::new(a.iter(), b.iter()).into_set_buf();

                let a = BTreeSet::from_iter(a);
                let b = BTreeSet::from_iter(b);
                let y = a.difference(&b);
                let y: Vec<_> = y.cloned().collect();

                x.as_slice() == y.as_slice()
            }
        }
    }

    mod iter_to_iter {
        use super::super::*;
        use crate::set::sort_dedup_vec;
        #[test]
        fn two_slices() {
            let a = vec![1, 2, 3];
            let b = vec![2, 4];

            // test iter of references
            let diff: Vec<i32> = IterDifference::new(a.iter(), b.iter()).into_iter().cloned().collect();
            assert_eq!(&diff[..], &[1, 3]);

            // test iter of values
            let diff: Vec<i32> = IterDifference::new(a, b).into_iter().collect();
            assert_eq!(&diff[..], &[1, 3]);
        }

        #[test]
        fn two_slices_special_case() {
            let a = vec![1, 2, 3];
            let b = vec![3];

            // test iter of references
            let diff: Vec<i32> = IterDifference::new(a.iter(), b.iter()).into_iter().cloned().collect();
            assert_eq!(&diff[..], &[1, 2]);

            // test iter of values
            let diff: Vec<i32> = IterDifference::new(a, b).into_iter().collect();
            assert_eq!(&diff[..], &[1, 2]);
        }

        quickcheck! {
            fn qc_difference(a: Vec<i32>, b: Vec<i32>) -> bool {
                use std::collections::BTreeSet;
                use std::iter::FromIterator;

                let mut a = a;
                let mut b = b;

                sort_dedup_vec(&mut a);
                sort_dedup_vec(&mut b);

                let x: Vec<i32> = IterDifference::new(a.iter(), b.iter()).into_iter().cloned().collect();

                let a = BTreeSet::from_iter(a);
                let b = BTreeSet::from_iter(b);
                let y = a.difference(&b);
                let y: Vec<_> = y.cloned().collect();

                x.as_slice() == y.as_slice()
            }
        }
    }
}

#[cfg(all(feature = "unstable", test))]
mod bench {
    extern crate test;
    use super::*;
    use self::test::Bencher;
    use crate::set::SetBuf;

    #[bench]
    fn two_slices_big(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (1..101).collect();

        bench.iter(|| {
            let difference_: SetBuf<i32> = IterDifference::new(a.iter(), b.iter()).into_set_buf();
            test::black_box(|| difference_);
        });
    }

    #[bench]
    fn two_slices_big2(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (51..151).collect();

        bench.iter(|| {
            let difference_: SetBuf<i32> = IterDifference::new(a.iter(), b.iter()).into_set_buf();
            test::black_box(|| difference_);
        });
    }

    #[bench]
    fn two_slices_big3(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (100..200).collect();

        bench.iter(|| {
            let difference_: SetBuf<i32> = IterDifference::new(a.iter(), b.iter()).into_set_buf();
            test::black_box(|| difference_);
        });
    }
}
