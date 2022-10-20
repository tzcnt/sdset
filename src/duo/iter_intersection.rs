use crate::{SetOperation, Collection};
use std::cmp::Ordering;

/// Represent the _intersection_ set operation that will be applied to two slices.
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
/// let op = IterOpBuilder::new(a.iter(), b.iter()).intersection();
///
/// let res: SetBuf<i32> = op.into_set_buf();
/// assert_eq!(&res[..], &[2, 4, 6, 7]);
/// # Ok(()) }
/// # try_main().unwrap();
/// ```
pub struct IterIntersection<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    iter: IterIntersectionIter<T, A, B>
}

impl<T, A, B> IterIntersection<T, A, B>
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
        Self {
            iter: IterIntersectionIter {
                a: a.into_iter(),
                b: b.into_iter(),
            }
        }
    }
}

impl<T, A, B> SetOperation<T> for IterIntersection<T, A, B>
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

impl<'a, T, A, B> SetOperation<T> for IterIntersection<&'a T, A, B>
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

impl<T, A, B> IntoIterator for IterIntersection<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    type Item = T;
    type IntoIter = IterIntersectionIter<T, A, B>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter
    }
}

pub struct IterIntersectionIter<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    a: A,
    b: B,
}

impl<T, A, B> Iterator for IterIntersectionIter<T, A, B>
where
T: Ord,
A: Iterator<Item=T>,
B: Iterator<Item=T>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let mut next_a = self.a.next();
        let mut next_b = self.b.next();
        loop {
            if next_a.is_none() || next_b.is_none() {
                return None;
            }
            match next_a.as_ref().cmp(&next_b.as_ref()) {
                Ordering::Equal => {
                    return next_a;
                },
                Ordering::Less => {
                    next_a = self.a.next();
                },
                Ordering::Greater => {
                    next_b = self.b.next();
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
            let b = vec![2, 3, 4];

            let intersection_: SetBuf<i32> = IterIntersection::new(a.iter(), b.iter()).into_set_buf();
            assert_eq!(&intersection_[..], &[2, 3]);
            
            let intersection_: SetBuf<i32> = IterIntersection::new(a, b).into_set_buf();
            assert_eq!(&intersection_[..], &[2, 3]);
        }

        quickcheck! {
            fn qc_intersection(a: Vec<i32>, b: Vec<i32>) -> bool {
                use std::collections::BTreeSet;
                use std::iter::FromIterator;

                let mut a = a;
                let mut b = b;

                sort_dedup_vec(&mut a);
                sort_dedup_vec(&mut b);

                let x: SetBuf<i32> = IterIntersection::new(a.iter(), b.iter()).into_set_buf();

                let a = BTreeSet::from_iter(a);
                let b = BTreeSet::from_iter(b);
                let y = a.intersection(&b);
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
            let b = vec![2, 3, 4];

            let intersection_: Vec<i32> = IterIntersection::new(a.iter(), b.iter()).into_iter().cloned().collect();
            assert_eq!(&intersection_[..], &[2, 3]);
            
            let intersection_: Vec<i32> = IterIntersection::new(a, b).into_iter().collect();
            assert_eq!(&intersection_[..], &[2, 3]);
        }

        quickcheck! {
            fn qc_intersection(a: Vec<i32>, b: Vec<i32>) -> bool {
                use std::collections::BTreeSet;
                use std::iter::FromIterator;

                let mut a = a;
                let mut b = b;

                sort_dedup_vec(&mut a);
                sort_dedup_vec(&mut b);

                let x: Vec<i32> = IterIntersection::new(a.iter(), b.iter()).into_iter().cloned().collect();

                let a = BTreeSet::from_iter(a);
                let b = BTreeSet::from_iter(b);
                let y = a.intersection(&b);
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
            let intersection_: SetBuf<i32> = IterIntersection::new(a.iter(), b.iter()).into_set_buf();
            test::black_box(|| intersection_);
        });
    }

    #[bench]
    fn two_slices_big2(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (51..151).collect();

        bench.iter(|| {
            let intersection_: SetBuf<i32> = IterIntersection::new(a.iter(), b.iter()).into_set_buf();
            test::black_box(|| intersection_);
        });
    }

    #[bench]
    fn two_slices_big3(bench: &mut Bencher) {
        let a: Vec<_> = (0..100).collect();
        let b: Vec<_> = (100..200).collect();

        bench.iter(|| {
            let intersection_: SetBuf<i32> = IterIntersection::new(a.iter(), b.iter()).into_set_buf();
            test::black_box(|| intersection_);
        });
    }
}
