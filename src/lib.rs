//! Insert or remove multiple elements from a [Vec] in `O(n)` time.
//!
//! This crate provides two types for versatile and efficient [Vec] mutation; [Inserter] and
//! [Remover]. These two types can be seen as more generic implementations of [Vec::insert] and
//! [Vec::drain], allowing you to for example efficiently insert a slice, conditionally drain
//! elements, or access elements of a [Vec] while draining from it.
//!
//! [Inserter] and [Remover] requires an ordering of the insert and removal indices; monotonically
//! non-increasing for [Inserter] and monotonically increasing for [Remover].
//!
//! For convenience, there are also extension traits adding common higher level operations using the
//! [Inserter] and [Remover]. See [ScanMut], [InsertSliceClone], and [InsertSliceCopy].
//!
//! # Examples
//!
//! Inserting a slice into a vec using [ScanMut::insert_all]:
//!
//! ```
//! use scanmut::prelude::*;
//!
//! let mut v = vec!['a', 'b', 'c'];
//! v.insert_all(1, ['d', 'e'].iter().cloned());
//! assert_eq!(v, vec!['a', 'd', 'e', 'b', 'c']);
//! ```
//! 
//! Removing multiple elements in one scan using [ScanMut::multi_remove]:
//!
//! ```
//! use scanmut::prelude::*;
//!
//! let mut v = vec!['a', 'b', 'c'];
//! v.multi_remove([0, 2].iter().cloned(), drop);
//! assert_eq!(v, vec!['b']);
//! ```

#![deny(missing_debug_implementations, missing_docs)]
#![no_std]

#[cfg(test)]
extern crate std;
extern crate alloc;

mod inserter;
mod remover;

#[cfg(test)]
pub mod proputils;

use alloc::vec::Vec;
pub use inserter::Inserter;
pub use remover::Remover;

/// Module of commonly-used traits
pub mod prelude {
    pub use super::{InsertSliceClone, InsertSliceCopy, ScanMut};
}

/// Multiple insert/remove functions
pub trait ScanMut<T> {
    /// Insert multiple elements at specific indices in `O(n)` time.
    ///
    /// Indices must be in monotonically non-increasing order (i.e. the next index must be smaller
    /// than or equal to the previous index).
    ///
    /// # Example
    ///
    /// ```
    /// use scanmut::ScanMut;
    ///
    /// let mut v = vec![1, 2, 3, 4, 5];
    /// v.multi_insert([(3, 8), (3, 7), (0, 6)].iter().cloned());
    ///
    /// assert_eq!(v, vec![6, 1, 2, 3, 7, 8, 4, 5]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The indices are not monotonically non-increasing.
    /// - An index is out of bounds.
    ///
    fn multi_insert<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (usize, T)>,
        I::IntoIter: ExactSizeIterator;

    /// Remove multiple elements by index and calls a sink function with the removed element.
    ///
    /// Indices must be in monotonically increasing order (i.e. the next index must be more than the
    /// previous index).
    ///
    /// # Example
    ///
    /// ```
    /// use scanmut::ScanMut;
    ///
    /// let mut v = vec![1, 2, 3, 4, 5];
    /// v.multi_remove([0, 3].iter().cloned(), drop);
    ///
    /// assert_eq!(v, vec![2, 3, 5]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The indices are not monotonically increasing.
    /// - An index is out of bounds.
    fn multi_remove<I, F>(&mut self, iter: I, sink: F)
    where
        I: IntoIterator<Item = usize>,
        F: FnMut(T);

    // Ideally, the above function  would return an iterator of removed elements instead, but that
    // currently does not seem possible without generic associated types. 🤷

    /// Inserts items from an iterator at the given index.
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The range `index..(index + items.len())` is out of bounds for this `Vec`.
    /// - The iterator is shorter or longer than the reported length.
    fn insert_all<I>(&mut self, index: usize, items: I)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator + DoubleEndedIterator;

    /// Inserts items in reverse from an iterator at the given index.
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The range `index..(index + items.len())` is out of bounds for this `Vec`.
    /// - The iterator is shorter or longer than the reported length.
    fn insert_all_rev<I>(&mut self, index: usize, items: I)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator;
}

impl<T> ScanMut<T> for Vec<T> {
    fn multi_insert<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (usize, T)>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = iter.into_iter();
        let mut inserter = Inserter::new(self, iter.len());
        iter.for_each(|(ix, item)| {
            inserter.move_to(ix);
            inserter.insert(item);
        });

        assert!(
            inserter.remaining_inserts() == 0,
            "Iterator shorter than reported length"
        );
    }

    fn multi_remove<I, F>(&mut self, iter: I, mut sink: F)
    where
        I: IntoIterator<Item = usize>,
        F: FnMut(T),
    {
        let mut remover = Remover::new(self);
        iter.into_iter().for_each(|ix| {
            remover.move_to(ix);
            sink(remover.remove());
        });
    }

    fn insert_all<I>(&mut self, index: usize, items: I)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator + DoubleEndedIterator,
    {
        let iter = items.into_iter();
        let mut inserter = Inserter::new(self, iter.len());
        inserter.move_to(index);
        inserter.insert_all(iter);

        assert!(
            inserter.remaining_inserts() == 0,
            "Iterator shorter than reported length"
        );
    }

    fn insert_all_rev<I>(&mut self, index: usize, items: I)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = items.into_iter();
        let mut inserter = Inserter::new(self, iter.len());
        inserter.move_to(index);
        inserter.insert_all_rev(iter);

        assert!(
            inserter.remaining_inserts() == 0,
            "Iterator shorter than reported length"
        );
    }
}

/// ScanMut extension trait for `Vec`s with cloneable items.
pub trait InsertSliceClone<T: Clone>: ScanMut<T> {
    /// Inserts items from a slice at the given index by cloning elements.
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The range `index..(index + slice.len())` is out of bounds for this `Vec`.
    fn insert_slice_clone(&mut self, index: usize, slice: &[T]);
}

impl<T: Clone> InsertSliceClone<T> for Vec<T> {
    fn insert_slice_clone(&mut self, index: usize, slice: &[T]) {
        let mut inserter = Inserter::new(self, slice.len());
        inserter.move_to(index);
        inserter.insert_slice_clone(slice);
    }
}

/// ScanMut extension trait for `Vec`s with copyable items.
pub trait InsertSliceCopy<T: Copy>: InsertSliceClone<T> {
    /// Inserts items from a slice at the given index by copying elements.
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The range `index..(index + slice.len())` is out of bounds for this `Vec`.
    fn insert_slice_copy(&mut self, index: usize, slice: &[T]);
}

impl<T: Copy> InsertSliceCopy<T> for Vec<T> {
    fn insert_slice_copy(&mut self, index: usize, slice: &[T]) {
        let mut inserter = Inserter::new(self, slice.len());
        inserter.move_to(index);
        inserter.insert_slice_copy(slice);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;
    use core::iter::once;

    #[test]
    fn multimutate_single_insert() {
        let mut items = Vec::new();
        items.multi_insert(once((0, 1)));
        assert_eq!(items, vec![1]);
    }

    #[test]
    fn multimutate_single_insert_pre() {
        let mut items = vec![0];
        items.multi_insert(once((0, 1)));
        assert_eq!(items, vec![1, 0]);
    }

    #[test]
    fn multimutate_single_insert_mid() {
        let mut items = vec![0, 2];
        items.multi_insert(once((1, 1)));
        assert_eq!(items, vec![0, 1, 2]);
    }

    #[test]
    fn multimutate_single_insert_post() {
        let mut items = vec![0];
        items.multi_insert(once((1, 1)));
        assert_eq!(items, vec![0, 1]);
    }

    #[test]
    #[should_panic]
    fn multimutate_single_insert_out_of_bounds() {
        let mut items = vec![0];
        items.multi_insert(once((2, 1)));
    }

    #[test]
    fn multimutate_multiple_insert() {
        let mut items = vec![1];
        items.multi_insert([(1, 2), (0, 0)].iter().cloned());
        assert_eq!(items, vec![0, 1, 2]);
    }

    #[test]
    fn multimutate_single_insert_zero_sized() {
        let mut items = vec![()];
        items.multi_insert(once((0, ())));
        assert_eq!(items, vec![(), ()]);
    }

    #[test]
    #[should_panic]
    fn multimutate_single_insert_zero_sized_out_of_bounds() {
        let mut items = vec![()];
        items.multi_insert(once((2, ())));
        assert_eq!(items, vec![(), ()]);
    }

    #[test]
    #[should_panic]
    fn multimutate_remove() {
        let mut items = vec![1, 2, 3];
        let mut index = 0;

        items.multi_remove(vec![1, 2], |x| {
            assert_eq!(
                x,
                match index {
                    0 => 1,
                    1 => 2,
                    _ => panic!(),
                }
            );

            index += 1;
        });

        assert_eq!(items, [1]);
    }

    #[test]
    fn insert_all() {
        let mut items = vec![1, 2, 3];
        items.insert_all(1, [4, 5, 6].iter().cloned());
        assert_eq!(items, [1, 4, 5, 6, 2, 3]);
    }

    #[test]
    fn insert_all_end() {
        let mut items = vec![1, 2, 3];
        items.insert_all(3, [4, 5, 6].iter().cloned());
        assert_eq!(items, [1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn insert_all_rev() {
        let mut items = vec![1, 2, 3];
        items.insert_all_rev(1, [4, 5, 6].iter().cloned());
        assert_eq!(items, [1, 6, 5, 4, 2, 3]);
    }

    #[test]
    fn insert_all_rev_end() {
        let mut items = vec![1, 2, 3];
        items.insert_all_rev(3, [4, 5, 6].iter().cloned());
        assert_eq!(items, [1, 2, 3, 6, 5, 4]);
    }

    #[test]
    fn insert_slice_clone() {
        let mut items = vec![1, 2, 3];
        items.insert_slice_clone(1, &[4, 5, 6]);
        assert_eq!(items, [1, 4, 5, 6, 2, 3]);
    }

    #[test]
    fn insert_slice_copy() {
        let mut items = vec![1, 2, 3];
        items.insert_slice_copy(1, &[4, 5, 6]);
        assert_eq!(items, [1, 4, 5, 6, 2, 3]);
    }
}
