//! Insert and remove multiple elments from a `Vec` in `O(n)` time.
//!
//! This crate provides the `Inserter` and `Remover` types for inserting and removing items from a
//! `Vec` in a single scan over the `Vec`. The indices of the insertions and removals need to be in
//! sorted order: monotnonically non-increasing for `Inserter` and monotonically increasing for
//! `Remover`. See the `Inserter` and `Remover` types for more information.
//!
//! For convenience, there is also an extension trait `ScanMut` that add `multi_insert` and
//! `multi_remove` methods to `Vec`.
//!
//! # Example
//!
//! ```
//! use scanmut::ScanMut;
//!
//! let mut v = vec!['a', 'b', 'c'];
//! v.multi_insert([(2, 'e'), (1, 'd')].iter().cloned());
//!
//! assert_eq!(v, vec!['a', 'd', 'b', 'e', 'c']);
//! ```

#![deny(missing_debug_implementations, missing_docs)]
#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use core as std;

/// An object which can insert multiple elements into a `Vec` in a single scan through the `Vec`.
///
/// An upper bound for the number of insertions (the *insertion capacity*) must be known beforehand
/// and the indices of inserted objects must be monotonically non-increasing (i.e. the next index
/// must be less than or equal to the last).
///
/// The elements below the last inserted index are the *unmerged elements*, while the elements above
/// or equal to the last inserted index are the *merged elements*. Initially all elements are
/// unmerged. As the `Inserter` progresses over the `Vec`, the inserted elements are merged with the
/// existing elements into the merged elements.
///
/// Dropping the inserter without using the entire insertion capacity has a runtime cost propotional
/// to the size of the merged elements. Dropping after using the entire insertion capacity has no
/// runtime cost.
///
/// Leaking the inserter (through `std::mem::forget` or similar) will leave the unmerged elements in
/// the `Vec` and leak the merged elements.
///
/// # Example
///
/// ```
/// use scanmut::Inserter;
///
/// let mut items = vec![1, 2, 3];
///
/// let mut inserter = Inserter::new(&mut items, 2);
/// inserter.insert(3, 4);
/// inserter.insert(1, 5);
/// drop(inserter);
///
/// assert_eq!(items, [1, 5, 2, 3, 4]);
/// ```
#[derive(Debug)]
pub struct Inserter<'a, T> {
    // The inserter works by keeping a "gap" of possibly uninitialized values. This gap is initially
    // the size of out insertion capacity and is situated at the end of the vec. It then  moves down
    // through the vec as we insert values, shrinking by one each time we insert a new element.
    //
    // The fields have the following invaraint:
    //     vec.len() <= merged_start <= merged_end <= vec.capacity()
    //
    // Where
    //     [0,vec.len()[              are the unmerged elements
    //     [vec.len(),merged_start[   is a gap of possibly unitialized values
    //     [merged_start,merged_end[  are the merged elements
    vec: &'a mut Vec<T>,
    merged_start: usize,
    merged_end: usize,
}

impl<'a, T> Inserter<'a, T> {
    /// Create a new `Inserter` with the specified maximum number of inserts
    ///
    /// # Panics
    ///
    /// Panics if the additional number of inserts overflow `usize`.
    #[inline]
    pub fn new(vec: &'a mut Vec<T>, additional: usize) -> Inserter<'a, T> {
        vec.reserve(additional);

        let len = vec.len();

        // Safety: len + capacity will not overflow as the previous reserve would otherwise panic.

        let merged_start = len + additional;

        Inserter {
            merged_start,
            merged_end: merged_start,
            vec,
        }
    }

    /// Get a slice of the unmerged elements.
    #[inline]
    pub fn unmerged(&self) -> &[T] {
        &self.vec[..]
    }

    /// Get a mutable slice of the unmerged elements.
    #[inline]
    pub fn unmerged_mut(&mut self) -> &mut [T] {
        &mut self.vec[..]
    }

    /// Get a slice of the merged elements.
    #[inline]
    pub fn merged(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(
                self.vec.as_ptr().add(self.merged_start),
                self.merged_end - self.merged_start,
            )
        }
    }

    /// Get a mutable slice of the merged elements.
    #[inline]
    pub fn merged_mut(&mut self) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(
                self.vec.as_mut_ptr().add(self.merged_start),
                self.merged_end - self.merged_start,
            )
        }
    }

    /// Returns the remaining number of allowed inserts in this `Inserter`.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.merged_start - self.vec.len()
    }

    /// Returns the maximum allowed index
    #[inline]
    pub fn max_index(&self) -> usize {
        self.vec.len()
    }

    /// Advances the index of this `Inserter` without inserting an item.
    #[inline]
    pub fn advance_to(&mut self, index: usize) {
        let copy_len = self
            .vec
            .len()
            .checked_sub(index)
            .expect("Index must be less than or equal to previous index and size");

        let ptr = self.vec.as_mut_ptr();

        unsafe {
            let write_ptr = ptr.add(self.merged_start - copy_len);
            ptr.add(index).copy_to(write_ptr, copy_len);

            self.vec.set_len(index);
            self.merged_start -= copy_len;
        }
    }

    /// Inserts an element into the `Vec` at the specified index.
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The index is larger than the last index.
    /// - The index is larger than the size of the vec.
    /// - There is no more capacity for inserts in this `Inserter`.
    #[inline]
    pub fn insert(&mut self, index: usize, item: T) {
        assert!(
            self.vec.len() < self.merged_start,
            "Insufficient insert capacity"
        );

        self.advance_to(index);

        let ptr = self.vec.as_mut_ptr();

        unsafe {
            self.merged_start -= 1;
            ptr.add(self.merged_start).write(item);
        }
    }
}

impl<'a, T> Drop for Inserter<'a, T> {
    #[inline]
    fn drop(&mut self) {
        let ptr = self.vec.as_mut_ptr();
        let merged_len = self.merged_end - self.merged_start;

        unsafe {
            ptr.add(self.merged_start)
                .copy_to(ptr.add(self.vec.len()), merged_len);

            self.vec.set_len(self.vec.len() + merged_len);
        }
    }
}

/// An object that can remove multiple elements from a `Vec` in a single scan through the `Vec`.
///
/// The indices of the removed elements must be monotonically increasing (i.e. the next index most
/// be more than the previous index).
///
/// The elements below the last removed index are the *filtered elements*, while the elements above
/// the last removed index are the *unfiltered elements*. Initially all elements are unfiltered. As
/// the `Remover` progresses over the `Vec`, these elements are either removed or moved to the
/// filtered elements.  
///
/// Leaking the remover (through `std::mem::forget` or similar) will leave the filtered elements in
/// the `Vec` and leak the unfiltered elements.
///
/// # Example
///
/// ```
/// use scanmut::Remover;
///
/// let mut items = vec![1, 2, 3];
///
/// let mut remover = Remover::new(&mut items);
/// assert_eq!(remover.remove(0), 1);
/// assert_eq!(remover.remove(2), 3);
/// drop(remover);
///
/// assert_eq!(items, [2]);
/// ```
#[derive(Debug)]
pub struct Remover<'a, T> {
    // The remover works by keeping a "gap" of possibly uninitialized values. This gap is initially
    // of length zero and at the end of the vec, and moves up through the vec as we remove elements,
    // increasing in size by one each time we remove an element.
    //
    // The fields have the following invaraint:
    //     vec.len() <= unfiltered_start <= unfiltered_end <= vec.capacity()
    //
    // Where
    //     [0,vec.len()[                      are the filtered elements
    //     [vec.len(),unfiltered_start[           is a gap of possibly unitialized values
    //     [unfiltered_start,unfiltered_end[  are the unfiltered elements
    vec: &'a mut Vec<T>,
    unfiltered_start: usize,
    unfiltered_end: usize,
}

impl<'a, T> Remover<'a, T> {
    /// Create a new new `Remover` for removing elements from a `Vec`.
    #[inline]
    pub fn new(vec: &'a mut Vec<T>) -> Remover<'a, T> {
        let unfiltered_end = vec.len();

        unsafe {
            vec.set_len(0);
        }

        Remover {
            vec,
            unfiltered_start: 0,
            unfiltered_end,
        }
    }

    /// The minimum index allowed for the next remove.
    #[inline]
    pub fn min_index(&self) -> usize {
        self.unfiltered_start
    }

    /// The length of the original `Vec`.
    #[inline]
    pub fn len(&self) -> usize {
        self.unfiltered_end
    }

    /// Get a slice of the filtered elements.
    #[inline]
    pub fn filtered(&self) -> &[T] {
        &self.vec[..]
    }

    /// Get a mutable slice of the filtered elements.
    #[inline]
    pub fn filtered_mut(&mut self) -> &mut [T] {
        &mut self.vec[..]
    }

    /// Get a slice of the unfiltered elements.
    #[inline]
    pub fn unfiltered(&self) -> &[T] {
        unsafe {
            std::slice::from_raw_parts(
                self.vec.as_ptr().add(self.unfiltered_start),
                self.unfiltered_end - self.unfiltered_start,
            )
        }
    }

    /// Get a mutable slice of the unfiltered elements.
    #[inline]
    pub fn unfiltered_mut(&mut self) -> &mut [T] {
        unsafe {
            std::slice::from_raw_parts_mut(
                self.vec.as_mut_ptr().add(self.unfiltered_start),
                self.unfiltered_end - self.unfiltered_start,
            )
        }
    }

    /// Advances the index of this `Remover` without removing an item.
    #[inline]
    pub fn advance_to(&mut self, index: usize) {
        assert!(index <= self.unfiltered_end, "Index out of bounds");

        let copy_len = index
            .checked_sub(self.unfiltered_start)
            .expect("Index must be more than the previous index");

        let ptr = self.vec.as_mut_ptr();

        unsafe {
            ptr.add(self.unfiltered_start)
                .copy_to(ptr.add(self.vec.len()), copy_len);

            self.vec.set_len(self.vec.len() + copy_len);
            self.unfiltered_start = index;
        }
    }

    /// Removes an element from the vec at the specified index.
    ///
    /// # Panics
    ///
    /// Panics if
    /// - The index is less than or equal to the last index.
    /// - The index is larger than the size of the vec.
    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.unfiltered_end, "Index out of bounds");

        self.advance_to(index);

        let ptr = self.vec.as_mut_ptr();

        unsafe {
            let item = ptr.add(self.unfiltered_start).read();
            self.unfiltered_start += 1;
            item
        }
    }
}

impl<'a, T> Drop for Remover<'a, T> {
    #[inline]
    fn drop(&mut self) {
        let ptr = self.vec.as_mut_ptr();
        let unfiltered_len = self.unfiltered_end - self.unfiltered_start;

        unsafe {
            ptr.add(self.unfiltered_start)
                .copy_to(ptr.add(self.vec.len()), unfiltered_len);

            self.vec.set_len(self.vec.len() + unfiltered_len)
        }
    }
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
        I: IntoIterator<Item = (usize)>,
        F: FnMut(T);

    // Ideally, the above function  would return an iterator of removed elements instead, but that
    // currently does not seem possible without generic associated types. 🤷
}

impl<T> ScanMut<T> for Vec<T> {
    fn multi_insert<I>(&mut self, iter: I)
    where
        I: IntoIterator<Item = (usize, T)>,
        I::IntoIter: ExactSizeIterator,
    {
        let iter = iter.into_iter();
        let mut inserter = Inserter::new(self, iter.len());
        iter.for_each(|(ix, item)| inserter.insert(ix, item));
        assert!(
            inserter.capacity() == 0,
            "Iterator shorter than reported length"
        );
    }

    fn multi_remove<I, F>(&mut self, iter: I, mut sink: F)
    where
        I: IntoIterator<Item = (usize)>,
        F: FnMut(T),
    {
        let mut remover = Remover::new(self);
        iter.into_iter().for_each(|ix| sink(remover.remove(ix)));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::iter::once;
    use alloc::vec;

    #[test]
    fn inserter_empty() {
        let mut items = Vec::new();
        Inserter::new(&mut items, 1).insert(0, 1);
        assert_eq!(items, vec![1]);
    }

    #[test]
    fn inserter_single_pre() {
        let mut items = vec![0];
        Inserter::new(&mut items, 1).insert(0, 1);
        assert_eq!(items, vec![1, 0]);
    }

    #[test]
    fn inserter_single_post() {
        let mut items = vec![0];
        Inserter::new(&mut items, 1).insert(1, 1);
        assert_eq!(items, vec![0, 1]);
    }

    #[test]
    fn inserter_threes() {
        let mut items = vec![1, 2, 3];
        let mut inserter = Inserter::new(&mut items, 3);
        inserter.insert(3, 4);
        inserter.insert(2, 5);
        inserter.insert(0, 6);
        drop(inserter);
        assert_eq!(items, vec![6, 1, 2, 5, 3, 4]);
    }

    #[test]
    #[should_panic]
    fn inserter_out_of_order() {
        let mut items = vec![1, 2, 3];
        let mut inserter = Inserter::new(&mut items, 3);
        inserter.insert(0, 6);
        inserter.insert(3, 4);
    }

    #[test]
    fn inserter_threes_additional_cap() {
        let mut items = vec![1, 2, 3];
        let mut inserter = Inserter::new(&mut items, 10);
        inserter.insert(3, 4);
        inserter.insert(2, 5);
        inserter.insert(0, 6);
        drop(inserter);
        assert_eq!(items, vec![6, 1, 2, 5, 3, 4]);
    }

    #[test]
    fn inserter_leak() {
        let mut items = vec![1, 2, 3];
        let mut inserter = Inserter::new(&mut items, 10);
        inserter.insert(1, 4);
        std::mem::forget(inserter);
        assert_eq!(items, vec![1]);
    }

    #[test]
    fn inserter_slices() {
        let mut items = vec![1, 2, 3];
        let mut inserter = Inserter::new(&mut items, 1);
        inserter.insert(1, 4);

        assert_eq!(inserter.unmerged(), [1]);
        assert_eq!(inserter.unmerged_mut(), [1]);
        assert_eq!(inserter.merged(), [4, 2, 3]);
        assert_eq!(inserter.merged_mut(), [4, 2, 3]);
    }

    #[test]
    fn inserter_max_index() {
        let mut items = vec![1, 2, 3];
        let mut inserter = Inserter::new(&mut items, 2);

        assert_eq!(inserter.max_index(), 3);
        inserter.insert(3, 4);
        assert_eq!(inserter.max_index(), 3);
        inserter.advance_to(2);
        assert_eq!(inserter.max_index(), 2);
    }

    #[test]
    #[should_panic]
    fn inserter_oob() {
        let mut items = vec![1];
        let mut inserter = Inserter::new(&mut items, 1);
        inserter.insert(2, 1);
    }

    #[test]
    #[should_panic]
    fn inserter_advance_oob() {
        let mut items = vec![1];
        let mut inserter = Inserter::new(&mut items, 1);
        inserter.advance_to(2);
    }

    #[test]
    fn remover_empty() {
        let mut items: Vec<usize> = Vec::new();
        drop(Remover::new(&mut items));
        assert_eq!(items, vec![]);
    }

    #[test]
    fn remover_single() {
        let mut items = vec![1];
        assert_eq!(Remover::new(&mut items).remove(0), 1);
        assert_eq!(items, vec![]);
    }

    #[test]
    fn remover_two_first() {
        let mut items = vec![1, 2];
        assert_eq!(Remover::new(&mut items).remove(0), 1);
        assert_eq!(items, vec![2]);
    }

    #[test]
    fn remover_two_second() {
        let mut items = vec![1, 2];
        assert_eq!(Remover::new(&mut items).remove(1), 2);
        assert_eq!(items, vec![1]);
    }

    #[test]
    fn remover_two_both() {
        let mut items = vec![1, 2];
        let mut remover = Remover::new(&mut items);
        assert_eq!(remover.remove(0), 1);
        assert_eq!(remover.remove(1), 2);
        drop(remover);
        assert_eq!(items, vec![]);
    }

    #[test]
    #[should_panic]
    fn remover_two_out_of_order() {
        let mut items = vec![1, 2];
        let mut remover = Remover::new(&mut items);
        assert_eq!(remover.remove(2), 2);
        drop(remover.remove(1));
    }

    #[test]
    #[should_panic]
    fn remover_out_of_bounds() {
        drop(Remover::new(&mut vec![1, 2]).remove(3));
    }

    #[test]
    #[should_panic]
    fn remover_advance_out_of_bounds() {
        Remover::new(&mut vec![1, 2]).advance_to(4);
    }

    #[test]
    fn remover_advance_one_past() {
        let mut items = vec![1, 2];
        let mut remover = Remover::new(&mut items);
        remover.advance_to(2);
        assert_eq!(remover.min_index(), 2);
    }

    #[test]
    fn remover_slices() {
        let mut items = vec![1, 2, 3, 4];
        let mut remover = Remover::new(&mut items);
        assert_eq!(remover.remove(2), 3);
        assert_eq!(remover.unfiltered(), [4]);
        assert_eq!(remover.unfiltered_mut(), [4]);
        assert_eq!(remover.filtered(), [1, 2]);
        assert_eq!(remover.filtered_mut(), [1, 2]);
    }

    #[test]
    fn remover_index() {
        let mut items = vec![1, 2, 3, 4];
        let mut remover = Remover::new(&mut items);
        assert_eq!(remover.min_index(), 0);
        assert_eq!(remover.remove(1), 2);
        assert_eq!(remover.min_index(), 2);
        remover.advance_to(3);
        assert_eq!(remover.min_index(), 3);
    }

    #[test]
    fn remover_len() {
        assert_eq!(Remover::new(&mut vec![1, 2, 3]).len(), 3);
    }

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
}
