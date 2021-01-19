use alloc::vec::Vec;
use core as std;

/// An object which can insert multiple elements into a [Vec] in a single scan through the [Vec].
///
/// The [Inserter] has a position in the [Vec] at which it inserts, called the index. Initially, the
/// index is at the **end** of the [Vec]. This index can only be moved further towards front of the
/// [Vec], meaning that the indices of the inserted objects must be monotonically non-increasing
/// (i.e. the next index must be less than or equal to the previous index).
///
/// Dropping the [Inserter] without using the entire insertion capacity has a runtime cost
/// proportional to the size of the merged elements. Dropping after using the entire insertion
/// capacity has no runtime cost.
///
/// Leaking the [Inserter] (through [std::mem::forget] or similar) may leak some items of the [Vec]
/// and will leave the [Vec] in an unspecified but valid state
///
/// # Example
///
/// ```
/// use scanmut::Inserter;
///
/// let mut items = vec!['a', 'b', 'c'];
///
/// let mut inserter = Inserter::new(&mut items, 2);
///
/// assert_eq!(inserter.index(), 3); // Initial index is at end of vec
///
/// inserter.insert('d');
/// inserter.move_to(1);
/// inserter.insert('e');
/// drop(inserter);
///
/// assert_eq!(items, ['a', 'e', 'b', 'c', 'd']);
/// ```
///
/// It is also possible to insert multiple items at the same position, but keep in mind that, since
/// the index does not shift with the new element, the order will be the reverse of insertion order.
///
/// ```
/// use scanmut::Inserter;
///
/// let mut items = vec![1, 2, 3];
///
/// let mut inserter = Inserter::new(&mut items, 2);
/// inserter.move_to(1);
/// inserter.insert(4);
/// inserter.insert(5);
/// drop(inserter);
///
/// assert_eq!(items, [1, 5, 4, 2, 3]);
/// ```

#[derive(Debug)]
pub struct Inserter<'a, T> {
    // The inserter works by keeping a "gap" of uninitialized values. This gap is initially
    // the size of out insertion capacity and is situated at the end of the vec. It then  moves down
    // through the vec as we insert values, shrinking by one each time we insert a new element.
    //
    // The fields have the following invariant:
    //     vec.len() <= merged_start <= merged_end <= vec.capacity()
    //
    // Where
    //     [0,vec.len()[              are the unmerged elements
    //     [vec.len(),merged_start[   is a gap of uninitialized values
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
    /// Panics if the length plus the additional number of inserts exceeds `isize::MAX` bytes.
    #[inline]
    pub fn new(vec: &'a mut Vec<T>, additional: usize) -> Inserter<'a, T> {
        vec.reserve(additional);

        let len = vec.len();

        // Safety: len + additional will not overflow as the previous reserve would otherwise panic.

        let merged_start = len + additional;

        Inserter {
            merged_start,
            merged_end: merged_start,
            vec,
        }
    }

    /// Returns a pair of slices representing the current state of the `Vec`being inserted into.
    ///
    /// The first slice is the part of the `Vec` below the index. The second slice is the part of
    /// the `Vec` above or equal to the index.
    #[inline]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        unsafe {
            (
                &self.vec[..],
                std::slice::from_raw_parts(
                    self.vec.as_ptr().add(self.merged_start),
                    self.merged_end - self.merged_start,
                ),
            )
        }
    }

    /// Returns a pair of mutable slices representing the current state of the `Vec` being inserted
    /// into.
    ///
    /// The first slice is the part of the `Vec` below the index. The second slice is the part of
    /// the `Vec` above or equal to the index.
    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        unsafe {
            (
                std::slice::from_raw_parts_mut(self.vec.as_mut_ptr(), self.vec.len()),
                std::slice::from_raw_parts_mut(
                    self.vec.as_mut_ptr().add(self.merged_start),
                    self.merged_end - self.merged_start,
                ),
            )
        }
    }

    /// Returns the remaining number of allowed inserts in this `Inserter`.
    #[inline]
    pub fn remaining_inserts(&self) -> usize {
        self.merged_start - self.vec.len()
    }

    /// Returns the current index of the inserter.
    #[inline]
    pub fn index(&self) -> usize {
        self.vec.len()
    }

    /// Moves this `Inserter` to the given index in the `Vec`.
    ///
    /// # Panics
    ///
    /// Panics if the index to move to is larger than the current index.
    #[inline]
    pub fn move_to(&mut self, index: usize) {
        let copy_len = self
            .vec
            .len()
            .checked_sub(index)
            .expect("Index must be less than or equal to previous index");

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
    /// Panics if there are no more inserts available for this `Inserter`.
    #[inline]
    pub fn insert(&mut self, item: T) {
        unsafe {
            self.allocate(1).write(item);
        }
    }

    /// Inserts all items from an iterator into the underlying `Vec` at the current index.
    pub fn insert_all<I>(&mut self, items: I)
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: DoubleEndedIterator,
    {
        items.into_iter().rev().for_each(|item| self.insert(item))
    }

    /// Inserts all items from an iterator into the underlying `Vec` at the current index in
    /// reverse.
    pub fn insert_all_rev<I>(&mut self, items: I)
    where
        I: IntoIterator<Item = T>,
    {
        items.into_iter().for_each(|item| self.insert(item))
    }

    fn allocate(&mut self, len: usize) -> *mut T {
        assert!(
            len <= self.remaining_inserts(),
            "Insufficient insert capacity"
        );

        self.merged_start -= len;

        unsafe { self.vec.as_mut_ptr().add(self.merged_start) }
    }
}

impl<'a, T: Clone> Inserter<'a, T> {
    /// Inserts items at the current index by cloning them from a slice
    pub fn insert_slice_clone(&mut self, items: &[T]) {
        self.insert_all(items.into_iter().cloned())
    }
}

impl<'a, T: Copy> Inserter<'a, T> {
    /// Inserts items at the current index by copying them from a slice
    pub fn insert_slice_copy(&mut self, items: &[T]) {
        unsafe {
            let ptr = self.allocate(items.len());
            items.as_ptr().copy_to_nonoverlapping(ptr, items.len());
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

#[cfg(test)]
mod tests {
    use super::Inserter;
    use crate::proputils::prop_eq;
    use alloc::{format, vec};
    use proptest::prelude::*;
    use std::fmt::Debug;
    use std::vec::Vec;

    #[test]
    fn inserter_empty() {
        let mut items = Vec::new();
        let mut ins = Inserter::new(&mut items, 1);
        ins.insert(1);
        drop(ins);
        assert_eq!(items, vec![1]);
    }

    #[test]
    fn inserter_single_pre() {
        let mut items = vec![0];
        let mut ins = Inserter::new(&mut items, 1);
        ins.move_to(0);
        ins.insert(1);
        drop(ins);
        assert_eq!(items, vec![1, 0]);
    }

    #[test]
    fn inserter_single_post() {
        let mut items = vec![0];
        let mut ins = Inserter::new(&mut items, 1);
        ins.move_to(1);
        ins.insert(1);
        drop(ins);
        assert_eq!(items, vec![0, 1]);
    }

    #[test]
    fn inserter_threes() {
        let mut items = vec![1, 2, 3];
        let mut ins = Inserter::new(&mut items, 3);
        ins.move_to(3);
        ins.insert(4);
        ins.move_to(2);
        ins.insert(5);
        ins.move_to(0);
        ins.insert(6);
        drop(ins);
        assert_eq!(items, vec![6, 1, 2, 5, 3, 4]);
    }

    #[test]
    #[should_panic]
    fn inserter_out_of_order() {
        let mut items = vec![1, 2, 3];
        let mut ins = Inserter::new(&mut items, 3);
        ins.move_to(6);
        ins.insert(0);
        ins.move_to(4);
        ins.insert(3);
    }

    #[test]
    fn inserter_threes_additional_cap() {
        let mut items = vec![1, 2, 3];
        let mut ins = Inserter::new(&mut items, 10);
        ins.move_to(3);
        ins.insert(4);
        ins.move_to(2);
        ins.insert(5);
        ins.move_to(0);
        ins.insert(6);
        drop(ins);
        assert_eq!(items, vec![6, 1, 2, 5, 3, 4]);
    }

    #[test]
    fn inserter_slices() {
        let mut items = vec![1, 2, 3];
        let mut ins = Inserter::new(&mut items, 1);
        ins.move_to(1);
        ins.insert(4);

        assert_eq!(ins.as_slices(), (&[1][..], &[4, 2, 3][..]));
        assert_eq!(ins.as_mut_slices(), (&mut [1][..], &mut [4, 2, 3][..]));
    }

    #[test]
    fn inserter_max_index() {
        let mut items = vec![1, 2, 3];
        let mut ins = Inserter::new(&mut items, 2);

        assert_eq!(ins.index(), 3);
        ins.move_to(3);
        ins.insert(4);
        assert_eq!(ins.index(), 3);
        ins.move_to(2);
        assert_eq!(ins.index(), 2);
    }

    #[test]
    #[should_panic]
    fn inserter_oob() {
        let mut items = vec![1];
        let mut ins = Inserter::new(&mut items, 1);
        ins.move_to(2);
    }

    struct NaiveInserter<'a, T> {
        vec: &'a mut Vec<T>,
        index: usize,
        remaining_inserts: usize,
    }

    impl<'a, T: Copy> NaiveInserter<'a, T> {
        fn new(vec: &mut Vec<T>, additional: usize) -> NaiveInserter<T> {
            let index = vec.len();
            NaiveInserter {
                vec,
                index,
                remaining_inserts: additional,
            }
        }

        fn index(&self) -> usize {
            self.index
        }

        fn remaining_inserts(&self) -> usize {
            self.remaining_inserts
        }

        fn insert(&mut self, item: T) {
            assert!(self.remaining_inserts > 0);
            self.vec.insert(self.index, item);
            self.remaining_inserts -= 1;
        }

        fn move_to(&mut self, index: usize) {
            assert!(index <= self.index);
            self.index = index;
        }

        fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
            self.vec.split_at_mut(self.index)
        }

        fn as_slices(&self) -> (&[T], &[T]) {
            self.vec.split_at(self.index)
        }

        fn insert_slice_copy(&mut self, slice: &[T]) {
            assert!(self.remaining_inserts >= slice.len());
            self.remaining_inserts -= slice.len();
            slice
                .iter()
                .rev()
                .copied()
                .for_each(|item| self.vec.insert(self.index, item));
        }
    }

    #[derive(Debug, Clone)]
    enum Op<T> {
        MoveTo(usize),
        Insert(T),
        InsertSlice(Vec<T>),
    }

    fn prop_strategy() -> impl Strategy<Value = (Vec<u8>, Vec<Op<u8>>, usize)> {
        proptest::collection::vec(any::<u8>(), 0..100).prop_flat_map(|base| {
            proptest::collection::vec(
                prop_oneof![
                    (0..base.len() + 1).prop_map(Op::MoveTo),
                    any::<u8>().prop_map(Op::Insert),
                    any::<Vec<u8>>().prop_map(Op::InsertSlice)
                ],
                0..100,
            )
            .prop_flat_map(move |ops| {
                let base = base.clone();
                (0..ops.len() + 1)
                    .prop_map(move |additional| (base.clone(), ops.clone(), additional))
            })
        })
    }

    fn check_equals_naive_inserter<T: Eq + Copy + Debug>(
        base: Vec<T>,
        ops: &[Op<T>],
        additional: usize,
    ) -> Result<(), TestCaseError> {
        let mut model_vec = base.clone();
        let mut model = NaiveInserter::new(&mut model_vec, additional);
        let mut tested_vec = base;
        let mut tested = Inserter::new(&mut tested_vec, additional);

        ops.iter().try_for_each(|op| {
            match op {
                &Op::MoveTo(index) => {
                    prop_eq(|| model.move_to(index), || tested.move_to(index))
                }
                Op::Insert(item) => prop_eq(
                    || model.insert(item.clone()),
                    || tested.insert(item.clone()),
                ),
                Op::InsertSlice(slice) => prop_eq(
                    || model.insert_slice_copy(slice),
                    || tested.insert_slice_copy(slice),
                ),
            }?;

            prop_assert_eq!(model.remaining_inserts(), tested.remaining_inserts());
            prop_assert_eq!(model.index(), tested.index());
            prop_assert_eq!(model.as_slices(), tested.as_slices());
            prop_assert_eq!(model.as_mut_slices(), tested.as_mut_slices());

            Ok(())
        })?;

        drop(tested);
        prop_assert_eq!(model_vec, tested_vec);

        Ok(())
    }

    proptest! {
        #[test]
        fn equals_naive_inserter((base, ops, additional) in prop_strategy()) {
            check_equals_naive_inserter(base, &ops[..], additional)?
        }
    }
}
