use alloc::vec::Vec;
use core as std;

/// An object that can remove multiple elements from a [Vec] in a single scan through the [Vec].
///
/// The [Remover] has a position in the [Vec] at which it inserts, called the index. Initially, the
/// index is at the **start** of the [Vec]. This index can only be moved further towards end of the
/// [Vec], meaning that the indices of the removed objects must be monotonically increasing
/// (i.e. the next index must be larger than the previous index).
///
/// Dropping the [Remover] without using the entire insertion capacity has a runtime cost
/// proportional to the size of the merged elements. Dropping after using the entire insertion
/// capacity has no runtime cost.
///
/// Leaking the [Remover] (through [std::mem::forget] or similar) may leak some items of the [Vec]
/// and will leave the [Vec] in an unspecified but valid state
///
/// # Example
///
/// ```
/// use scanmut::Remover;
///
/// let mut items = vec!['a', 'b', 'c'];
///
/// let mut remover = Remover::new(&mut items);
///
/// assert_eq!(remover.index(), 0); // Initial index is at start of the vec
/// assert_eq!(remover.remove(), 'a');
///
/// assert_eq!(remover.index(), 1);  // Removing an element increments the index
/// remover.move_to(2);
///
/// assert_eq!(remover.index(), 2);
/// assert_eq!(remover.remove(), 'c');
///
/// assert_eq!(remover.index(), 3);
///
/// drop(remover);
///
/// assert_eq!(items, ['b']);
/// ```
///
/// As calling [Remover::remove] will increment the index, it can be used to remove items in a row:
///
/// ```
/// use scanmut::Remover;
///
/// let mut items = vec!['a', 'b', 'c', 'd'];
///
/// let mut remover = Remover::new(&mut items);
///
/// remover.move_to(1);
/// assert_eq!(remover.remove(), 'b');
/// assert_eq!(remover.remove(), 'c');
/// drop(remover);
///
/// assert_eq!(items, ['a', 'd']);
/// ```
#[derive(Debug)]
pub struct Remover<'a, T> {
    // The remover works by keeping a "gap" of uninitialized values. This gap is initially
    // of length zero and at the start of the vec, and moves up through the vec as we remove elements,
    // increasing in size by one each time we remove an element.
    //
    // The fields have the following invariant:
    //     vec.len() <= unfiltered_start <= unfiltered_end <= vec.capacity()
    //
    // Where
    //     [0,vec.len()[                      are the filtered elements
    //     [vec.len(),unfiltered_start[       is a gap of uninitialized values
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

    /// The current index of this remover.
    #[inline]
    pub fn index(&self) -> usize {
        self.unfiltered_start
    }

    /// Returns a reference to the item at the current index or `None` if the remover is past the
    /// end of the underlying `Vec`.
    #[inline]
    pub fn current(&self) -> Option<&T> {
        if self.unfiltered_start < self.unfiltered_end {
            unsafe { Some(&*self.vec.as_ptr().add(self.unfiltered_start)) }
        } else {
            None
        }
    }

    /// Returns a mutable reference to the item at the current index or `None` if the remover is
    /// past the end of the underlying `Vec`.
    #[inline]
    pub fn current_mut(&mut self) -> Option<&mut T> {
        if self.unfiltered_start < self.unfiltered_end {
            unsafe { Some(&mut *self.vec.as_mut_ptr().add(self.unfiltered_start)) }
        } else {
            None
        }
    }

    /// Returns a pair of slices representing the current state of the `Vec` being removed from.
    ///
    /// The first slice is the part of the `Vec` below the index. The second slice is the part of
    /// the `Vec` above or equal to the index.
    #[inline]
    pub fn as_slices(&self) -> (&[T], &[T]) {
        unsafe {
            (
                &self.vec[..],
                std::slice::from_raw_parts(
                    self.vec.as_ptr().add(self.unfiltered_start),
                    self.unfiltered_end - self.unfiltered_start,
                ),
            )
        }
    }

    /// Returns a pair of mutable slices representing the current state of the `Vec` being removed
    /// from.
    ///
    /// The first slice is the part of the `Vec` below the index. The second slice is the part of
    /// the `Vec` above or equal to the index.
    #[inline]
    pub fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
        unsafe {
            (
                std::slice::from_raw_parts_mut(self.vec.as_mut_ptr(), self.vec.len()),
                std::slice::from_raw_parts_mut(
                    self.vec.as_mut_ptr().add(self.unfiltered_start),
                    self.unfiltered_end - self.unfiltered_start,
                ),
            )
        }
    }

    /// Moves this `Remover` to the given index in the `Vec`.
    ///
    /// # Panics
    ///
    /// Panics if the index is less than or equal to the current index.
    #[inline]
    pub fn move_to(&mut self, index: usize) {
        assert!(index <= self.unfiltered_end, "Index out of bounds");

        let copy_len = index
            .checked_sub(self.unfiltered_start)
            .expect("Index must be larger than previous index");

        unsafe {
            let ptr = self.vec.as_mut_ptr();

            ptr.add(self.unfiltered_start)
                .copy_to(ptr.add(self.vec.len()), copy_len);

            self.vec.set_len(self.vec.len() + copy_len);
            self.unfiltered_start = index;
        }
    }

    /// Removes an element from the `Vec` at the current index.
    ///
    /// This also increments the index to the next position.
    ///
    /// # Panics
    ///
    /// Panics if the index is at the end of the vec.
    #[inline]
    pub fn remove(&mut self) -> T {
        assert!(
            self.unfiltered_start < self.unfiltered_end,
            "Removing out of bounds"
        );

        unsafe {
            let item = self.vec.as_mut_ptr().add(self.unfiltered_start).read();
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

#[cfg(test)]
mod tests {
    use super::Remover;
    use crate::proputils::prop_eq;
    use alloc::{format, vec};
    use proptest::prelude::*;
    use std::fmt::Debug;
    use std::vec::Vec;

    #[test]
    fn remover_empty() {
        let mut items: Vec<usize> = Vec::new();
        Remover::new(&mut items);
        assert_eq!(items, vec![]);
    }

    #[test]
    fn remover_single() {
        let mut items = vec![1];
        assert_eq!(Remover::new(&mut items).remove(), 1);
        assert_eq!(items, vec![]);
    }

    #[test]
    fn remover_two_first() {
        let mut items = vec![1, 2];
        assert_eq!(Remover::new(&mut items).remove(), 1);
        assert_eq!(items, vec![2]);
    }

    #[test]
    fn remover_two_second() {
        let mut items = vec![1, 2];
        let mut rem = Remover::new(&mut items);
        rem.move_to(1);
        assert_eq!(rem.remove(), 2);
        drop(rem);
        assert_eq!(items, vec![1]);
    }

    #[test]
    fn remover_two_both() {
        let mut items = vec![1, 2];
        let mut rem = Remover::new(&mut items);
        rem.move_to(0);
        assert_eq!(rem.remove(), 1);
        rem.move_to(1);
        assert_eq!(rem.remove(), 2);
        drop(rem);
        assert_eq!(items, vec![]);
    }

    #[test]
    #[should_panic]
    fn remover_two_out_of_order() {
        let mut items = vec![1, 2];
        let mut remover = Remover::new(&mut items);
        remover.move_to(1);
        assert_eq!(remover.remove(), 2);
        remover.move_to(0)
    }

    #[test]
    #[should_panic]
    fn remover_out_of_bounds() {
        drop(Remover::new(&mut vec![1, 2]).move_to(3));
    }

    #[test]
    #[should_panic]
    fn remover_advance_out_of_bounds() {
        Remover::new(&mut vec![1, 2]).move_to(4);
    }

    #[test]
    fn remover_advance_one_past() {
        let mut items = vec![1, 2];
        let mut rem = Remover::new(&mut items);
        rem.move_to(2);
        assert_eq!(rem.index(), 2);
    }

    #[test]
    fn remover_slices() {
        let mut items = vec![1, 2, 3, 4];
        let mut rem = Remover::new(&mut items);
        rem.move_to(2);
        assert_eq!(rem.remove(), 3);
        assert_eq!(rem.as_slices(), (&[1, 2][..], &[4][..]));
        assert_eq!(rem.as_mut_slices(), (&mut [1, 2][..], &mut [4][..]));
    }

    #[test]
    fn remover_index() {
        let mut items = vec![1, 2, 3, 4];
        let mut remover = Remover::new(&mut items);
        assert_eq!(remover.index(), 0);
        remover.move_to(1);
        assert_eq!(remover.remove(), 2);
        assert_eq!(remover.index(), 2);
        remover.move_to(3);
        assert_eq!(remover.index(), 3);
    }

    struct NaiveRemover<'a, T> {
        vec: &'a mut Vec<T>,
        old_index: usize,
        new_index: usize,
    }

    impl<'a, T> NaiveRemover<'a, T> {
        fn new(vec: &mut Vec<T>) -> NaiveRemover<T> {
            NaiveRemover {
                vec,
                old_index: 0,
                new_index: 0,
            }
        }

        fn index(&self) -> usize {
            self.old_index
        }

        fn current(&self) -> Option<&T> {
            self.vec.get(self.new_index)
        }

        fn remove(&mut self) -> T {
            let item = self.vec.remove(self.new_index);
            self.old_index += 1;
            item
        }

        fn move_to(&mut self, index: usize) {
            self.new_index += index.checked_sub(self.old_index).unwrap();
            self.old_index = index;
        }

        fn as_mut_slices(&mut self) -> (&mut [T], &mut [T]) {
            self.vec.split_at_mut(self.new_index)
        }

        fn as_slices(&self) -> (&[T], &[T]) {
            self.vec.split_at(self.new_index)
        }
    }

    #[derive(Debug, Clone)]
    enum Op {
        MoveTo(usize),
        Remove,
    }

    fn prop_strategy() -> impl Strategy<Value = (Vec<u8>, Vec<Op>)> {
        proptest::collection::vec(any::<u8>(), 0..100).prop_flat_map(|base| {
            proptest::collection::vec(
                prop_oneof![(0..base.len() + 1).prop_map(Op::MoveTo), Just(Op::Remove)],
                0..100,
            )
            .prop_map(move |ops| (base.clone(), ops))
        })
    }

    fn check_equals_naive_remover<T: Eq + Clone + Debug>(
        base: Vec<T>,
        ops: &[Op],
    ) -> Result<(), TestCaseError> {
        let mut model_vec = base.clone();
        let mut model = NaiveRemover::new(&mut model_vec);
        let mut tested_vec = base;
        let mut tested = Remover::new(&mut tested_vec);

        ops.iter().try_for_each(|op| {
            match op {
                &Op::MoveTo(index) => {
                    prop_eq(|| model.move_to(index), || tested.move_to(index))
                }
                Op::Remove => prop_eq(|| model.remove(), || tested.remove()),
            }?;

            prop_assert_eq!(model.current(), tested.current());
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
        fn equals_naive_remover((base, ops) in prop_strategy()) {
            check_equals_naive_remover(base, &ops[..])?
        }
    }
}
