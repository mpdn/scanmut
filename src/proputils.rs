use proptest::prelude::*;

/// Compares the result of two closures.
///
/// Results are considered equal if both panic.
pub fn prop_eq<T: Eq + std::fmt::Debug>(
    model: impl FnOnce() -> T,
    tested: impl FnOnce() -> T,
) -> Result<(), TestCaseError> {
    use alloc::format;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    let a = catch_unwind(AssertUnwindSafe(|| model()));
    let b = catch_unwind(AssertUnwindSafe(|| tested()));

    prop_assert_eq!(a.is_ok(), b.is_ok(), "{:?},{:?}", a, b);

    if let (Ok(a), Ok(b)) = (a, b) {
        prop_assert_eq!(a, b);
    }
    
    Ok(())
}
