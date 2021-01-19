# scanmut

Insert or remove multiple elements from a `Vec` in `O(n)` time.

This crate provides two types for versatile and efficient `Vec` mutation; `Inserter` and
`Remover`. These two types can be seen as more generic implementations of `Vec::insert` and
`Vec::drain`, allowing you to for example efficiently insert a slice, conditionally drain
elements, or access elements of a `Vec` while draining from it.

`Inserter` and `Remover` requires an ordering of the insert and removal indices; monotonically
non-increasing for `Inserter` and monotonically increasing for `Remover`.

For convenience, there are also extension traits adding common higher level operations using the
`Inserter` and `Remover`. See `ScanMut`, `InsertSliceClone`, and `InsertSliceCopy`.

## Examples

Inserting a slice into a vec using [ScanMut::insert_all]:

```rust
use scanmut::prelude::*;

let mut v = vec!['a', 'b', 'c'];
v.insert_all(1, ['d', 'e'].iter().cloned());
assert_eq!(v, vec!['a', 'd', 'e', 'b', 'c']);
```

Removing multiple elements in one scan using [ScanMut::multi_remove]:

```rust
use scanmut::prelude::*;

let mut v = vec!['a', 'b', 'c'];
v.multi_remove([0, 2].iter().cloned(), drop);
assert_eq!(v, vec!['b']);
```

License: MIT
