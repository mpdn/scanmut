# scanmut

Insert and remove multiple elments from a `Vec` in `O(n)` time.

This crate provides the `Inserter` and `Remover` types for inserting and removing items from a
`Vec` in a single scan over the `Vec`. The indices of the insertions and removals need to be in
sorted order: monotnonically non-increasing for `Inserter` and monotonically increasing for
`Remover`. See the `Inserter` and `Remover` types for more information.

For convenience, there is also an extension trait `ScanMut` that add `multi_insert` and
`multi_remove` methods to `Vec`.

## Example

```rust
use scanmut::ScanMut;

let mut v = vec!['a', 'b', 'c'];
v.multi_insert([(2, 'e'), (1, 'd')].iter().cloned());

assert_eq!(v, vec!['a', 'd', 'b', 'e', 'c']);
```

License: MIT
