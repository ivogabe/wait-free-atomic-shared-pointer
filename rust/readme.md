# Wait-free atomically mutable Arc

This repository contains an implementation of an atomically mutable cell containing a pointer to a reference-counted object, in Rust.
An `Arc`, as present in the standard library of Rust, is a reference to a reference-counted object. This is similar to `shared_ptr` in C++.
The `Arc` itself is immutable. This can be made mutable by wrapping it in a `Mutex`, but that introduces locks.
This repository introduces an `AtomicArc`
(open for discussion for the name, but `AtomicArc` or `ArcCell` would be consistent with other mutable objects in the standard library)
which does allows updates in a thread-safe way. This is similar to `atomic<shared_ptr<T>>` in C++.

Existing approaches for mutable shared pointers to reference-counted objects are at best lock-free.
The implementation in this repository is wait-free.

## Implementation details
Note that the reference count of a reference-counted object is stored together with the object in Rust (see `ArcObject` in `src/arc.rs`),
whereas this is stored separately in a control block in C++.

`AtomicArcInternal` (in `src/arc.rs`) provides the actual implementation of the proposed solution.
`AtomicArc` and `AtomicOptionalArc` wrap this in a type-safe implementations that are respectively non-nullable and nullable.
