# Wait-free atomic shared pointer
This repository contains an implementations of atomic shared pointers, thread-safe mutable reference-counted variables, in C++ and Rust.
Such variables or mutable cells require special handling for read-reclaim races,
where a read of a mutable variable races with a write that deallocates the old value.
Use-after-free errors occur if the object is deallocated by the writing thread before the reading thread can increment the reference count.
Existing solutions are not wait-free,
have a space overhead (with delayed reclamation)
and/or take time linear in the number of threads for stores.

We introduce an implementation for concurrent reference counting with no delayed reclamation, which is wait-free, easy to implement and fast in practice. *Writes* operate in constant time and
*reads* usually in constant time, and in the worst-case, linear with respect to the number
of threads that actually work with the variable. Our algorithm is based on the *split reference count* technique, which is used in production but is only lock-free.

## Terminology
A shared pointer in C++ and Arc in Rust is an immutable pointer to a reference-counted object.
An atomic shared pointer in C++ and ArcCell in Rust is a mutable variable or cell containing a shared pointer. Concurrent reads and writes are allowed.
(Im)mutability refers to the (in)ability to modify the pointer, we don't consider whether it is allowed to update fields of the object.

In C++, all these types allow null values. In Rust, null values are not allowed. OptionalArcCell is similar to ArcCell, but supports null values (or actually, it stores an `Option<Arc<T>>`).

## Code
File `cpp/atomic_shared_ptr.h` contains the C++ implementation and `rust/src/arc.rs` has the Rust version.
Both implementations have some very basic test code, which runs via `cd cpp; sh test.sh` and `cd rust; cargo run`.

## Benchmarks
Benchmarks to compare our atomic shared pointers with other implementations in C++ can be found at [thetazero/atomic_shared_ptr_benchmarks](https://github.com/thetazero/atomic_shared_ptr_benchmarks).
