// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic hash map and set aliases (ay-sat local).
//!
//! #8529: Previously used `std::collections::HashMap`/`HashSet` which delegate
//! to `hashbrown` with `foldhash::fast::RandomState`. RandomState seeds from
//! ASLR + time + allocator addresses, making HashMap/HashSet iteration order
//! non-deterministic across process runs. For an SMT solver, this causes
//! non-deterministic solving paths — some of which miss required theory
//! conflicts, producing false-SAT results.
//!
//! Fix: use `hashbrown` with `foldhash::fast::FixedState` (compile-time-fixed
//! global seed), matching ay-core's `kani_compat` module. The module keeps its
//! historical name; it no longer has a model-checking variant.

pub(crate) type DetHashMap<K, V> = hashbrown::HashMap<K, V, foldhash::fast::FixedState>;
pub(crate) type DetHashSet<T> = hashbrown::HashSet<T, foldhash::fast::FixedState>;

/// Create an empty `DetHashSet`.
#[inline]
pub(crate) fn det_hash_set_new<T>() -> DetHashSet<T> {
    Default::default()
}

/// Create a `DetHashSet` with pre-allocated capacity.
#[inline]
pub(crate) fn det_hash_set_with_capacity<T>(capacity: usize) -> DetHashSet<T> {
    hashbrown::HashSet::with_capacity_and_hasher(capacity, foldhash::fast::FixedState::default())
}
