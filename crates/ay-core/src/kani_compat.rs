// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deterministic hash map and set aliases.
//!
//! #8529: hashbrown 0.15 uses foldhash::fast::RandomState by default, which
//! seeds from ASLR + time + allocator address. This makes HashMap/HashSet
//! iteration order non-deterministic across process runs. For an SMT solver,
//! non-deterministic iteration order in theory propagation, bound axiom
//! generation, and atom processing causes non-deterministic solving paths —
//! some of which miss required theory conflicts, producing false-SAT results.
//!
//! Fix: use foldhash::fast::FixedState which uses a compile-time-fixed global
//! seed. Iteration order is still arbitrary but DETERMINISTIC across runs.
//!
//! The module and its `Kani*` aliases keep their historical names because ay's
//! crates and its consumers import them; there is no model-checking variant.
//!
//! # Usage
//!
//! ```rust
//! use ay_core::kani_compat::{DetHashMap, DetHashSet, det_hash_map_new, det_hash_set_new};
//!
//! let mut map: DetHashMap<u32, u32> = det_hash_map_new();
//! map.insert(1, 2);
//!
//! let mut set: DetHashSet<u32> = det_hash_set_new();
//! set.insert(1);
//!
//! assert_eq!(map.get(&1), Some(&2));
//! assert!(set.contains(&1));
//! ```

/// Deterministic map type: hashbrown with fixed hash seed for reproducible
/// iteration order across process runs.
pub type DetHashMap<K, V> = hashbrown::HashMap<K, V, foldhash::fast::FixedState>;

/// Deterministic set type: hashbrown with fixed hash seed for reproducible
/// iteration order across process runs.
pub type DetHashSet<T> = hashbrown::HashSet<T, foldhash::fast::FixedState>;

/// Alias for `DetHashMap` (historical name).
pub type KaniHashMap<K, V> = DetHashMap<K, V>;

/// Alias for `DetHashSet` (historical name).
pub type KaniHashSet<T> = DetHashSet<T>;

/// Create an empty `DetHashMap`.
#[inline]
pub fn det_hash_map_new<K, V>() -> DetHashMap<K, V> {
    Default::default()
}

/// Create a `DetHashMap` with pre-allocated capacity.
#[inline]
pub fn det_hash_map_with_capacity<K, V>(capacity: usize) -> DetHashMap<K, V> {
    hashbrown::HashMap::with_capacity_and_hasher(capacity, foldhash::fast::FixedState::default())
}

/// Create an empty `DetHashSet`.
#[inline]
pub fn det_hash_set_new<T>() -> DetHashSet<T> {
    Default::default()
}

/// Create a `DetHashSet` with pre-allocated capacity.
#[inline]
pub fn det_hash_set_with_capacity<T>(capacity: usize) -> DetHashSet<T> {
    hashbrown::HashSet::with_capacity_and_hasher(capacity, foldhash::fast::FixedState::default())
}
