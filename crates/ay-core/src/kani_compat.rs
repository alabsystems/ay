// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani-compatible type aliases for HashMap and HashSet.
//!
//! Under `#[cfg(kani)]`, CBMC cannot handle `hashbrown::RawTable` operations
//! (SIMD, pointer arithmetic, `getrandom`). This module provides alternatives:
//!
//! - **Kani builds**: `BTreeMap`/`BTreeSet` — no unsafe, fully CBMC-compatible.
//!   Keys must implement `Ord` (all ay key types do).
//! - **Normal builds**: `hashbrown::HashMap`/`HashSet` — full performance.
//!
//! This unblocks 39+ Kani harnesses that were previously intractable due to
//! hashbrown internals. See ay #5979.
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

// ── cfg(kani): BTreeMap/BTreeSet ──────────────────────────────────────────────

#[cfg(kani)]
/// Kani-compatible map type (BTreeMap under CBMC, hashbrown::HashMap otherwise).
pub type DetHashMap<K, V> = std::collections::BTreeMap<K, V>;

#[cfg(kani)]
/// Kani-compatible set type (BTreeSet under CBMC, hashbrown::HashSet otherwise).
pub type DetHashSet<T> = std::collections::BTreeSet<T>;

// ── cfg(not(kani)): hashbrown with FixedState ────────────────────────────────
//
// #8529: hashbrown 0.15 uses foldhash::fast::RandomState by default, which
// seeds from ASLR + time + allocator address. This makes HashMap/HashSet
// iteration order non-deterministic across process runs. For an SMT solver,
// non-deterministic iteration order in theory propagation, bound axiom
// generation, and atom processing causes non-deterministic solving paths —
// some of which miss required theory conflicts, producing false-SAT results.
//
// Fix: use foldhash::fast::FixedState which uses a compile-time-fixed global
// seed. Iteration order is still arbitrary but DETERMINISTIC across runs.

#[cfg(not(kani))]
/// Deterministic map type: hashbrown with fixed hash seed for reproducible
/// iteration order across process runs. Under CBMC/Kani, uses BTreeMap.
pub type DetHashMap<K, V> = hashbrown::HashMap<K, V, foldhash::fast::FixedState>;

#[cfg(not(kani))]
/// Deterministic set type: hashbrown with fixed hash seed for reproducible
/// iteration order across process runs. Under CBMC/Kani, uses BTreeSet.
pub type DetHashSet<T> = hashbrown::HashSet<T, foldhash::fast::FixedState>;

// ── Legacy aliases (origin/main naming) ───────────────────────────────────────

/// Alias for `DetHashMap` — matches the `KaniHashMap` naming from ay-core's
/// initial kani_compat module.
pub type KaniHashMap<K, V> = DetHashMap<K, V>;

/// Alias for `DetHashSet` — matches the `KaniHashSet` naming from ay-core's
/// initial kani_compat module.
pub type KaniHashSet<T> = DetHashSet<T>;

// ── Constructor helpers (API compatibility) ───────────────────────────────────

/// Create an empty `DetHashMap`.
#[inline]
pub fn det_hash_map_new<K, V>() -> DetHashMap<K, V>
where
    K: Ord,
{
    Default::default()
}

/// Create a `DetHashMap` with pre-allocated capacity.
///
/// Under Kani (BTreeMap), capacity is ignored since BTreeMap does not
/// pre-allocate. Under normal builds, uses hashbrown's `with_capacity`
/// with a fixed hash seed for deterministic iteration order.
#[inline]
pub fn det_hash_map_with_capacity<K, V>(capacity: usize) -> DetHashMap<K, V>
where
    K: Ord + std::hash::Hash + Eq,
{
    #[cfg(kani)]
    {
        let _ = capacity;
        std::collections::BTreeMap::new()
    }
    #[cfg(not(kani))]
    {
        hashbrown::HashMap::with_capacity_and_hasher(
            capacity,
            foldhash::fast::FixedState::default(),
        )
    }
}

/// Create an empty `DetHashSet`.
#[inline]
pub fn det_hash_set_new<T>() -> DetHashSet<T>
where
    T: Ord,
{
    Default::default()
}

/// Create a `DetHashSet` with pre-allocated capacity.
///
/// Under Kani (BTreeSet), capacity is ignored. Under normal builds,
/// uses hashbrown's `with_capacity` with a fixed hash seed for
/// deterministic iteration order.
#[inline]
pub fn det_hash_set_with_capacity<T>(capacity: usize) -> DetHashSet<T>
where
    T: Ord + std::hash::Hash + Eq,
{
    #[cfg(kani)]
    {
        let _ = capacity;
        std::collections::BTreeSet::new()
    }
    #[cfg(not(kani))]
    {
        hashbrown::HashSet::with_capacity_and_hasher(
            capacity,
            foldhash::fast::FixedState::default(),
        )
    }
}
