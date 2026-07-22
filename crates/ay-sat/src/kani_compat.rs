// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani-compatible type aliases for HashMap and HashSet (ay-sat local).
//!
//! Under `#[cfg(kani)]`, uses `BTreeMap`/`BTreeSet` to avoid CBMC-intractable
//! `hashbrown::RawTable` operations. Under normal builds, uses `hashbrown`
//! with `foldhash::fast::FixedState` for deterministic iteration order.
//!
//! #8529: Previously used `std::collections::HashMap`/`HashSet` which delegate
//! to `hashbrown` with `foldhash::fast::RandomState`. RandomState seeds from
//! ASLR + time + allocator addresses, making HashMap/HashSet iteration order
//! non-deterministic across process runs. For an SMT solver, this causes
//! non-deterministic solving paths — some of which miss required theory
//! conflicts, producing false-SAT results.
//!
//! Fix: use `hashbrown` with `foldhash::fast::FixedState` (compile-time-fixed
//! global seed), matching ay-core's `kani_compat` module.
//!
//! See also: `ay_core::kani_compat` for the shared cross-crate version.

// ── cfg(kani): BTreeMap/BTreeSet ──────────────────────────────────────────────

#[cfg(kani)]
pub(crate) type DetHashMap<K, V> = std::collections::BTreeMap<K, V>;
#[cfg(kani)]
pub(crate) type DetHashSet<T> = std::collections::BTreeSet<T>;

// ── cfg(not(kani)): hashbrown with FixedState ────────────────────────────────

#[cfg(not(kani))]
pub(crate) type DetHashMap<K, V> = hashbrown::HashMap<K, V, foldhash::fast::FixedState>;
#[cfg(not(kani))]
pub(crate) type DetHashSet<T> = hashbrown::HashSet<T, foldhash::fast::FixedState>;

// ── Constructor helpers ───────────────────────────────────────────────────────

/// Create an empty `DetHashSet`.
///
/// Under Kani, `HashSet::new()` may be unavailable for custom hashers.
/// `Default::default()` works for all backends.
#[inline]
pub(crate) fn det_hash_set_new<T>() -> DetHashSet<T>
where
    T: Ord,
{
    Default::default()
}

/// Create a `DetHashSet` with pre-allocated capacity.
#[inline]
pub(crate) fn det_hash_set_with_capacity<T>(capacity: usize) -> DetHashSet<T>
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
