// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `LiveIdSet`: a compact bitmap-backed u64 set for monotonically-issued
//! LRAT clause IDs (#8599).
//!
//! Replaces `DetHashSet<u64>` in `ProofManager` (`known_lrat_ids`,
//! `backward_reserved_ids`). LRAT clause IDs are issued monotonically by
//! the proof writer, so a bitmap with a shifting `low_water` is a much
//! denser representation than a hash set.
//!
//! # Memory
//!
//! For `high` tracked IDs, this uses ~`(high - low_water)` bits. A
//! `hashbrown::HashSet<u64>` uses ~64 bits per live entry plus load-factor
//! overhead (typically 2x), so a ~100× memory reduction is realistic for
//! long LRAT proofs on top of the 64× reduction from switching from
//! 8 bytes/entry to 1 bit/entry.
//!
//! # Semantics
//!
//! Exactly mirrors `HashSet<u64>`:
//! - `insert(id)`: record `id` as live. Returns `true` if newly inserted.
//! - `remove(id)`: mark `id` as not live. Returns `true` if present.
//! - `contains(id)`: `true` iff `id` was inserted and not subsequently
//!   removed.
//!
//! Unlike the narrower design sketch in the development design notes, this
//! implementation uses a true "presence" bitmap (one bit per slot: 1=live,
//! 0=absent) rather than a "deletion" bitmap layered over an implicit
//! `[low_water, high)` range. The presence bitmap tolerates gaps in the
//! ID sequence (which do occur — e.g., the solver's `next_clause_id`
//! counter can advance ahead of `register_clause_id` calls via
//! `conflict_analysis_lrat.rs` sync points). Using a deletion bitmap
//! would cause `contains(gap_id)` to return `true` and alter hint
//! filtering in `emit_add`, which would change LRAT output bytes.
//!
//! `low_water` is advanced opportunistically by `gc()` to scan past a
//! trailing run of zero bits and truncate the bitmap. All `insert`/
//! `remove`/`contains` operations handle IDs below `low_water` as absent.

use fixedbitset::FixedBitSet;

/// Presence bitmap for monotonically-issued `u64` IDs.
///
/// Membership: `id` is in the set iff `id >= low_water &&
/// bits[id - low_water]`. IDs below `low_water` are always absent.
#[derive(Debug, Clone)]
pub(crate) struct LiveIdSet {
    /// Lowest id that may be present. All ids `< low_water` are absent
    /// by construction (they were all removed or never inserted).
    low_water: u64,
    /// `bits[i] == true` iff `low_water + i` is currently present.
    bits: FixedBitSet,
}

impl LiveIdSet {
    /// Create an empty set.
    pub(crate) fn new() -> Self {
        Self {
            low_water: 0,
            bits: FixedBitSet::new(),
        }
    }

    /// Ensure the bitmap can index `id` (relative to `low_water`).
    #[inline]
    fn ensure_capacity(&mut self, id: u64) {
        debug_assert!(id >= self.low_water, "caller must gate on low_water");
        // Relative index; fits usize because `bits.len()` is usize.
        let rel = (id - self.low_water) as usize;
        if rel >= self.bits.len() {
            // Grow with headroom to amortize repeated monotonic inserts.
            let new_len = rel
                .saturating_add(1)
                .max(self.bits.len().saturating_mul(2))
                .max(64);
            self.bits.grow(new_len);
        }
    }

    /// Insert `id`. Returns `true` if `id` was not previously present.
    pub(crate) fn insert(&mut self, id: u64) -> bool {
        if id < self.low_water {
            // Below low_water: this id was GC'd (i.e., inserted then
            // removed, causing `shrink_to_fit` to advance past it). It
            // is currently absent, so re-insertion must restore it.
            // This path is unreachable in production (LRAT IDs are
            // monotonically issued), but we handle it to preserve exact
            // `HashSet<u64>` semantics for the fuzz equivalence test.
            self.lower_low_water(id);
        }
        self.ensure_capacity(id);
        let rel = (id - self.low_water) as usize;
        if self.bits.contains(rel) {
            false
        } else {
            self.bits.insert(rel);
            true
        }
    }

    /// Prepend zero bits so that `new_low_water == id`, preserving all
    /// currently-live ids at their shifted relative positions.
    fn lower_low_water(&mut self, new_low_water: u64) {
        debug_assert!(new_low_water < self.low_water);
        let shift = (self.low_water - new_low_water) as usize;
        let new_len = self.bits.len() + shift;
        let mut new_bits = FixedBitSet::with_capacity(new_len);
        for rel in self.bits.ones() {
            new_bits.insert(rel + shift);
        }
        self.bits = new_bits;
        self.low_water = new_low_water;
    }

    /// Remove `id`. Returns `true` if `id` was present.
    pub(crate) fn remove(&mut self, id: u64) -> bool {
        if id < self.low_water {
            return false;
        }
        let rel = (id - self.low_water) as usize;
        if rel >= self.bits.len() {
            return false;
        }
        if self.bits.contains(rel) {
            self.bits.set(rel, false);
            true
        } else {
            false
        }
    }

    /// Test membership.
    #[inline]
    pub(crate) fn contains(&self, id: u64) -> bool {
        if id < self.low_water {
            return false;
        }
        let rel = (id - self.low_water) as usize;
        rel < self.bits.len() && self.bits.contains(rel)
    }

    /// Number of live ids.
    #[inline]
    #[allow(dead_code)]
    pub(crate) fn len(&self) -> usize {
        self.bits.count_ones(..)
    }

    /// True iff no ids are live.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.bits.count_ones(..) == 0
    }

    /// Remove all ids.
    #[allow(dead_code)]
    pub(crate) fn clear(&mut self) {
        self.bits.clear();
    }

    /// Release all memory and reset `low_water` to 0.
    ///
    /// This mirrors `HashSet::shrink_to(0)` and is used by
    /// `ProofManager::clear_backward_reserved_ids` after proof
    /// finalization.
    pub(crate) fn clear_and_shrink(&mut self) {
        self.low_water = 0;
        self.bits = FixedBitSet::new();
    }

    /// Reserved capacity, in bits. Used in tests and diagnostics.
    #[cfg(test)]
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.bits.len()
    }

    /// Shrink capacity toward the highest live id.
    ///
    /// Scans for trailing zero bits and truncates them, then advances
    /// `low_water` past any leading zero bits. Cheap to call
    /// opportunistically (e.g., from `shrink_to_fit`).
    pub(crate) fn shrink_to_fit(&mut self) {
        self.gc_low_water();
        self.gc_high();
    }

    /// Advance `low_water` past a leading run of zero bits.
    fn gc_low_water(&mut self) {
        let mut drop_prefix: usize = 0;
        for block in self.bits.as_slice() {
            if *block == 0 {
                drop_prefix += 32; // fixedbitset blocks are u32
            } else {
                drop_prefix += block.trailing_zeros() as usize;
                break;
            }
        }
        // Clamp to bitmap length.
        drop_prefix = drop_prefix.min(self.bits.len());
        if drop_prefix == 0 {
            return;
        }
        // Rebuild the bitmap without the dropped prefix.
        let new_len = self.bits.len() - drop_prefix;
        let mut new_bits = FixedBitSet::with_capacity(new_len);
        for rel in self.bits.ones() {
            if rel >= drop_prefix {
                new_bits.insert(rel - drop_prefix);
            }
        }
        self.bits = new_bits;
        self.low_water += drop_prefix as u64;
    }

    /// Truncate trailing zero bits.
    fn gc_high(&mut self) {
        // Find the highest set bit, truncate bits above it.
        let highest = self.bits.ones().next_back();
        let new_len = match highest {
            Some(i) => i + 1,
            None => 0,
        };
        if new_len < self.bits.len() {
            // FixedBitSet has no truncate(); rebuild with capacity.
            let mut new_bits = FixedBitSet::with_capacity(new_len);
            for rel in self.bits.ones() {
                if rel < new_len {
                    new_bits.insert(rel);
                }
            }
            self.bits = new_bits;
        }
    }
}

impl Default for LiveIdSet {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::LiveIdSet;
    use std::collections::HashSet;

    #[test]
    fn test_empty_set_is_empty() {
        let s = LiveIdSet::new();
        assert!(s.is_empty());
        assert_eq!(s.len(), 0);
        assert!(!s.contains(0));
        assert!(!s.contains(42));
    }

    #[test]
    fn test_insert_contains_remove_basic() {
        let mut s = LiveIdSet::new();
        assert!(s.insert(1));
        assert!(s.insert(2));
        assert!(!s.insert(1), "re-insert returns false");
        assert!(s.contains(1));
        assert!(s.contains(2));
        assert!(!s.contains(3));
        assert_eq!(s.len(), 2);

        assert!(s.remove(1));
        assert!(!s.remove(1), "double remove returns false");
        assert!(!s.contains(1));
        assert!(s.contains(2));
        assert_eq!(s.len(), 1);
    }

    #[test]
    fn test_contains_below_low_water_is_false() {
        let mut s = LiveIdSet::new();
        s.insert(1000);
        s.remove(1000);
        s.shrink_to_fit();
        // After gc, low_water may have advanced; ids below it must be absent.
        assert!(!s.contains(500));
        assert!(!s.contains(0));
    }

    #[test]
    fn test_shrink_to_fit_preserves_contents() {
        let mut s = LiveIdSet::new();
        for i in 100..200u64 {
            s.insert(i);
        }
        for i in 100..150u64 {
            s.remove(i);
        }
        let before_len = s.len();
        s.shrink_to_fit();
        assert_eq!(s.len(), before_len);
        for i in 150..200u64 {
            assert!(s.contains(i), "{i} should remain after gc");
        }
        for i in 100..150u64 {
            assert!(!s.contains(i), "{i} should be gone after remove+gc");
        }
    }

    #[test]
    fn test_clear_and_shrink_empties() {
        let mut s = LiveIdSet::new();
        for i in 1..=50u64 {
            s.insert(i);
        }
        s.clear_and_shrink();
        assert!(s.is_empty());
        assert_eq!(s.capacity(), 0);
        for i in 1..=50u64 {
            assert!(!s.contains(i));
        }
    }

    /// Fuzz `LiveIdSet` against `std::collections::HashSet<u64>` for
    /// equivalence on a random insert/remove/contains sequence.
    ///
    /// Uses a deterministic LCG so failures are reproducible without a
    /// rand dep. Sequence length is modest so the test runs in
    /// milliseconds.
    #[test]
    fn test_fuzz_equivalence_to_std_hashset() {
        // Seeds chosen to exercise: (a) dense low region, (b) sparse high ids,
        // (c) remove-then-reinsert, (d) GC after mass removal.
        for seed in [0xDEAD_BEEFu64, 0x1234_5678, 0xA5A5_A5A5] {
            let mut s = LiveIdSet::new();
            let mut reference: HashSet<u64> = HashSet::new();
            let mut rng = seed;
            for step in 0..10_000 {
                // LCG (Numerical Recipes constants).
                rng = rng.wrapping_mul(1_664_525).wrapping_add(1_013_904_223);
                // Keep ids in a small range so we see collisions.
                let id = (rng >> 16) % 2048;
                // Skip id 0 — the caller filters ID 0 in LRAT paths.
                if id == 0 {
                    continue;
                }
                let op = rng & 0x3;
                match op {
                    0 | 1 => {
                        // 50% insert
                        let a = s.insert(id);
                        let b = reference.insert(id);
                        assert_eq!(a, b, "seed={seed} step={step} insert({id})");
                    }
                    2 => {
                        // 25% remove
                        let a = s.remove(id);
                        let b = reference.remove(&id);
                        assert_eq!(a, b, "seed={seed} step={step} remove({id})");
                    }
                    _ => {
                        // 25% contains
                        let a = s.contains(id);
                        let b = reference.contains(&id);
                        assert_eq!(a, b, "seed={seed} step={step} contains({id})");
                    }
                }
                // Periodic GC must not change observable semantics.
                if step % 997 == 0 {
                    s.shrink_to_fit();
                    assert_eq!(s.len(), reference.len());
                }
            }
            assert_eq!(s.len(), reference.len(), "final len mismatch seed={seed}");
            for &id in &reference {
                assert!(s.contains(id), "seed={seed} missing id={id}");
            }
        }
    }
}
