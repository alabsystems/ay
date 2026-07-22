// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Component cache: canonical component keys mapped to exact counts, with a
//! DFS **watermark purge** for learned-clause cache pollution.
//!
//! Keys are delta-varint encodings of `(sorted vars, sorted clause ids)` —
//! see the soundness note in [`crate::engine`] for why this pair uniquely
//! determines the residual formula.
//!
//! Entries are append-only in STAMP order, so creation stamps are
//! DFS-contiguous per search branch: every entry finalized between a branch's
//! start and end belongs to that branch's recursion subtree. `purge_since
//! (mark)` therefore deletes exactly the pollution set sharpSAT computes via
//! its father/descendant forest (see `learning-pollution-spec.md` §4.4): on
//! any zero branch, all entries created inside the branch window are dropped
//! before the branch exits.
//!
//! Eviction (memory budget) tombstones the oldest live entries and then
//! COMPACTS the tombstoned prefix out of the slot vector, sliding `base`
//! forward so outstanding stamps stay valid (stamps are ABSOLUTE creation
//! indices: `base + slots.len()`). Deleting cache entries is always sound.
//! The compaction matters: an earlier revision kept every evicted key alive
//! in the append-only vector while SUBTRACTING its bytes from the budget
//! accounting, so once eviction engaged, real memory grew at the raw
//! key-insert rate with the budget none the wiser (a prime contributor to
//! the 2026-07-10 machine panic — 60s timeout runs ballooning to many GB).
//!
//! The key bytes are stored ONCE: `CompKey` wraps `Arc<[u8]>`, so the
//! hashmap's copy of the key is a refcount bump, not a second heap copy of a
//! 20–300KB encoding (dense components produce keys that large).

use std::sync::Arc;

use rustc_hash::FxHashMap;

use crate::value::CountValue;

/// Canonical component key (delta-varint packed vars + clause ids).
/// Cheap to clone: the encoding is behind an `Arc`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct CompKey(Arc<[u8]>);

impl CompKey {
    /// Encode sorted variable ids and sorted clause ids.
    ///
    /// Both slices MUST be sorted ascending (the delta encoding relies on it);
    /// the engine's component discovery sorts both before calling.
    pub fn encode(vars: &[u32], clauses: &[u32]) -> Self {
        debug_assert!(vars.windows(2).all(|w| w[0] < w[1]));
        debug_assert!(clauses.windows(2).all(|w| w[0] < w[1]));
        let mut buf = Vec::with_capacity(4 + vars.len() * 2 + clauses.len() * 2);
        push_varint(&mut buf, vars.len() as u64);
        let mut prev = 0u32;
        for &v in vars {
            push_varint(&mut buf, u64::from(v - prev));
            prev = v;
        }
        prev = 0;
        for &c in clauses {
            push_varint(&mut buf, u64::from(c - prev));
            prev = c;
        }
        CompKey(Arc::from(buf))
    }

    fn bytes(&self) -> usize {
        self.0.len()
    }
}

fn push_varint(buf: &mut Vec<u8>, mut x: u64) {
    loop {
        let byte = (x & 0x7f) as u8;
        x >>= 7;
        if x == 0 {
            buf.push(byte);
            return;
        }
        buf.push(byte | 0x80);
    }
}

/// Approximate per-entry bookkeeping bytes beyond key + value payloads: the
/// hashmap node (key handle + stamp + hash-table slack), the slot vector's
/// `Option<(CompKey, W)>`, and the `Arc` header.
const ENTRY_OVERHEAD: usize = 96;

/// Component cache with watermark purging and byte-budget eviction.
///
/// `slots[i]` holds the entry with absolute stamp `base + i`; `None` marks a
/// slot tombstoned by eviction (key AND value dropped — only the slot itself
/// survives until the next compaction).
pub struct CompCache<W> {
    /// Absolute creation stamps (never reused; monotone across compactions).
    map: FxHashMap<CompKey, u64>,
    slots: Vec<Option<(CompKey, W)>>,
    /// Absolute stamp of `slots[0]`.
    base: u64,
    live_bytes: usize,
    budget: usize,
    /// Slots below this index are all tombstoned (eviction frontier).
    evict_cursor: usize,
    /// Total tombstoned by eviction (stats).
    pub evictions: u64,
    /// Total removed by pollution purges (stats).
    pub purged: u64,
}

impl<W: CountValue> CompCache<W> {
    /// Create a cache with the given approximate byte budget.
    pub fn new(budget_bytes: usize) -> Self {
        Self {
            map: FxHashMap::default(),
            slots: Vec::new(),
            base: 0,
            live_bytes: 0,
            budget: budget_bytes.max(1 << 20),
            evict_cursor: 0,
            evictions: 0,
            purged: 0,
        }
    }

    /// Current creation stamp (for branch watermarks).
    pub fn stamp(&self) -> u64 {
        self.base + self.slots.len() as u64
    }

    /// Look up a component count.
    pub fn get(&self, key: &CompKey) -> Option<W> {
        let &stamp = self.map.get(key)?;
        debug_assert!(stamp >= self.base, "map entry below eviction base");
        let (_, value) = self.slots[(stamp - self.base) as usize]
            .as_ref()
            .expect("mapped slot is live");
        Some(value.clone())
    }

    /// Insert a finalized component count.
    pub fn put(&mut self, key: CompKey, value: W) {
        self.live_bytes += key.bytes() + value.approx_bytes() + ENTRY_OVERHEAD;
        let stamp = self.stamp();
        self.map.insert(key.clone(), stamp);
        self.slots.push(Some((key, value)));
        if self.live_bytes > self.budget {
            self.evict_oldest_half();
        }
    }

    /// Delete every entry created at or after `mark` (the pollution purge).
    ///
    /// A `mark` below `base` is valid: every slot the window would cover
    /// below `base` was already evicted (always sound), and every remaining
    /// slot has a stamp `>= base > mark`, so all of them are dropped.
    pub fn purge_since(&mut self, mark: u64) {
        // Slots to keep: those with stamps below `mark`. A mark below `base`
        // keeps nothing (everything remaining is younger than the mark).
        let keep = usize::try_from(mark.saturating_sub(self.base)).unwrap_or(usize::MAX);
        while self.slots.len() > keep {
            let slot = self.slots.pop().expect("len > keep implies non-empty");
            if let Some((key, value)) = slot {
                self.live_bytes = self
                    .live_bytes
                    .saturating_sub(key.bytes() + value.approx_bytes() + ENTRY_OVERHEAD);
                self.map.remove(&key);
                self.purged += 1;
            }
        }
        self.evict_cursor = self.evict_cursor.min(self.slots.len());
    }

    /// Evict the oldest live entries until half the byte budget is free, then
    /// compact the fully-tombstoned prefix so the freed keys, values, AND
    /// slots are actually returned to the allocator.
    fn evict_oldest_half(&mut self) {
        let target = self.budget / 2;
        while self.live_bytes > target && self.evict_cursor < self.slots.len() {
            let idx = self.evict_cursor;
            self.evict_cursor += 1;
            if let Some((key, value)) = self.slots[idx].take() {
                self.live_bytes = self
                    .live_bytes
                    .saturating_sub(key.bytes() + value.approx_bytes() + ENTRY_OVERHEAD);
                self.map.remove(&key);
                self.evictions += 1;
            }
        }
        // Slide the window: stamps are absolute, so dropping the tombstoned
        // prefix only moves `base`; outstanding watermarks stay valid.
        if self.evict_cursor > 0 {
            self.slots.drain(..self.evict_cursor);
            self.base += self.evict_cursor as u64;
            self.evict_cursor = 0;
        }
    }

    /// Number of live entries.
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// True when the cache holds no live entries.
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    /// Total slots currently held (live + tombstoned); test-only visibility
    /// for the compaction guarantee.
    #[cfg(test)]
    fn slot_count(&self) -> usize {
        self.slots.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigUint;

    #[test]
    fn key_roundtrip_distinct() {
        let a = CompKey::encode(&[1, 5, 9], &[0, 3]);
        let b = CompKey::encode(&[1, 5, 9], &[0, 4]);
        let c = CompKey::encode(&[1, 5], &[0, 3, 9]);
        assert_ne!(a, b);
        assert_ne!(a, c);
        assert_eq!(a, CompKey::encode(&[1, 5, 9], &[0, 3]));
    }

    #[test]
    fn key_length_prefix_separates_vars_from_clauses() {
        // Same flattened sequence, different var/clause split.
        let a = CompKey::encode(&[1, 2], &[3]);
        let b = CompKey::encode(&[1, 2, 3], &[]);
        assert_ne!(a, b);
    }

    #[test]
    fn watermark_purge_removes_exactly_the_window() {
        let mut cache: CompCache<BigUint> = CompCache::new(1 << 22);
        let k1 = CompKey::encode(&[1], &[0]);
        let k2 = CompKey::encode(&[2], &[1]);
        let k3 = CompKey::encode(&[3], &[2]);
        cache.put(k1.clone(), BigUint::from(1u32));
        let mark = cache.stamp();
        cache.put(k2.clone(), BigUint::from(2u32));
        cache.put(k3.clone(), BigUint::from(3u32));
        cache.purge_since(mark);
        assert_eq!(cache.get(&k1), Some(BigUint::from(1u32)));
        assert_eq!(cache.get(&k2), None);
        assert_eq!(cache.get(&k3), None);
        assert_eq!(cache.purged, 2);
        // Re-inserting after a purge works.
        cache.put(k2.clone(), BigUint::from(5u32));
        assert_eq!(cache.get(&k2), Some(BigUint::from(5u32)));
    }

    #[test]
    fn eviction_tombstones_oldest_and_keeps_stamps_valid() {
        let mut cache: CompCache<BigUint> = CompCache::new(1 << 20);
        for i in 0..20_000u32 {
            cache.put(CompKey::encode(&[i, i + 1], &[i]), BigUint::from(i));
        }
        assert!(cache.evictions > 0);
        // Newest entries survive.
        let last = CompKey::encode(&[19_999, 20_000], &[19_999]);
        assert_eq!(cache.get(&last), Some(BigUint::from(19_999u32)));
        // Purge after eviction stays consistent.
        cache.purge_since(0);
        assert!(cache.is_empty());
    }

    #[test]
    fn eviction_compacts_slots_and_reclaims_key_memory() {
        // Regression for the 2026-07-10 leak: evicted keys must actually be
        // dropped, not retained in an append-only vector. The observable
        // guarantee is that the slot vector cannot grow unboundedly past the
        // live entry count while eviction is engaged.
        let mut cache: CompCache<BigUint> = CompCache::new(1 << 20);
        for i in 0..200_000u32 {
            cache.put(CompKey::encode(&[i, i + 1], &[i]), BigUint::from(i));
        }
        assert!(cache.evictions > 0);
        assert!(
            cache.slot_count() <= cache.len() + 1,
            "tombstoned prefix must be compacted away: {} slots for {} live",
            cache.slot_count(),
            cache.len()
        );
    }

    #[test]
    fn purge_with_mark_below_base_drops_everything_after_the_mark() {
        // Eviction slides `base` past outstanding watermarks; a purge with
        // such a stale mark must drop every remaining (younger) entry and
        // stay internally consistent.
        let mut cache: CompCache<BigUint> = CompCache::new(1 << 20);
        let mark = cache.stamp();
        for i in 0..50_000u32 {
            cache.put(CompKey::encode(&[i, i + 1], &[i]), BigUint::from(i));
        }
        assert!(cache.evictions > 0, "test needs eviction to move base");
        cache.purge_since(mark);
        assert!(cache.is_empty());
        assert_eq!(cache.stamp(), cache.stamp().max(mark));
        // The cache remains usable.
        let k = CompKey::encode(&[7], &[3]);
        cache.put(k.clone(), BigUint::from(9u32));
        assert_eq!(cache.get(&k), Some(BigUint::from(9u32)));
    }
}
