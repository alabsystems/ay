// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! 2-Watched Literal scheme with interleaved 8-byte AoS entries (#9773).
//!
//! Watch entries are stored as ONE contiguous `Vec<u64>` where each entry
//! packs the blocker literal and the clause reference into a single 8-byte
//! word. During BCP, ONE load serves both the blocker fast-path check and
//! (on a blocker miss) the clause reference — there is no second dependent
//! stream. Eight entries fit per 64-byte cache line.
//!
//! Rationale (#9773): hardware counters (xctrace CPU Bottlenecks) showed the
//! previous SoA layout (parallel `blockers: Vec<u32>` + `clauses: Vec<u64>`)
//! made BCP backend/data-bound: every blocker miss issued a 3-stream serial
//! dependent load chain (`blockers[i]` → `vals[blocker]` → branch →
//! `clauses[i]` → clause header). Interleaving the two fields into one 8-byte
//! entry collapses the watch-list traffic to a single stream: the entry load
//! feeds both `vals[blocker]` and the clause-header load directly.
//!
//! # Entry layout
//!
//! ```text
//! bit  63 ........ 32 | 31   | 30 ........ 0
//!      clause offset  | flag | blocker raw
//! ```
//!
//! - bits 0..=30: blocker literal raw (`Literal.0`)
//! - bit 31: [`ENTRY_BINARY_FLAG`] — set iff the watched clause is binary
//! - bits 32..=63: clause word offset (full `u32` range)
//!
//! The flag lives on the **blocker half** because the clause half has no free
//! bit: clause word offsets legitimately span the whole `u32` range
//! ([`crate::arena_limits::MAX_ARENA_WORDS`] == `u32::MAX`, see #9670 and the
//! boundary-offset regression tests). Blocker raws, in contrast, are literal
//! indices `< 2 * num_vars`; the packed layout requires `2 * num_vars <=
//! 2^31` (i.e. at most 2^30 variables), which is asserted at every
//! entry-construction and watch-list sizing choke point ([`pack_entry`],
//! [`WatchedLists::new`], [`WatchedLists::ensure_num_vars`]). A solver with
//! 2^30 variables would need >32 GiB for watch metadata alone, so the bound
//! is unreachable in practice — but it fails loudly, never silently.
//!
//! The `WatchedLists` struct stores ALL watch entries for ALL literals in one
//! contiguous buffer. Each literal has a `(offset, len, capacity)` triple
//! describing its region within the buffer. This replaces 2N separate heap
//! allocations (one Vec per literal) with a single allocation, improving
//! spatial locality.
//!
//! Reference: CaDiCaL `watch.hpp` packed-watch pattern; Kissat `vector.c`
//! unified buffer.

use crate::literal::Literal;

#[cfg(test)]
mod tests;
#[cfg(kani)]
mod verification;

/// Defragment watch buffers once dead slots exceed 1/8 of the unified buffer.
///
/// #8465: large-instance BCP is sensitive to scattered watch regions. The
/// previous 1/4 threshold left too much reclaimed watcher space in the hot
/// scan footprint between reduce/arena-GC passes.
const WATCH_DEFRAG_DEAD_SLOT_DIVISOR: usize = 8;

/// Buffer size (in 8-byte entries) above which the unified watch buffer stops
/// using `Vec`'s doubling policy for its own capacity.
///
/// 4Mi entries is 32 MB. Below that a doubling wastes at most 32 MB, which no
/// memory envelope cares about and which is cheaper to waste than to copy —
/// so everything under this threshold keeps the stock `Vec` policy EXACTLY,
/// including the capacity `heap_bytes()` reports to the clause-DB byte-limit
/// reduction trigger. The bounded policies below therefore cannot perturb any
/// instance whose watch buffer stays under 32 MB.
const WATCH_BUF_LARGE_ENTRIES: usize = 1 << 22;

/// Relocation headroom left past the exact plan, as a fraction of the plan.
///
/// [`apply_exact_layout`] ends with `len == capacity` on `buf_entries`: the
/// plan IS the allocation. The first post-build [`grow_and_push`] therefore
/// calls `Vec::reserve` on a FULL vector, which takes Rust's amortised path
/// (`cap = max(2 * cap, needed)`) and DOUBLES the buffer to admit a handful of
/// relocations. Measured on the 51.9M-clause DtAx lowering of vlsat3_b99: the
/// buffer ends only 170,938 entries (1.3 MB) past the exact plan, yet capacity
/// had gone from 151,256,006 to 302,512,012 entries — 1,153 MB of
/// mapped-but-never-written slack. That slack is invisible in RSS and charged
/// in FULL against `--memory`, which trips on counting-allocator live bytes /
/// `phys_footprint`, not RSS.
///
/// 1/64 of the plan covers that measured overshoot ~13x over while costing
/// 1.6% of the plan. The headroom is uninitialised CAPACITY — `len` is still
/// exactly the plan — so it changes no offset, no region, and no watch order.
///
/// [`apply_exact_layout`]: WatchedLists::apply_exact_layout
/// [`grow_and_push`]: WatchedLists::grow_and_push
const WATCH_BUF_EXACT_BUILD_HEADROOM_DIVISOR: usize = 64;

/// Growth step for a large unified watch buffer, as a fraction of capacity.
///
/// The point is to stay geometric — so growth is still amortised O(1) — without
/// doubling, which on a 151M-entry buffer strands a full gigabyte of untouched
/// capacity to buy headroom the solve never uses (measured on vlsat3_b99:
/// 2,308 MB allocated against 1,155 MB used).
///
/// Sized relative to [`WATCH_DEFRAG_DEAD_SLOT_DIVISOR`], but do NOT read that as
/// "one step per defrag cycle". Review measured the real relationship and it is
/// coarser: `grow_and_push` appends `old_len * 2` entries while adding only
/// `old_len` dead ones, so a cycle reaches the `dead_slots > len / 8` trigger
/// after appending about `len / 4` — roughly two growth steps, not one. And
/// `shrink_capacity` is not polled on the push path at all (it runs from
/// `arena_gc` and `shrink_lists`), so nothing here bounds the number of
/// reallocations between those boundaries.
///
/// What the constant does guarantee is the property that matters: growth is
/// always at least 1.125x (when `additional > cap / 8`, the target exceeds
/// `1.125 * cap`), so there is no quadratic path.
const WATCH_BUF_GROWTH_STEP_DIVISOR: usize = 8;

/// Index of a clause in the clause database
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub struct ClauseRef(pub(crate) u32);

impl ClauseRef {
    /// Create a new clause reference from a raw index
    #[inline]
    pub fn new(id: u32) -> Self {
        Self(id)
    }

    /// Get the raw index value
    #[inline]
    pub fn index(self) -> usize {
        self.0 as usize
    }

    /// Get the raw u32 value
    #[inline]
    pub fn id(self) -> u32 {
        self.0
    }
}

/// Binary-clause flag in a *clause word* (the `u64` API currency carried by
/// [`Watcher::clause_raw`] and the `clause_raw()` accessors, #9670).
///
/// Historically the clause word was a `u32` whose high bit (`0x8000_0000`)
/// doubled as the binary flag, capping the arena at `2^31` words: any clause
/// allocated at offset `>= 2^31` aliased the flag and corrupted BCP, which
/// could yield a spurious UNSAT. The clause word is a `u64` with the flag at
/// **bit 32**, leaving the full low 32 bits free for the clause word offset.
/// `ClauseRef` stays a `u32`, so the addressable arena rises to the whole
/// `u32` offset space (see [`crate::arena_limits::MAX_ARENA_WORDS`]).
///
/// NOTE: this is the flag position in the *clause word* exchanged through the
/// accessor API. Inside a packed 8-byte watch entry the flag is stored at
/// [`ENTRY_BINARY_FLAG`] (bit 31, on the blocker half) instead — see the
/// module docs (#9773).
pub(crate) const BINARY_FLAG: u64 = 1 << 32;

// The clause word offset occupies the low 32 bits of the watch clause word, so
// the largest representable offset is `u32::MAX`. `arena_limits::MAX_ARENA_WORDS`
// exposes that bound to callers building large CNFs; keep them in sync (compile
// error if they ever diverge).
const _: () = assert!((BINARY_FLAG - 1) == crate::arena_limits::MAX_ARENA_WORDS);

// ─── Packed 8-byte watch entry (#9773) ──────────────────────────────

/// Binary-clause flag inside a packed 8-byte watch entry: bit 31, the top bit
/// of the **blocker half** (#9773).
///
/// The flag cannot live on the clause half: clause word offsets span the full
/// `u32` range (`MAX_ARENA_WORDS == u32::MAX`), so bit 31 *and* bit 63 of the
/// entry are both needed for offsets. Blocker raws are literal indices
/// `< 2 * num_vars <= 2^31` (asserted at entry construction and watch-list
/// sizing), so bit 31 of the blocker half is provably free.
pub(crate) const ENTRY_BINARY_FLAG: u64 = 1 << 31;

/// Low 31 bits of a packed entry: the blocker literal raw.
const ENTRY_BLOCKER_MASK: u64 = ENTRY_BINARY_FLAG - 1;

/// Pack a (blocker raw, clause word) pair into one 8-byte watch entry.
///
/// `clause_raw` is a clause word: low 32 bits = clause word offset,
/// bit 32 = [`BINARY_FLAG`]. The flag is relocated to bit 31 of the entry.
///
/// # Panics
///
/// Panics if `blocker_raw` has bit 31 set (variable index >= 2^30). This is
/// the entry-construction assert documenting the packed-layout invariant; the
/// same bound is enforced when sizing watch lists ([`WatchedLists::new`] /
/// [`WatchedLists::ensure_num_vars`]), so every literal that can ever appear
/// as a blocker satisfies it.
#[inline(always)]
pub(crate) fn pack_entry(blocker_raw: u32, clause_raw: u64) -> u64 {
    assert!(
        u64::from(blocker_raw) & ENTRY_BINARY_FLAG == 0,
        "BUG: blocker literal raw {blocker_raw} has bit 31 set (variable index >= 2^30); \
         unsupported by the packed 8-byte watch-entry layout (#9773)"
    );
    debug_assert!(
        clause_raw >> 33 == 0,
        "BUG: clause word {clause_raw:#x} has bits above the bit-32 binary flag"
    );
    u64::from(blocker_raw) | ((clause_raw & BINARY_FLAG) >> 1) | ((clause_raw & 0xFFFF_FFFF) << 32)
}

/// Extract the blocker literal raw from a packed entry (masks the flag bit).
#[inline(always)]
pub(crate) const fn entry_blocker_raw(entry: u64) -> u32 {
    (entry & ENTRY_BLOCKER_MASK) as u32
}

/// Reconstruct the clause word (offset in low 32 bits, [`BINARY_FLAG`] at
/// bit 32) from a packed entry.
#[inline(always)]
pub(crate) const fn entry_clause_raw(entry: u64) -> u64 {
    (entry >> 32) | ((entry & ENTRY_BINARY_FLAG) << 1)
}

/// Check the binary flag of a packed entry.
#[inline(always)]
pub(crate) const fn entry_is_binary(entry: u64) -> bool {
    entry & ENTRY_BINARY_FLAG != 0
}

/// Extract the clause word offset from a packed entry.
#[inline(always)]
pub(crate) const fn entry_clause_off(entry: u64) -> u32 {
    (entry >> 32) as u32
}

/// Replace the blocker half of a packed entry, preserving the binary flag and
/// clause offset. Hot-path helper for BCP blocker refresh; the bit-31
/// invariant is enforced at [`pack_entry`] / watch-list sizing choke points,
/// so this uses a debug assert only.
#[inline(always)]
pub(crate) fn entry_with_blocker(entry: u64, blocker_raw: u32) -> u64 {
    debug_assert!(
        u64::from(blocker_raw) & ENTRY_BINARY_FLAG == 0,
        "BUG: blocker literal raw {blocker_raw} has bit 31 set (variable index >= 2^30)"
    );
    (entry & !ENTRY_BLOCKER_MASK) | u64::from(blocker_raw)
}

/// Count the leading binary entries in a binary-first packed-entry slice.
#[inline]
fn count_binary_prefix(entries: &[u64]) -> u32 {
    let mut bc: u32 = 0;
    for &e in entries {
        if !entry_is_binary(e) {
            break;
        }
        bc += 1;
    }
    #[cfg(debug_assertions)]
    {
        debug_assert!(
            entries[..bc as usize].iter().all(|&e| entry_is_binary(e)),
            "BUG: counted non-binary entry in binary watch prefix"
        );
        debug_assert!(
            entries[bc as usize..].iter().all(|&e| !entry_is_binary(e)),
            "BUG: binary entry found after long watch suffix started"
        );
    }
    bc
}

/// A watcher entry (parameter type for add_watch API)
///
/// For binary clauses: `blocker_raw` stores the other literal's raw value
/// For longer clauses: `blocker_raw` is a hint for early satisfaction check
///
/// `BINARY_FLAG` (bit 32 of `clause_raw`) indicates whether this is a binary
/// clause; the low 32 bits hold the clause word offset (#9670). This is the
/// API currency — storage repacks it into an 8-byte entry (#9773).
#[derive(Debug, Clone, Copy)]
pub(crate) struct Watcher {
    /// The clause being watched. `BINARY_FLAG` (bit 32) set if binary; the low
    /// 32 bits hold the clause word offset (#9670).
    pub(crate) clause_raw: u64,
    /// For binary clauses: the other literal in the clause
    /// For non-binary clauses: blocker literal for faster filtering
    pub(crate) blocker_raw: u32,
}

impl Watcher {
    /// Create a watcher for a binary clause
    #[inline]
    pub(crate) fn binary(clause: ClauseRef, other_lit: Literal) -> Self {
        Self {
            clause_raw: u64::from(clause.0) | BINARY_FLAG,
            blocker_raw: other_lit.0,
        }
    }

    /// Create a watcher for a non-binary clause (3+ literals)
    #[inline]
    pub(crate) fn new(clause: ClauseRef, blocker: Literal) -> Self {
        Self {
            clause_raw: u64::from(clause.0),
            blocker_raw: blocker.0,
        }
    }

    /// Check if this is a binary clause watcher
    #[inline]
    #[cfg(kani)]
    pub(crate) fn is_binary(self) -> bool {
        self.clause_raw & BINARY_FLAG != 0
    }

    /// Get the clause reference (strips binary flag)
    #[inline]
    #[cfg(kani)]
    pub(crate) fn clause_ref(self) -> ClauseRef {
        ClauseRef((self.clause_raw & !BINARY_FLAG) as u32)
    }

    /// Get the blocker/other literal
    #[inline]
    #[cfg(kani)]
    pub(crate) fn blocker(self) -> Literal {
        Literal(self.blocker_raw)
    }
}

/// Standalone watch list for scratch / deferred-swap buffers (packed AoS).
///
/// Stores packed 8-byte entries in one contiguous array. During the BCP scan
/// one entry load serves both the blocker fast path and the clause reference
/// (#9773); 8 entries fit per 64-byte cache line.
///
/// Used by `Solver::deferred_watch_list` for the BCP deferred-copy path,
/// and by tests that build watch lists independently.
#[derive(Debug, Default, Clone)]
pub(crate) struct WatchList {
    /// Packed 8-byte watch entries (see module docs for the layout).
    entries: Vec<u64>,
}

impl WatchList {
    /// Create an empty watch list
    pub(crate) fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    /// Number of watchers
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Direct mutable access to the packed entries.
    ///
    /// Used by the BCP hot loop: taking the slice out of the struct lets the
    /// caller hold `&mut entries[..]` and `&self.vals[..]` simultaneously
    /// because they are disjoint borrows. The compiler then caches both data
    /// pointers in registers across consecutive fast-path iterations
    /// (#3758, #8465, #9773).
    #[inline]
    pub(crate) fn entries_mut(&mut self) -> &mut [u64] {
        &mut self.entries
    }

    /// Prefetch hint for first watch entry.
    ///
    /// CaDiCaL propagate.cpp:160-166: `__builtin_prefetch(&ws[0], 0, 1)`.
    /// BCP will scan entries on the next propagation step. Prefetch
    /// is isolated in `ay-prefetch`; ay-sat's own audited unsafe exceptions
    /// remain confined to their hot-path modules.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn prefetch_first(&self) {
        if let Some(first) = self.entries.first() {
            ay_prefetch::prefetch_read_l2(std::ptr::from_ref::<u64>(first));
        }
    }

    /// Get blocker raw value at index
    #[inline]
    pub(crate) fn blocker_raw(&self, i: usize) -> u32 {
        entry_blocker_raw(self.entries[i])
    }

    /// Get clause raw value at index (includes BINARY_FLAG if binary)
    #[inline]
    pub(crate) fn clause_raw(&self, i: usize) -> u64 {
        entry_clause_raw(self.entries[i])
    }

    /// Get the packed 8-byte entry at index.
    #[inline]
    pub(crate) fn entry_raw(&self, i: usize) -> u64 {
        self.entries[i]
    }

    /// Get blocker as Literal at index
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn blocker(&self, i: usize) -> Literal {
        Literal(entry_blocker_raw(self.entries[i]))
    }

    /// Get clause ref at index (strips BINARY_FLAG)
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn clause_ref(&self, i: usize) -> ClauseRef {
        ClauseRef(entry_clause_off(self.entries[i]))
    }

    /// Check if watcher at index is binary
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn is_binary(&self, i: usize) -> bool {
        entry_is_binary(self.entries[i])
    }

    /// Push a watcher given raw values
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn push(&mut self, blocker_raw: u32, clause_raw: u64) {
        self.entries.push(pack_entry(blocker_raw, clause_raw));
    }

    /// Push a Watcher struct
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn push_watcher(&mut self, w: Watcher) {
        self.entries.push(pack_entry(w.blocker_raw, w.clause_raw));
    }

    /// Extend from another WatchList starting at index `start`
    #[cfg(test)]
    #[inline]
    pub(crate) fn extend_from(&mut self, other: &Self, start: usize) {
        self.entries.extend_from_slice(&other.entries[start..]);
    }

    /// Extend from another WatchList for the half-open range [start, end).
    #[cfg(test)]
    #[inline]
    pub(crate) fn extend_range_from(&mut self, other: &Self, start: usize, end: usize) {
        self.entries.extend_from_slice(&other.entries[start..end]);
    }

    /// Swap-remove element at index (O(1) removal)
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn swap_remove(&mut self, i: usize) {
        self.entries.swap_remove(i);
    }

    /// Truncate the watch list to `new_len` entries (in-place compaction).
    #[inline]
    pub(crate) fn truncate(&mut self, new_len: usize) {
        self.entries.truncate(new_len);
    }

    /// Write a (blocker, clause) pair at position `dst` (in-place compaction).
    #[inline]
    pub(crate) fn set_entry(&mut self, dst: usize, blocker_raw: u32, clause_raw: u64) {
        self.entries[dst] = pack_entry(blocker_raw, clause_raw);
    }

    /// Copy entries `[src_start..src_end)` to `[dst..)` within the same list.
    #[inline]
    pub(crate) fn copy_within(&mut self, src_start: usize, src_end: usize, dst: usize) {
        self.entries.copy_within(src_start..src_end, dst);
    }

    /// Clear all entries
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
    }

    /// Total capacity (for memory stats)
    #[cfg(test)]
    #[inline]
    pub(crate) fn capacity(&self) -> usize {
        self.entries.capacity()
    }

    /// Sort watchers so binary clauses come first (stable relative order).
    ///
    /// Mirrors [`WatchedLists::debug_assert_binary_first`] invariant for a standalone list.
    #[cfg(test)]
    pub(crate) fn sort_binary_first(&mut self) {
        if self.entries.len() <= 1 {
            return;
        }
        let mut non_binary: Vec<u64> = Vec::new();
        let mut write = 0;
        for read in 0..self.entries.len() {
            let e = self.entries[read];
            if entry_is_binary(e) {
                self.entries[write] = e;
                write += 1;
            } else {
                non_binary.push(e);
            }
        }
        self.entries[write..write + non_binary.len()].copy_from_slice(&non_binary);
    }

    /// Remap clause refs using a relocation map, dropping dead entries.
    ///
    /// Mirrors [`WatchedLists::remap_clause_refs`] for a standalone list.
    #[cfg(test)]
    pub(crate) fn remap_clause_refs(&mut self, remap: &[u32]) {
        let mut j = 0;
        for i in 0..self.entries.len() {
            let entry = self.entries[i];
            let old_offset = entry_clause_off(entry) as usize;
            if old_offset >= remap.len() || remap[old_offset] == u32::MAX {
                continue;
            }
            let new_offset = remap[old_offset];
            // Keep the low half (blocker + flag), replace the offset half.
            self.entries[j] = (entry & 0xFFFF_FFFF) | (u64::from(new_offset) << 32);
            j += 1;
        }
        self.entries.truncate(j);
    }
}

// ─── Exact-size initial watch construction ──────────────────────────

/// Per-literal watch counts gathered by pass 1 of the exact initial build.
///
/// The full clause set is known before watches are attached, so every
/// literal's region size is computable exactly. Pass 1 fills this table;
/// [`WatchedLists::apply_exact_layout`] turns it into a one-shot layout with
/// zero slack, and pass 2 fills the regions in place — no `grow_and_push`,
/// no relocation, no abandoned regions.
#[derive(Debug, Default)]
pub(crate) struct ExactWatchPlan {
    /// Number of watches the build will attach to each literal index.
    counts: Vec<u32>,
}

impl ExactWatchPlan {
    /// Start a plan sized for `num_lits` literal indices (it grows on demand).
    pub(crate) fn new(num_lits: usize) -> Self {
        Self {
            counts: vec![0; num_lits],
        }
    }

    /// Record one watch for `lit` (pass 1).
    #[inline]
    pub(crate) fn count_watch(&mut self, lit: Literal) {
        let li = lit.index();
        if li >= self.counts.len() {
            self.counts.resize(li + 1, 0);
        }
        // Overflow-checks are on in release: a literal watched more than
        // `u32::MAX` times fails loudly rather than wrapping into a
        // too-small region.
        self.counts[li] += 1;
    }
}

// ─── Per-literal metadata into the unified buffer ───────────────────

/// Metadata for a single literal's region in the unified watch buffer.
#[derive(Debug, Clone, Copy, Default)]
struct WatchMeta {
    /// Start index into the unified buffer.
    offset: u32,
    /// Number of active entries.
    len: u32,
    /// Allocated capacity (slots in buffer starting at offset).
    capacity: u32,
    /// Number of binary watch entries at the front of this region.
    /// Invariant: entries [offset..offset+binary_count) have the entry binary
    /// flag set, entries [offset+binary_count..offset+len) do not.
    binary_count: u32,
}

/// Watched literal lists with a unified packed-entry buffer (#8465, #9773).
///
/// All watch entries for all literals are stored in ONE contiguous buffer
/// `buf_entries: Vec<u64>` of packed 8-byte entries (blocker raw + binary
/// flag in the low half, clause word offset in the high half — see module
/// docs). Each literal has a `WatchMeta` triple `(offset, len, capacity)`
/// describing its region within the buffer.
///
/// The interleaved AoS layout makes the BCP scan single-stream: one entry
/// load feeds both the blocker check and, on a miss, the clause reference —
/// no second dependent array walk (#9773). 8 entries fit per cache line.
///
/// Defragmentation (`defragment()`) compacts the buffer by sorting non-empty
/// regions by offset and copying forward, reclaiming gaps left by cleared
/// or shrunk watch lists. Called from `shrink_capacity()` after arena GC.
#[derive(Debug, Default, Clone)]
pub(crate) struct WatchedLists {
    /// Packed 8-byte watch entries for ALL literals (see module docs).
    buf_entries: Vec<u64>,
    /// Per-literal metadata: (offset, len, capacity) into the buffer.
    /// Indexed by `literal.index()` (= var * 2 + sign).
    meta: Vec<WatchMeta>,
    /// Total number of "dead" (freed but not reclaimed) slots in the buffer.
    dead_slots: usize,
}

impl WatchedLists {
    /// Assert the packed-entry blocker bound: every literal index must fit in
    /// the 31-bit blocker half of an entry (#9773).
    #[inline]
    fn assert_lit_index_bound(num_lits: usize) {
        assert!(
            num_lits <= ENTRY_BINARY_FLAG as usize,
            "BUG: {num_lits} literal indices exceed the 2^31 packed watch-entry blocker \
             bound (max 2^30 variables, #9773)"
        );
    }

    /// Create new watched lists for n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        let num_lits = num_vars.saturating_mul(2);
        Self::assert_lit_index_bound(num_lits);
        Self {
            buf_entries: Vec::new(),
            meta: vec![WatchMeta::default(); num_lits],
            dead_slots: 0,
        }
    }

    /// Ensure the watched lists can index literals for `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        let target = num_vars.saturating_mul(2);
        if self.meta.len() < target {
            Self::assert_lit_index_bound(target);
            self.meta.resize(target, WatchMeta::default());
        }
    }

    /// Clear all watch lists without deallocating the buffers.
    pub(crate) fn clear(&mut self) {
        for m in &mut self.meta {
            m.len = 0;
            m.capacity = 0;
            m.offset = 0;
            m.binary_count = 0;
        }
        self.buf_entries.clear();
        self.dead_slots = 0;
    }

    /// Number of watch lists (one per literal index).
    #[inline]
    pub(crate) fn num_lists(&self) -> usize {
        self.meta.len()
    }

    // ─── Single-literal read access (indexed by literal + watcher index) ─

    /// Number of watchers for a literal
    #[inline]
    pub(crate) fn len_of(&self, lit: Literal) -> usize {
        self.meta[lit.index()].len as usize
    }

    /// Number of binary watchers in a literal's binary-first prefix.
    #[inline]
    pub(crate) fn binary_count_of(&self, lit: Literal) -> usize {
        self.meta[lit.index()].binary_count as usize
    }

    /// Get the packed 8-byte entry at watcher index within a literal's list.
    #[inline]
    pub(crate) fn entry_raw(&self, lit: Literal, i: usize) -> u64 {
        let start = self.meta[lit.index()].offset as usize;
        self.buf_entries[start + i]
    }

    /// Get blocker raw value at watcher index within a literal's watch list
    #[inline]
    pub(crate) fn blocker_raw(&self, lit: Literal, i: usize) -> u32 {
        entry_blocker_raw(self.entry_raw(lit, i))
    }

    /// Get clause raw value at watcher index (includes BINARY_FLAG if binary)
    #[inline]
    pub(crate) fn clause_raw(&self, lit: Literal, i: usize) -> u64 {
        entry_clause_raw(self.entry_raw(lit, i))
    }

    /// Get blocker as Literal at watcher index
    #[inline]
    pub(crate) fn blocker(&self, lit: Literal, i: usize) -> Literal {
        Literal(self.blocker_raw(lit, i))
    }

    /// Get clause ref at watcher index (strips BINARY_FLAG)
    #[inline]
    pub(crate) fn clause_ref(&self, lit: Literal, i: usize) -> ClauseRef {
        ClauseRef(entry_clause_off(self.entry_raw(lit, i)))
    }

    /// Check if watcher at index is binary
    #[inline]
    pub(crate) fn is_binary(&self, lit: Literal, i: usize) -> bool {
        entry_is_binary(self.entry_raw(lit, i))
    }

    // ─── Single-literal write access ────────────────────────────────

    /// Write a (blocker, clause) pair at position `dst` within a literal's region.
    #[inline]
    pub(crate) fn set_entry(
        &mut self,
        lit: Literal,
        dst: usize,
        blocker_raw: u32,
        clause_raw: u64,
    ) {
        let start = self.meta[lit.index()].offset as usize;
        self.buf_entries[start + dst] = pack_entry(blocker_raw, clause_raw);
    }

    /// Swap-remove element at watcher index within a literal's watch list.
    ///
    /// Two-step swap pattern (Gemini 3.1 review): naive swap_remove with the
    /// last element would break the binary-first partition. Instead:
    ///
    /// - Deleting a binary entry (i < binary_count):
    ///   1. Swap with last binary entry (at binary_count - 1).
    ///   2. Swap that vacated position with the last long entry (at len - 1).
    ///   3. Decrement binary_count and len.
    ///
    /// - Deleting a long entry (i >= binary_count):
    ///   1. Swap with the last entry (at len - 1).
    ///   2. Decrement len.
    #[inline]
    pub(crate) fn swap_remove(&mut self, lit: Literal, i: usize) {
        let m = &mut self.meta[lit.index()];
        let start = m.offset as usize;
        let last = m.len as usize - 1;
        let bc = m.binary_count as usize;

        if i < bc {
            // Deleting a binary entry.
            let last_binary = bc - 1;
            // Step 1: swap deleted binary with last binary.
            if i != last_binary {
                self.buf_entries.swap(start + i, start + last_binary);
            }
            // Step 2: fill the vacated binary slot with the last long entry
            // (which is at position `last`), if there are any long entries.
            if last_binary < last {
                self.buf_entries.swap(start + last_binary, start + last);
            }
            m.binary_count -= 1;
        } else {
            // Deleting a long entry: swap with last entry.
            if i != last {
                self.buf_entries.swap(start + i, start + last);
            }
        }
        m.len -= 1;
        self.dead_slots += 1;
    }

    /// Truncate a literal's watch list to `new_len` entries.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn truncate_lit(&mut self, lit: Literal, new_len: usize) {
        let m = &mut self.meta[lit.index()];
        let old_len = m.len as usize;
        if new_len < old_len {
            self.dead_slots += old_len - new_len;
            m.len = new_len as u32;
            // Clamp binary_count if truncation removes binary entries.
            if (m.binary_count as usize) > new_len {
                m.binary_count = new_len as u32;
            }
        }
    }

    /// Clear a single literal's watch list.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn clear_lit(&mut self, lit: Literal) {
        let m = &mut self.meta[lit.index()];
        self.dead_slots += m.len as usize;
        m.len = 0;
        m.binary_count = 0;
    }

    // ─── Slice access into the unified buffer ───────────────────────

    /// Get the packed entries for a literal as an immutable slice.
    #[inline]
    pub(crate) fn entry_slice(&self, lit: Literal) -> &[u64] {
        let m = &self.meta[lit.index()];
        let start = m.offset as usize;
        &self.buf_entries[start..start + m.len as usize]
    }

    /// Raw mutable pointer to a literal's packed-entry region + length.
    ///
    /// Used by `propagate_bcp_ic3` for CaDiCaL-style in-place pointer
    /// iteration. The caller must ensure no aliasing references exist and
    /// that indices stay within `[0, len)`.
    #[cfg(feature = "raw-pointer-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) fn entries_raw_mut(&mut self, lit: Literal) -> (*mut u64, usize) {
        let m = self.meta[lit.index()];
        let start = m.offset as usize;
        let len = m.len as usize;
        // SAFETY: `start` is derived from `meta[lit.index()].offset`, which is
        // only set by `grow_and_push`, `restore_from_deferred`,
        // `restore_from_deferred_with_bc`, `defragment`, and
        // `apply_exact_layout` (the one-shot presized build, which assigns
        // prefix-sum offsets over a buffer resized to their total, so the
        // bound below holds there by construction). All paths ensure
        // `start + capacity <= buf_entries.len()` (the buffer is always
        // resized/pushed to hold the full region), and `len <= capacity`,
        // so `start + len <= buf_entries.len()`. Therefore `.add(start)`
        // produces a pointer to a valid slot (or the one-past-end slot when
        // the list is empty), which is allowed for `ptr::add`. We do not
        // dereference here — the returned pointer's use is bounded by the
        // `len` return value, which the caller must respect.
        let entries_ptr = unsafe { self.buf_entries.as_mut_ptr().add(start) };
        (entries_ptr, len)
    }

    /// Raw mutable pointer + length + binary count for two-phase BCP (#8569).
    ///
    /// Like `entries_raw_mut` but also returns `binary_count`, enabling the
    /// caller to split binary and long clause processing into separate loops.
    /// The binary-first invariant guarantees entries [0..binary_count) are
    /// binary and [binary_count..len) are long.
    #[cfg(feature = "raw-pointer-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) fn entries_raw_mut_with_bc(&mut self, lit: Literal) -> (*mut u64, usize, usize) {
        let m = self.meta[lit.index()];
        let start = m.offset as usize;
        let len = m.len as usize;
        let bc = m.binary_count as usize;
        // SAFETY: Same invariants as `entries_raw_mut` above — `start` comes
        // from `meta[lit.index()].offset`, and every mutation of `buf_entries`
        // (grow_and_push / restore_from_deferred* / defragment) preserves
        // `start + len <= buf_entries.len()`. `.add(start)` is sound because
        // the resulting pointer is either a valid slot or the one-past-end
        // slot. No dereference occurs here; callers must confine accesses
        // to indices `[0, len)` using the returned `len`. `binary_count <=
        // len` is a struct invariant enforced by `debug_assert_binary_first`
        // and upheld by every push/remove path, so callers using `bc` to
        // split binary vs long regions cannot escape `[0, len)`.
        let entries_ptr = unsafe { self.buf_entries.as_mut_ptr().add(start) };
        (entries_ptr, len, bc)
    }

    /// Unsafe length update for in-place compaction by the unsafe BCP loop.
    ///
    /// # Safety
    /// `new_len` must be <= the current length. All entries in `[0, new_len)`
    /// must be valid (initialized). This is guaranteed by the BCP compaction
    /// invariant: `j <= i <= original_len`.
    ///
    /// BCP compaction preserves binary-first order because: (a) the watch list
    /// starts sorted (binary entries first), and (b) BCP only drops long-clause
    /// watchers (replacement found). Binary watchers are always kept. So
    /// binary_count is unchanged; we only clamp it if new_len is smaller.
    #[cfg(feature = "raw-pointer-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) unsafe fn set_len_after_bcp_compaction(&mut self, lit: Literal, new_len: usize) {
        // SAFETY: This function is only memory-unsafe in the sense that it
        // shrinks the logical length of a watch list region without dropping
        // any resources — the `u64` entries stored in `buf_entries` are
        // `Copy` and hold no ownership, so setting `meta[lit].len` to a
        // smaller value leaves every "dropped" entry still trivially valid in
        // the underlying `Vec`. The `unsafe` marker exists to document the
        // caller-side invariant required by the BCP compaction loop:
        // `new_len <= current len` and entries in `[0, new_len)` are the
        // compacted (live) ones. The debug_assert checks the length bound in
        // debug builds; release builds rely on BCP's `j <= i <= original_len`
        // compaction invariant.
        let m = &mut self.meta[lit.index()];
        debug_assert!(new_len <= m.len as usize);
        debug_assert!(
            new_len >= m.binary_count as usize,
            "BUG: BCP compaction must not drop binary watchers"
        );
        // BCP moves watches between literals; it does not delete them. The tail
        // remains reusable capacity for this literal, not deletion garbage.
        m.len = new_len as u32;
        // Clamp binary_count. In normal BCP this is a no-op since binary
        // watchers are never dropped, but defensive for edge cases.
        if m.binary_count > m.len {
            m.binary_count = m.len;
        }
    }

    /// Prefetch hint for first watch entry of a literal.
    ///
    /// CaDiCaL propagate.cpp:160-166: `__builtin_prefetch(&ws[0], 0, 1)`.
    /// With the packed AoS layout, the entries array is the only scan target.
    ///
    /// Branchless (#8465): always issue the prefetch using the offset from
    /// meta[], even for empty watch lists. Prefetch is a no-op hint that
    /// never faults, so an out-of-range or stale address is harmless. This
    /// eliminates a branch (m.len > 0 check) that the CPU would otherwise
    /// need to predict on every enqueue/prefetch call.
    #[inline(always)]
    pub(crate) fn prefetch_first(&self, lit: Literal) {
        let m = &self.meta[lit.index()];
        let start = m.offset as usize;
        // SAFETY: prefetch never faults. If start is at the end of
        // buf_entries (empty watch list), the prefetch address is the
        // one-past-end slot or a slot belonging to another literal's
        // watch list — both are valid addresses within the allocation.
        // wrapping_add avoids creating a reference to potentially
        // out-of-bounds memory.
        let ptr = self.buf_entries.as_ptr().wrapping_add(start);
        ay_prefetch::prefetch_read_l2(ptr);
    }

    // ─── Push / add operations ──────────────────────────────────────

    /// Push a (blocker, clause) pair to a literal's watch list, growing if needed.
    ///
    /// Maintains the binary-first invariant: binary watches occupy
    /// `[offset..offset+binary_count)`, long watches occupy
    /// `[offset+binary_count..offset+len)`.
    ///
    /// - Binary insert: swap the first long entry to position `len`, place
    ///   the new binary entry at position `binary_count`. O(1).
    /// - Long insert: append at position `len`. O(1).
    fn push_entry(&mut self, lit: Literal, blocker_raw: u32, clause_raw: u64) {
        let li = lit.index();
        // Defensive grow: the arena can contain clauses referencing variables
        // beyond what the watch metadata was last sized for (theory-extension
        // clauses attached before the watch lists were grown to the new variable
        // count). Without this, `meta[li]` indexes out of bounds and crashes
        // (observed on QF_UF hardware-BMC benchmarks: li 196608 vs meta len
        // 161390). `meta` is grow-only; new entries default to an empty region.
        if li >= self.meta.len() {
            Self::assert_lit_index_bound(li + 1);
            self.meta.resize(li + 1, WatchMeta::default());
        }
        let entry = pack_entry(blocker_raw, clause_raw);
        let is_binary = entry_is_binary(entry);
        let m = self.meta[li];
        if m.len < m.capacity {
            // Fast path: space available in existing region.
            let start = m.offset as usize;
            if is_binary {
                // Swap first long entry to end, insert binary at binary_count.
                let bc = m.binary_count as usize;
                if bc < m.len as usize {
                    // There is at least one long entry: move it to the end.
                    self.buf_entries[start + m.len as usize] = self.buf_entries[start + bc];
                }
                self.buf_entries[start + bc] = entry;
                self.meta[li].binary_count += 1;
            } else {
                // Long insert: append at end.
                self.buf_entries[start + m.len as usize] = entry;
            }
            self.meta[li].len += 1;
        } else {
            // Slow path: allocate new region at end of buffers.
            self.grow_and_push(li, entry);
        }
    }

    /// Reserve room for `additional` more entries with a BOUNDED growth step.
    ///
    /// Every relocating path (`grow_and_push`, the three
    /// `restore_from_deferred*` overflow paths) appends a fresh region at the
    /// end of `buf_entries` and must first make room for it. `Vec::reserve`
    /// answers that with `cap = max(2 * cap, needed)`, which is the right
    /// policy for a vector filled from empty and the wrong one here once the
    /// buffer is large: after [`apply_exact_layout`] the buffer already holds
    /// its planned size, and the relocations that follow are rare and small,
    /// so doubling multiplies the solver's single largest allocation to admit
    /// kilobytes. On vlsat3_b99 that cost 1,153 MB of never-written capacity
    /// — enough to decide whether the instance fits its memory envelope.
    ///
    /// Below [`WATCH_BUF_LARGE_ENTRIES`] this defers to `Vec::reserve`
    /// unchanged, so small and medium instances keep byte-identical capacity
    /// (and hence a byte-identical [`heap_bytes`], which feeds the clause-DB
    /// byte-limit reduction trigger). Above it, capacity grows by
    /// `cap / WATCH_BUF_GROWTH_STEP_DIVISOR` per step, still geometric — so
    /// still amortised O(1) per entry — but with a step sized to one
    /// defragmentation cycle instead of a whole extra buffer.
    ///
    /// [`apply_exact_layout`]: WatchedLists::apply_exact_layout
    /// [`heap_bytes`]: WatchedLists::heap_bytes
    #[inline]
    fn reserve_entries(&mut self, additional: usize) {
        let cap = self.buf_entries.capacity();
        let len = self.buf_entries.len();
        let needed = len + additional;
        if needed <= cap {
            // The common case once the exact build leaves headroom: no
            // allocation, no relocation, no copy.
            return;
        }
        if cap < WATCH_BUF_LARGE_ENTRIES {
            self.buf_entries.reserve(additional);
            return;
        }
        let target = needed.max(cap + cap / WATCH_BUF_GROWTH_STEP_DIVISOR);
        self.buf_entries.reserve_exact(target - len);
    }

    /// Grow a literal's region (allocate at end of the buffer) and push one
    /// packed entry.
    ///
    /// Maintains binary-first invariant: copies existing entries preserving
    /// the partition, then inserts the new entry at the correct position.
    #[cold]
    fn grow_and_push(&mut self, li: usize, entry: u64) {
        let m = self.meta[li];
        let old_len = m.len as usize;
        let old_offset = m.offset as usize;
        let old_bc = m.binary_count as usize;
        let new_capacity = if old_len == 0 { 2 } else { old_len * 2 };
        let new_offset = self.buf_entries.len();
        let is_binary = entry_is_binary(entry);

        // Allocate new region at the end of the buffer.
        self.reserve_entries(new_capacity);

        if is_binary {
            // Bulk-copy the existing binary prefix, insert the new binary
            // watcher, then bulk-copy the long suffix. This keeps the
            // binary-first partition while avoiding one push/bounds check per
            // relocated watcher on the growth path.
            self.buf_entries
                .extend_from_within(old_offset..old_offset + old_bc);
            self.buf_entries.push(entry);
            self.buf_entries
                .extend_from_within(old_offset + old_bc..old_offset + old_len);
        } else {
            // Copy all existing entries (already partitioned) in bulk, then
            // append the new long watcher.
            self.buf_entries
                .extend_from_within(old_offset..old_offset + old_len);
            self.buf_entries.push(entry);
        }

        // Pad remaining capacity with zeros.
        for _ in (old_len + 1)..new_capacity {
            self.buf_entries.push(0);
        }

        // Mark old region as dead.
        self.dead_slots += m.capacity as usize;

        self.meta[li] = WatchMeta {
            offset: new_offset as u32,
            len: (old_len + 1) as u32,
            capacity: new_capacity as u32,
            binary_count: (old_bc + usize::from(is_binary)) as u32,
        };
    }

    // ─── Exact-size one-shot build (pass 2) ─────────────────────────

    /// True when no watch entries are stored — the state after [`clear`] and
    /// the precondition of the exact-size build.
    ///
    /// [`clear`]: WatchedLists::clear
    #[inline]
    pub(crate) fn is_unbuilt(&self) -> bool {
        self.buf_entries.is_empty()
    }

    /// Would the incremental builder have relocated a region of this length?
    ///
    /// [`grow_and_push`] runs exactly when `len == capacity`, and the capacity
    /// schedule for a region grown from empty is `0 → 2 → 4 → 8 → …` (see
    /// `new_capacity` there). Walking that schedule, the relocation lengths are
    /// `{0} ∪ {2, 4, 8, 16, …}`: at `len == 1` the capacity is already 2, so
    /// the one power of two that is NOT a growth step is 1.
    ///
    /// This is needed because the two insert paths order the long suffix
    /// DIFFERENTLY on a binary insert (rotation vs shift, see
    /// [`push_entry_presized`]). Reproducing the search exactly therefore means
    /// reproducing which path each push would have taken.
    ///
    /// [`grow_and_push`]: WatchedLists::grow_and_push
    /// [`push_entry_presized`]: WatchedLists::push_entry_presized
    #[inline]
    fn is_growth_step(len: usize) -> bool {
        len == 0 || (len != 1 && len.is_power_of_two())
    }

    /// The capacity the incremental builder would hold after `count` pushes.
    ///
    /// `grow_and_push` doubles: 0 -> 2 -> 4 -> 8 ... and never shrinks, so a
    /// region holding N watches has capacity `max(2, next_power_of_two(N))`
    /// (N = 0 stays 0: nothing was ever pushed, so nothing was ever reserved).
    /// Matching it exactly is what keeps post-build `push_entry` branch
    /// selection — and therefore watch order — identical to the incremental
    /// path.
    fn schedule_capacity(count: u32) -> u32 {
        match count {
            0 => 0,
            1 | 2 => 2,
            n => n.next_power_of_two(),
        }
    }

    /// Lay out every literal's region at its exact size from a pass-1 plan.
    ///
    /// One allocation, `sum(counts)` slots, regions in literal-index order.
    /// `capacity == count` for every literal: no doubling overshoot, no dead
    /// slots. Callers must attach exactly the counted watches afterwards with
    /// [`push_entry_presized`].
    ///
    /// [`push_entry_presized`]: WatchedLists::push_entry_presized
    pub(crate) fn apply_exact_layout(&mut self, plan: &ExactWatchPlan) {
        assert!(
            self.is_unbuilt(),
            "BUG: exact watch layout applied over {} existing entries",
            self.buf_entries.len()
        );
        let num_lits = plan.counts.len();
        if self.meta.len() < num_lits {
            Self::assert_lit_index_bound(num_lits);
            self.meta.resize(num_lits, WatchMeta::default());
        }
        // Sized by CAPACITY, not count. `capacity` is schedule-rounded (see
        // below), and `push_entry`'s in-capacity branch writes at
        // `start + len` whenever `len < capacity` — so a region reserved at
        // only `count` slots would let the first post-build push write into
        // the NEXT region's first slot. Reserving the rounded capacity is what
        // makes that branch's bound real rather than nominal.
        let total: usize = plan
            .counts
            .iter()
            .map(|&c| Self::schedule_capacity(c) as usize)
            .sum();
        // `WatchMeta::offset` is a u32, so the whole buffer must be u32
        // addressable. The incremental builder truncates here silently
        // (`new_offset as u32` in `grow_and_push`); this path refuses.
        let total_u32 =
            u32::try_from(total).expect("BUG: watch entries exceed the u32 buffer offset space");
        let mut next_offset: u32 = 0;
        for (li, &count) in plan.counts.iter().enumerate() {
            self.meta[li] = WatchMeta {
                offset: next_offset,
                len: 0,
                // NOT `count`: `capacity` is what selects which `push_entry`
                // branch every SUBSEQUENT push takes, and the two branches
                // order a region's long suffix differently (in-capacity
                // rotates the first long watch to the end; the relocating
                // path right-shifts). Handing the solve an exact capacity
                // therefore diverges watch order on the first post-build push
                // — demonstrated by review on the sequence
                // [(l,bin),(l,long),(l,long)] + one binary:
                //   incremental -> [B0, B1, L1, L0]
                //   exact       -> [B0, B1, L0, L1]
                // No answer or search count changed on 116 instances, but
                // watch order steers propagation and this is unproven-safe.
                // Rounding to the schedule keeps the state bit-identical to
                // the incremental builder while still removing every
                // ABANDONED region, which is the dominant term.
                capacity: Self::schedule_capacity(count),
                binary_count: 0,
            };
            next_offset += Self::schedule_capacity(count);
        }
        debug_assert_eq!(next_offset, total_u32);
        // Regions past the plan hold no watches; the plan covers every literal
        // the build will touch, so anything beyond it must be an empty region.
        for m in self.meta[num_lits..].iter_mut() {
            *m = WatchMeta::default();
        }
        // Reserve the plan PLUS a relocation headroom, and reserve it exactly.
        //
        // Exactly: `resize`'s amortised growth would round the final size up
        // to a power-of-two-ish capacity, and there is nothing to amortise
        // against — the plan IS the final size of the build.
        //
        // Plus headroom: without it the build ends at `len == capacity`, and
        // the first `grow_and_push` of the following BCP hits `Vec::reserve`
        // on a FULL vector, which doubles the whole buffer to admit the few
        // relocations the solve actually performs (see
        // `WATCH_BUF_EXACT_BUILD_HEADROOM_DIVISOR`). The headroom is spare
        // CAPACITY only — `len` below is still exactly `total` — so every
        // region offset, region capacity, entry, and watch order is unchanged;
        // this buys the relocations somewhere to land, nothing else.
        //
        // Only above `WATCH_BUF_LARGE_ENTRIES`: under 32 MB a doubling is not
        // worth a byte of divergence from the stock policy, and `heap_bytes()`
        // (the clause-DB byte-limit reduction trigger) stays identical there.
        let reserved = if total >= WATCH_BUF_LARGE_ENTRIES {
            total + total / WATCH_BUF_EXACT_BUILD_HEADROOM_DIVISOR
        } else {
            total
        };
        if self.buf_entries.capacity() < reserved {
            self.buf_entries.reserve_exact(reserved);
        }
        self.buf_entries.resize(total, 0);
        self.dead_slots = 0;
    }

    /// Push one watch into its pre-sized region (pass 2 of the exact build).
    ///
    /// Reproduces [`push_entry`]'s resulting order BIT FOR BIT, which is why
    /// it branches on [`is_growth_step`]: on a binary insert the in-capacity
    /// path moves only the FIRST long watch to the end (a rotation of the long
    /// suffix), whereas the relocating path rebuilds the region as
    /// `[binaries][new][longs]` (a right shift of the long suffix). The two
    /// disagree whenever the region holds 2+ long watches, so watch order —
    /// and hence propagation order — depends on which path each push took.
    ///
    /// [`push_entry`]: WatchedLists::push_entry
    /// [`is_growth_step`]: WatchedLists::is_growth_step
    pub(crate) fn push_entry_presized(&mut self, lit: Literal, blocker_raw: u32, clause_raw: u64) {
        let li = lit.index();
        debug_assert!(
            li < self.meta.len(),
            "BUG: exact build pushed to unplanned literal index {li}"
        );
        let entry = pack_entry(blocker_raw, clause_raw);
        let m = self.meta[li];
        let start = m.offset as usize;
        let len = m.len as usize;
        let bc = m.binary_count as usize;
        assert!(
            len < m.capacity as usize,
            "BUG: exact watch region for literal index {li} overflowed \
             (capacity {}, pass 1 undercounted)",
            m.capacity
        );
        if entry_is_binary(entry) {
            if bc < len {
                if Self::is_growth_step(len) {
                    // Relocating path: shift the long suffix right by one.
                    self.buf_entries
                        .copy_within(start + bc..start + len, start + bc + 1);
                } else {
                    // In-capacity path: rotate the first long to the end.
                    self.buf_entries[start + len] = self.buf_entries[start + bc];
                }
            }
            self.buf_entries[start + bc] = entry;
            self.meta[li].binary_count = (bc + 1) as u32;
        } else {
            // Long insert: append at the end, on both paths.
            self.buf_entries[start + len] = entry;
        }
        self.meta[li].len = (len + 1) as u32;
    }

    /// Set up both watches for a clause during the exact build.
    ///
    /// Mirrors [`watch_clause`] but writes into pre-sized regions.
    ///
    /// [`watch_clause`]: WatchedLists::watch_clause
    #[inline]
    pub(crate) fn watch_clause_presized(
        &mut self,
        clause_ref: ClauseRef,
        lit0: Literal,
        lit1: Literal,
        is_binary: bool,
    ) {
        let (w0, w1) = if is_binary {
            (
                Watcher::binary(clause_ref, lit1),
                Watcher::binary(clause_ref, lit0),
            )
        } else {
            (
                Watcher::new(clause_ref, lit1),
                Watcher::new(clause_ref, lit0),
            )
        };
        self.push_entry_presized(lit0, w0.blocker_raw, w0.clause_raw);
        self.push_entry_presized(lit1, w1.blocker_raw, w1.clause_raw);
    }

    /// Push a Watcher to a literal's watch list.
    #[inline]
    pub(crate) fn push_watcher(&mut self, lit: Literal, w: Watcher) {
        self.push_entry(lit, w.blocker_raw, w.clause_raw);
    }

    /// Add a watcher for a literal
    #[inline]
    pub(crate) fn add_watch(&mut self, lit: Literal, watcher: Watcher) {
        self.push_watcher(lit, watcher);
    }

    /// Set up both watches for a clause on its first two literals.
    #[inline]
    pub(crate) fn watch_clause(
        &mut self,
        clause_ref: ClauseRef,
        lit0: Literal,
        lit1: Literal,
        is_binary: bool,
    ) {
        if is_binary {
            self.add_watch(lit0, Watcher::binary(clause_ref, lit1));
            self.add_watch(lit1, Watcher::binary(clause_ref, lit0));
        } else {
            self.add_watch(lit0, Watcher::new(clause_ref, lit1));
            self.add_watch(lit1, Watcher::new(clause_ref, lit0));
        }
    }

    // ─── BCP deferred-copy path ─────────────────────────────────────

    /// Copy a literal's watch entries into the standalone WatchList (deferred buffer).
    ///
    /// After this call, the literal's watch list in the unified buffer has len=0
    /// (capacity/offset preserved) and all its entries are in `deferred`.
    /// The deferred buffer is cleared first.
    ///
    /// Returns `(len, binary_count)` from this literal's region.
    /// BCP compaction preserves all binary entries (they are never dropped),
    /// so the caller can pass this count directly to `restore_from_deferred_with_bc`
    /// without re-scanning (#8465).
    #[inline(always)]
    pub(crate) fn copy_to_deferred(
        &mut self,
        lit: Literal,
        deferred: &mut WatchList,
    ) -> (usize, u32) {
        deferred.entries.clear();
        let m = self.meta[lit.index()];
        let start = m.offset as usize;
        let len = m.len as usize;
        let bc = m.binary_count;
        if len == 0 {
            debug_assert_eq!(bc, 0, "empty watch list cannot have binary entries");
            self.meta[lit.index()].binary_count = 0;
            return (0, 0);
        }
        deferred
            .entries
            .extend_from_slice(&self.buf_entries[start..start + len]);
        // Mark the literal's region as empty. Don't add to dead_slots since
        // we'll restore shortly and want to reuse the capacity.
        self.meta[lit.index()].len = 0;
        self.meta[lit.index()].binary_count = 0;
        (len, bc)
    }

    /// Restore entries from the standalone WatchList back into a literal's region.
    ///
    /// If the deferred buffer's length fits in the literal's existing capacity,
    /// entries are copied in-place. Otherwise, a new region is allocated.
    /// Also handles overflow entries added to this literal during the BCP scan
    /// (e.g., HBR watchers targeting false_lit in probe mode).
    ///
    /// For the no-overflow paths, BCP compaction preserves binary-first order
    /// (binary watchers are never dropped), so we just count leading binaries.
    /// For the overflow path (HBR), we merge maintaining binary-first order.
    pub(crate) fn restore_from_deferred(&mut self, lit: Literal, deferred: &mut WatchList) {
        let li = lit.index();
        let deferred_len = deferred.entries.len();
        let overflow_len = self.meta[li].len as usize;
        let total_len = deferred_len + overflow_len;

        if total_len == 0 {
            return;
        }

        let m = self.meta[li];
        if total_len <= m.capacity as usize && overflow_len == 0 {
            // Fast path: fits in existing capacity, no overflow.
            let start = m.offset as usize;
            self.buf_entries[start..start + deferred_len].copy_from_slice(&deferred.entries);
            self.meta[li].len = deferred_len as u32;
            // Count the binary prefix in the compacted deferred data.
            // NOTE: this is O(binary-prefix) overhead per restore; use
            // restore_from_deferred_with_bc when binary count is known.
            self.meta[li].binary_count = count_binary_prefix(&deferred.entries);
        } else if overflow_len == 0 {
            // Need more capacity, no overflow. Allocate at end.
            let new_capacity = total_len.next_power_of_two().max(4);
            let new_offset = self.buf_entries.len();
            self.reserve_entries(new_capacity);
            self.buf_entries.extend_from_slice(&deferred.entries);
            self.buf_entries.resize(new_offset + new_capacity, 0);
            self.dead_slots += m.capacity as usize;
            let bc = count_binary_prefix(&deferred.entries);
            self.meta[li] = WatchMeta {
                offset: new_offset as u32,
                len: deferred_len as u32,
                capacity: new_capacity as u32,
                binary_count: bc,
            };
        } else {
            // Overflow exists: merge deferred + overflow with binary-first order.
            let start = m.offset as usize;
            let deferred_bc = count_binary_prefix(&deferred.entries) as usize;
            let overflow_bc = m.binary_count as usize;
            debug_assert!(
                overflow_bc <= overflow_len,
                "restore_from_deferred: overflow binary_count ({overflow_bc}) > len ({overflow_len})"
            );
            #[cfg(debug_assertions)]
            {
                debug_assert!(
                    self.buf_entries[start..start + overflow_bc]
                        .iter()
                        .all(|&e| entry_is_binary(e)),
                    "BUG: overflow binary prefix contains a long watch"
                );
                debug_assert!(
                    self.buf_entries[start + overflow_bc..start + overflow_len]
                        .iter()
                        .all(|&e| !entry_is_binary(e)),
                    "BUG: overflow long suffix contains a binary watch"
                );
            }
            let new_capacity = total_len.next_power_of_two().max(4);
            let new_offset = self.buf_entries.len();
            self.reserve_entries(new_capacity);

            self.buf_entries
                .extend_from_slice(&deferred.entries[..deferred_bc]);
            self.buf_entries
                .extend_from_within(start..start + overflow_bc);
            self.buf_entries
                .extend_from_slice(&deferred.entries[deferred_bc..deferred_len]);
            self.buf_entries
                .extend_from_within(start + overflow_bc..start + overflow_len);

            // Pad remaining capacity.
            self.buf_entries.resize(new_offset + new_capacity, 0);
            self.dead_slots += self.meta[li].capacity as usize;
            self.meta[li] = WatchMeta {
                offset: new_offset as u32,
                len: total_len as u32,
                capacity: new_capacity as u32,
                binary_count: (deferred_bc + overflow_bc) as u32,
            };
        }

        deferred.entries.clear();
    }

    /// Restore entries from deferred back with a pre-computed binary count (#8465).
    ///
    /// Identical to [`restore_from_deferred`] for the no-overflow fast path,
    /// but skips the O(n) `count_binary_clauses` scan by accepting the count
    /// from the caller. Used by SEARCH mode BCP where the binary count is
    /// tracked during compaction. PROBE/VIVIFY modes still use the generic
    /// `restore_from_deferred` since HBR overflow can change the binary count.
    ///
    /// REQUIRES: `binary_count` is the exact count of entries in `deferred`
    /// with the binary flag set. Only valid when `overflow_len == 0` (SEARCH mode).
    #[inline]
    pub(crate) fn restore_from_deferred_with_bc(
        &mut self,
        lit: Literal,
        deferred: &mut WatchList,
        binary_count: u32,
    ) {
        let li = lit.index();
        let deferred_len = deferred.entries.len();

        debug_assert_eq!(
            self.meta[li].len, 0,
            "restore_from_deferred_with_bc: overflow_len != 0 for lit {li}"
        );

        if deferred_len == 0 {
            return;
        }

        let m = self.meta[li];
        if deferred_len <= m.capacity as usize {
            // Fast path: fits in existing capacity.
            let start = m.offset as usize;
            self.buf_entries[start..start + deferred_len].copy_from_slice(&deferred.entries);
            self.meta[li].len = deferred_len as u32;
            self.meta[li].binary_count = binary_count;
        } else {
            // Need more capacity. Allocate at end.
            let new_capacity = deferred_len.next_power_of_two().max(4);
            let new_offset = self.buf_entries.len();
            self.reserve_entries(new_capacity);
            self.buf_entries.extend_from_slice(&deferred.entries);
            self.buf_entries.resize(new_offset + new_capacity, 0);
            self.dead_slots += m.capacity as usize;
            self.meta[li] = WatchMeta {
                offset: new_offset as u32,
                len: deferred_len as u32,
                capacity: new_capacity as u32,
                binary_count,
            };
        }

        deferred.entries.clear();
    }

    // ─── Bulk operations ────────────────────────────────────────────

    /// Assert that all watch lists satisfy the binary-first invariant.
    ///
    /// In debug builds, verifies that entries [0..binary_count) have the entry
    /// binary flag set and entries [binary_count..len) do not. No-op in
    /// release builds.
    ///
    /// Replaces the previous `sort_all_binary_first()` which was O(total_watches).
    /// The invariant is now maintained incrementally on every insert/remove.
    pub(crate) fn debug_assert_binary_first(&self) {
        #[cfg(debug_assertions)]
        {
            for li in 0..self.meta.len() {
                let m = self.meta[li];
                let start = m.offset as usize;
                let bc = m.binary_count as usize;
                let len = m.len as usize;
                debug_assert!(
                    bc <= len,
                    "BUG: binary_count ({bc}) > len ({len}) for lit index {li}"
                );
                for i in 0..bc {
                    debug_assert!(
                        entry_is_binary(self.buf_entries[start + i]),
                        "BUG: entry {i} in binary zone (0..{bc}) of lit {li} is not binary"
                    );
                }
                for i in bc..len {
                    debug_assert!(
                        !entry_is_binary(self.buf_entries[start + i]),
                        "BUG: entry {i} in long zone ({bc}..{len}) of lit {li} is binary"
                    );
                }
            }
        }
    }

    /// Remap clause refs in all watch lists using a relocation map.
    ///
    /// Recounts binary entries per literal after remapping since entries may
    /// be dropped (dead clauses). Uses single-pass compaction (matching the
    /// original algorithm) and then recounts binary entries. The binary-first
    /// invariant is preserved because: (a) the input is already binary-first,
    /// (b) the single-pass stable compaction preserves relative order.
    pub(crate) fn remap_clause_refs(&mut self, remap: &[u32]) {
        for li in 0..self.meta.len() {
            let m = self.meta[li];
            let start = m.offset as usize;
            let len = m.len as usize;
            let mut j = 0;
            let mut bc: u32 = 0;
            for i in 0..len {
                let entry = self.buf_entries[start + i];
                let old_offset = entry_clause_off(entry) as usize;
                if old_offset >= remap.len() || remap[old_offset] == u32::MAX {
                    continue;
                }
                let new_offset = remap[old_offset];
                // Keep the low half (blocker + binary flag) and replace the
                // offset half. A `u32` arena offset can never collide with the
                // bit-31 entry flag because the flag lives on the blocker half
                // (#9670, #9773).
                self.buf_entries[start + j] = (entry & 0xFFFF_FFFF) | (u64::from(new_offset) << 32);
                if entry_is_binary(entry) {
                    bc += 1;
                }
                j += 1;
            }
            if j < len {
                self.dead_slots += len - j;
                self.meta[li].len = j as u32;
            }
            self.meta[li].binary_count = bc;
        }
    }

    /// Shrink the unified buffer if dead slots exceed a threshold.
    pub(crate) fn shrink_capacity(&mut self) {
        if self.dead_slots > self.buf_entries.len() / WATCH_DEFRAG_DEAD_SLOT_DIVISOR {
            self.defragment();
        }
    }

    /// Shrink over-provisioned watch lists after reduce_db (#8031).
    ///
    /// After clause deletion, many watch lists retain their peak capacity
    /// despite having far fewer entries. This wastes memory and pollutes
    /// cache lines during BCP scanning. For any list where
    /// `len < capacity / 2`, reduce capacity to `len * 3 / 2` (keeping
    /// modest headroom for future additions).
    ///
    /// In the unified buffer design, "shrinking" a literal's capacity means
    /// marking the excess slots as dead and then triggering defragmentation
    /// to physically reclaim the space.
    ///
    /// Reference: CaDiCaL `collect.cpp:225` (`shrink_vector(ws)` after
    /// `flush_watches`).
    ///
    /// Returns the number of watch lists that were shrunk.
    pub(crate) fn shrink_watch_lists(&mut self) -> u64 {
        let mut shrunk: u64 = 0;
        for li in 0..self.meta.len() {
            let m = &self.meta[li];
            let len = m.len as usize;
            let cap = m.capacity as usize;
            // Only shrink if using less than half of capacity and capacity
            // is non-trivial (skip tiny lists where shrinking saves nothing).
            if cap >= 4 && len < cap / 2 {
                // Target capacity: len * 3/2, floored to at least len.
                let new_cap = (len * 3 / 2).max(len);
                if new_cap < cap {
                    let freed = cap - new_cap;
                    self.dead_slots += freed;
                    self.meta[li].capacity = new_cap as u32;
                    shrunk += 1;
                }
            }
        }

        // If shrinking freed substantial space, defragment to reclaim it.
        if shrunk > 0 {
            self.shrink_capacity();
        }

        shrunk
    }

    /// Compact the unified buffer (Kissat `kissat_defrag_vectors`).
    ///
    /// Sorts non-empty regions by offset and copies forward, reclaiming gaps.
    /// Preserves `binary_count` for each literal's region.
    pub(crate) fn defragment(&mut self) {
        if self.buf_entries.is_empty() {
            self.dead_slots = 0;
            return;
        }

        let mut active: Vec<usize> = (0..self.meta.len())
            .filter(|&li| self.meta[li].len > 0)
            .collect();
        active.sort_by_key(|&li| self.meta[li].offset);

        let mut write_pos: usize = 0;
        for &li in &active {
            let m = self.meta[li];
            let src_start = m.offset as usize;
            let len = m.len as usize;
            if write_pos != src_start {
                self.buf_entries
                    .copy_within(src_start..src_start + len, write_pos);
            }
            self.meta[li] = WatchMeta {
                offset: write_pos as u32,
                len: len as u32,
                capacity: len as u32,
                binary_count: m.binary_count,
            };
            write_pos += len;
        }

        for li in 0..self.meta.len() {
            if self.meta[li].len == 0 {
                self.meta[li] = WatchMeta::default();
            }
        }

        self.buf_entries.truncate(write_pos);
        // Amortized shrink: the copy_within above already compacted the buffer
        // (the actual defrag work). Reallocating to an *exact* fit on every
        // defrag causes grow/shrink realloc thrash on large instances — the
        // next watch insertion immediately reallocates the whole buffer. Only
        // pay the O(n) realloc when at least a third of capacity is dead;
        // otherwise keep the headroom so subsequent grow_and_push is free.
        // Correctness-neutral: capacity management only, len is unchanged.
        // (Kissat's defrag likewise does not shrink_to_fit every pass.)
        if self.buf_entries.capacity() > write_pos + write_pos / 2 {
            self.buf_entries.shrink_to_fit();
        }
        self.dead_slots = 0;
    }

    /// Retain only entries for a literal where the predicate returns `true`.
    ///
    /// Preserves binary-first order (stable compaction) and recounts binary entries.
    pub(crate) fn retain_lit(&mut self, lit: Literal, mut keep: impl FnMut(u64, u32) -> bool) {
        let li = lit.index();
        let m = self.meta[li];
        let start = m.offset as usize;
        let len = m.len as usize;
        let mut j = 0;
        let mut bc: u32 = 0;
        for i in 0..len {
            let entry = self.buf_entries[start + i];
            let clause_raw = entry_clause_raw(entry);
            let blocker_raw = entry_blocker_raw(entry);
            if keep(clause_raw, blocker_raw) {
                self.buf_entries[start + j] = entry;
                if entry_is_binary(entry) {
                    bc += 1;
                }
                j += 1;
            }
        }
        if j < len {
            self.dead_slots += len - j;
            self.meta[li].len = j as u32;
        }
        self.meta[li].binary_count = bc;
    }

    /// Count total watches for a clause (used for verification)
    #[cfg(test)]
    pub(crate) fn count_watches_for_clause(&self, clause_ref: ClauseRef) -> usize {
        let target = clause_ref.0;
        let mut count = 0;
        for li in 0..self.meta.len() {
            let m = self.meta[li];
            let start = m.offset as usize;
            for i in 0..m.len as usize {
                if entry_clause_off(self.buf_entries[start + i]) == target {
                    count += 1;
                }
            }
        }
        count
    }

    /// Heap-backed bytes used by the unified buffer plus the meta table.
    ///
    /// Exposed in production (not `#[cfg(test)]`) so the clause-DB byte-limit
    /// trigger (`Solver::should_reduce_db`) can account for watcher memory in
    /// addition to the arena (#8672). Watches can rival or exceed the arena on
    /// large learned-clause sets.
    pub(crate) fn heap_bytes(&self) -> usize {
        use std::mem::size_of;
        self.buf_entries.capacity() * size_of::<u64>()
            + self.meta.capacity() * size_of::<WatchMeta>()
    }

    /// Capacity of the meta table (for statistics).
    #[cfg(test)]
    pub(crate) fn outer_capacity(&self) -> usize {
        self.meta.capacity()
    }

    /// Freed-but-unreclaimed slots in the unified buffer (tests).
    #[cfg(test)]
    pub(crate) fn dead_slots(&self) -> usize {
        self.dead_slots
    }

    /// Slots in the unified buffer, live and reserved alike (tests).
    #[cfg(test)]
    pub(crate) fn buffer_slots(&self) -> usize {
        self.buf_entries.len()
    }

    /// Get the length of a watch list (kani proofs only)
    #[inline]
    #[cfg(kani)]
    pub(crate) fn watch_count(&self, lit: Literal) -> usize {
        self.meta[lit.index()].len as usize
    }

    /// Capacity of a single literal's watch list region.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn capacity_of(&self, lit: Literal) -> usize {
        self.meta[lit.index()].capacity as usize
    }

    /// Return an immutable view of a literal's watch list.
    #[inline]
    pub(crate) fn get_watches(&self, lit: Literal) -> WatchListView<'_> {
        WatchListView { lists: self, lit }
    }

    /// Return a mutable view of a literal's watch list.
    #[inline]
    pub(crate) fn get_watches_mut(&mut self, lit: Literal) -> WatchListViewMut<'_> {
        WatchListViewMut { lists: self, lit }
    }
}

// ─── Watch list view types ─────────────────────────────────────────

/// Immutable view into a single literal's watch list within a `WatchedLists`.
///
/// Wraps `(&WatchedLists, Literal)` and delegates per-watcher read methods.
pub(crate) struct WatchListView<'a> {
    lists: &'a WatchedLists,
    lit: Literal,
}

impl WatchListView<'_> {
    /// Number of watchers in this list.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.lists.len_of(self.lit)
    }

    /// Allocated capacity for this literal's region.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn capacity(&self) -> usize {
        self.lists.capacity_of(self.lit)
    }

    /// Get the clause reference at watcher index (strips BINARY_FLAG).
    #[inline]
    pub(crate) fn clause_ref(&self, i: usize) -> ClauseRef {
        self.lists.clause_ref(self.lit, i)
    }

    /// Get the raw clause value at watcher index (includes BINARY_FLAG).
    #[inline]
    #[allow(dead_code)] // immutable raw access is used only by diagnostic/test lanes
    pub(crate) fn clause_raw(&self, i: usize) -> u64 {
        self.lists.clause_raw(self.lit, i)
    }

    /// Get the raw blocker value at watcher index.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn blocker_raw(&self, i: usize) -> u32 {
        self.lists.blocker_raw(self.lit, i)
    }

    /// Get the blocker as a `Literal` at watcher index.
    #[inline]
    pub(crate) fn blocker(&self, i: usize) -> Literal {
        self.lists.blocker(self.lit, i)
    }

    /// Check if watcher at index is binary.
    #[inline]
    pub(crate) fn is_binary(&self, i: usize) -> bool {
        self.lists.is_binary(self.lit, i)
    }
}

/// Mutable view into a single literal's watch list within a `WatchedLists`.
///
/// Wraps `(&mut WatchedLists, Literal)` and delegates read/write methods.
pub(crate) struct WatchListViewMut<'a> {
    lists: &'a mut WatchedLists,
    lit: Literal,
}

impl WatchListViewMut<'_> {
    /// Number of watchers in this list.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.lists.len_of(self.lit)
    }

    /// Allocated capacity for this literal's region.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn capacity(&self) -> usize {
        self.lists.capacity_of(self.lit)
    }

    /// Get the clause reference at watcher index (strips BINARY_FLAG).
    #[inline]
    pub(crate) fn clause_ref(&self, i: usize) -> ClauseRef {
        self.lists.clause_ref(self.lit, i)
    }

    /// Get the raw clause value at watcher index (includes BINARY_FLAG).
    #[inline]
    pub(crate) fn clause_raw(&self, i: usize) -> u64 {
        self.lists.clause_raw(self.lit, i)
    }

    /// Get the raw blocker value at watcher index.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn blocker_raw(&self, i: usize) -> u32 {
        self.lists.blocker_raw(self.lit, i)
    }

    /// Get the blocker as a `Literal` at watcher index.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn blocker(&self, i: usize) -> Literal {
        self.lists.blocker(self.lit, i)
    }

    /// Check if watcher at index is binary.
    #[inline]
    pub(crate) fn is_binary(&self, i: usize) -> bool {
        self.lists.is_binary(self.lit, i)
    }

    /// Write a (blocker, clause) pair at position `dst`.
    #[inline]
    pub(crate) fn set_entry(&mut self, dst: usize, blocker_raw: u32, clause_raw: u64) {
        self.lists.set_entry(self.lit, dst, blocker_raw, clause_raw);
    }

    /// Swap-remove element at watcher index (O(1) removal).
    #[inline]
    pub(crate) fn swap_remove(&mut self, i: usize) {
        self.lists.swap_remove(self.lit, i);
    }

    /// Truncate the watch list to `new_len` entries.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn truncate(&mut self, new_len: usize) {
        self.lists.truncate_lit(self.lit, new_len);
    }

    /// Push a `Watcher` to this literal's watch list.
    #[inline]
    pub(crate) fn push_watcher(&mut self, w: Watcher) {
        self.lists.push_watcher(self.lit, w);
    }

    /// Clear all entries in this literal's watch list.
    #[inline]
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn clear(&mut self) {
        self.lists.clear_lit(self.lit);
    }

    /// Raw mutable pointer to the packed-entry region + length.
    ///
    /// See [`WatchedLists::entries_raw_mut`] for safety requirements.
    #[cfg(feature = "raw-pointer-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) fn entries_raw_mut(&mut self) -> (*mut u64, usize) {
        self.lists.entries_raw_mut(self.lit)
    }

    /// Raw mutable pointer + length + binary count for two-phase BCP (#8569).
    ///
    /// See [`WatchedLists::entries_raw_mut_with_bc`] for safety requirements.
    #[cfg(feature = "raw-pointer-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) fn entries_raw_mut_with_bc(&mut self) -> (*mut u64, usize, usize) {
        self.lists.entries_raw_mut_with_bc(self.lit)
    }

    /// Unsafe length update for in-place BCP compaction.
    ///
    /// See [`WatchedLists::set_len_after_bcp_compaction`] for safety requirements.
    #[cfg(feature = "raw-pointer-bcp")]
    #[allow(unsafe_code)]
    #[inline]
    pub(crate) unsafe fn set_len_after_bcp_compaction(&mut self, new_len: usize) {
        // SAFETY: The safety requirement of
        // `WatchedLists::set_len_after_bcp_compaction` is that `new_len <=
        // current_len_of(self.lit)` and that entries in `[0, new_len)` of this
        // literal's watch region remain validly initialized `u64` values. This
        // view holds `self.lit` immutably and exclusively borrows `self.lists`,
        // so the caller's length applies to the same literal being shrunk.
        unsafe {
            self.lists.set_len_after_bcp_compaction(self.lit, new_len);
        }
    }
}
