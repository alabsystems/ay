// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The checked slice accessors, with their bound stated as a native Trust
//! contract clause. Each `requires` moves the index obligation to the CALL
//! SITE, where the BCP loop bounds and the arena's insertion-time validation
//! are visible, instead of leaving the verifier to refute `slice[index]` here
//! -- which it did, correctly: a public function with no stated precondition
//! CAN be called out of range. The panic is unchanged and is still the API.
//!
//! Native clauses are raw grammar, so stock rustc rejects this file at parse
//! time; `checked_stock.rs` is the exact clause-stripped twin every other
//! compiler reads, and `build.rs` refuses drift between the two (the same
//! shape as `ay-proof-common/src/literal.rs`).

/// Slice index for `i8` arrays (val lookup in the BCP hot path).
///
/// Panics when `index` is out of bounds. Keeping this public function checked
/// is required for a sound safe API; callers that have proved a raw-pointer
/// access valid can use the explicitly unsafe helpers below.
#[inline(always)]
pub fn val_at(vals: &[i8], index: usize) -> i8
    requires index < vals.len()
{
    vals[index]
}

/// Checked slice index for `u32` arrays (arena word lookup in BCP hot path).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used for arena
/// literal access during the BCP replacement scan where the clause offset +
/// literal index is known to be within the arena's allocated words.
#[inline(always)]
pub fn word_at(words: &[u32], index: usize) -> u32
    requires index < words.len()
{
    words[index]
}

/// Checked slice read for `u32` arrays (SoA blocker/clause_ref in BCP hot path).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used in the SoA
/// blocker fast path to read blocker values (#8243).
/// With SoA layout, 32 blockers fit per cache line (vs 16 packed u64 entries),
/// doubling the blocker scan throughput.
#[inline(always)]
pub fn blocker_at(blockers: &[u32], index: usize) -> u32
    requires index < blockers.len()
{
    blockers[index]
}

/// Checked mutable slice write for `u32` arrays (SoA blocker store in BCP).
///
/// Like [`blocker_at`], this panics on an out-of-bounds index. Used in the BCP
/// compaction loop for the speculative copy `blockers[j] = blockers[i]` (#8243).
#[inline(always)]
pub fn blocker_set(blockers: &mut [u32], index: usize, value: u32)
    requires index < blockers.len()
{
    blockers[index] = value;
}

/// Checked slice read for `u64` arrays (SoA clause_ref in BCP slow path).
///
/// Like [`blocker_at`], this panics on an out-of-bounds index. It is only
/// accessed on blocker miss, avoiding cache pollution on the fast path (#8243).
/// Each clause_ref word is a `u64` carrying the binary flag at bit 32 plus the
/// full 32-bit clause word offset in the low bits (#9670).
#[inline(always)]
pub fn clause_ref_at(clause_refs: &[u64], index: usize) -> u64
    requires index < clause_refs.len()
{
    clause_refs[index]
}

/// Checked mutable slice write for `u64` arrays (SoA clause_ref store).
///
/// Like [`blocker_at`], this panics on an out-of-bounds index.
#[inline(always)]
pub fn clause_ref_set(clause_refs: &mut [u64], index: usize, value: u64)
    requires index < clause_refs.len()
{
    clause_refs[index] = value;
}

/// Checked slice read for `u64` arrays (watch entry load in BCP hot path).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used in the BCP
/// blocker fast path to read packed watch entries.
#[inline(always)]
pub fn entry_at(entries: &[u64], index: usize) -> u64
    requires index < entries.len()
{
    entries[index]
}

/// Checked mutable slice write for `u64` arrays (watch entry store in BCP).
///
/// Like [`entry_at`], this panics on an out-of-bounds index. Used in the BCP
/// blocker fast path for the speculative copy `entries[j] = entries[i]`.
/// The compaction invariant `j <= i < entries.len()` guarantees safety.
#[inline(always)]
pub fn entry_set(entries: &mut [u64], index: usize, value: u64)
    requires index < entries.len()
{
    entries[index] = value;
}

/// Checked mutable slice write for `i8` arrays (val store in enqueue).
///
/// Like [`val_at`], this panics on an out-of-bounds index. Used in `enqueue()`
/// to set `vals[lit] = 1` and `vals[¬lit] = -1`.
#[inline(always)]
pub fn val_set(vals: &mut [i8], index: usize, value: i8)
    requires index < vals.len()
{
    vals[index] = value;
}
