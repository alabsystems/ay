// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TermId;

/// Verify: mark_empty_split is idempotent — second call on same term always
/// returns false, for all possible TermId values.
#[kani::proof]
fn proof_empty_split_idempotent() {
    let id: u32 = kani::any();
    let x = TermId(id);
    let mut cache = SkolemCache::new();
    let first = cache.mark_empty_split(x);
    let second = cache.mark_empty_split(x);
    assert!(first, "first mark on fresh cache must return true");
    assert!(!second, "second mark on same term must return false");
}

/// Verify: mark_const_split distinguishes different char offsets,
/// for all possible TermId and offset values (bounded).
#[kani::proof]
fn proof_const_split_offset_distinguishes() {
    let x_id: u32 = kani::any();
    let c_id: u32 = kani::any();
    let off1: u8 = kani::any();
    let off2: u8 = kani::any();
    kani::assume(off1 != off2);

    let x = TermId(x_id);
    let c = TermId(c_id);
    let mut cache = SkolemCache::new();
    let first = cache.mark_const_split(x, c, off1 as usize);
    let second = cache.mark_const_split(x, c, off2 as usize);
    assert!(first, "first offset must be new");
    assert!(second, "different offset must also be new");
}

/// Verify: normalize_var_pair is symmetric — (x,y) and (y,x) produce the
/// same normalized pair, for all possible TermId values.
#[kani::proof]
fn proof_var_split_symmetry() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();
    let x = TermId(x_id);
    let y = TermId(y_id);

    let (a1, b1) = SkolemCache::normalize_var_pair(x, y);
    let (a2, b2) = SkolemCache::normalize_var_pair(y, x);
    assert_eq!(a1, a2, "symmetric inputs must produce same first element");
    assert_eq!(b1, b2, "symmetric inputs must produce same second element");
}

/// Verify: normalize_var_pair output satisfies a <= b (ordering invariant),
/// for all possible TermId values.
#[kani::proof]
fn proof_var_pair_ordered() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();
    let x = TermId(x_id);
    let y = TermId(y_id);

    let (lo, hi) = SkolemCache::normalize_var_pair(x, y);
    assert!(lo <= hi, "normalized pair must be ordered: lo <= hi");
}

/// Verify: push/pop restores empty-split dedup state — a mark before push
/// persists after pop, a mark after push is undone.
#[kani::proof]
fn proof_push_pop_scope_restoration() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();
    kani::assume(x_id != y_id);

    let x = TermId(x_id);
    let y = TermId(y_id);
    let mut cache = SkolemCache::new();

    // Mark x before push — should persist.
    assert!(cache.mark_empty_split(x));
    cache.push();

    // Mark y in inner scope — should be undone.
    assert!(cache.mark_empty_split(y));
    assert!(!cache.mark_empty_split(y), "y already marked in this scope");

    cache.pop();

    // x's mark survives pop; y's mark is undone.
    assert!(
        !cache.mark_empty_split(x),
        "x was marked before push, must persist"
    );
    assert!(
        cache.mark_empty_split(y),
        "y was marked after push, must be undone by pop"
    );
}

/// Verify: mark_var_split deduplicates symmetric pairs — marking (x,y)
/// then (y,x) returns false for the second call.
#[kani::proof]
fn proof_var_split_symmetric_dedup() {
    let x_id: u32 = kani::any();
    let y_id: u32 = kani::any();
    let x = TermId(x_id);
    let y = TermId(y_id);

    let mut cache = SkolemCache::new();
    let first = cache.mark_var_split(x, y);
    let second = cache.mark_var_split(y, x);
    // If x == y, first will be true but second will be false (same normalized key).
    // If x != y, first is true, second is false (symmetric pair normalized to same key).
    assert!(first, "first var split on fresh cache must be true");
    assert!(!second, "symmetric pair must deduplicate");
}

/// Verify: reset clears all state — after reset, previously-marked splits
/// become available again.
#[kani::proof]
fn proof_reset_clears_all_marks() {
    let x_id: u32 = kani::any();
    let x = TermId(x_id);
    let mut cache = SkolemCache::new();

    assert!(cache.mark_empty_split(x));
    assert!(!cache.mark_empty_split(x));
    cache.reset();
    assert!(cache.mark_empty_split(x), "reset must clear all marks");
}
