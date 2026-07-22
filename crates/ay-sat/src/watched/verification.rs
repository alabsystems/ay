// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kani verification harnesses for watched lists.

use super::*;
use crate::literal::Variable;

/// Watcher struct preserves its fields correctly (non-binary)
#[kani::proof]
fn watcher_fields_preserved() {
    let clause: ClauseRef = kani::any();
    let blocker: Literal = kani::any();

    // Bound to prevent overflow and avoid binary flag collision
    kani::assume(clause.0 < 1000);
    kani::assume(blocker.0 < 1000);

    let watcher = Watcher::new(clause, blocker);

    // Fields are preserved
    assert!(watcher.clause_ref() == clause);
    assert!(watcher.blocker() == blocker);
    assert!(!watcher.is_binary());
}

/// Binary watcher preserves its fields correctly
#[kani::proof]
fn binary_watcher_fields_preserved() {
    let clause: ClauseRef = kani::any();
    let other_lit: Literal = kani::any();

    // Bound to prevent overflow
    kani::assume(clause.0 < 1000);
    kani::assume(other_lit.0 < 1000);

    let watcher = Watcher::binary(clause, other_lit);

    // Fields are preserved, binary flag is set
    assert!(watcher.clause_ref() == clause);
    assert!(watcher.blocker() == other_lit);
    assert!(watcher.is_binary());
}

/// ClauseRef is correctly identified
#[kani::proof]
fn clause_ref_equality() {
    let a: ClauseRef = kani::any();
    let b: ClauseRef = kani::any();

    kani::assume(a.0 < 1000 && b.0 < 1000);

    // Equality is based on inner value
    if a.0 == b.0 {
        assert!(a == b);
    }
    if a != b {
        assert!(a.0 != b.0);
    }
}

/// Literal index calculation is consistent for watched lists
#[kani::proof]
fn literal_index_for_watches() {
    let var: Variable = kani::any();
    kani::assume(var.0 < 100);

    let pos = Literal::positive(var);
    let neg = Literal::negative(var);

    // Positive and negative have different indices
    assert!(pos.index() != neg.index());

    // Both indices are within bounds for a watched list of size 2*num_vars
    let expected_max_index = (var.0 as usize + 1) * 2;
    assert!(pos.index() < expected_max_index);
    assert!(neg.index() < expected_max_index);
}

/// AoS WatchList roundtrip: push then read back
#[kani::proof]
fn watch_list_aos_roundtrip() {
    let blocker_raw: u32 = kani::any();
    let clause_raw: u64 = kani::any();
    kani::assume(blocker_raw < 1000);
    kani::assume(clause_raw < 1000);

    let mut list = WatchList::new();
    list.push(blocker_raw, clause_raw);

    assert_eq!(list.len(), 1);
    assert_eq!(list.blocker_raw(0), blocker_raw);
    assert_eq!(list.clause_raw(0), clause_raw);
    assert_eq!(list.blocker(0), Literal(blocker_raw));
    assert_eq!(
        list.clause_ref(0),
        ClauseRef((clause_raw & !BINARY_FLAG) as u32)
    );
}

/// AoS WatchList binary detection
#[kani::proof]
fn watch_list_aos_binary_roundtrip() {
    let clause: ClauseRef = kani::any();
    let other_lit: Literal = kani::any();
    kani::assume(clause.0 < 1000);
    kani::assume(other_lit.0 < 1000);

    let w = Watcher::binary(clause, other_lit);
    let mut list = WatchList::new();
    list.push_watcher(w);

    assert!(list.is_binary(0));
    assert_eq!(list.clause_ref(0), clause);
    assert_eq!(list.blocker(0), other_lit);
}

/// AoS WatchList swap_remove
#[kani::proof]
fn watch_list_swap_remove() {
    let mut list = WatchList::new();
    list.push(10, 20);
    list.push(30, 40);
    list.push(50, 60);

    assert_eq!(list.len(), 3);

    // Remove first element (swaps last into position 0)
    list.swap_remove(0);
    assert_eq!(list.len(), 2);
    assert_eq!(list.blocker_raw(0), 50);
    assert_eq!(list.clause_raw(0), 60);
}

/// Adding a watch increases the watch count by exactly one
#[kani::proof]
fn watch_add_increases_count() {
    let num_vars = 4;
    let mut watches = WatchedLists::new(num_vars);

    let var_idx: u32 = kani::any();
    kani::assume(var_idx < num_vars as u32);
    let lit = Literal::positive(Variable(var_idx));

    let clause: ClauseRef = kani::any();
    let blocker: Literal = kani::any();
    kani::assume(clause.0 < 100 && blocker.0 < 100);

    let before = watches.watch_count(lit);
    watches.add_watch(lit, Watcher::new(clause, blocker));
    let after = watches.watch_count(lit);

    assert_eq!(after, before + 1);
}

/// Watched list clear resets all counts to zero
#[kani::proof]
fn watch_clear_resets_counts() {
    let num_vars = 4;
    let mut watches = WatchedLists::new(num_vars);

    // Add some watchers
    let lit = Literal::positive(Variable(0));
    watches.add_watch(lit, Watcher::new(ClauseRef(0), Literal(1)));
    watches.add_watch(lit, Watcher::new(ClauseRef(1), Literal(2)));

    // Clear
    watches.clear();

    // All counts should be zero
    for var_idx in 0..num_vars {
        let pos_lit = Literal::positive(Variable(var_idx as u32));
        let neg_lit = Literal::negative(Variable(var_idx as u32));
        assert_eq!(watches.watch_count(pos_lit), 0);
        assert_eq!(watches.watch_count(neg_lit), 0);
    }
}
