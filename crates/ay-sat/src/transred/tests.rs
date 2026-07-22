// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for transitive reduction.

use super::*;
use crate::test_util::lit;
use crate::watched::{ClauseRef, WatchedLists, Watcher};

fn build_binary_watches(clauses: &ClauseArena, num_vars: usize) -> WatchedLists {
    let mut watches = WatchedLists::new(num_vars);
    for idx in clauses.indices() {
        if clauses.is_empty_clause(idx) || clauses.len_of(idx) < 2 {
            continue;
        }
        let lit0 = clauses.literal(idx, 0);
        let lit1 = clauses.literal(idx, 1);
        watches.add_watch(lit0, Watcher::binary(ClauseRef(idx as u32), lit1));
        watches.add_watch(lit1, Watcher::binary(ClauseRef(idx as u32), lit0));
    }
    watches
}

#[test]
fn test_transred_simple_transitive() {
    // Create a transitive situation:
    // C0: (~x0 \/ x1)  means x0 -> x1
    // C1: (~x1 \/ x2)  means x1 -> x2
    // C2: (~x0 \/ x2)  means x0 -> x2 (transitive via C0, C1)
    //
    // C2 should be detected as transitive

    let mut clauses = ClauseArena::new();
    let _c0 = clauses.add(&[lit(0, false), lit(1, true)], false); // C0: ~x0 \/ x1
    let _c1 = clauses.add(&[lit(1, false), lit(2, true)], false); // C1: ~x1 \/ x2
    let c2 = clauses.add(&[lit(0, false), lit(2, true)], false); // C2: ~x0 \/ x2

    let watches = build_binary_watches(&clauses, 3);
    let vals = vec![0i8; 6];
    let mut transred = TransRed::new(3);

    let result = transred.run(&clauses, &watches, &vals, clauses.len(), u64::MAX);

    // C2 should be identified as transitive
    assert!(
        result.transitive_clauses.contains(&ClauseRef(c2 as u32)),
        "C2 should be transitive, got: {:?}",
        result.transitive_clauses
    );
}

#[test]
fn test_transred_skips_learned_witnesses() {
    // Regression test for #1818:
    // Transitive reduction must not use LEARNED binary clauses as witnesses
    // to delete ORIGINAL (irredundant) binary clauses.
    //
    // C0: (~x0 \/ x1)  means x0 -> x1  (original)
    // C1: (~x0 \/ x2)  means x0 -> x2  (learned)
    // C2: (~x2 \/ x1)  means x2 -> x1  (learned)
    //
    // If learned clauses were allowed as witnesses, C0 would appear transitive
    // via x0 -> x2 -> x1 and could be deleted unsoundly if the learned
    // clauses are later removed.

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false); // C0: ~x0 \/ x1 (original)
    clauses.add(&[lit(0, false), lit(2, true)], true); // C1: ~x0 \/ x2 (learned)
    clauses.add(&[lit(2, false), lit(1, true)], true); // C2: ~x2 \/ x1 (learned)

    let watches = build_binary_watches(&clauses, 3);
    let vals = vec![0i8; 6];
    let mut transred = TransRed::new(3);

    let result = transred.run(&clauses, &watches, &vals, clauses.len(), u64::MAX);

    assert!(
        !result.transitive_clauses.contains(&ClauseRef(0)),
        "C0 must not be deleted using learned witnesses, got: {:?}",
        result.transitive_clauses
    );
}

#[test]
fn test_transred_skips_derived_irredundant_witnesses() {
    // Regression for #3312:
    // Derived irredundant binaries must not witness deletion of original
    // binary clauses.
    //
    // Original clauses (indices < 2):
    // C0: (~x0 \/ x1)  target
    // C1: (~x0 \/ x2)
    //
    // Derived irredundant clause (index >= 2):
    // C2: (~x2 \/ x1)
    //
    // If C2 is treated as a transitivity witness, C0 can be deleted.

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false); // C0 original target
    clauses.add(&[lit(0, false), lit(2, true)], false); // C1 original
    let c2_off = clauses.len(); // word offset where derived clauses start
    clauses.add(&[lit(2, false), lit(1, true)], false); // C2 derived irredundant

    let watches = build_binary_watches(&clauses, 3);
    let vals = vec![0i8; 6];

    // Baseline: with no original-clause limit, derived clauses can witness C0.
    let mut permissive = TransRed::new(3);
    let baseline = permissive.run(&clauses, &watches, &vals, clauses.len(), u64::MAX);
    assert!(
        baseline.transitive_clauses.contains(&ClauseRef(0)),
        "Expected C0 to appear transitive when derived witnesses are allowed, got {:?}",
        baseline.transitive_clauses
    );

    // Correct behavior: only original clauses (offsets < c2_off) may be witnesses.
    let mut transred = TransRed::new(3);
    let guarded = transred.run(&clauses, &watches, &vals, c2_off, u64::MAX);
    assert!(
        !guarded.transitive_clauses.contains(&ClauseRef(0)),
        "C0 must not be deleted through derived irredundant witnesses, got {:?}",
        guarded.transitive_clauses
    );
}

#[test]
fn test_transred_skips_deleted_witnesses() {
    // Regression for #3312: stale watchers may still reference deleted
    // clauses; transred must not treat those deleted clauses as witnesses.
    //
    // C0: (~x0 \/ x1) original candidate
    // C1: (~x0 \/ x2) original witness path edge
    // C2: (~x2 \/ x1) original witness path edge
    //
    // After deleting C1/C2 from ClauseArena (without removing their watches),
    // C0 must NOT be considered transitive.

    let mut clauses = ClauseArena::new();
    let _c0 = clauses.add(&[lit(0, false), lit(1, true)], false); // C0
    let c1 = clauses.add(&[lit(0, false), lit(2, true)], false); // C1
    let c2 = clauses.add(&[lit(2, false), lit(1, true)], false); // C2

    let watches = build_binary_watches(&clauses, 3);

    // Simulate stale watch entries: clause DB marks C1/C2 deleted while the
    // watch lists still contain their binary watchers.
    clauses.delete(c1);
    clauses.delete(c2);

    let vals = vec![0i8; 6];
    let mut transred = TransRed::new(3);
    let result = transred.run(&clauses, &watches, &vals, clauses.len(), u64::MAX);

    assert!(
        !result.transitive_clauses.contains(&ClauseRef(0)),
        "C0 must not be deleted using deleted-clause witnesses, got: {:?}",
        result.transitive_clauses
    );
}

#[test]
fn test_transred_keeps_one_duplicate_irredundant_clause() {
    // Two duplicate original clauses can witness each other as transitive.
    // Deleting both in the same round is unsound; one copy must remain.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false); // C0
    clauses.add(&[lit(0, false), lit(1, true)], false); // C1 duplicate

    let watches = build_binary_watches(&clauses, 2);
    let vals = vec![0i8; 4];
    let mut transred = TransRed::new(2);
    let result = transred.run(&clauses, &watches, &vals, clauses.len(), u64::MAX);

    assert_eq!(
        result.transitive_clauses.len(),
        1,
        "exactly one duplicate may be removed per round, got: {:?}",
        result.transitive_clauses
    );
}

#[test]
fn test_transred_not_transitive() {
    // Non-transitive situation:
    // C0: (~x0 \/ x1)  means x0 -> x1
    // C1: (~x0 \/ x2)  means x0 -> x2
    // No alternate path from x0 to x2

    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    let watches = build_binary_watches(&clauses, 3);
    let vals = vec![0i8; 6];
    let mut transred = TransRed::new(3);

    let result = transred.run(&clauses, &watches, &vals, clauses.len(), u64::MAX);

    // Neither clause should be transitive
    assert!(
        result.transitive_clauses.is_empty(),
        "No clauses should be transitive, got: {:?}",
        result.transitive_clauses
    );
}

#[test]
fn test_transred_stats() {
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false);

    let watches = build_binary_watches(&clauses, 3);
    let vals = vec![0i8; 6];
    let mut transred = TransRed::new(3);

    transred.run(&clauses, &watches, &vals, clauses.len(), u64::MAX);

    let stats = transred.stats();
    assert_eq!(stats.rounds, 1);
    assert!(stats.propagations > 0);
}

#[test]
fn test_transred_effort_limit_respected() {
    // With effort_limit = 0, no clauses should be checked and no
    // transitive deletions should occur.
    let mut clauses = ClauseArena::new();
    clauses.add(&[lit(0, false), lit(1, true)], false);
    clauses.add(&[lit(1, false), lit(2, true)], false);
    clauses.add(&[lit(0, false), lit(2, true)], false); // transitive

    let watches = build_binary_watches(&clauses, 3);
    let vals = vec![0i8; 6];
    let mut transred = TransRed::new(3);

    // effort_limit = 0 should prevent any work
    let result = transred.run(&clauses, &watches, &vals, clauses.len(), 0);
    assert!(
        result.transitive_clauses.is_empty(),
        "effort_limit=0 should prevent transitive deletion, got: {:?}",
        result.transitive_clauses
    );
}

#[test]
fn test_transred_last_propagations_tracking() {
    let transred = TransRed::new(3);
    assert_eq!(transred.last_propagations(), 0);
}
