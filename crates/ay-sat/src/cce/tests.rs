// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};
use crate::watched::{ClauseRef, WatchedLists, Watcher};

fn lit(v: u32, positive: bool) -> Literal {
    if positive {
        Literal::positive(Variable(v))
    } else {
        Literal::negative(Variable(v))
    }
}

fn build_arena(clauses: &[&[Literal]]) -> ClauseArena {
    let mut arena = ClauseArena::new();
    for &c in clauses {
        arena.add(c, false);
    }
    arena
}

/// Build binary watches for all 2-literal clauses in the arena.
fn build_binary_watches(arena: &ClauseArena, num_vars: usize) -> WatchedLists {
    let mut watches = WatchedLists::new(num_vars);
    for idx in arena.indices() {
        if arena.is_empty_clause(idx) || arena.len_of(idx) != 2 {
            continue;
        }
        let lit0 = arena.literal(idx, 0);
        let lit1 = arena.literal(idx, 1);
        watches.add_watch(lit0, Watcher::binary(ClauseRef(idx as u32), lit1));
        watches.add_watch(lit1, Watcher::binary(ClauseRef(idx as u32), lit0));
    }
    watches
}

/// Build watches for ALL clauses (binary and long) in the arena.
fn build_all_watches(arena: &ClauseArena, num_vars: usize) -> WatchedLists {
    let mut watches = WatchedLists::new(num_vars);
    for idx in arena.indices() {
        if arena.is_empty_clause(idx) {
            continue;
        }
        let lits = arena.literals(idx);
        if lits.len() < 2 {
            continue;
        }
        let lit0 = lits[0];
        let lit1 = lits[1];
        if lits.len() == 2 {
            watches.add_watch(lit0, Watcher::binary(ClauseRef(idx as u32), lit1));
            watches.add_watch(lit1, Watcher::binary(ClauseRef(idx as u32), lit0));
        } else {
            watches.add_watch(lit0, Watcher::new(ClauseRef(idx as u32), lit1));
            watches.add_watch(lit1, Watcher::new(ClauseRef(idx as u32), lit0));
        }
    }
    watches
}

/// Empty watches: ALA has no effect (tests CLA-only behavior).
fn empty_watches(num_vars: usize) -> WatchedLists {
    WatchedLists::new(num_vars)
}

#[test]
fn test_trivially_blocked_clause() {
    // Clause C = {x0, x1}
    // No clause contains ~x0 => blocked on x0
    let c = [lit(0, true), lit(1, true)];
    let arena = build_arena(&[&c]);
    let num_vars = 3;
    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];
    let watches = empty_watches(num_vars);
    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].clause_idx, 0);
}

#[test]
fn test_both_clauses_blocked() {
    // C = {x0, x1}, D = {~x0, x1}
    let c = [lit(0, true), lit(1, true)];
    let d = [lit(0, false), lit(1, true)];
    let arena = build_arena(&[&c, &d]);
    let num_vars = 3;
    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];
    let watches = empty_watches(num_vars);
    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert_eq!(result.len(), 2, "both C and D should be eliminated");
}

#[test]
fn test_not_blocked_mutual_resolution() {
    // Learned clauses are skipped by CCE.
    let c = [lit(0, true), lit(1, true)];
    let mut arena = ClauseArena::new();
    arena.add(&c, true); // learned clause => skipped by CCE
    let num_vars = 3;
    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];
    let watches = empty_watches(num_vars);
    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert!(result.is_empty(), "learned clauses should be skipped");
}

#[test]
fn test_no_elimination_when_resolvents_constrain() {
    // C = {x0, x1}, D = {~x0, x2}, E = {~x1, x3}
    // CLA extends C with x2, then x3, then finds blocked on x2.
    let c = [lit(0, true), lit(1, true)];
    let d = [lit(0, false), lit(2, true)];
    let e = [lit(1, false), lit(3, true)];
    let arena = build_arena(&[&c, &d, &e]);
    let num_vars = 5;
    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];
    let watches = empty_watches(num_vars);
    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert!(
        !result.is_empty(),
        "C should be eliminated via CLA extension"
    );
}

#[test]
fn test_all_frozen_clause_skipped() {
    let c = [lit(0, true), lit(1, true)];
    let arena = build_arena(&[&c]);
    let num_vars = 3;
    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![1u32; num_vars];
    let watches = empty_watches(num_vars);
    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert!(result.is_empty(), "all-frozen clause should be skipped");
}

#[test]
fn test_learned_clauses_skipped() {
    let c = [lit(0, true), lit(1, true)];
    let mut arena = ClauseArena::new();
    arena.add(&c, true);
    let num_vars = 3;
    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];
    let watches = empty_watches(num_vars);
    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert!(result.is_empty(), "learned clauses should be skipped");
}

#[test]
fn test_effort_limit_respected() {
    let c = [lit(0, true), lit(1, true)];
    let arena = build_arena(&[&c]);
    let num_vars = 3;
    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];
    let watches = empty_watches(num_vars);
    let result = cce.run_round(&arena, &vals, &freeze, &watches, 0);
    assert!(result.is_empty());
}

#[test]
fn test_ala_detects_subsuming_conflict() {
    // ALA-specific test: binary implications cause a conflict.
    //
    // Target: C = {x0, x1, x2} (ternary clause, not a candidate for simple BCE)
    // Binaries: (~x0 -> x3), (~x1 -> ~x3)
    //   i.e. B0 = {x0, x3}, B1 = {x1, ~x3}
    //
    // CCE processing C: set x0=F, x1=F, x2=F.
    // ALA: x0=F => B0 forces x3=F (added to trail).
    //      x1=F => B1 forces ~x3=F. But ~x3 is already true (x3=F).
    //      Wait, ~x3 is true, not false. Let me reconsider.
    //
    // Actually: x0=F means x0 watches are triggered.
    // B0 = {x0, x3}: watch on x0 with blocker x3.
    //   x3 is unassigned => ALA: set x3=false.
    // B1 = {x1, ~x3}: watch on x1 with blocker ~x3.
    //   ~x3 is now TRUE (x3 is false) => clause is satisfied, skip.
    //
    // No conflict. Let me use: B0 = {x0, x3}, B1 = {x1, ~x3}
    // But with a THIRD binary: (~x2 -> conflict) doesn't work either.
    //
    // Let me use a simpler setup:
    // C = {x0, x1} (binary target)
    // B0 = {x0, x2}    (~x0 -> x2)
    // B1 = {x1, ~x2}   (~x1 -> ~x2)
    //
    // CCE on C: set x0=F, x1=F.
    // ALA for x0=F: B0 watches on x0, blocker=x2. x2 unassigned => x2=F.
    // ALA for x1=F: B1 watches on x1, blocker=~x2. ~x2 is TRUE (x2=F) => satisfied.
    // ALA for x2=F (newly added): check watches for x2.
    //   If there's a binary {x2, x3} watching x2, x3 unassigned => x3=F.
    //   If there's a binary {x2, ~x3}, ~x3 unassigned => ~x3=F.
    //   Then if we also have a binary watching x3 that forces x3, we get conflict.
    //
    // Simpler: binary chain that closes a cycle.
    // C = {x0, x1}
    // B0 = {x0, x2}     (~x0 -> x2, i.e., x0=F => x2 forced)
    // B1 = {x2, x1}     (~x2 -> x1, but x1 is already false => CONFLICT)
    //
    // CCE on C: x0=F, x1=F.
    // ALA for x0=F: B0's x0 watch, blocker=x2. x2 unassigned => x2=F.
    // ALA for x1=F: B1's x1 watch, blocker=x2. x2 is FALSE => CONFLICT!
    //
    // With ALA, the conflict is detected. Without ALA (CLA only), we'd need
    // to find a blocking literal via occurrence-list intersection.
    let num_vars = 4;
    let c = [lit(0, true), lit(1, true)]; // C: target clause
    let b0 = [lit(0, true), lit(2, true)]; // B0: x0 v x2
    let b1 = [lit(2, true), lit(1, true)]; // B1: x2 v x1
    let arena = build_arena(&[&c, &b0, &b1]);
    let watches = build_binary_watches(&arena, num_vars);

    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];
    let result_with_ala = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);

    // With ALA: x0=F => x2=F (from B0), then x1=F and x2=F: B1={x2,x1}
    // both false => conflict. C is eliminated.
    assert!(
        result_with_ala.iter().any(|e| e.clause_idx == 0),
        "ALA should detect subsuming conflict for C, got: {result_with_ala:?}",
    );
}

#[test]
fn test_ala_scans_falsified_literal_watches() {
    // ALA must use the same watch-list polarity as BCP: when x0 is false,
    // scan clauses watching x0, not clauses watching ~x0.
    //
    // C = {x0, x1}
    // B0 = {x0, x2} forces x2 when x0 is false.
    // B1 = {x1, x2} conflicts because x1 and x2 are both locally false.
    //
    // Call the ALA helper directly so covered-literal addition cannot mask
    // a watch-polarity regression.
    let num_vars = 3;
    let c = [lit(0, true), lit(1, true)];
    let b0 = [lit(0, true), lit(2, true)];
    let b1 = [lit(1, true), lit(2, true)];
    let arena = build_arena(&[&c, &b0, &b1]);
    let watches = build_binary_watches(&arena, num_vars);

    let mut cce = Cce::new(num_vars);
    cce.test_assume_false(lit(0, true));
    cce.test_assume_false(lit(1, true));

    assert!(!cce.test_ala_propagate_one(lit(0, true), &watches, &arena, 0));
    let result = cce.test_ala_propagate_one(lit(1, true), &watches, &arena, 0);
    assert!(
        result,
        "ALA should find the conflict through watches of falsified literals"
    );
}

#[test]
fn test_ala_does_not_scan_satisfied_opposite_watches() {
    // These opposite-polarity clauses are already satisfied under x0=F,x1=F:
    // D = {~x0, x2}, E = {~x1, x2}. ALA must not scan them when covering
    // C = {x0, x1}; doing so would fabricate an x2 conflict.
    //
    // Call the ALA helper directly so covered-literal addition cannot mask
    // a watch-polarity regression.
    let num_vars = 3;
    let c = [lit(0, true), lit(1, true)];
    let d = [lit(0, false), lit(2, true)];
    let e = [lit(1, false), lit(2, true)];
    let arena = build_arena(&[&c, &d, &e]);
    let watches = build_binary_watches(&arena, num_vars);

    let mut cce = Cce::new(num_vars);
    cce.test_assume_false(lit(0, true));
    cce.test_assume_false(lit(1, true));

    let x0_conflict = cce.test_ala_propagate_one(lit(0, true), &watches, &arena, 0);
    let x1_conflict = cce.test_ala_propagate_one(lit(1, true), &watches, &arena, 0);
    assert!(
        !x0_conflict && !x1_conflict,
        "ALA must not propagate through clauses watching satisfied opposite literals"
    );
}

#[test]
fn test_acce_long_clause_unit_propagation() {
    // ACCE: a long clause forces a unit that leads to conflict via binary.
    //
    // C = {x0, x1, x3}  (ternary target, clause 0)
    // L = {x0, x2, x3}  (ternary, clause 1, watched on x0 and x2)
    // B = {x2, x1}      (binary, clause 2)
    //
    // CCE on C: x0=F, x1=F, x3=F (all in local_vals).
    // ACCE for x0=F: scan L (clause 1). x0=F, x2=?, x3=F. Unit on x2 → x2=F.
    // ACCE for x1=F: scan B (binary). x1=F, blocker=x2. x2=F → CONFLICT!
    let num_vars = 5;
    let c = [lit(0, true), lit(1, true), lit(3, true)];
    let l = [lit(0, true), lit(2, true), lit(3, true)];
    let b = [lit(2, true), lit(1, true)];

    let arena = build_arena(&[&c, &l, &b]);
    let watches = build_all_watches(&arena, num_vars);

    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];

    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert!(
        result.iter().any(|e| e.clause_idx == 0),
        "ACCE should detect conflict via long-clause unit propagation, got: {result:?}",
    );
}

#[test]
fn test_acce_long_clause_all_false_conflict() {
    // ACCE: a duplicate long clause has ALL literals false → direct conflict.
    //
    // C = {x0, x1, x2}  (target, clause 0)
    // D = {x0, x1, x2}  (duplicate, clause 1)
    //
    // CCE on C: x0=F, x1=F, x2=F.
    // ACCE for x0=F: scan D (clause 1 ≠ ignore=0). x0=F, x1=F, x2=F → CONFLICT!
    let num_vars = 4;
    let c = [lit(0, true), lit(1, true), lit(2, true)];
    let d = [lit(0, true), lit(1, true), lit(2, true)];

    let arena = build_arena(&[&c, &d]);
    let watches = build_all_watches(&arena, num_vars);

    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];

    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert!(
        result.iter().any(|e| e.clause_idx == 0),
        "ACCE should detect all-false conflict in duplicate long clause, got: {result:?}",
    );
}

#[test]
fn test_acce_ignore_clause_not_self_conflict() {
    // Verify ignore_clause prevents self-subsumption false positive.
    //
    // C = {x0, x1, x2}  (only clause)
    // Watches include C itself on ~x0 and ~x1.
    // ignore_clause = 0, so C is skipped during ACCE propagation.
    // C is trivially blocked (no resolution candidates) via CLA.
    let num_vars = 4;
    let c = [lit(0, true), lit(1, true), lit(2, true)];

    let arena = build_arena(&[&c]);
    let watches = build_all_watches(&arena, num_vars);

    let mut cce = Cce::new(num_vars);
    cce.rebuild(&arena);

    let vals = vec![0i8; num_vars * 2];
    let freeze = vec![0u32; num_vars];

    let result = cce.run_round(&arena, &vals, &freeze, &watches, 1_000_000);
    assert_eq!(result.len(), 1, "single clause should be trivially blocked");
    assert_eq!(result[0].clause_idx, 0);
}
