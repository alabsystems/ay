// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for Globally Blocked Clause Elimination (conditioning).

use super::*;
use crate::clause_arena::ClauseArena;
use crate::test_util::lit_signed as lit;

fn make_vals(num_vars: usize, assignment: &[(i32, bool)]) -> Vec<i8> {
    let mut vals = vec![0i8; num_vars * 2];
    for &(v, positive) in assignment {
        let l = if positive { lit(v) } else { lit(-v) };
        vals[l.index()] = 1;
        vals[l.negated().index()] = -1;
    }
    vals
}

#[test]
fn test_conditioning_basic_blocked_clause() {
    // Formula: (1 ∨ 2) ∧ (¬1 ∨ 3) ∧ (¬2 ∨ 3)
    // With assignment: 1=T, 2=T, 3=T
    // All clauses satisfied.
    // No all-negative clauses → no conditional literals → all are autarky.
    // Every candidate should be globally blocked.
    let mut db = ClauseArena::new();
    db.add(&[lit(1), lit(2)], false);
    db.add(&[lit(-1), lit(3)], false);
    db.add(&[lit(-2), lit(3)], false);

    let vals = make_vals(3, &[(1, true), (2, true), (3, true)]);
    let frozen = vec![0u32; 3];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(3);
    cond.ensure_num_vars(3);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    assert!(
        !result.eliminated.is_empty(),
        "Should find globally blocked clauses"
    );
    // Full autarky set: all 3 variables are autarky.
    for elim in &result.eliminated {
        assert_eq!(
            elim.witnesses.len(),
            3,
            "Full autarky witness set should contain all assigned variables"
        );
    }
}

#[test]
fn test_conditioning_no_blocked_with_unsatisfied() {
    // Formula: (1) ∧ (¬1)
    // With assignment: 1=T → clause (¬1) is unsatisfied.
    // Variable 1 is conditional → clause (1) has no autarky → not blocked.
    let mut db = ClauseArena::new();
    db.add(&[lit(1)], false);
    db.add(&[lit(-1)], false);

    let vals = make_vals(1, &[(1, true)]);
    let frozen = vec![0u32; 1];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(1);
    cond.ensure_num_vars(1);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    assert!(
        result.eliminated.is_empty(),
        "No clauses should be eliminated for UNSAT formula"
    );
}

#[test]
fn test_conditioning_respects_frozen() {
    let mut db = ClauseArena::new();
    db.add(&[lit(1), lit(2)], false);
    db.add(&[lit(-1), lit(3)], false);
    db.add(&[lit(-2), lit(3)], false);

    let vals = make_vals(3, &[(1, true), (2, true), (3, true)]);
    let mut frozen = vec![0u32; 3];
    frozen[0] = 1; // Freeze variable 1

    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(3);
    cond.ensure_num_vars(3);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    for c in &result.eliminated {
        let lits = db.literals(c.clause_idx);
        for &l in lits {
            assert_ne!(
                l.variable().index(),
                0,
                "Frozen variable should not appear in eliminated clauses"
            );
        }
    }
}

#[test]
fn test_conditioning_statistics() {
    let mut db = ClauseArena::new();
    db.add(&[lit(1), lit(2)], false);

    let vals = make_vals(2, &[(1, true), (2, true)]);
    let frozen = vec![0u32; 2];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(2);
    cond.ensure_num_vars(2);
    let _result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    assert_eq!(cond.stats().rounds, 1);
    assert!(cond.stats().candidates_checked > 0);
}

/// Test that the fixpoint refinement loop (Phase 1b) correctly promotes
/// autarky variables to conditional through mixed-clause propagation.
///
/// Without fixpoint refinement, the initial partition from all-negative
/// clauses (Phase 1) would leave var 2 as autarky, allowing clause (2)
/// to be incorrectly eliminated. The fixpoint detects that in the mixed
/// clause (1 ∨ ¬2), ALL positive literals (lit 1) are conditional,
/// so the false literal ¬2's negation (var 2) must also become
/// conditional — preventing unsound elimination.
///
/// Related: #3432, #3751
#[test]
fn test_conditioning_fixpoint_refinement_promotes_autarky() {
    // Formula: (¬1) ∧ (1 ∨ ¬2) ∧ (2)
    // Assignment: 1=T, 2=T
    //
    // Phase 1 (initial partition):
    //   C1=(¬1): all-negative → var 1 conditional
    //   C2=(1 ∨ ¬2): mixed → candidate
    //   C3=(2): positive → candidate
    //   After phase 1: var 1=conditional, var 2=autarky
    //
    // Phase 1b (fixpoint refinement):
    //   C2=(1 ∨ ¬2): lit 1 positive+conditional, lit ¬2 negative.
    //   ALL positive lits conditional → promote var 2 to conditional.
    //   After fixpoint: var 1=conditional, var 2=conditional
    //
    // Phase 2: no autarky variables → no eliminations.
    // Without fixpoint: var 2 autarky → C3=(2) would be eliminated (WRONG).
    let mut db = ClauseArena::new();
    let _c1 = db.add(&[lit(-1)], false); // (¬1)
    let _c2 = db.add(&[lit(1), lit(-2)], false); // (1 ∨ ¬2)
    let _c3 = db.add(&[lit(2)], false); // (2)

    let vals = make_vals(2, &[(1, true), (2, true)]);
    let frozen = vec![0u32; 2];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(2);
    cond.ensure_num_vars(2);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    // With fixpoint: both vars conditional → no autarky → no eliminations.
    assert!(
        result.eliminated.is_empty(),
        "Fixpoint refinement should promote var 2 to conditional, \
         preventing any eliminations. Got {} eliminations.",
        result.eliminated.len()
    );
}

/// Test fixpoint refinement across multiple iterations: a chain of
/// promotions where each iteration discovers new conditional variables.
///
/// Chain: C1 makes var 1 conditional → C2 promotes var 2 → C3 promotes
/// var 3. Only var 4 remains autarky.
///
/// Related: #3432
#[test]
fn test_conditioning_fixpoint_chain_propagation() {
    // Formula:
    //   C1=(¬1)        — all-negative → var 1 conditional
    //   C2=(1 ∨ ¬2)    — fixpoint iter 1: var 2 → conditional
    //   C3=(2 ∨ ¬3)    — fixpoint iter 2: var 3 → conditional
    //   C4=(3 ∨ 4)     — candidate
    // Assignment: 1=T, 2=T, 3=T, 4=T
    //
    // After fixpoint: vars 1,2,3 conditional, var 4 autarky.
    // C4 has autarky lit (var 4) → eliminated.
    // Without fixpoint: vars 2,3,4 autarky → more eliminations.
    let mut db = ClauseArena::new();
    let _c1 = db.add(&[lit(-1)], false); // (¬1)
    let _c2 = db.add(&[lit(1), lit(-2)], false); // (1 ∨ ¬2)
    let _c3 = db.add(&[lit(2), lit(-3)], false); // (2 ∨ ¬3)
    let c4 = db.add(&[lit(3), lit(4)], false); // (3 ∨ 4)

    let vals = make_vals(4, &[(1, true), (2, true), (3, true), (4, true)]);
    let frozen = vec![0u32; 4];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(4);
    cond.ensure_num_vars(4);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    // Only C4 should be eliminated (var 4 is the sole autarky variable).
    assert_eq!(
        result.eliminated.len(),
        1,
        "Expected exactly 1 elimination (C4). Got {}.",
        result.eliminated.len()
    );
    assert_eq!(
        result.eliminated[0].clause_idx, c4,
        "Eliminated clause should be C4"
    );

    // Witness set should contain only var 4 (the sole autarky variable).
    assert_eq!(
        result.eliminated[0].witnesses.len(),
        1,
        "Witness should be the single autarky variable (var 4)"
    );
    assert_eq!(
        result.eliminated[0].witnesses[0].variable().index(),
        3, // var 4 is internal index 3
        "Witness variable should be var 4 (internal index 3)"
    );
}

/// Test that root_vals divergence from vals causes root-satisfied clauses
/// to be skipped, changing the conditional/autarky partition.
///
/// When vals and root_vals differ (var 1 is root-assigned, excluded from
/// vals but present in root_vals), clause (1 ∨ ¬2) is root-satisfied and
/// skipped. Without root_vals divergence (vals == root_vals), the same
/// clause contributes to the partition differently.
///
/// Related: #3902
#[test]
fn test_conditioning_root_vals_divergence() {
    // Variables: 1, 2, 3
    // Root assignment: var 1=T at level 0
    // Non-root: var 2=T, var 3=T
    //
    // root_vals: var 1=T, var 2=T, var 3=T
    // vals: var 1=UNASSIGNED, var 2=T, var 3=T
    //
    // Formula:
    //   C1=(1 ∨ ¬2)  — root_satisfied (lit 1: root_vals>0, vals==0) → SKIP
    //   C2=(¬3)       — all-negative → var 3 conditional
    //   C3=(2 ∨ 3)   — candidate. var 2=autarky, var 3=conditional → eliminated
    //
    // Without root_vals (using vals for both root_vals):
    //   C1=(1 ∨ ¬2)  — vals[lit1]=0, root_vals[lit1]=0 → NOT root_satisfied
    //     lit 1 val=0, lit ¬2 val=-1 → has_positive=false, has_negative=true
    //     → marks var 2 as conditional!
    //   C2=(¬3)       — var 3 conditional
    //   C3=(2 ∨ 3)   — vars 2,3 both conditional → NO autarky → NOT eliminated

    let mut db = ClauseArena::new();
    let _c1 = db.add(&[lit(1), lit(-2)], false); // (1 ∨ ¬2)
    let _c2 = db.add(&[lit(-3)], false); // (¬3)
    let c3 = db.add(&[lit(2), lit(3)], false); // (2 ∨ 3)

    // root_vals: all three vars true
    let root_vals = make_vals(3, &[(1, true), (2, true), (3, true)]);
    // vals: var 1 unassigned (root-level exclusion), vars 2,3 true
    let vals = make_vals(3, &[(2, true), (3, true)]);

    let frozen = vec![0u32; 3];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(3);
    cond.ensure_num_vars(3);

    // With root_vals divergence: C1 garbage-collected, var 2 stays autarky → C3 eliminated
    let result = cond.condition_round(
        &mut db,
        &vals,
        &root_vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );
    assert_eq!(
        result.eliminated.len(),
        1,
        "With root_vals divergence, C3 should be eliminated. Got {} eliminations.",
        result.eliminated.len()
    );
    assert_eq!(
        result.eliminated[0].clause_idx, c3,
        "Eliminated clause should be C3"
    );
    // C1 should be marked for garbage collection (root-satisfied).
    assert_eq!(
        result.root_satisfied.len(),
        1,
        "C1 should be root-satisfied and marked for garbage collection"
    );

    // Without root_vals divergence: C1 not skipped, var 2 becomes conditional → no eliminations
    let mut cond2 = Conditioning::new(3);
    cond2.ensure_num_vars(3);
    let result_no_diverge = cond2.condition_round(
        &mut db,
        &vals,
        &vals, // same array for both
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );
    assert!(
        result_no_diverge.eliminated.is_empty(),
        "Without root_vals divergence, C1 makes var 2 conditional → no eliminations. \
         Got {} eliminations.",
        result_no_diverge.eliminated.len()
    );
}

/// Per-candidate refinement eliminates clauses the global fixpoint misses.
///
/// Formula: C1=(¬1), C2=(1 ∨ ¬2), C3=(¬1 ∨ 2). Assignment: 1=T, 2=T.
///
/// Global fixpoint: C1 makes var 1 conditional. C2=(1 ∨ ¬2) has all
/// positive lits (var 1) conditional → promotes var 2. After fixpoint:
/// both vars conditional → C3 has no autarky → NOT eliminated.
///
/// Per-candidate refinement for C3=(¬1 ∨ 2): var 1 is conditional, but
/// lit(¬1) IS in C3 → var 1 is NOT unassigned → C2 never triggers →
/// var 2 stays autarky → C3 HAS autarky literal lit(2) → eliminated.
///
/// Reference: CaDiCaL condition.cpp:565-705 (per-candidate refinement).
#[test]
fn test_conditioning_per_candidate_refinement() {
    let mut db = ClauseArena::new();
    let _c1 = db.add(&[lit(-1)], false); // (¬1)
    let _c2 = db.add(&[lit(1), lit(-2)], false); // (1 ∨ ¬2)
    let c3 = db.add(&[lit(-1), lit(2)], false); // (¬1 ∨ 2) — candidate

    let vals = make_vals(2, &[(1, true), (2, true)]);
    let frozen = vec![0u32; 2];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(2);
    cond.ensure_num_vars(2);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    // Per-candidate refinement: C3 contains lit(¬1), so the conditional
    // literal (var 1) is NOT unassigned for this candidate. The promotion
    // chain (var 1 → var 2) never triggers. var 2 stays autarky →
    // C3 has autarky literal (var 2) → eliminated.
    assert_eq!(
        result.eliminated.len(),
        1,
        "Per-candidate refinement should eliminate C3. Got {} eliminations.",
        result.eliminated.len()
    );
    assert_eq!(
        result.eliminated[0].clause_idx, c3,
        "Eliminated clause should be C3"
    );

    // Witness should include var 2 (autarky).
    assert!(
        result.eliminated[0]
            .witnesses
            .iter()
            .any(|w| w.variable().index() == 1), // var 2 = internal index 1
        "Witness should include var 2 (internal index 1)"
    );
}

/// Regression test: per-candidate refinement must check the NEGATION of
/// the conditional literal against the candidate clause, not the variable.
///
/// CaDiCaL condition.cpp:574: `is_in_candidate_clause(-conditional_lit)`
/// checks the negated literal. Previously AY checked CANDIDATE_BIT on the
/// variable, which conflated `lit` with `~lit`. This caused unsound GBCE
/// on UNSAT formulas where a conditional literal appeared POSITIVELY in
/// the candidate clause.
///
/// Formula: C1=(¬1 ∨ ¬2 ∨ ¬4), C2=(1 ∨ 3), C3=(1 ∨ ¬3), C4=(¬1 ∨ ¬2 ∨ 4)
/// Root assignment: var 2 = true (at level 0, excluded from total_vals)
/// Total assignment: var 1=T, var 3=T, var 4=T (var 2 unassigned)
///
/// This is UNSAT. Conditioning must NOT eliminate C2=(1 ∨ 3).
#[test]
fn test_conditioning_literal_polarity_candidate_check() {
    // 4 variables: var 0 (DIMACS 1), var 1 (DIMACS 2), var 2 (DIMACS 3), var 3 (DIMACS 4)
    let mut db = ClauseArena::new();
    let _c1 = db.add(&[lit(-1), lit(-2), lit(-4)], false); // (¬1 ∨ ¬2 ∨ ¬4)
    let c2 = db.add(&[lit(1), lit(3)], false); // (1 ∨ 3)
    let _c3 = db.add(&[lit(1), lit(-3)], false); // (1 ∨ ¬3)
    let _c4 = db.add(&[lit(-1), lit(-2), lit(4)], false); // (¬1 ∨ ¬2 ∨ 4)

    // Root: var 1 (DIMACS 2) assigned true → unassigned in total_vals.
    // Total_vals: var 0 (1)=T, var 2 (3)=T, var 3 (4)=T, var 1 (2)=unassigned.
    let vals = make_vals(4, &[(1, true), (3, true), (4, true)]);
    // Root_vals includes var 1 (DIMACS 2).
    let root_vals = make_vals(4, &[(1, true), (2, true), (3, true), (4, true)]);
    let frozen = vec![0u32; 4];
    let reason_marks = vec![0u32; 20]; // enough for any clause index

    let mut cond = Conditioning::new(4);
    cond.ensure_num_vars(4);
    let result = cond.condition_round(
        &mut db,
        &vals,
        &root_vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    // The formula is UNSAT. Conditioning must NOT eliminate any clause.
    assert!(
        !result.eliminated.iter().any(|e| e.clause_idx == c2),
        "BUG: C2=(1 ∨ 3) was eliminated by conditioning on an UNSAT formula. \
         This is the literal-polarity candidate check regression. \
         Eliminated {} clauses: {:?}",
        result.eliminated.len(),
        result
            .eliminated
            .iter()
            .map(|e| e.clause_idx)
            .collect::<Vec<_>>()
    );
}

/// Regression test for #5052 / #5066 Fix 1: conditioning must return
/// root-satisfied clause indices in `ConditionResult.root_satisfied`
/// so the caller can garbage-collect them.
#[test]
fn test_conditioning_root_satisfied_returned_for_gc() {
    // 3 variables: var 0 (DIMACS 1), var 1 (DIMACS 2), var 2 (DIMACS 3)
    // Root assignment: var 0 = true at level 0
    // Total vals: var 1=T, var 2=T (var 0 unassigned in total_vals)
    let mut db = ClauseArena::new();
    let c0 = db.add(&[lit(1), lit(2)], false); // root-satisfied via lit(1)
    let _c1 = db.add(&[lit(-2), lit(3)], false); // not root-satisfied
    let _c2 = db.add(&[lit(1), lit(-3)], false); // root-satisfied via lit(1)

    // root_vals: var 0=T, var 1=T, var 2=T
    let root_vals = make_vals(3, &[(1, true), (2, true), (3, true)]);
    // total_vals: var 0 unassigned, var 1=T, var 2=T
    let total_vals = make_vals(3, &[(2, true), (3, true)]);

    let frozen = vec![0u32; 3];
    let reason_marks = vec![0u32; db.len()];

    let mut cond = Conditioning::new(3);
    cond.ensure_num_vars(3);
    let result = cond.condition_round(
        &mut db,
        &total_vals,
        &root_vals,
        &frozen,
        &reason_marks,
        1,
        1000,
        100_000,
    );

    // C0 and C2 are root-satisfied (lit(1) is true in root_vals, unassigned in total_vals).
    assert_eq!(
        result.root_satisfied.len(),
        2,
        "Expected 2 root-satisfied clauses, got {:?}",
        result.root_satisfied
    );
    assert!(
        result.root_satisfied.contains(&c0),
        "C0 should be root-satisfied, got {:?}",
        result.root_satisfied
    );
}

/// Test the dynamic propagation limit computation.
#[test]
fn test_compute_prop_limit_scales_with_propagations() {
    let limit = Conditioning::compute_prop_limit(0, 100, 200);
    assert!(limit >= 200, "Expected >= 200, got {limit}");
    let limit = Conditioning::compute_prop_limit(100_000, 100, 200);
    assert!(limit >= 200, "Expected >= 200, got {limit}");
    let limit = Conditioning::compute_prop_limit(10_000_000, 100, 200);
    assert!((200..=10_000_000).contains(&limit), "Got {limit}");
}

/// Test the clause-variable ratio guard.
#[test]
fn test_should_skip_ratio() {
    assert!(!Conditioning::should_skip_ratio(200, 100));
    assert!(Conditioning::should_skip_ratio(10100, 100));
    assert!(Conditioning::should_skip_ratio(100, 0));
    assert!(!Conditioning::should_skip_ratio(10000, 100));
}

/// Test round-robin scheduling with the conditioned bit.
#[test]
fn test_conditioning_round_robin_scheduling() {
    let mut db = ClauseArena::new();
    let _c0 = db.add(&[lit(1), lit(2)], false);
    let _c1 = db.add(&[lit(3), lit(4)], false);
    let _c2 = db.add(&[lit(5), lit(6)], false);
    let vals = make_vals(
        6,
        &[
            (1, true),
            (2, true),
            (3, true),
            (4, true),
            (5, true),
            (6, true),
        ],
    );
    let frozen = vec![0u32; 6];
    let reason_marks = vec![0u32; db.len()];
    let mut cond = Conditioning::new(6);
    cond.ensure_num_vars(6);
    let result = cond.condition_round(&mut db, &vals, &vals, &frozen, &reason_marks, 1, 2, 100_000);
    assert_eq!(
        result.eliminated.len(),
        2,
        "Should eliminate 2 (max_eliminations=2)"
    );
    assert_eq!(cond.stats().candidates_checked, 2);
    assert_eq!(cond.stats().rounds, 1);
}
