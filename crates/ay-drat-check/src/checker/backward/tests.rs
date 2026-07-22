// Copyright 2026 Andrew Yates
// Tests for the backward DRAT checker.
// Pigeonhole and soundness regression tests are in tests_regression.rs.

use super::*;
use crate::checker::test_helpers::lit;

#[test]
fn test_backward_simple_proof() {
    // Same test as forward checker: 4 clauses encoding x XOR y,
    // proof derives x=true, y=true, then empty clause.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(0, true), lit(1, false)],
        vec![lit(0, false), lit(1, false)],
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),
        ProofStep::Add(vec![lit(1, true)]),
        ProofStep::Delete(vec![lit(0, true), lit(1, true)]),
        ProofStep::Add(vec![]),
    ];
    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward must accept");
    let mut bwd = BackwardChecker::new(2, false);
    assert!(bwd.verify(&clauses, &steps).is_ok(), "backward must accept");
}

#[test]
fn test_backward_soft_delete_updates_occurrences() {
    let clause = vec![lit(0, false), lit(1, true), lit(0, false)];
    let neg_pivot = lit(0, false);
    let mut checker = BackwardChecker::new(2, true);
    checker.add_original_tracking(&clause);
    assert_eq!(checker.inner.occ_lists[neg_pivot.index()], vec![0]);

    let cidx = checker
        .delete_forward(&clause)
        .expect("the tracked clause should be present");
    assert!(checker.inner.occ_lists[neg_pivot.index()].is_empty());

    checker.restore_clause(cidx);
    assert_eq!(checker.inner.occ_lists[neg_pivot.index()], vec![cidx]);
}

#[test]
fn test_backward_rejects_invalid_proof() {
    let clauses = vec![vec![lit(0, true), lit(1, true)]];
    let steps = vec![ProofStep::Add(vec![lit(0, false)])];
    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_err(), "forward must reject");
    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward must reject"
    );
}

#[test]
fn test_backward_rejects_no_empty_clause() {
    let clauses = vec![
        vec![lit(0, true), lit(1, true), lit(2, true)],
        vec![lit(0, false), lit(1, true), lit(2, true)],
    ];
    let steps = vec![ProofStep::Add(vec![lit(1, true), lit(2, true)])];
    let mut fwd = DratChecker::new(3, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(fwd_result.is_err(), "forward must reject: no empty clause");
    let mut bwd = BackwardChecker::new(3, false);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(bwd_result.is_err());
    assert!(bwd_result.unwrap_err().to_string().contains("empty clause"));
}

#[test]
fn test_backward_already_inconsistent() {
    let clauses = vec![vec![lit(0, true)], vec![lit(0, false)]];
    let steps = vec![];
    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward must accept");
    let mut bwd = BackwardChecker::new(2, false);
    assert!(bwd.verify(&clauses, &steps).is_ok(), "backward must accept");
}

#[test]
fn test_backward_skips_non_active_clauses() {
    // Proof has both needed and unneeded intermediate clauses.
    // The backward checker should skip verification of unneeded ones.
    //
    // Formula: (a), (~a v b), (~b) — UNSAT via unit propagation chain.
    let clauses = vec![
        vec![lit(0, true)],                // a
        vec![lit(0, false), lit(1, true)], // ~a v b
        vec![lit(1, false)],               // ~b
    ];
    // Proof: add an unnecessary clause (c v d), then derive empty.
    // The unnecessary clause should NOT be verified in backward mode.
    let steps = vec![
        ProofStep::Add(vec![lit(2, true), lit(3, true)]), // unnecessary: c v d
        ProofStep::Add(vec![]),                           // empty clause
    ];
    let mut fwd = DratChecker::new(4, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward must accept");
    let mut bwd = BackwardChecker::new(4, false);
    assert!(bwd.verify(&clauses, &steps).is_ok(), "backward must accept");
}

#[test]
fn test_backward_tautological_clause_no_crash() {
    // Regression test: adding a tautological clause (a v ~a v b) in the
    // proof should not crash the backward checker. add_clause_internal
    // discards tautologies without inserting into the arena, so the
    // backward pass must handle the usize::MAX sentinel in StepRecord.
    let clauses = vec![vec![lit(0, true)], vec![lit(0, false)]];
    let steps = vec![
        // Tautology: (a v ~a v b) — discarded by add_clause_internal
        ProofStep::Add(vec![lit(0, true), lit(0, false), lit(1, true)]),
        ProofStep::Add(vec![]), // empty clause
    ];
    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward must accept");
    let mut bwd = BackwardChecker::new(2, false);
    assert!(bwd.verify(&clauses, &steps).is_ok(), "backward must accept");
}

#[test]
fn test_backward_satisfied_clause_no_crash() {
    // Adding a clause that is already satisfied under the current
    // assignment is discarded by add_clause_internal. The backward
    // checker must handle this without crashing.
    //
    // Formula: (a) — forces a=true via unit propagation.
    // Proof adds (a v b) which is satisfied (a is true), then adds empty.
    let clauses = vec![
        vec![lit(0, true)],  // a (forces a=true)
        vec![lit(0, false)], // ~a (makes formula inconsistent)
    ];
    let steps = vec![ProofStep::Add(vec![])];
    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward must accept");
    let mut bwd = BackwardChecker::new(2, false);
    assert!(bwd.verify(&clauses, &steps).is_ok(), "backward must accept");
}

#[test]
fn test_backward_rat_vacuous() {
    // Backward checking with RAT enabled (vacuous RAT).
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT (XOR).
    // Proof: add (c) via RAT (pivot c, no ~c in DB — vacuous),
    //        then derive (a) via RUP, then empty clause.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, true)],  // ~a v b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true)]), // (c) — vacuous RAT with pivot c
        ProofStep::Add(vec![lit(0, true)]), // (a) — RUP: ~a -> b, ~b -> contradiction
        ProofStep::Add(vec![]),             // empty clause
    ];
    let mut fwd = DratChecker::new(3, true);
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward should verify"
    );
    let mut bwd = BackwardChecker::new(3, true);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward should verify"
    );
}

#[test]
fn test_backward_multi_step_dependency_chain() {
    // Exercise mark_rup_dependencies with a multi-step derivation chain.
    // Formula: (a v b), (~a v c), (~b v c), (~c v d), (~d)
    // UNSAT: a v b, ~a -> c, ~b -> c, so c. c -> d, ~d contradiction.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(2, true)],
        vec![lit(1, false), lit(2, true)],
        vec![lit(2, false), lit(3, true)],
        vec![lit(3, false)],
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true)]),
        ProofStep::Add(vec![lit(3, true)]),
        ProofStep::Add(vec![]),
    ];
    let mut fwd = DratChecker::new(4, false);
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward should verify"
    );
    let mut bwd = BackwardChecker::new(4, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward should verify"
    );
}

// Rejection and edge case tests are in tests_backward_rejection.rs.

// -- Pseudo-unit deletion protection tests (drat-trim.c:806-814) --

#[test]
fn test_backward_pseudo_unit_deletion_skipped() {
    // Regression test for #5306: deleting a clause that is the propagation
    // reason for a literal must be silently skipped (drat-trim.c:807-814).
    //
    // Important: original clauses must ALL be binary (no units), because
    // add_clause_internal simplifies clauses during insertion — a binary
    // clause with one falsified literal becomes a unit and is stored as [lit],
    // which makes is_reason_for_first_lit return false (requires len >= 2).
    //
    // Formula: (a v b), (~a v ~b), (a v ~b), (~a v b) — XOR, UNSAT.
    // All binary, no BCP from originals.
    //
    // Proof: add (a) — RUP. BCP: C1=(~a v ~b) propagates ~b with reason C1.
    //        Then delete C1. Must be skipped (pseudo-unit protection).
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, false)], // C1: ~a v ~b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, true)],  // C3: ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),                    // (a) — RUP
        ProofStep::Delete(vec![lit(0, false), lit(1, false)]), // delete C1 — reason for ~b
        ProofStep::Add(vec![lit(1, true)]),                    // (b) — always OK, inconsistent
        ProofStep::Add(vec![]),                                // empty clause
    ];

    let mut fwd = DratChecker::new(2, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(fwd_result.is_ok(), "forward must accept: {fwd_result:?}");
    assert!(
        fwd.stats.pseudo_unit_skips > 0,
        "forward checker must skip pseudo-unit deletion"
    );

    let mut bwd = BackwardChecker::new(2, false);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(bwd_result.is_ok(), "backward must accept: {bwd_result:?}");
    assert!(
        bwd.stats().pseudo_unit_skips > 0,
        "backward checker must skip pseudo-unit deletion"
    );
}

#[test]
fn test_backward_rejects_stale_assignment_after_unit_deletion() {
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),
        ProofStep::Delete(vec![lit(0, true)]),
        ProofStep::Add(vec![lit(0, false)]),
        ProofStep::Add(vec![]),
    ];
    let mut checker = BackwardChecker::new(1, true);
    assert!(checker.verify(&[], &steps).is_err());
    assert_eq!(checker.inner.stats.pseudo_unit_skips, 1);
}

#[test]
fn test_pseudo_unit_deletion_forward_checker() {
    // Forward-only pseudo-unit test. Same XOR formula as above.
    // After deriving (a), C1=(~a v ~b) is the reason for ~b.
    // Delete of C1 must be skipped.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, false)], // C1: ~a v ~b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, true)],  // C3: ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]),                    // (a) — RUP
        ProofStep::Delete(vec![lit(0, false), lit(1, false)]), // delete C1 — reason for ~b
    ];
    let mut fwd = DratChecker::new(2, false);
    let _result = fwd.verify(&clauses, &steps);
    // No empty clause so verify returns Err. We only care about pseudo_unit_skips.
    assert_eq!(
        fwd.stats.pseudo_unit_skips, 1,
        "forward checker must skip deletion of pseudo-unit clause C1"
    );
}

// Core-first BCP tests (#5268) are in tests_core_first.rs.

// Clause reduction tests (drat-trim.c:174-179, 935-950) are in tests_clause_reduction.rs.
