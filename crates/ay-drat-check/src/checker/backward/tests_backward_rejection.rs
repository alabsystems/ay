// Copyright 2026 Andrew Yates
// Backward checker rejection and edge case tests.
// Tests that verify the backward checker correctly rejects invalid proofs,
// handles edge cases (empty clause on SAT formula, unit clause rejection),
// and agrees with the forward checker on soundness properties.
//
// Split from tests.rs to stay under the 500-line file limit.

use super::*;
use crate::checker::test_helpers::lit;

#[test]
fn test_backward_rejects_empty_clause_on_sat_formula() {
    // Backward checker must reject a proof that adds the empty clause to a
    // satisfiable formula. The empty clause is discarded by add_clause_internal
    // (cidx=usize::MAX) but the backward pass now verifies discarded ACTIVE
    // clauses via RUP using the original proof step literals.
    //
    // Formula: (a v b), (~a v b) — SAT: b=true.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(1, true)],
    ];
    let steps = vec![ProofStep::Add(vec![])];

    // Forward checker correctly rejects:
    let mut fwd = DratChecker::new(2, false);
    assert!(
        fwd.verify(&clauses, &steps).is_err(),
        "forward checker must reject bogus empty clause"
    );

    // Backward checker also rejects:
    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward checker must reject bogus empty clause"
    );
}

#[test]
fn test_backward_forward_consistency_xor() {
    // Verify forward and backward agree on the same XOR proof.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(0, true), lit(1, false)],
        vec![lit(0, false), lit(1, false)],
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),
        ProofStep::Add(vec![lit(1, false)]),
        ProofStep::Add(vec![]),
    ];
    let mut fwd = DratChecker::new(2, false);
    let mut bwd = BackwardChecker::new(2, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert_eq!(
        fwd_result.is_ok(),
        bwd_result.is_ok(),
        "forward and backward must agree: fwd={fwd_result:?} bwd={bwd_result:?}"
    );
}

#[test]
fn test_backward_with_deletions() {
    // Backward mode correctly undoes deletions (re-adds clauses).
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT (XOR).
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(0, true), lit(1, false)],
        vec![lit(0, false), lit(1, false)],
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),
        ProofStep::Delete(vec![lit(0, true), lit(1, true)]),
        ProofStep::Delete(vec![lit(0, false), lit(1, true)]),
        ProofStep::Add(vec![lit(1, false)]),
        ProofStep::Add(vec![]),
    ];
    let mut fwd = DratChecker::new(2, false);
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward should verify"
    );
    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward should verify"
    );
}

#[test]
fn test_backward_deletion_restore_needed_for_rup() {
    // Regression test: backward checker must properly restore clause data
    // when undoing deletions. The backward pass walks in reverse and must
    // undo deletions (restore clauses to the DB) so that earlier ACTIVE
    // addition steps can use them in their RUP checks.
    //
    // Formula (UNSAT):
    //   C1=(a v b), C2=(~a v b), C3=(a v ~b), C4=(~a v ~b)
    //   This is the XOR encoding: exactly one of {a,b} must be true
    //   and exactly one must be false — contradiction.
    //
    // Proof:
    //   step 1: add (b)       — RUP: ~b => C1 forces a, C4=(~a v ~b) all false => conflict
    //   step 2: delete C1     — remove (a v b) from DB
    //   step 3: add (~b)      — RUP: b => C2 forces b (wait, b is assigned)...
    //                           Actually: ~(~b) = b. Assume b. C3=(a v ~b): ~b=false, forces a.
    //                           C4=(~a v ~b): ~a=false, ~b=false => conflict.
    //   step 4: add ()        — empty clause
    //
    // Backward pass: step 4 (empty clause) → step 3 (~b) → step 2 (undo delete) → step 1 (b).
    // At step 1, C1 must be in the DB (restored by undoing step 2) for the
    // RUP check to succeed.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C1: a v b
        vec![lit(0, false), lit(1, true)],  // C2: ~a v b
        vec![lit(0, true), lit(1, false)],  // C3: a v ~b
        vec![lit(0, false), lit(1, false)], // C4: ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),                  // (b) — RUP
        ProofStep::Delete(vec![lit(0, true), lit(1, true)]), // delete C1=(a v b)
        ProofStep::Add(vec![lit(1, false)]),                 // (~b) — RUP
        ProofStep::Add(vec![]),                              // empty clause
    ];

    // Forward checker: valid proof.
    let mut fwd = DratChecker::new(2, false);
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward should verify"
    );

    // Backward checker: step 1's RUP check for (b) needs C1=(a v b) in the
    // DB. C1 was deleted in step 2, but the backward pass undoes step 2
    // before checking step 1. If clause restore is broken, step 1 fails.
    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward should verify (deletion restore must work)"
    );
}

#[test]
fn test_backward_rejects_empty_clause_after_valid_steps() {
    // A proof with valid intermediate derivations followed by an unjustified
    // empty clause. The backward checker must reject: the intermediate steps
    // are valid but the empty clause itself is not RUP-implied.
    //
    // Formula: (a v b), (~a v b) — SAT: b=true.
    // Proof: add (b) via RUP (valid), then add () (invalid — formula is SAT).
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // a v b
        vec![lit(0, false), lit(1, true)], // ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]), // (b) — valid RUP
        ProofStep::Add(vec![]),             // () — invalid: formula is SAT
    ];

    let mut fwd = DratChecker::new(2, false);
    assert!(
        fwd.verify(&clauses, &steps).is_err(),
        "forward must reject: empty clause not RUP on SAT formula"
    );

    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward must reject: empty clause not RUP on SAT formula"
    );
}

#[test]
fn test_backward_rejects_unit_clause_on_sat_3var() {
    // Backward checker must reject an unjustified unit clause addition.
    // Formula: (a v b v c) — SAT.
    // Proof: add (a) (not RUP — ~a does not cause conflict), then add ().
    let clauses = vec![vec![lit(0, true), lit(1, true), lit(2, true)]];
    let steps = vec![
        ProofStep::Add(vec![lit(0, true)]), // (a) — NOT RUP: ~a leaves b,c free
        ProofStep::Add(vec![]),             // ()
    ];

    let mut fwd = DratChecker::new(3, false);
    assert!(
        fwd.verify(&clauses, &steps).is_err(),
        "forward must reject: (a) not RUP"
    );

    let mut bwd = BackwardChecker::new(3, false);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward must reject: (a) not RUP"
    );
}

#[test]
fn test_backward_empty_clause_already_inconsistent() {
    // When the formula is already UNSAT from original clauses (inconsistent
    // before proof starts), adding an empty clause is fine — both forward
    // and backward should accept.
    let clauses = vec![
        vec![lit(0, true)],  // a
        vec![lit(0, false)], // ~a
    ];
    let steps = vec![ProofStep::Add(vec![])]; // redundant empty clause

    let mut fwd = DratChecker::new(1, false);
    assert!(
        fwd.verify(&clauses, &steps).is_ok(),
        "forward: formula already UNSAT, any proof accepted"
    );

    let mut bwd = BackwardChecker::new(1, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward: formula already UNSAT, any proof accepted"
    );
}

#[test]
fn test_backward_transitive_propagation_unwinding() {
    // Exercises unassign_if_reason with transitive BCP chains.
    //
    // Formula (UNSAT, no BCP from originals):
    //   C1=(a v b), C2=(~a v b), C3=(~b v c), C4=(a v ~c), C5=(~a v ~c)
    //   Resolution: C1+C2 => b. C3 => c. C4+C5 => ~c. Contradiction.
    //
    // Proof: add (b) => unit, BCP: C3 forces c=true (transitive).
    //        add (~c) => simplifies to empty. add () => conflict.
    //
    // Fixed in #5203: unwind_trail_to properly unwinds transitive
    // propagation (c) when undoing step 1, matching drat-trim's
    // unassignUnit behavior.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C1: a v b
        vec![lit(0, false), lit(1, true)],  // C2: ~a v b
        vec![lit(1, false), lit(2, true)],  // C3: ~b v c
        vec![lit(0, true), lit(2, false)],  // C4: a v ~c
        vec![lit(0, false), lit(2, false)], // C5: ~a v ~c
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // (b) — RUP
        ProofStep::Add(vec![lit(2, false)]), // (~c) — simplified to empty
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut fwd = DratChecker::new(3, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(fwd_result.is_ok(), "forward accepts: {fwd_result:?}");

    let mut bwd = BackwardChecker::new(3, false);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert_eq!(
        fwd_result.is_ok(),
        bwd_result.is_ok(),
        "forward and backward must agree: fwd={fwd_result:?} bwd={bwd_result:?}"
    );
}

#[test]
fn test_backward_stale_trail_false_acceptance() {
    // Backward checker must reject a bogus proof on a SAT formula.
    //
    // Formula (SAT: a=true, b=true, c=false):
    //   C1=(a v b), C2=(~a v b), C3=(~b v ~c)
    //
    // Proof claims UNSAT: add (b), add (c), add ().
    //   Forward checker rejects at step 2: (c) is not RUP.
    //   In backward replay mode: step 1 propagates b=true, BCP on C3
    //   forces c=false. Step 2 (c) simplifies to empty → inconsistent.
    //
    // Fixed in #5203: unwind_trail_to properly unwinds all transitive
    // propagations, eliminating stale trail assignments.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C1: a v b
        vec![lit(0, false), lit(1, true)],  // C2: ~a v b
        vec![lit(1, false), lit(2, false)], // C3: ~b v ~c
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]), // (b) — RUP (valid)
        ProofStep::Add(vec![lit(2, true)]), // (c) — NOT RUP (formula is SAT)
        ProofStep::Add(vec![]),             // empty clause
    ];

    let mut fwd = DratChecker::new(3, false);
    let fwd_result = fwd.verify(&clauses, &steps);
    assert!(
        fwd_result.is_err(),
        "forward must reject: formula is SAT, (c) is not RUP"
    );

    let mut bwd = BackwardChecker::new(3, false);
    let bwd_result = bwd.verify(&clauses, &steps);
    assert!(
        bwd_result.is_err(),
        "backward must reject bogus proof on SAT formula: {bwd_result:?}"
    );
}
