// Copyright 2026 Andrew Yates
// Core-first BCP tests for the backward DRAT checker (#5268).
// Extracted from tests.rs for the 500-line limit (#5142).

use super::*;
use crate::checker::test_helpers::lit;

#[test]
fn test_backward_core_first_marks_watches() {
    // Verify that mark_active sets the `core` flag on watch entries.
    // After backward checking, ACTIVE clauses that participate in the
    // proof should be marked, while unused clauses should not.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT XOR.
    // All 4 clauses are needed for the proof.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // (b) — RUP via C0+C1
        ProofStep::Add(vec![lit(1, false)]), // (~b) — RUP via C2+C3
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut bwd = BackwardChecker::new(2, false);
    assert!(bwd.verify(&clauses, &steps).is_ok());

    // The proof needs (b) and (~b) to derive the empty clause.
    // (b) requires C0 and C1 (or a subset). (~b) requires C2 and C3.
    // At least some of C0-C3 should be ACTIVE.
    let active_count = (0..4).filter(|&i| bwd.is_active(i)).count();
    assert!(
        active_count >= 2,
        "at least 2 original clauses should be ACTIVE, got {active_count}"
    );
}

#[test]
fn test_backward_core_first_propagation_complex() {
    // Exercise core-first BCP with a non-trivial proof where the backward
    // pass actually uses two-pass propagation. The key is having both
    // ACTIVE and non-ACTIVE clauses in the watch lists simultaneously.
    //
    // Formula (UNSAT):
    //   C0=(a v b), C1=(~a v b), C2=(a v ~b), C3=(~a v ~b)
    //   C4=(c v d), C5=(~c v d)  ← SAT fragment, not needed
    // Proof: add (b) via RUP, add (~b) via RUP, add () — only needs C0-C3.
    // C4, C5 should NOT be ACTIVE.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
        vec![lit(2, true), lit(3, true)],   // C4: c v d (unused)
        vec![lit(2, false), lit(3, true)],  // C5: ~c v d (unused)
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // (b) — RUP
        ProofStep::Add(vec![lit(1, false)]), // (~b) — RUP
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut fwd = DratChecker::new(4, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward");

    let mut bwd = BackwardChecker::new(4, false);
    assert!(bwd.verify(&clauses, &steps).is_ok(), "backward");

    // C4 and C5 should not be ACTIVE (not needed for the proof).
    // The backward checker's core-first BCP should still work correctly
    // with non-ACTIVE watches in the watch lists.
    assert!(!bwd.is_active(4), "C4 should NOT be ACTIVE");
    assert!(!bwd.is_active(5), "C5 should NOT be ACTIVE");
}

#[test]
fn test_backward_adaptive_prep_toggle() {
    // Verify the adaptive prep toggle (drat-trim.c:647-652).
    // With a multi-step proof, the backward pass should adaptively switch
    // between core-first and single-pass BCP based on resolution depth.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b), (c v d), (~c v d),
    //          (c v ~d), (~c v ~d) — UNSAT (two independent XOR blocks).
    // Proof: derive (b), derive (d), derive (~b), derive (~d), derive ().
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, true)],  // ~a v b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
        vec![lit(2, true), lit(3, true)],   // c v d
        vec![lit(2, false), lit(3, true)],  // ~c v d
        vec![lit(2, true), lit(3, false)],  // c v ~d
        vec![lit(2, false), lit(3, false)], // ~c v ~d
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // (b) — RUP
        ProofStep::Add(vec![lit(3, true)]),  // (d) — RUP
        ProofStep::Add(vec![lit(1, false)]), // (~b) — RUP
        ProofStep::Add(vec![lit(3, false)]), // (~d) — RUP
        ProofStep::Add(vec![]),              // empty clause
    ];

    let mut fwd = DratChecker::new(4, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward");

    let mut bwd = BackwardChecker::new(4, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward with prep toggle"
    );
}

#[test]
fn test_backward_core_first_with_deletions() {
    // Core-first BCP must work correctly when deletions are interleaved.
    // When a deletion is undone in the backward pass, the restored watches
    // should carry the correct core flag.
    //
    // Formula: (a v b), (~a v b), (a v ~b), (~a v ~b) — UNSAT XOR.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // C0: a v b
        vec![lit(0, false), lit(1, true)],  // C1: ~a v b
        vec![lit(0, true), lit(1, false)],  // C2: a v ~b
        vec![lit(0, false), lit(1, false)], // C3: ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),                  // (b) — RUP
        ProofStep::Delete(vec![lit(0, true), lit(1, true)]), // delete C0
        ProofStep::Add(vec![lit(1, false)]),                 // (~b) — RUP
        ProofStep::Add(vec![]),                              // empty clause
    ];

    let mut fwd = DratChecker::new(2, false);
    assert!(fwd.verify(&clauses, &steps).is_ok(), "forward");

    let mut bwd = BackwardChecker::new(2, false);
    assert!(
        bwd.verify(&clauses, &steps).is_ok(),
        "backward with core-first + deletions"
    );
}

#[test]
fn test_backward_core_first_soundness_reject_invalid() {
    // Core-first BCP must not introduce false acceptances.
    // An invalid proof must still be rejected with core-first enabled.
    //
    // Formula: (a v b), (~a v b) — SAT (b=T).
    // Proof: add (c) via vacuous RAT, add empty clause — not RUP.
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // a v b
        vec![lit(0, false), lit(1, true)], // ~a v b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(2, true)]), // (c) — vacuous RAT
        ProofStep::Add(vec![]),             // empty clause — not RUP
    ];

    let mut fwd = DratChecker::new(3, true);
    assert!(fwd.verify(&clauses, &steps).is_err(), "forward must reject");

    let mut bwd = BackwardChecker::new(3, true);
    assert!(
        bwd.verify(&clauses, &steps).is_err(),
        "backward with core-first must reject invalid proof"
    );
}
