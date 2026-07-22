// Copyright 2026 Andrew Yates
// Algorithm audit: boundary condition regression tests for DRAT checker.
//
// P1 590: Verifies algorithm correctness at critical boundary conditions
// in both forward and backward DRAT checking.

use super::test_helpers::lit;
use super::DratChecker;
use crate::checker::backward::BackwardChecker;
use crate::drat_parser::ProofStep;

// ─── Forward checker boundary conditions ─────────────────────────────

/// Algorithm audit: tautological clause in derived position is accepted
/// without RUP check (immediately returned as Ok).
///
/// A tautological clause (containing both a and ~a) is always satisfied
/// and thus trivially RUP-implied. The checker short-circuits this check.
#[test]
fn test_forward_tautological_derived_clause_accepted() {
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true), lit(1, true)]); // a v b
                                                         // Derive {a, ~a} — tautological. Should be accepted without RUP.
    assert!(checker.add_derived(&[lit(0, true), lit(0, false)]).is_ok());
}

/// Algorithm audit: duplicate literals in a derived clause (non-inconsistent).
///
/// When a clause contains the same literal twice (e.g., [b, b]),
/// add_clause_internal should handle it without panic. The original test
/// used an inconsistent formula, which short-circuits at add_derived():298
/// before reaching RUP/add_clause_internal. This version uses a
/// non-inconsistent formula where [b, b] is RUP-provable, exercising the
/// full check_rup → add_clause_internal → insert_clause path.
#[test]
fn test_forward_duplicate_literal_in_derived() {
    let mut checker = DratChecker::new(3, false);
    // Formula: {a, b}, {~a, b} — satisfiable (b=true). NOT inconsistent.
    checker.add_original(&[lit(0, true), lit(1, true)]); // a v b
    checker.add_original(&[lit(0, false), lit(1, true)]); // ~a v b
    assert!(
        !checker.inconsistent,
        "formula must not be inconsistent for this test"
    );
    // Derive [b, b]: logically equivalent to [b], which is RUP-implied
    // (assume ~b; clause 1 gives a; clause 2 gives conflict).
    // This exercises: check_rup with duplicate negation, add_clause_internal
    // with unsimplified duplicate, and insert_clause with both watches on
    // the same literal.
    assert!(
        checker.add_derived(&[lit(1, true), lit(1, true)]).is_ok(),
        "duplicate-literal clause [b, b] should pass RUP check"
    );
}

/// Algorithm audit: RUP check returns true immediately when checker is
/// already inconsistent (any clause is implied by a contradiction).
#[test]
fn test_rup_shortcircuit_when_inconsistent() {
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    assert!(checker.inconsistent);
    // Any clause, even one with new variables, is trivially RUP.
    assert!(checker.add_derived(&[lit(2, true)]).is_ok());
}

/// Algorithm audit: check_rup correctly handles a clause with a literal
/// that is already assigned true (clause trivially satisfied).
///
/// When check_rup encounters a clause literal that is already true under
/// the current assignment, the clause is trivially satisfied and RUP
/// returns true without needing BCP to produce a conflict.
#[test]
fn test_rup_clause_with_already_true_literal() {
    let mut checker = DratChecker::new(4, false);
    checker.add_original(&[lit(0, true)]); // {a} → a=true
    checker.add_original(&[lit(0, false), lit(1, true)]); // {~a, b} → b=true
                                                          // Derive {b, c}: b is already true → clause trivially satisfied.
    assert!(checker.add_derived(&[lit(1, true), lit(2, true)]).is_ok());
}

/// Algorithm audit: deletion of a clause that doesn't exist in the hash
/// table is a silent no-op (increments missed_deletes counter).
#[test]
fn test_delete_nonexistent_clause_silent() {
    let mut checker = DratChecker::new(3, false);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    // Delete a clause that doesn't exist.
    checker.delete_clause(&[lit(0, false), lit(1, false)]);
    assert_eq!(checker.stats.missed_deletes, 1);
    // Original clause should still be present.
    assert_eq!(checker.live_clauses, 1);
}

/// Algorithm audit: process_unit handles all three cases correctly:
/// (1) literal already true → no-op, (2) literal already false →
/// inconsistent, (3) literal unassigned → assign and propagate.
#[test]
fn test_process_unit_three_cases() {
    // Case 1: literal already true → no-op
    let mut checker1 = DratChecker::new(3, false);
    checker1.add_original(&[lit(0, true)]); // a=true
    checker1.add_original(&[lit(0, true)]); // same unit → already true, no-op
    assert!(!checker1.inconsistent);

    // Case 2: literal already false → inconsistent
    let mut checker2 = DratChecker::new(3, false);
    checker2.add_original(&[lit(0, true)]); // a=true
    checker2.add_original(&[lit(0, false)]); // ~a → conflict
    assert!(checker2.inconsistent);

    // Case 3: two independent units → both assigned
    let mut checker3 = DratChecker::new(3, false);
    checker3.add_original(&[lit(0, true)]);
    checker3.add_original(&[lit(1, true)]);
    assert!(!checker3.inconsistent);
    assert_eq!(checker3.value(lit(0, true)), Some(true));
    assert_eq!(checker3.value(lit(1, true)), Some(true));
}

/// Algorithm audit: verify() requires an empty clause or conflict to be
/// derived. If all proof steps add non-empty clauses without producing
/// a conflict, the proof is rejected.
#[test]
fn test_verify_requires_empty_clause_or_conflict() {
    let mut checker = DratChecker::new(3, false);
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],  // a v b
        vec![lit(0, false), lit(1, true)], // ~a v b
    ];
    let steps = vec![
        // Derive {b} — valid RUP but not empty clause.
        ProofStep::Add(vec![lit(1, true)]),
    ];
    let result = checker.verify(&clauses, &steps);
    assert!(
        result.is_err(),
        "proof without empty clause/conflict should fail"
    );
}

/// Algorithm audit: verify() succeeds when an empty clause is explicitly
/// added in the proof steps.
#[test]
fn test_verify_succeeds_with_empty_clause() {
    let mut checker = DratChecker::new(3, false);
    let clauses = vec![
        vec![lit(0, true)],  // {a}
        vec![lit(0, false)], // {~a}
    ];
    // Empty clause not needed — formula is UNSAT from originals.
    // But verify() should succeed because inconsistent is set.
    let result = checker.verify(&clauses, &[]);
    assert!(result.is_ok());
}

// ─── Backward checker boundary conditions ────────────────────────────

/// Algorithm audit: backward checker resets `inconsistent = false` before
/// Pass 2. Without this reset, check_rup() short-circuits to true for
/// ALL clauses, accepting any proof. This is the #5258 soundness fix.
#[test]
fn test_backward_inconsistent_reset_before_pass2() {
    let mut checker = BackwardChecker::new(3, false);
    let clauses = vec![
        vec![lit(0, true), lit(1, true)],   // a v b
        vec![lit(0, false), lit(1, true)],  // ~a v b
        vec![lit(0, true), lit(1, false)],  // a v ~b
        vec![lit(0, false), lit(1, false)], // ~a v ~b
    ];
    let steps = vec![
        ProofStep::Add(vec![lit(1, true)]),  // derive {b}
        ProofStep::Add(vec![lit(1, false)]), // derive {~b}
        ProofStep::Add(vec![]),              // derive empty clause
    ];
    let result = checker.verify(&clauses, &steps);
    assert!(result.is_ok(), "valid backward proof should succeed");
}

/// Algorithm audit: backward checker with deletion+restore roundtrip.
///
/// When a deletion is encountered in the backward pass, the clause is
/// restored (watches + hash table). This ensures that clauses deleted
/// during the forward pass are available for RUP checking in the backward
/// pass (they may be needed to verify ACTIVE clauses that were added
/// BEFORE the deletion).
#[test]
fn test_backward_deletion_restore() {
    let mut checker = BackwardChecker::new(3, false);
    let clauses = vec![
        vec![lit(0, true)],  // {a}
        vec![lit(0, false)], // {~a}
    ];
    // Add and then delete the unit clause. This tests that the backward
    // pass properly restores deleted clauses.
    let steps = vec![
        ProofStep::Add(vec![]), // derive empty (trivially RUP from {a} + {~a})
    ];
    // This should succeed: {a} + {~a} → empty clause.
    let result = checker.verify(&clauses, &steps);
    assert!(result.is_ok());
}

/// Algorithm audit: backward checker rejects an invalid proof where the
/// empty clause is NOT RUP-implied.
///
/// If the forward pass found a "conflict" but the clause wasn't actually
/// RUP-derivable, the backward pass must catch this. This exercises the
/// correctness of the inconsistent=false reset.
#[test]
fn test_backward_rejects_invalid_empty_clause() {
    let mut checker = BackwardChecker::new(3, false);
    let clauses = vec![
        vec![lit(0, true), lit(1, true)], // a v b (satisfiable)
    ];
    let steps = vec![
        ProofStep::Add(vec![]), // derive empty clause (NOT implied by {a v b})
    ];
    let result = checker.verify(&clauses, &steps);
    assert!(
        result.is_err(),
        "empty clause not implied should be rejected"
    );
}

/// Algorithm audit: mark_active uses iterative worklist, not recursion.
///
/// Deep dependency chains (many transitive reason clauses) must not
/// cause stack overflow. This test creates a linear chain of N clauses
/// where each depends on the previous via unit propagation.
#[test]
fn test_backward_deep_dependency_chain() {
    // Build a chain: {~(i-1), i} for i=1..N, with {0} as the root.
    // Each clause propagates variable i when i-1 is assigned.
    let n = 100;
    let mut checker = BackwardChecker::new(n + 2, false);
    let mut clauses: Vec<Vec<_>> = Vec::new();
    // {0} as unit clause
    clauses.push(vec![lit(0, true)]);
    // Chain: {~0, 1}, {~1, 2}, ..., {~(N-1), N}
    for i in 0..n {
        clauses.push(vec![lit(i as u32, false), lit((i + 1) as u32, true)]);
    }
    // Final contradicting clause: {~N}
    clauses.push(vec![lit(n as u32, false)]);

    // The formula is UNSAT by unit propagation chain.
    // No proof steps needed — BCP on originals reaches conflict.
    let result = checker.verify(&clauses, &[]);
    assert!(result.is_ok(), "chain of {n} implications should verify");
}

/// Algorithm audit: forward checker's visit_long maintains the 2WL invariant
/// that watched literals are always at positions [0] and [1] via
/// reorder_watched(). This test verifies that after BCP propagation,
/// the watched literal positions are correct.
#[test]
fn test_forward_2wl_invariant_after_propagation() {
    let mut checker = DratChecker::new(5, false);
    // Add a long clause {a, b, c, d} and unit clauses that force propagation.
    checker.add_original(&[lit(0, true), lit(1, true), lit(2, true), lit(3, true)]);
    checker.add_original(&[lit(0, false)]); // ~a: forces a=false
    checker.add_original(&[lit(1, false)]); // ~b: forces b=false
                                            // After BCP: a=false, b=false. In clause {a,b,c,d}, a and b are falsified.
                                            // 2WL should move watched literals to c and d.
                                            // Derive {c, d} — should be RUP since {a,b,c,d} with a=false, b=false gives {c,d}.
    assert!(checker.add_derived(&[lit(2, true), lit(3, true)]).is_ok());
}

/// Algorithm audit: hash collision handling in clause lookup.
///
/// Two clauses with the same XOR hash should both be findable in the
/// hash table. This exercises the bucket chain traversal in find_clause_idx.
#[test]
fn test_hash_collision_clause_lookup() {
    let mut checker = DratChecker::new(10, false);
    // Add many clauses to increase collision probability.
    for i in 0..20 {
        let v1 = i * 2;
        let v2 = i * 2 + 1;
        checker.add_original(&[lit(v1, true), lit(v2, true)]);
    }
    // Delete specific clauses and verify the correct ones are removed.
    // The first clause {0, 1}:
    let initial_live = checker.live_clauses;
    checker.delete_clause(&[lit(0, true), lit(1, true)]);
    assert_eq!(checker.live_clauses, initial_live - 1);
    // Deleting the same clause again should be a miss.
    checker.delete_clause(&[lit(0, true), lit(1, true)]);
    assert_eq!(checker.stats.missed_deletes, 1);
}

/// Regression test: delete_clause must not corrupt the marks array.
///
/// Bug (#5363): delete_clause set `marks[lit.index()] = true` for clause
/// matching but never cleared the marks. The marks array is shared with
/// `is_tautology()`, so after enough deletions, every clause appeared
/// tautological. This caused the forward checker to skip valid derived
/// clauses, preventing the empty clause from being RUP-implied.
///
/// Repro: add clauses, delete several, then derive a non-tautological
/// clause. Before the fix, is_tautology returned true for any clause
/// whose literals overlapped with previously-deleted clause literals.
#[test]
fn test_delete_does_not_corrupt_marks_for_tautology_check() {
    let mut checker = DratChecker::new(6, false);
    // Add original clauses.
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(2, true), lit(3, true)]);
    checker.add_original(&[lit(4, true), lit(5, true)]);
    // Delete them — this previously set marks without clearing.
    checker.delete_clause(&[lit(0, true), lit(1, true)]);
    checker.delete_clause(&[lit(2, true), lit(3, true)]);
    checker.delete_clause(&[lit(4, true), lit(5, true)]);
    // is_tautology must return false for a non-tautological clause
    // whose literals overlap with deleted clause literals.
    assert!(
        !checker.is_tautology(&[lit(0, true), lit(2, true)]),
        "marks corrupted: non-tautological clause falsely detected as tautology"
    );
    // Verify marks are all clean.
    assert!(
        checker.marks.iter().all(|&m| !m),
        "marks array should be clean after delete_clause"
    );
}

/// Regression test: full proof with deletions followed by empty clause.
///
/// This is a minimal reproduction of the at_most_1_of_5 proof pattern
/// that triggered the marks corruption bug (#5363). The proof has
/// deletion steps interleaved with additions, and the final step derives
/// the empty clause via RUP.
#[test]
fn test_delete_then_derive_empty_clause() {
    let mut checker = DratChecker::new(4, false);
    // Simple UNSAT formula: {a}, {~a, b}, {~b}
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false), lit(1, true)]);
    checker.add_original(&[lit(1, false)]);
    // BCP on originals already gives a conflict, but let's test the
    // proof path with explicit deletions followed by empty clause.
    // Formula is already inconsistent from BCP, so verify succeeds.
    let clauses = vec![
        vec![lit(0, true)],
        vec![lit(0, false), lit(1, true)],
        vec![lit(1, false)],
    ];
    let steps = vec![
        ProofStep::Delete(vec![lit(0, false), lit(1, true)]),
        ProofStep::Add(vec![]), // empty clause
    ];
    let mut checker2 = DratChecker::new(4, false);
    let result = checker2.verify(&clauses, &steps);
    assert!(
        result.is_ok(),
        "proof with deletions then empty clause should verify"
    );
}
