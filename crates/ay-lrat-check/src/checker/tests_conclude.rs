// Copyright 2026 Andrew Yates
// Tests for conclude_unsat() proof finalization (#5280).

use super::*;
use crate::lrat_parser::LratStep;

// ─── conclude_unsat() unit tests ─────────────────────────────────────

/// A valid proof that derives the empty clause should conclude as Verified.
#[test]
fn test_conclude_unsat_valid_proof() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
}

/// A proof that never derives any clauses should fail with NoStepsProcessed.
#[test]
fn test_conclude_unsat_no_steps() {
    let mut checker = LratChecker::new(2);
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::NoStepsProcessed)
    );
}

/// A proof that derives non-empty clauses but never the empty clause
/// should fail with NoEmptyClause.
#[test]
fn test_conclude_unsat_no_empty_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
                                                 // Derive {b} but not the empty clause.
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2]));
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::NoEmptyClause)
    );
}

/// verify_proof delegates to conclude_unsat: an empty step list should fail.
#[test]
fn test_verify_proof_empty_steps() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    assert!(!checker.verify_proof(&[]));
}

/// verify_proof should accept a valid proof and return true.
#[test]
fn test_verify_proof_valid_concludes() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![],
        hints: vec![1, 2],
    }];
    assert!(checker.verify_proof(&steps));
}

// ─── Truncated proof tests ───────────────────────────────────────────

/// A truncated proof that derives the empty clause early but is missing
/// subsequent deletion steps. verify_proof accepts this because all
/// processed steps are valid and the empty clause was derived.
/// This is consistent with drat-trim lrat-check.c behavior (line 489).
#[test]
fn test_truncated_proof_with_empty_clause_derived() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Full proof would be: derive empty clause, then delete originals.
    // Truncated: only the derivation step.
    let steps = vec![LratStep::Add {
        id: 3,
        clause: vec![],
        hints: vec![1, 2],
    }];
    // This is valid: empty clause derived, no failures.
    assert!(checker.verify_proof(&steps));
    // verify_proof already called conclude_unsat; double-conclusion guard fires.
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::AlreadyConcluded)
    );
}

/// A proof that contains only deletion steps and no derivations
/// should fail (no empty clause derived).
#[test]
fn test_proof_only_deletions() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    let steps = vec![LratStep::Delete { ids: vec![1] }];
    assert!(!checker.verify_proof(&steps));
}

/// A proof where a derivation step fails should cause verify_proof to
/// return false immediately (early exit), without reaching conclude_unsat.
#[test]
fn test_verify_proof_fails_on_bad_step() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
                                                // Try to derive empty clause with insufficient hints.
    let steps = vec![LratStep::Add {
        id: 2,
        clause: vec![],
        hints: vec![1], // hint {a,b} is not unit after assuming nothing
    }];
    assert!(!checker.verify_proof(&steps));
}

// ─── conclude_unsat via manual step-by-step API ──────────────────────

/// Fail-fast (#5301): a failed derivation sets failed=true in strict mode,
/// blocking all subsequent operations. CaDiCaL lratchecker.cpp aborts on
/// first error; ay short-circuits instead.
#[test]
fn test_conclude_unsat_step_failures_fail_fast() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Bad derivation: wrong hints, fails. Sets failed=true in strict mode.
    assert!(!checker.add_derived(3, &[lit(2)], &[999]));
    assert_eq!(checker.stats.failures, 1);
    assert!(checker.failed);
    // Fail-fast: subsequent add_derived returns false immediately.
    assert!(!checker.add_derived(4, &[], &[1, 2]));
    // Empty clause was never derived because second add was rejected.
    assert!(!checker.derived_empty_clause());
}

/// Lenient mode (#5301): failures increment stats.failures but do not
/// block subsequent operations. This allows batch error collection.
#[test]
fn test_conclude_unsat_step_failures_lenient() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Bad derivation: wrong hints, fails.
    assert!(!checker.add_derived(3, &[lit(2)], &[999]));
    assert_eq!(checker.stats.failures, 1);
    // In lenient mode, failed is NOT set.
    assert!(!checker.failed);
    // Subsequent operations still execute.
    assert!(checker.add_derived(4, &[], &[1, 2]));
    assert!(checker.derived_empty_clause());
    // conclude_unsat catches the earlier failure.
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::StepFailures)
    );
}

/// StepFailures takes precedence over NoEmptyClause (#5307).
///
/// When a step failure prevents the empty clause from being derived,
/// the root cause is the failure — not the missing empty clause.
/// conclude_unsat must return StepFailures, not NoEmptyClause.
#[test]
fn test_conclude_failures_before_empty_clause() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Bad derivation: non-existent hint 999.
    assert!(!checker.add_derived(3, &[lit(2)], &[999]));
    assert_eq!(checker.stats.failures, 1);
    // Empty clause NOT derived (the failed step was the only derivation attempt).
    assert!(!checker.derived_empty_clause());
    // Should return StepFailures (root cause), not NoEmptyClause.
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::StepFailures)
    );
}

/// Double-conclusion guard: calling conclude_unsat() twice returns
/// AlreadyConcluded on the second call.
#[test]
fn test_conclude_unsat_double_conclusion() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::AlreadyConcluded)
    );
}

/// Using add_derived step-by-step (not verify_proof), conclude_unsat
/// should work correctly. With double-conclusion guard, each checker
/// instance can only conclude once.
#[test]
fn test_conclude_after_manual_steps() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(2)]); // ~a v b
    checker.add_original(3, &[lit(-2)]); // ~b
                                         // Step 1: derive {b}, then derive empty clause.
    assert!(checker.add_derived(4, &[lit(2)], &[1, 2]));
    assert!(checker.add_derived(5, &[], &[4, 3]));
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
}

// ─── Strict deletion tests (#5288) ──────────────────────────────────

/// verify_proof fails on deletion of non-existent clause ID (#5288).
/// CaDiCaL lratchecker.cpp:665-672 treats this as fatal.
#[test]
fn test_verify_proof_fails_on_nonexistent_deletion() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    let steps = vec![
        LratStep::Add {
            id: 3,
            clause: vec![],
            hints: vec![1, 2],
        },
        LratStep::Delete { ids: vec![999] }, // non-existent
    ];
    assert!(
        !checker.verify_proof(&steps),
        "verify_proof must fail on deletion of non-existent clause"
    );
}

/// verify_proof succeeds when deletions reference existing clauses.
#[test]
fn test_verify_proof_valid_with_deletions() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    let steps = vec![
        LratStep::Add {
            id: 3,
            clause: vec![],
            hints: vec![1, 2],
        },
        LratStep::Delete { ids: vec![1, 2] }, // existing clauses
    ];
    assert!(checker.verify_proof(&steps));
}

/// conclude_unsat detects deletion failures even if empty clause was derived.
#[test]
fn test_conclude_unsat_deletion_failures() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    // Manually trigger a deletion failure.
    assert!(!checker.delete(999));
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::StepFailures),
        "conclude_unsat must detect deletion failures"
    );
}

// Finalization tests extracted to tests_finalization.rs (#5305 500-line limit).
