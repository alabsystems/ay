// Copyright 2026 Andrew Yates
// Tests for finalize_clause() and finalization coverage (#5300).
//
// Extracted from tests_conclude.rs to stay under the 500-line file limit.

use super::*;

// ─── Finalization tests (#5300) ──────────────────────────────────────
//
// CaDiCaL lratchecker.cpp has a finalization/completeness audit:
// finalize_clause(id, clause) verifies each original clause is accounted
// for, and report_status() checks num_finalized == num_clauses.
//
// When finalize_clause() is never called, conclude_unsat() skips the
// coverage check (backward compatibility). When finalize_clause() is
// called at least once, conclude_unsat() enforces that
// finalized + deleted == originals.

/// Without finalization: proof using subset of originals is accepted.
///
/// Formula: {a} ∧ {~a} ∧ {b} ∧ {~b} — proof derives empty from {a,~a}
/// only, never referencing clauses 3 or 4. Logically valid and accepted
/// because finalize_clause() is never called.
#[test]
fn test_no_finalization_subset_proof_accepted() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ~a
    checker.add_original(3, &[lit(2)]); // b (never used)
    checker.add_original(4, &[lit(-2)]); // ~b (never used)
    assert!(checker.add_derived(5, &[], &[1, 2]));
    // No finalize_clause() calls → coverage check skipped.
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
    assert_eq!(checker.stats.originals, 4);
    assert_eq!(checker.stats.finalized, 0);
}

/// With finalization: incomplete coverage is rejected.
///
/// When finalize_clause() is used but not all originals are accounted
/// for, conclude_unsat() returns IncompleteCoverage.
#[test]
fn test_finalization_incomplete_coverage_rejected() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ~a
    checker.add_original(3, &[lit(2), lit(3)]); // b v c (unused)
    assert!(checker.add_derived(4, &[], &[1, 2]));
    // Finalize only clauses 1 and 2 — clause 3 is unaccounted for.
    assert!(checker.finalize_clause(1, &[lit(1)]));
    assert!(checker.finalize_clause(2, &[lit(-1)]));
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::IncompleteCoverage {
            originals: 3,
            finalized: 2,
            deleted_originals: 0,
        })
    );
}

/// With finalization: complete coverage is accepted.
///
/// All originals are either finalized or deleted.
#[test]
fn test_finalization_complete_coverage_accepted() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ~a
    checker.add_original(3, &[lit(2)]); // b
    checker.add_original(4, &[lit(-2)]); // ~b
                                         // Delete unused clauses.
    assert!(checker.delete(3));
    assert!(checker.delete(4));
    assert!(checker.add_derived(5, &[], &[1, 2]));
    // Finalize the remaining clauses.
    assert!(checker.finalize_clause(1, &[lit(1)]));
    assert!(checker.finalize_clause(2, &[lit(-1)]));
    // finalized (2) + deleted (2) == originals (4) → pass.
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
    assert_eq!(checker.stats.originals, 4);
    assert_eq!(checker.stats.finalized, 2);
    assert_eq!(checker.stats.deleted, 2);
}

/// finalize_clause: non-existent clause ID returns false.
#[test]
fn test_finalize_clause_nonexistent() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    assert!(!checker.finalize_clause(999, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
}

/// finalize_clause: content mismatch returns false.
#[test]
fn test_finalize_clause_content_mismatch() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]); // {a, b}
                                                // Claim clause 1 is {a, c} — mismatch.
    assert!(!checker.finalize_clause(1, &[lit(1), lit(3)]));
    assert_eq!(checker.stats.failures, 1);
    assert_eq!(checker.stats.finalized, 0);
}

/// finalize_clause: length mismatch (subset) returns false.
#[test]
fn test_finalize_clause_length_mismatch() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]); // {a, b}
                                                // Claim clause 1 is {a} — length mismatch.
    assert!(!checker.finalize_clause(1, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
    assert_eq!(checker.stats.finalized, 0);
}

/// finalize_clause: correct content succeeds and increments stats.
#[test]
fn test_finalize_clause_correct_content() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(2)]); // {a, b}
    assert!(checker.finalize_clause(1, &[lit(1), lit(2)]));
    assert_eq!(checker.stats.finalized, 1);
    assert_eq!(checker.stats.failures, 0);
}

/// finalize_clause: does NOT remove the clause from the index.
#[test]
fn test_finalize_clause_does_not_remove() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    assert!(checker.finalize_clause(1, &[lit(1)]));
    // Clause still exists — can be finalized again or used as hint.
    assert!(checker.clause_index.contains_key(&1));
}

/// finalize_clause: strict mode blocks after failure.
#[test]
fn test_finalize_clause_strict_mode() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    // Force a failure.
    assert!(!checker.finalize_clause(999, &[lit(1)]));
    assert!(checker.failed);
    // Subsequent finalize_clause returns false.
    assert!(!checker.finalize_clause(1, &[lit(1)]));
}

/// Regression: derived-clause deletions must NOT inflate original coverage.
///
/// Before the fix, `stats.deleted` counted ALL deletions (original + derived).
/// `conclude_unsat()` used `finalized + deleted` to check original coverage.
/// If a proof derived and deleted clauses, those derived deletions inflated
/// the count, potentially masking unaccounted original clauses.
///
/// Scenario: 3 originals, derive 2 intermediate clauses, delete both derived,
/// finalize only 2 originals. Without the fix, `finalized (2) + deleted (2)`
/// would equal `originals (3)` only if total deleted happened to fill the gap.
/// With the fix, `finalized (2) + deleted_originals (0)` ≠ `originals (3)`.
#[test]
fn test_derived_deletions_do_not_inflate_original_coverage() {
    let mut checker = LratChecker::new_lenient(3);
    // 3 original clauses.
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ~a
    checker.add_original(3, &[lit(2), lit(3)]); // b v c (unaccounted)
                                                // Derive intermediate clause and empty clause.
    assert!(checker.add_derived(4, &[lit(2)], &[1, 2])); // bogus but lenient
                                                         // Actually, let's derive empty clause from originals.
    assert!(checker.add_derived(10, &[], &[1, 2]));
    // Delete both derived clauses — these are NOT originals.
    assert!(checker.delete(4));
    assert!(checker.delete(10));
    // Finalize 2 of 3 originals. Clause 3 is unaccounted.
    assert!(checker.finalize_clause(1, &[lit(1)]));
    assert!(checker.finalize_clause(2, &[lit(-1)]));
    // With the bug: finalized(2) + deleted(2) == originals(3)? No, 4 ≠ 3.
    // But a subtler case: if we had deleted exactly 1 derived clause,
    // finalized(2) + deleted(1) == originals(3) would falsely pass.
    // Verify stats are correct:
    assert_eq!(checker.stats.originals, 3);
    assert_eq!(checker.stats.finalized, 2);
    assert_eq!(checker.stats.deleted, 2); // both derived
    assert_eq!(checker.stats.deleted_originals, 0); // no originals deleted
                                                    // conclude_unsat must detect the gap: clause 3 is unaccounted.
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::IncompleteCoverage {
            originals: 3,
            finalized: 2,
            deleted_originals: 0,
        })
    );
}

/// Regression: with exactly the right number of derived deletions to mask the gap.
///
/// This is the precise exploit scenario: 3 originals, finalize 2, delete 1 derived.
/// With the old code: `finalized(2) + deleted(1) == originals(3)` → false Verified.
/// With the fix: `finalized(2) + deleted_originals(0) == originals(3)` → IncompleteCoverage.
#[test]
fn test_derived_deletion_exact_mask_scenario() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1)]); // a
    checker.add_original(2, &[lit(-1)]); // ~a
    checker.add_original(3, &[lit(2), lit(3)]); // b v c (unaccounted)
    assert!(checker.add_derived(10, &[], &[1, 2]));
    // Delete the derived clause — this would inflate coverage in the old code.
    assert!(checker.delete(10));
    // Finalize 2 of 3 originals.
    assert!(checker.finalize_clause(1, &[lit(1)]));
    assert!(checker.finalize_clause(2, &[lit(-1)]));
    assert_eq!(checker.stats.originals, 3);
    assert_eq!(checker.stats.finalized, 2);
    assert_eq!(checker.stats.deleted, 1); // 1 derived deletion
    assert_eq!(checker.stats.deleted_originals, 0);
    // Old code: finalized(2) + deleted(1) == 3 == originals → Verified (WRONG)
    // Fixed code: finalized(2) + deleted_originals(0) == 2 ≠ 3 → IncompleteCoverage
    assert_eq!(
        checker.conclude_unsat(),
        ConcludeResult::Failed(ConcludeFailure::IncompleteCoverage {
            originals: 3,
            finalized: 2,
            deleted_originals: 0,
        }),
        "derived-clause deletion must not mask incomplete original coverage"
    );
}

/// Deleted + finalized mixed coverage: only finalized + deleted counts.
#[test]
fn test_finalization_mixed_deleted_and_finalized() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]); // a — will be finalized
    checker.add_original(2, &[lit(-1)]); // ~a — will be deleted after use
                                         // Derive empty using both clauses first.
    assert!(checker.add_derived(3, &[], &[1, 2]));
    // Now delete clause 2 and finalize clause 1.
    assert!(checker.delete(2));
    assert!(checker.finalize_clause(1, &[lit(1)]));
    // finalized (1) + deleted (1) == originals (2) → pass.
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
}

/// finalize_clause() on a derived clause succeeds but does NOT increment
/// stats.finalized. CaDiCaL only counts originals in finalization coverage.
#[test]
fn test_finalize_derived_clause_does_not_increment_counter() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    checker.add_original(2, &[lit(-1), lit(2)]);
    assert!(checker.add_derived(3, &[lit(2)], &[1, 2]));
    let before = checker.stats.finalized;
    assert!(checker.finalize_clause(3, &[lit(2)]));
    assert_eq!(
        checker.stats.finalized, before,
        "derived clause finalization must not increment counter"
    );
}
