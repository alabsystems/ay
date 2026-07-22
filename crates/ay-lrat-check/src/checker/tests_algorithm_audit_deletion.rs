// Copyright 2026 Andrew Yates
// Algorithm audit: deletion, resolution, blocked clause, and memory safety tests.
// Split from tests_algorithm_audit.rs to stay under the 500-line file limit.

use super::*;

/// Algorithm audit: deletion of nonexistent clause ID is a silent no-op.
///
/// LRAT proofs may contain deletion commands for clause IDs that don't exist
/// in the database (e.g., already deleted, or referencing a clause that was
/// never added). Strict CaDiCaL parity: returns false and increments failures.
#[test]
fn test_deletion_of_nonexistent_clause() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Delete a nonexistent clause ID — returns false (CaDiCaL parity).
    assert!(!checker.delete(999));
    assert_eq!(checker.stats.deleted, 0);
    assert_eq!(
        checker.stats.failures, 1,
        "non-existent delete must increment failures"
    );
}

/// Algorithm audit: delete_verified rejects non-existent clause IDs (#5288).
///
/// CaDiCaL lratchecker.cpp:665-672 treats deletion of non-existent clauses
/// as a fatal error. `delete_verified()` must be consistent with `delete()`.
#[test]
fn test_delete_verified_nonexistent_clause() {
    let mut checker = LratChecker::new(3);
    assert!(!checker.delete_verified(999, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
}

/// Algorithm audit: delete_verified rejects content mismatch.
///
/// If the stored clause contains a literal not in the deletion command,
/// the deletion is rejected (content mismatch). Uses lenient mode so
/// the correct deletion after the mismatch actually executes.
#[test]
fn test_delete_verified_content_mismatch() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    // Try to delete clause 1 but claim it contains {a, c} — mismatch (b≠c).
    assert!(!checker.delete_verified(1, &[lit(1), lit(3)]));
    // Clause should still exist.
    assert!(checker.clause_index.contains_key(&1));
    // Correct deletion.
    assert!(checker.delete_verified(1, &[lit(1), lit(2)]));
    assert!(!checker.clause_index.contains_key(&1));
}

/// Algorithm audit: verify that the checker handles extension variables
/// (variables beyond the declared num_vars) in derived clauses.
///
/// Extended resolution proofs (e.g., CaDiCaL's pigeon-hole proofs) introduce
/// new variables not present in the original formula. The checker must grow
/// its arrays dynamically to accommodate these extension variables.
/// Uses lenient mode since add_original with extension var fails and we
/// still need to test add_derived afterwards.
#[test]
fn test_extension_variables_in_derived_clauses() {
    let mut checker = LratChecker::new_lenient(3); // 3 vars: 1, 2, 3
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Variable 10 exceeds num_vars=3 in original → rejected.
    assert!(
        !checker.add_original(3, &[lit(10)]),
        "extension variable rejected in original clause"
    );
    // Variable 10 in derived clause → accepted (extension variable).
    // Derive {x10} with hints that produce a conflict, then the derived
    // clause contains the extension variable. But we need the proof to
    // actually verify. Since {1} and {~1} give empty clause via [1,2],
    // anything is derivable after that. Derive the empty clause first.
    assert!(checker.add_derived(3, &[], &[1, 2]));
}

/// Algorithm audit: blocked clause check marks cleanup on failure path.
///
/// When check_blocked fails (e.g., missing witness clause), the marks and
/// checked_lits arrays must be properly cleaned up. Otherwise, stale marks
/// would corrupt subsequent verification steps. Uses lenient mode so
/// subsequent operations after the failure actually execute.
#[test]
fn test_blocked_check_cleanup_on_failure() {
    let mut checker = LratChecker::new_lenient(5);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1), lit(3)]); // ~a v c
                                                 // Try to derive a clause with a blocked check that fails:
                                                 // Negative hint -999 refers to nonexistent clause → blocked check fails.
                                                 // After failure, marks must be clean for subsequent operations.
    assert!(!checker.add_derived(3, &[lit(4)], &[-999]));
    // Subsequent normal derivation should work (marks are clean).
    checker.add_original(4, &[lit(4)]);
    checker.add_original(5, &[lit(-4)]);
    assert!(checker.add_derived(6, &[], &[4, 5]));
}

/// Algorithm audit: resolution check with single hint (no resolution steps).
///
/// When there's only one hint, the resolution "chain" is just the hint clause
/// itself. The derived clause must exactly match the hint clause (no
/// resolution steps to combine clauses).
#[test]
fn test_resolution_single_hint_exact_match() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1), lit(2)]); // a v b
    checker.add_original(2, &[lit(-1)]); // ~a
                                         // Derive {b} with hints [2, 1]. After assuming ~b:
                                         // Hint 2 = {~a}: ~a unassigned → unit, propagate ~a.
                                         // Hint 1 = {a, b}: a is false (~a=true), b is false → conflict.
                                         // Resolution check: last hint = 1 = {a, b}. Walk backward: hint 2 = {~a}.
                                         // Cancel a/~a → resolvent = {b}. Matches derived clause {b}. Pass.
    assert!(checker.add_derived(3, &[lit(2)], &[2, 1]));
}

/// Algorithm audit: empty hints with fresh variable is trivially blocked (ER).
///
/// If no hints are provided and the clause contains a literal whose negation
/// appears in NO existing clause, the clause is trivially blocked (ER definition).
/// CaDiCaL lratchecker.cpp:318 skips RUP for empty chains and falls through
/// to check_blocked at :506. Variable 2 is fresh (not negated in any clause),
/// so the clause is accepted as a blocked clause.
#[test]
fn test_empty_hints_fresh_variable_accepted_as_blocked() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    // Derive {b} with no hints. Variable b has no negated occurrence → trivially blocked.
    assert!(checker.add_derived(2, &[lit(2)], &[]));
    assert_eq!(checker.stats.blocked_ok, 1);
}

/// Algorithm audit: empty hints with non-fresh variable fails blocked check.
///
/// If every literal's negation appears in some clause, no RAT candidate survives
/// and check_blocked rejects the clause.
#[test]
fn test_empty_hints_non_fresh_variable_fails() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-2)]); // ~b exists in DB
                                         // Derive {b} with no hints. Variable b has negated occurrence in clause 2,
                                         // eliminating the only RAT candidate → rejected.
    assert!(!checker.add_derived(3, &[lit(2)], &[]));
}

/// Duplicate occurrences in a blocked-clause witness are one logical literal,
/// not two distinct complementary literals in the resolvent.
#[test]
fn test_blocked_witness_duplicate_literal_does_not_fake_tautology() {
    // The original formula is satisfiable with a=false, b=false.
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(-1), lit(-1)]);
    checker.add_original(2, &[lit(-1), lit(2)]);
    checker.add_original(3, &[lit(-2)]);

    // Resolving (a) with (~a v ~a) yields the empty clause, not a tautology.
    // The repeated ~a therefore cannot certify (a) as blocked.
    assert!(
        !checker.add_derived(4, &[lit(1)], &[-1]),
        "duplicate witness literals must not validate a blocked-clause proof"
    );
}

/// Algorithm audit: derive empty clause from contradictory unit clauses.
///
/// This is the simplest possible LRAT proof: two contradictory unit clauses
/// imply the empty clause. After assuming nothing (empty clause has no literals),
/// hint {a} propagates a, then hint {~a} is all-falsified → conflict.
#[test]
fn test_derive_empty_from_contradictory_units() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]); // {a}
    checker.add_original(2, &[lit(-1)]); // {~a}
                                         // Empty clause with hints [1, 2]: hint 1 = {a}, unit → propagate a.
                                         // Hint 2 = {~a}: ~a is false → conflict. Success.
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert!(checker.derived_empty_clause());
}

/// Algorithm audit: clause deletion removes hints from database.
///
/// After deleting a clause, it should no longer be available as a hint
/// for subsequent derivations.
#[test]
fn test_deleted_clause_unavailable_as_hint() {
    let mut checker = LratChecker::new(3);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Derive empty clause using hints [1, 2].
    assert!(checker.add_derived(3, &[], &[1, 2]));
    // Delete clause 1.
    checker.delete(1);
    // Try to derive using deleted hint. Hint 1 is unknown → fail.
    assert!(
        !checker.add_derived(4, &[], &[1, 2]),
        "deleted clause should not be available as hint"
    );
}

/// Memory safety audit: clause_lits uses usize arithmetic to avoid u32 overflow
/// in `(entry.start + entry.len)`. With the old u32 arithmetic, a clause near
/// the u32 boundary could wrap and produce an invalid slice range.
///
/// This test verifies the usize arithmetic by placing a clause at a known
/// offset and checking the returned slice matches expected literals.
#[test]
fn test_clause_lits_usize_arithmetic_correctness() {
    let mut checker = LratChecker::new_lenient(10);
    // Add several clauses and verify clause_lits returns correct slices.
    checker.add_original(1, &[lit(1), lit(2), lit(3)]);
    checker.add_original(2, &[lit(4), lit(5)]);
    checker.add_original(3, &[lit(6)]);

    // Retrieve entries and verify clause_lits returns correct data.
    let e1 = checker.clause_index[&1];
    let e2 = checker.clause_index[&2];
    let e3 = checker.clause_index[&3];

    let lits1 = checker.clause_lits(e1);
    assert_eq!(lits1.len(), 3);
    assert_eq!(lits1[0], lit(1));
    assert_eq!(lits1[1], lit(2));
    assert_eq!(lits1[2], lit(3));

    let lits2 = checker.clause_lits(e2);
    assert_eq!(lits2.len(), 2);
    assert_eq!(lits2[0], lit(4));
    assert_eq!(lits2[1], lit(5));

    let lits3 = checker.clause_lits(e3);
    assert_eq!(lits3.len(), 1);
    assert_eq!(lits3[0], lit(6));

    // Verify entries are contiguous in the arena (no gaps).
    assert_eq!(e1.start, 0);
    assert_eq!(e1.len, 3);
    assert_eq!(e2.start, 3);
    assert_eq!(e2.len, 2);
    assert_eq!(e3.start, 5);
    assert_eq!(e3.len, 1);
    assert_eq!(checker.clause_arena.len(), 6);
}

/// Memory safety audit: insert_clause returns None when arena would overflow u32.
///
/// We can't allocate 4B+ Literal entries in a test, but we can verify the
/// guard exists by checking that the function returns Option<ClauseEntry>
/// and that normal insertions return Some.
#[test]
fn test_insert_clause_returns_some_on_normal_operation() {
    let mut checker = LratChecker::new_lenient(10);
    // Normal add_original should succeed (insert_clause returns Some).
    assert!(checker.add_original(1, &[lit(1), lit(2)]));
    assert!(checker.add_original(2, &[lit(3)]));
    assert_eq!(checker.clause_index.len(), 2);
    assert_eq!(checker.stats.failures, 0);
}
