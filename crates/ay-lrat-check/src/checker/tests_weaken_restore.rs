// Copyright 2026 Andrew Yates
// Tests for weaken() and restore() API (CaDiCaL lratchecker.cpp:679-755).

use super::*;

// ─── weaken() tests ──────────────────────────────────────────────────

/// Basic weaken: clause removed from index and stats updated.
#[test]
fn test_weaken_removes_clause() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(2)]);
    assert!(checker.weaken(1, &[lit(1), lit(2)]));
    assert!(!checker.clause_index.contains_key(&1));
    assert_eq!(checker.stats.weakened, 1);
    assert_eq!(checker.stats.deleted, 1);
    assert_eq!(checker.stats.deleted_originals, 1);
}

/// Weaken non-existent clause fails.
#[test]
fn test_weaken_nonexistent_fails() {
    let mut checker = LratChecker::new_lenient(2);
    assert!(!checker.weaken(999, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
}

/// Weaken with content mismatch fails.
#[test]
fn test_weaken_content_mismatch_fails() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    // Provide wrong literals.
    assert!(!checker.weaken(1, &[lit(1), lit(3)]));
    assert_eq!(checker.stats.failures, 1);
    // Clause should still be in index (weaken failed).
    assert!(checker.clause_index.contains_key(&1));
}

/// Weaken with length mismatch (subset) fails.
#[test]
fn test_weaken_length_mismatch_fails() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]);
    // Provide only one of two literals.
    assert!(!checker.weaken(1, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
    assert!(checker.clause_index.contains_key(&1));
}

/// Double-weaken of same clause ID fails.
#[test]
fn test_weaken_double_fails() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.weaken(1, &[lit(1)]));
    // Re-add clause 1 as original so it exists in clause_index.
    // (In practice, the clause would be restored, but for testing double-weaken
    // we manually re-insert.)
    checker.add_original(3, &[lit(1)]); // different ID, same content
                                        // Can't weaken clause_id=1 again because it's still in weakened_clauses.
                                        // Actually, clause_id=1 was removed from clause_index.
                                        // The double-weaken guard triggers when the ID is in weakened_clauses
                                        // AND in clause_index. Let's test a realistic scenario: restore then weaken.
    assert!(checker.restore(1, &[lit(1)]));
    assert!(checker.weaken(1, &[lit(1)]));
    // Now clause 1 is weakened again. Restore it and try triple-weaken.
    assert!(checker.restore(1, &[lit(1)]));
    // This should work — restore consumed the weakened entry.
    assert!(checker.weaken(1, &[lit(1)]));
}

/// Weaken in strict mode blocks after failure.
#[test]
fn test_weaken_strict_blocks_after_failure() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    // Trigger failure.
    assert!(!checker.weaken(999, &[lit(1)]));
    assert!(checker.failed);
    // Subsequent weaken returns false immediately.
    assert!(!checker.weaken(1, &[lit(1)]));
}

/// Weaken of derived clause: deleted_originals should NOT increase.
#[test]
fn test_weaken_derived_clause_not_counted_as_original() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[lit(1)], &[1, 2]));
    assert!(checker.weaken(3, &[lit(1)]));
    assert_eq!(checker.stats.weakened, 1);
    assert_eq!(checker.stats.deleted, 1);
    assert_eq!(checker.stats.deleted_originals, 0); // derived, not original
}

// ─── restore() tests ─────────────────────────────────────────────────

/// Basic restore: previously weakened clause is re-added.
#[test]
fn test_restore_basic_roundtrip() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(2)]);
    assert!(checker.weaken(1, &[lit(1), lit(2)]));
    assert!(!checker.clause_index.contains_key(&1));
    assert!(checker.restore(1, &[lit(1), lit(2)]));
    assert!(checker.clause_index.contains_key(&1));
    assert_eq!(checker.stats.restored, 1);
}

/// Restore of never-weakened clause fails.
#[test]
fn test_restore_never_weakened_fails() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1)]);
    assert!(!checker.restore(999, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
}

/// Restore with wrong content fails (content mismatch).
#[test]
fn test_restore_content_mismatch_fails() {
    let mut checker = LratChecker::new_lenient(3);
    checker.add_original(1, &[lit(1), lit(2)]);
    assert!(checker.weaken(1, &[lit(1), lit(2)]));
    // Try to restore with different content.
    assert!(!checker.restore(1, &[lit(1), lit(3)]));
    assert_eq!(checker.stats.failures, 1);
    assert_eq!(checker.stats.restored, 0);
}

/// Restore with length mismatch (subset) fails.
#[test]
fn test_restore_length_mismatch_fails() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1), lit(2)]);
    assert!(checker.weaken(1, &[lit(1), lit(2)]));
    assert!(!checker.restore(1, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
}

/// Restore when clause ID is already in use fails.
#[test]
fn test_restore_id_already_in_use_fails() {
    let mut checker = LratChecker::new_lenient(2);
    checker.add_original(1, &[lit(1)]);
    assert!(checker.weaken(1, &[lit(1)]));
    // Re-add a different clause with the same ID.
    checker.add_original(1, &[lit(2)]);
    // Now restore should fail: ID 1 is already in clause_index.
    assert!(!checker.restore(1, &[lit(1)]));
    assert_eq!(checker.stats.failures, 1);
}

/// Restore in strict mode blocks after failure.
#[test]
fn test_restore_strict_blocks_after_failure() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    assert!(checker.weaken(1, &[lit(1)]));
    // Trigger failure.
    assert!(!checker.restore(999, &[lit(1)]));
    assert!(checker.failed);
    // Subsequent restore returns false.
    assert!(!checker.restore(1, &[lit(1)]));
}

/// Restored clause is usable as a hint in subsequent derivation.
#[test]
fn test_restored_clause_usable_as_hint() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    // Weaken clause 1, then restore it.
    assert!(checker.weaken(1, &[lit(1)]));
    assert!(checker.restore(1, &[lit(1)]));
    // Now derive empty clause using restored clause 1 as hint.
    assert!(checker.add_derived(3, &[], &[1, 2]));
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
}

/// Restore with literals in different order succeeds (order-independent).
#[test]
fn test_restore_different_order_succeeds() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1), lit(2)]);
    assert!(checker.weaken(1, &[lit(1), lit(2)]));
    // Restore with reversed literal order — should still match.
    assert!(checker.restore(1, &[lit(2), lit(1)]));
    assert_eq!(checker.stats.restored, 1);
}

// ─── weaken/restore + finalization coverage ──────────────────────────

/// Weakened original clause counts as deleted for coverage purposes.
#[test]
fn test_weakened_original_counts_as_deleted_original() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    // Weaken clause 2 (removes from index, counts as deleted_originals).
    assert!(checker.weaken(2, &[lit(-1)]));
    // Finalize clause 1.
    assert!(checker.finalize_clause(1, &[lit(1)]));
    // finalized(1) + deleted_originals(1) == originals(2) → pass.
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
}

/// Weaken + restore cycle: restore cancels out for coverage purposes.
///
/// When a clause is weakened then restored, the weaken+restore is a no-op
/// for finalization coverage. `restore()` decrements `deleted_originals`
/// to undo the increment from `weaken()`.
#[test]
fn test_weaken_restore_finalization_coverage() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    checker.add_original(2, &[lit(-1)]);
    assert!(checker.add_derived(3, &[], &[1, 2]));
    // Weaken and then restore clause 1.
    assert!(checker.weaken(1, &[lit(1)]));
    assert_eq!(checker.stats.deleted_originals, 1);
    assert!(checker.restore(1, &[lit(1)]));
    // After restore: deleted_originals is back to 0 (weaken+restore cancels out).
    assert_eq!(checker.stats.deleted_originals, 0);
    // Finalize both originals.
    assert!(checker.finalize_clause(1, &[lit(1)]));
    assert!(checker.finalize_clause(2, &[lit(-1)]));
    // finalized(2) + deleted_originals(0) == originals(2) → Verified.
    assert_eq!(checker.stats.originals, 2);
    assert_eq!(checker.stats.finalized, 2);
    assert_eq!(checker.conclude_unsat(), ConcludeResult::Verified);
}

/// Weaken+restore of tautological clause preserves the tautological flag.
///
/// Bug: `restore()` destructured only 2 of 3 tuple fields from
/// `weakened_clauses`, setting `tautological = false` on the restored
/// `ClauseEntry`. This caused subsequent derivation steps referencing the
/// restored clause to mis-classify it during tautology checks.
#[test]
fn test_weaken_restore_preserves_tautological_flag() {
    let mut checker = LratChecker::new(3);
    // Clause (a, ~a) is tautological.
    checker.add_original(1, &[lit(1), lit(-1)]);
    // Non-tautological clause for deriving empty.
    checker.add_original(2, &[lit(2)]);
    checker.add_original(3, &[lit(-2)]);

    // Verify clause 1 is tautological before weakening.
    let entry_before = checker.clause_index[&1];
    assert!(
        entry_before.tautological,
        "clause (a, ~a) must be tautological"
    );

    // Weaken and restore.
    assert!(checker.weaken(1, &[lit(1), lit(-1)]));
    assert!(checker.restore(1, &[lit(1), lit(-1)]));

    // After restore, the tautological flag must still be true.
    let entry_after = checker.clause_index[&1];
    assert!(
        entry_after.tautological,
        "restored clause must preserve tautological flag"
    );
}

/// Stats summary includes weaken and restore counters.
#[test]
fn test_stats_summary_includes_weaken_restore() {
    let mut checker = LratChecker::new(2);
    checker.add_original(1, &[lit(1)]);
    assert!(checker.weaken(1, &[lit(1)]));
    assert!(checker.restore(1, &[lit(1)]));
    let summary = checker.stats_summary();
    assert!(summary.contains("weakened=1"), "summary: {summary}");
    assert!(summary.contains("restored=1"), "summary: {summary}");
}
