// Copyright 2026 Andrew Yates
// Direct unit tests for the adapter_api.rs public interface.
//
// These 7 functions were previously only tested cross-crate via ay-sat's
// ForwardChecker. This file provides first-party coverage within ay-drat-check.
// Coverage gap identified by P1:588 proof_coverage reflection.

use super::*;
use crate::checker::test_helpers::lit;

// ─── trail_len ──────────────────────────────────────────────────────

#[test]
fn test_trail_len_starts_at_zero() {
    let checker = DratChecker::new(5, false);
    assert_eq!(checker.trail_len(), 0);
}

#[test]
fn test_trail_len_grows_with_unit_propagation() {
    let mut checker = DratChecker::new(5, false);
    // Unit clause (a) forces propagation of a.
    checker.add_original(&[lit(0, true)]); // unit: assigns var 0
    assert!(
        checker.trail_len() > 0,
        "trail_len should increase after unit clause propagation"
    );
}

// ─── is_inconsistent / set_inconsistent ─────────────────────────────

#[test]
fn test_is_inconsistent_initially_false() {
    let checker = DratChecker::new(5, false);
    assert!(!checker.is_inconsistent());
}

#[test]
fn test_is_inconsistent_after_contradictory_units() {
    let mut checker = DratChecker::new(5, false);
    checker.add_original(&[lit(0, true)]); // (a)
    checker.add_original(&[lit(0, false)]); // (~a) — contradicts
    assert!(
        checker.is_inconsistent(),
        "contradictory unit clauses should set inconsistent"
    );
}

#[test]
fn test_set_inconsistent_round_trip() {
    let mut checker = DratChecker::new(5, false);
    assert!(!checker.is_inconsistent());
    checker.set_inconsistent(true);
    assert!(checker.is_inconsistent());
    checker.set_inconsistent(false);
    assert!(!checker.is_inconsistent());
}

// ─── backtrack_to ───────────────────────────────────────────────────

#[test]
fn test_backtrack_to_restores_trail_length() {
    let mut checker = DratChecker::new(5, false);
    let saved = checker.trail_len();
    checker.add_original(&[lit(0, true)]); // unit propagation
    assert!(checker.trail_len() > saved);
    checker.backtrack_to(saved);
    assert_eq!(
        checker.trail_len(),
        saved,
        "backtrack should restore trail length"
    );
}

#[test]
fn test_backtrack_to_clears_assignment() {
    let mut checker = DratChecker::new(5, false);
    let saved = checker.trail_len();
    checker.add_original(&[lit(0, true)]); // assigns var 0 = true
    assert_eq!(checker.lit_value(lit(0, true)), Some(true));
    checker.backtrack_to(saved);
    assert_eq!(
        checker.lit_value(lit(0, true)),
        None,
        "backtrack should unassign the variable"
    );
}

// ─── lit_value ──────────────────────────────────────────────────────

#[test]
fn test_lit_value_unassigned_returns_none() {
    let checker = DratChecker::new(5, false);
    assert_eq!(checker.lit_value(lit(0, true)), None);
    assert_eq!(checker.lit_value(lit(0, false)), None);
}

#[test]
fn test_lit_value_after_unit_clause() {
    let mut checker = DratChecker::new(5, false);
    checker.add_original(&[lit(0, true)]); // forces a = true
    assert_eq!(checker.lit_value(lit(0, true)), Some(true));
    assert_eq!(checker.lit_value(lit(0, false)), Some(false));
}

#[test]
fn test_lit_value_out_of_bounds_returns_none() {
    let checker = DratChecker::new(2, false);
    // Variable 10 is beyond num_vars=2.
    assert_eq!(checker.lit_value(lit(10, true)), None);
}

// ─── add_trusted ────────────────────────────────────────────────────

#[test]
fn test_add_trusted_adds_clause_without_rup_check() {
    let mut checker = DratChecker::new(5, false);
    let before = checker.live_clause_count();
    checker.add_trusted(&[lit(0, true), lit(1, true)]); // (a v b) — no RUP check
    assert_eq!(
        checker.live_clause_count(),
        before + 1,
        "add_trusted should insert clause"
    );
}

#[test]
fn test_add_trusted_unit_clause_propagates() {
    let mut checker = DratChecker::new(5, false);
    let saved_trail = checker.trail_len();
    checker.add_trusted(&[lit(2, true)]); // unit: c
    assert!(
        checker.trail_len() > saved_trail,
        "add_trusted unit clause should propagate"
    );
    assert_eq!(checker.lit_value(lit(2, true)), Some(true));
}

#[test]
fn test_add_trusted_when_inconsistent_is_noop() {
    let mut checker = DratChecker::new(5, false);
    checker.set_inconsistent(true);
    let before = checker.live_clause_count();
    checker.add_trusted(&[lit(0, true), lit(1, true)]);
    assert_eq!(
        checker.live_clause_count(),
        before,
        "add_trusted should be a no-op when inconsistent"
    );
}

// ─── live_clause_count ──────────────────────────────────────────────

#[test]
fn test_live_clause_count_starts_at_zero() {
    let checker = DratChecker::new(5, false);
    assert_eq!(checker.live_clause_count(), 0);
}

#[test]
fn test_live_clause_count_tracks_adds_and_deletes() {
    let mut checker = DratChecker::new(5, false);
    checker.add_original(&[lit(0, true), lit(1, true)]); // (a v b)
    checker.add_original(&[lit(2, true), lit(3, true)]); // (c v d)
    assert_eq!(checker.live_clause_count(), 2);

    checker.delete_clause(&[lit(0, true), lit(1, true)]);
    assert_eq!(checker.live_clause_count(), 1);
}

// ─── Edge case: verify with deletion-only proof (no empty clause) ───

#[test]
fn test_verify_deletion_only_proof_rejected() {
    let mut checker = DratChecker::new(3, false);
    let clauses = vec![vec![lit(0, true), lit(1, true)]];
    let steps = vec![ProofStep::Delete(vec![lit(0, true), lit(1, true)])];
    let result = checker.verify(&clauses, &steps);
    assert!(
        result.is_err(),
        "deletion-only proof should be rejected: no empty clause derived"
    );
    assert!(
        result.unwrap_err().to_string().contains("empty clause"),
        "error should mention empty clause"
    );
}
