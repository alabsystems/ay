// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::test_util::lit;

#[test]
fn test_original_clause_added_without_check() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(2, true)]);
    checker.add_original(&[lit(1, false), lit(2, false)]);
    assert_eq!(checker.inner.stats().original, 3);
    assert_eq!(checker.inner.stats().failures, 0);
}

#[test]
fn test_derived_unit_resolution_passes_rup() {
    let mut checker = ForwardChecker::new(3);
    // (a ∨ b) ∧ (¬a ∨ b) → b is RUP
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(1, true)]);
    checker.add_derived(&[lit(1, true)]);
    assert_eq!(checker.derived_count, 1);
    assert_eq!(checker.inner.stats().failures, 0);
}

/// A non-RUP-implied derived clause is added as trusted and counted as a
/// RUP failure (#7929). Previously this panicked, but inprocessing steps
/// (BVE, backbone, sweep) can emit clauses whose derivation chains are not
/// reproducible by the forward checker. External DRAT/LRAT checkers validate
/// these steps against the full proof.
#[test]
fn test_derived_clause_not_implied_adds_trusted() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_derived(&[lit(0, false), lit(1, false)]);
    assert_eq!(checker.rup_failures(), 1, "should record one RUP failure");
    assert_eq!(checker.derived_count, 1, "should count the derived clause");
}

#[test]
fn test_resolution_chain_rup() {
    let mut checker = ForwardChecker::new(4);
    // (a∨b), (¬a∨c), (¬b∨c) → c is RUP. Assume ¬c: clause 2 → ¬a,
    // clause 3 → ¬b, clause 1 (a∨b) all false → conflict.
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(2, true)]);
    checker.add_original(&[lit(1, false), lit(2, true)]);
    checker.add_derived(&[lit(2, true)]);
    assert_eq!(checker.inner.stats().failures, 0);
}

#[test]
fn test_empty_clause_makes_inconsistent() {
    let mut checker = ForwardChecker::new(2);
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    assert!(checker.inner.is_inconsistent());
}

#[test]
fn test_delete_clause() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(1, true)]);
    checker.add_original(&[lit(0, true), lit(1, false)]);
    checker.add_derived(&[lit(0, true)]);
    checker.delete_clause(&[lit(0, true), lit(1, true)]);
    assert_eq!(checker.inner.stats().deletions, 1);
}

#[test]
#[cfg(debug_assertions)]
fn test_push_pop_restores_after_scoped_unsat() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    assert!(!checker.inner.is_inconsistent());
    checker.push();
    checker.add_original(&[lit(0, false)]);
    checker.add_original(&[lit(1, false)]);
    assert!(checker.inner.is_inconsistent());
    checker.pop();
    assert!(
        !checker.inner.is_inconsistent(),
        "checker must resume after pop"
    );
    checker.add_original(&[lit(0, false), lit(1, true)]);
    checker.add_derived(&[lit(1, true)]);
    assert_eq!(checker.inner.stats().failures, 0);
}

#[test]
#[cfg(debug_assertions)]
fn test_push_pop_still_detects_invalid_after_pop() {
    // After push/UNSAT/pop, invalid derived clauses are detected as RUP
    // failures and added as trusted (#7929).
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.push();
    checker.add_original(&[lit(0, false)]);
    checker.add_original(&[lit(1, false)]);
    assert!(checker.inner.is_inconsistent());
    checker.pop();
    checker.add_derived(&[lit(0, false), lit(1, false)]);
    assert_eq!(
        checker.rup_failures(),
        1,
        "should detect RUP failure after pop"
    );
}

#[test]
fn test_empty_clause_step_is_counted_after_inconsistent() {
    let mut checker = ForwardChecker::new(2);
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(0, false)]);
    assert!(checker.inner.is_inconsistent());
    checker.add_derived(&[]);
    assert_eq!(checker.derived_count(), 1);
    assert_eq!(checker.inner.stats().failures, 0);
}

#[test]
fn test_trusted_transform_accepts_non_rup_clause() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_trusted_transform(&[lit(0, false), lit(1, false)]);
}

#[test]
fn test_trusted_transform_warns_on_fully_falsified() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true)]);
    checker.add_original(&[lit(1, true)]);
    checker.add_trusted_transform(&[lit(0, false), lit(1, false)]);
}

#[test]
fn test_trusted_transform_skips_tautology() {
    let mut checker = ForwardChecker::new(2);
    checker.add_trusted_transform(&[lit(0, true), lit(0, false)]);
}

/// ForwardChecker detects a deliberately-wrong BVE unit clause (#7929).
#[test]
fn test_bve_wrong_unit_clause_detected_by_forward_checker() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_original(&[lit(0, false), lit(2, true)]);
    checker.add_derived(&[lit(1, true), lit(2, true)]);
    checker.add_original(&[lit(1, false)]);
    checker.add_derived(&[lit(2, false)]);
    assert_eq!(
        checker.rup_failures(),
        1,
        "wrong unit clause should be a RUP failure"
    );
}

#[test]
fn test_empty_clause_rup_failure_bypass_sets_inconsistent() {
    let mut checker = ForwardChecker::new(3);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    assert!(!checker.inner.is_inconsistent());
    checker.add_derived(&[]);
    assert!(checker.inner.is_inconsistent());
}

/// Multiple RUP failures are counted correctly (#7929).
#[test]
fn test_multiple_rup_failures_counted() {
    let mut checker = ForwardChecker::new(4);
    checker.add_original(&[lit(0, true), lit(1, true)]);
    checker.add_derived(&[lit(2, true)]);
    checker.add_derived(&[lit(3, true)]);
    assert_eq!(checker.rup_failures(), 2);
    assert_eq!(checker.derived_count, 2);
}
