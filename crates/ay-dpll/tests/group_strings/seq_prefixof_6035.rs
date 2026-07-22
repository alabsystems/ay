// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for seq.prefixof/suffixof ground completeness (#6035, #6036).
//!
//! Before this fix, `(not (seq.prefixof s t))` returned false-SAT when s was
//! demonstrably a prefix of t via concrete construction. The fix adds ground
//! evaluation: when both operands resolve to concrete sequences, prefixof/
//! suffixof is evaluated directly and forced to the correct boolean value.
//!
//! Also tests nth-ground equality axiom injection (#6036) which makes ground
//! evaluation work even when sequences are defined only via nth constraints.

use ntest::timeout;

// ========== Prefixof completeness (#6035) ==========

/// NOT prefixof when s IS a concrete prefix of t should be UNSAT.
/// This is the exact reproduction case from #6035.
#[test]
#[timeout(30_000)]
fn test_not_prefixof_concrete_prefix_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "NOT prefixof(unit(1), unit(1)++unit(2)) should be UNSAT"
    );
}

/// Prefixof should be true when s IS a prefix of t (positive direction).
#[test]
#[timeout(30_000)]
fn test_prefixof_concrete_prefix_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (seq.prefixof s t))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "prefixof(unit(1), unit(1)++unit(2)) should be SAT"
    );
}

/// NOT prefixof when s is NOT a prefix of t should be SAT.
#[test]
#[timeout(30_000)]
fn test_not_prefixof_different_elements_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (= t (seq.++ (seq.unit 2) (seq.unit 3))))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "NOT prefixof(unit(1), unit(2)++unit(3)) should be SAT"
    );
}

/// Prefixof with empty prefix is always true.
#[test]
#[timeout(30_000)]
fn test_prefixof_empty_prefix_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (assert (= t (seq.unit 42)))
         (assert (seq.prefixof (as seq.empty (Seq Int)) t))
         (check-sat)",
    );
    assert_eq!(result, "sat", "empty is always a prefix");
}

/// NOT prefixof with empty prefix is always UNSAT.
#[test]
#[timeout(30_000)]
fn test_not_prefixof_empty_prefix_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (assert (= t (seq.unit 42)))
         (assert (not (seq.prefixof (as seq.empty (Seq Int)) t)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "empty is always a prefix, so NOT prefixof(empty, t) is UNSAT"
    );
}

/// NOT prefixof when s is longer than t should be SAT.
#[test]
#[timeout(30_000)]
fn test_not_prefixof_longer_prefix_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 3))))
         (assert (= t (seq.unit 1)))
         (assert (not (seq.prefixof s t)))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "NOT prefixof when s longer than t should be SAT"
    );
}

/// Prefixof with equal sequences should be true.
#[test]
#[timeout(30_000)]
fn test_prefixof_equal_sequences_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (seq.prefixof s t))
         (check-sat)",
    );
    assert_eq!(result, "sat", "s = t implies prefixof(s, t)");
}

// ========== Suffixof completeness (#6035) ==========

/// NOT suffixof when s IS a concrete suffix of t should be UNSAT.
#[test]
#[timeout(30_000)]
fn test_not_suffixof_concrete_suffix_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 2)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (not (seq.suffixof s t)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "NOT suffixof(unit(2), unit(1)++unit(2)) should be UNSAT"
    );
}

/// Suffixof should be true when s IS a suffix of t (positive direction).
#[test]
#[timeout(30_000)]
fn test_suffixof_concrete_suffix_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 2)))
         (assert (= t (seq.++ (seq.unit 1) (seq.unit 2))))
         (assert (seq.suffixof s t))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "suffixof(unit(2), unit(1)++unit(2)) should be SAT"
    );
}

/// NOT suffixof when s is NOT a suffix of t should be SAT.
#[test]
#[timeout(30_000)]
fn test_not_suffixof_different_elements_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const s (Seq Int))
         (declare-const t (Seq Int))
         (assert (= s (seq.unit 1)))
         (assert (= t (seq.++ (seq.unit 2) (seq.unit 3))))
         (assert (not (seq.suffixof s t)))
         (check-sat)",
    );
    assert_eq!(
        result, "sat",
        "NOT suffixof(unit(1), unit(2)++unit(3)) should be SAT"
    );
}

/// NOT suffixof with empty suffix is always UNSAT (empty is suffix of everything).
#[test]
#[timeout(30_000)]
fn test_not_suffixof_empty_suffix_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SEQLIA)
         (declare-const t (Seq Int))
         (assert (= t (seq.unit 42)))
         (assert (not (seq.suffixof (as seq.empty (Seq Int)) t)))
         (check-sat)",
    );
    assert_eq!(
        result, "unsat",
        "empty is always a suffix, so NOT suffixof(empty, t) is UNSAT"
    );
}
