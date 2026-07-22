// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6010: QF_SLIA logic must route Seq-sorted
//! formulas to the Seq solver, not the String solver.
//!
//! When a formula uses `(set-logic QF_SLIA)` with `(Seq T)` variables,
//! the executor must upgrade to QF_SEQLIA so Seq axioms are generated.
//! Before the fix, these all returned `unknown`.

/// Exact reproduction case from #6010.
#[test]
fn test_slia_seq_unit_sat() {
    let result = crate::common::solve(
        "(set-logic QF_SLIA)
         (declare-const s (Seq Int))
         (assert (= s (seq.unit 42)))
         (assert (= (seq.len s) 1))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

/// QF_SLIA with Seq + arithmetic: length constraint.
#[test]
fn test_slia_seq_len_arith() {
    let result = crate::common::solve(
        "(set-logic QF_SLIA)
         (declare-const s (Seq Int))
         (declare-const n Int)
         (assert (= n (seq.len s)))
         (assert (>= n 0))
         (check-sat)",
    );
    assert_eq!(result, "sat");
}

/// QF_SLIA with Seq: unsatisfiable negative length.
#[test]
fn test_slia_seq_negative_len_unsat() {
    let result = crate::common::solve(
        "(set-logic QF_SLIA)
         (declare-const s (Seq Int))
         (assert (< (seq.len s) 0))
         (check-sat)",
    );
    assert_eq!(result, "unsat");
}

/// QF_SLIA with mixed String + Seq: routes to QF_SEQLIA since Seq
/// is present. The Seq solver may not handle String ops (pre-existing
/// limitation), so accept unknown. The routing fix itself is verified
/// by the pure Seq tests above.
#[test]
fn test_slia_mixed_string_and_seq() {
    let result = crate::common::solve(
        "(set-logic QF_SLIA)
         (declare-const x String)
         (declare-const s (Seq Int))
         (assert (= (str.len x) 3))
         (assert (= (seq.len s) 2))
         (check-sat)",
    );
    let r = result.as_str();
    assert!(
        r == "sat" || r == "unknown",
        "expected sat or unknown, got {r}"
    );
}

/// Pure QF_SLIA without Seq should not crash or return unsat.
/// Currently returns unknown because the String solver has limited
/// support. When String solving improves, tighten to assert_eq "sat".
#[test]
fn test_slia_pure_strings_no_crash() {
    let result = crate::common::solve(
        "(set-logic QF_SLIA)
         (declare-const x String)
         (assert (= (str.len x) 5))
         (check-sat)",
    );
    let r = result.as_str();
    assert!(
        r == "sat" || r == "unknown",
        "expected sat or unknown, got {r}"
    );
}
