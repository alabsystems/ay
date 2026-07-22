// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_UFLIA soundness gate tests — congruence-to-LIA propagation (#6825).
//!
//! These tests exercise the Nelson-Oppen fixpoint loop between EUF and LIA.
//! The bug pattern: EUF discovers an equality (f(x0) = f(x2)) via congruence
//! closure, but this equality is not forwarded to LIA when using
//! `check_during_propagate()` instead of the full N-O loop. The fix (#6825)
//! adds `run_final_check_if_needed()` to run the full N-O fixpoint before
//! accepting a SAT model.

use ntest::timeout;

use super::helpers::{
    assert_not_sat_file, assert_sat_validates, assert_sat_validates_file, assert_unsat_with_proof,
    ProofExpectation,
};

/// Exact reproduction of #6825: congruence-derived equality must reach LIA.
///
/// f(x2) = 0 AND f(x0) >= 2 AND x2 = x0 is UNSAT because:
///   x2 = x0 → f(x2) = f(x0) (congruence) → f(x0) = 0 → contradicts f(x0) >= 2.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflia_congruence_to_lia_6825() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_UFLIA)
        (set-option :produce-proofs true)
        (declare-fun f (Int) Int)
        (declare-fun x0 () Int)
        (declare-fun x2 () Int)
        (assert (= (f x2) 0))
        (assert (>= (f x0) 2))
        (assert (= x2 x0))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

/// SAT case: congruence does NOT produce a contradiction.
///
/// f(x0) = 5 AND f(x1) >= 3 AND x0 != x1 is SAT because x0 != x1 means
/// no congruence: f(x0) and f(x1) are independent.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflia_no_congruence_sat() {
    assert_sat_validates(
        r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun x0 () Int)
        (declare-fun x1 () Int)
        (assert (= (f x0) 5))
        (assert (>= (f x1) 3))
        (assert (not (= x0 x1)))
        (check-sat)
    "#,
    );
}

/// Transitivity chain: congruence through a=b, b=c must reach LIA.
///
/// f(a) = 0 AND f(c) >= 1 AND a = b AND b = c is UNSAT because:
///   a = b, b = c → a = c → f(a) = f(c) → f(c) = 0 → contradicts f(c) >= 1.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflia_transitive_congruence_to_lia() {
    assert_unsat_with_proof(
        r#"
        (set-logic QF_UFLIA)
        (set-option :produce-proofs true)
        (declare-fun f (Int) Int)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (declare-fun c () Int)
        (assert (= (f a) 0))
        (assert (>= (f c) 1))
        (assert (= a b))
        (assert (= b c))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

/// Exact benchmark-level canary for the #6825 congruence-to-LIA bug.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflia_6825_unsat_benchmark_not_sat() {
    assert_not_sat_file("benchmarks/smt/QF_UFLIA/unsat_congruence_to_lia.smt2");
}

/// Benchmark-level SAT control: congruence on equal arguments must still
/// validate on the saved UFLIA benchmark file, not just the inline packet.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflia_6825_sat_benchmark_validates_model() {
    assert_sat_validates_file("benchmarks/smt/QF_UFLIA/sat_multiarg_congruence.smt2");
}

/// Performance regression gate for Seq-dense QF_UFLIA (#8404).
///
/// ghost_vec pattern: 8 push operations with frame axioms + length axioms +
/// concrete values + postcondition. This exercises the Nelson-Oppen EUF+LIA
/// combination with dense integer arithmetic from Seq index constraints.
///
/// Before fix: >120s timeout (global simplex pivot budget counted BCP
/// propagation pivots, causing budget exhaustion).
/// After fix: <2s (propagation pivots excluded from full-check budget).
///
/// Timeout set to 30s to catch regressions while allowing headroom on loaded
/// CI and developer machines.
#[test]
#[timeout(30_000)]
fn test_gate_qf_uflia_8404_seq_dense_ghost_vec_sat() {
    assert_sat_validates_file("benchmarks/smt/QF_UFLIA/seq_dense_ghost_vec.smt2");
}
