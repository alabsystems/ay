// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QF_UFLRA soundness gate tests.
//!
//! Regression test for #6812: ay returns `unsat` on a `sat` QF_UFLRA benchmark
//! (cpachecker-induction.modulus_true-unreach-call.i.smt2). The root cause is
//! incremental split-loop clause poisoning: theory conflict clauses learned in
//! earlier iterations accumulate in the persistent SAT solver and form a
//! contradictory clause database by iteration 5.

use ntest::timeout;

use super::helpers::{
    assert_not_sat_file, assert_not_unsat_file, assert_sat_validates, assert_scope_results,
    assert_unsat_with_proof, ProofExpectation,
};

// --- Consumer coverage: deductive-checks uses QF_UFLRA incrementally ---

/// SAT with model validation: UF over Real-sorted terms with LRA constraints.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflra_sat_validates_model() {
    assert_sat_validates(
        r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (= x 3.0))
        (assert (= y (f x)))
        (assert (> y 0.0))
        (assert (<= y 100.0))
        (check-sat)
    "#,
    );
}

/// UNSAT with proof envelope: UF congruence + LRA contradiction.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflra_unsat_proof_envelope() {
    // f(x) = f(y) via congruence (x = y), but f(x) > 0 and f(y) < 0.
    assert_unsat_with_proof(
        r#"
        (set-logic QF_UFLRA)
        (set-option :produce-proofs true)
        (declare-fun f (Real) Real)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (= x y))
        (assert (> (f x) 0.0))
        (assert (< (f y) 0.0))
        (check-sat)
        (get-proof)
    "#,
        ProofExpectation::TextOnly,
    );
}

/// Incremental push/pop scope: deductive-checks pattern with UF+LRA constraints.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflra_incremental_scope() {
    assert_scope_results(
        r#"
        (set-logic QF_UFLRA)
        (declare-fun f (Real) Real)
        (declare-fun x () Real)
        (assert (= x 5.0))
        (assert (= (f x) 10.0))
        (check-sat)
        (push 1)
        (assert (not (= (f 5.0) 10.0)))
        (check-sat)
        (pop 1)
        (check-sat)
    "#,
        &["sat", "unsat", "sat"],
    );
}

/// Regression for #6812: QF_UFLRA false-UNSAT on cpachecker modulus benchmark.
///
/// The benchmark encodes a CPA-checker k-induction proof obligation with:
/// - `Rational__%_` (UF encoding of modulus)
/// - `_<<_` (UF encoding of left-shift)
/// - `__BASE_ADDRESS_OF__` (UF for pointer base)
/// - An ITE pattern `(ite (= m@4 (Rational__%_ n@3 d@3)) 1 0)`
///
/// ay incorrectly returns `unsat`; z3 correctly returns `sat`.
/// The `:status sat` annotation in the benchmark confirms `sat` is correct.
#[test]
#[timeout(30_000)]
fn test_gate_qf_uflra_6812_cpachecker_modulus_sat() {
    assert_not_unsat_file(
        "benchmarks/smt/QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.modulus_true-unreach-call.i.smt2",
    );
}

/// Exact-file UNSAT control: the #6812 mitigation must not over-escalate
/// genuine UFLRA contradictions.
#[test]
#[timeout(10_000)]
fn test_gate_qf_uflra_exact_unsat_control_not_sat() {
    assert_not_sat_file("benchmarks/smt/QF_UFLRA/unsat_equality_propagation.smt2");
}

/// #6812 control benchmark from the QF_UFLRA BMC family.
#[test]
#[timeout(30_000)]
fn test_gate_qf_uflra_6812_cpachecker_bmc_control_not_unsat() {
    assert_not_unsat_file(
        "benchmarks/smt/QF_UFLRA/cpachecker-bmc-svcomp14/cpachecker-bmc.implicitfloatconversion_false-unreach-call.i.smt2",
    );
}

/// Regression for W19-5 differential testing: false-UNSAT on QF_UFLRA email_spec3.
///
/// Root cause: `(define-fun _7 () Real 0)` elaborated the numeral `0` as Int
/// instead of coercing to Real. This caused sort-mismatched model equalities
/// in the Nelson-Oppen loop, producing bogus theory conflicts.
#[test]
#[timeout(30_000)]
fn test_gate_qf_uflra_email_spec3_not_false_unsat() {
    assert_not_unsat_file(
        "benchmarks/smt/QF_UFLRA/cpachecker-induction-svcomp14/cpachecker-induction.email_spec3_product31_false-unreach-call.cil.c.smt2",
    );
}
