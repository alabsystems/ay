// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for mixed Int/BitVec formulas (#5356).
//!
//! When a formula uses both Int and BitVec sorts without conversion functions
//! (bv2nat/int2bv), the solver routes to the BV-first strategy: try BV solver
//! (which handles extract/concat/etc.), fall back to AUFLIA if model validation
//! fails on Int constraints.

use ntest::timeout;

/// Core repro case from #5356: mixed Int + BitVec with `set-logic ALL`.
/// Previously returned `unknown` because AUFLIA treated BV extract as UF.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_sat_all_logic_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= x 0))
        (assert (= ((_ extract 0 0) S) #b1))
        (check-sat)
        (get-value (x S))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "Expected sat for mixed Int/BV formula, got: {outputs:?}"
    );
}

/// Same formula without explicit logic (auto-detection).
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_sat_auto_detect_5356() {
    let smt = r#"
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (= x 0))
        (assert (= ((_ extract 0 0) S) #b1))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Contradictory Int constraints with BV: must return UNSAT.
/// BV solver may produce false SAT (treats Int predicates as opaque),
/// but model validation catches it and falls back to AUFLIA.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_unsat_contradictory_int_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 2))
        (assert (<= x 1))
        (assert (= ((_ extract 0 0) S) #b1))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Disjunction across Int and BV theories.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_disjunction_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (>= x 0))
        (assert (<= x 1))
        (assert (or (and (= x 0) (= ((_ extract 0 0) S) #b1))
                    (and (= x 1) (= ((_ extract 1 1) S) #b1))))
        (check-sat)
        (get-value (x S))
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "sat",
        "Expected sat for disjunctive mixed formula, got: {outputs:?}"
    );
}

/// BV-only UNSAT should still work through the BV-first path.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_unsat_bv_contradiction_5356() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const S (_ BitVec 2))
        (assert (= x 0))
        (assert (= ((_ extract 0 0) S) #b1))
        (assert (= ((_ extract 0 0) S) #b0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// Mixed Int/BV formulas with unsupported symbolic arithmetic must fail closed.
///
/// The BV-first route can satisfy the bitvector slice while AUFLIA reports
/// symbolic integer div/mod as unsupported. That diagnostic must not be
/// upgraded into SAT, because verification-consumer would treat the resulting model as proof
/// evidence for the whole mixed VC.
#[test]
#[timeout(60_000)]
fn test_mixed_int_bv_symbolic_div_fails_closed_unsupported_arithmetic() {
    let smt = r#"
        (set-logic ALL)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const S (_ BitVec 2))
        (assert (= x 1))
        (assert (> y 1))
        (assert (= 1 (div x y)))
        (assert (= ((_ extract 0 0) S) #b1))
        (check-sat)
        (get-info :reason-unknown)
        (get-info :all-statistics)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs[0], "unknown",
        "unsupported mixed Int/BV div must not be surfaced as SAT: {outputs:?}"
    );
    assert_eq!(
        outputs[1], "(:reason-unknown (unsupported arithmetic))",
        "mixed Int/BV div should preserve the arithmetic unsupported reason: {outputs:?}"
    );
    assert!(
        outputs[2].contains(".unsupported-fragment") && outputs[2].contains("arithmetic-div-mod"),
        "mixed Int/BV div should carry structured unsupported-fragment stats: {outputs:?}"
    );
}
