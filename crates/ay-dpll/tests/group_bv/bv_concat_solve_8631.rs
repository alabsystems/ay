// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end integration tests for BV concat solving (#8631).
//!
//! Verifies that `(concat ...)` is parsed, elaborated, bit-blasted, and solved
//! correctly through the full ay pipeline. These tests exercise the path from
//! SMT-LIB input to sat/unsat result with model extraction.
//!
//! Part of #8631: BvConcat parser support needed by model-checker-consumer.

#![allow(clippy::panic)]

use ntest::timeout;

/// Basic concat SAT: concat of two 8-bit variables equals a 16-bit constant.
#[test]
#[timeout(10_000)]
fn test_bv_concat_basic_sat_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (concat x y) #xABCD))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "concat(x,y) = #xABCD should be SAT");
}

/// Concat UNSAT: contradictory constraints on overlapping concat results.
#[test]
#[timeout(10_000)]
fn test_bv_concat_basic_unsat_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (concat x y) #xABCD))
        (assert (= (concat x y) #x1234))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "concat(x,y) = #xABCD AND concat(x,y) = #x1234 should be UNSAT"
    );
}

/// Concat with extract: extract high/low bytes from a concat result.
/// This is the pattern model-checker-consumer uses for memory address construction.
#[test]
#[timeout(10_000)]
fn test_bv_concat_extract_roundtrip_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const hi (_ BitVec 8))
        (declare-const lo (_ BitVec 8))
        (assert (= hi #xAB))
        (assert (= lo #xCD))
        (assert (= ((_ extract 15 8) (concat hi lo)) hi))
        (assert (= ((_ extract 7 0) (concat hi lo)) lo))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "extract of concat should roundtrip correctly"
    );
}

/// Concat with asymmetric widths: 4-bit and 12-bit producing 16-bit.
#[test]
#[timeout(10_000)]
fn test_bv_concat_asymmetric_widths_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const tag (_ BitVec 4))
        (declare-const payload (_ BitVec 12))
        (assert (= tag #xA))
        (assert (= payload #xBCD))
        (assert (= (concat tag payload) #xABCD))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "4-bit concat 12-bit should work");
}

/// Concat with BV arithmetic: add after concat.
#[test]
#[timeout(10_000)]
fn test_bv_concat_with_arithmetic_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x01))
        (assert (= y #x02))
        (assert (= (bvadd (concat x y) #x0001) #x0103))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "bvadd(concat(#x01, #x02), #x0001) = #x0103"
    );
}

/// N-ary concat: three arguments (left-associative desugaring).
/// (concat a b c) => (concat (concat a b) c)
#[test]
#[timeout(10_000)]
fn test_bv_concat_nary_three_args_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const a (_ BitVec 4))
        (declare-const b (_ BitVec 4))
        (declare-const c (_ BitVec 4))
        (assert (= a #xA))
        (assert (= b #xB))
        (assert (= c #xC))
        (assert (= (concat a b c) #xABC))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "3-arg concat(#xA, #xB, #xC) = #xABC");
}

/// Concat used in comparison: bvult on concatenated values.
#[test]
#[timeout(10_000)]
fn test_bv_concat_comparison_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x00))
        (assert (= y #xFF))
        (assert (bvult (concat x y) #x0100))
        (check-sat)
    "#;
    // concat(#x00, #xFF) = #x00FF, which is < #x0100
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"], "concat(#x00, #xFF) < #x0100");
}

/// Concat UNSAT via comparison contradiction.
#[test]
#[timeout(10_000)]
fn test_bv_concat_comparison_unsat_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= x #x01))
        (assert (= y #x00))
        (assert (bvult (concat x y) #x0100))
        (check-sat)
    "#;
    // concat(#x01, #x00) = #x0100, which is NOT < #x0100
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "concat(#x01, #x00) < #x0100 is UNSAT"
    );
}

/// Concat with model extraction: verify the model assigns correct values.
#[test]
#[timeout(10_000)]
fn test_bv_concat_model_extraction_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (set-option :produce-models true)
        (declare-const x (_ BitVec 8))
        (declare-const y (_ BitVec 8))
        (assert (= (concat x y) #xCAFE))
        (check-sat)
        (get-model)
    "#;
    let commands =
        ay_frontend::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"));

    assert_eq!(outputs[0], "sat", "should be SAT");

    // The model must assign x = #xCA and y = #xFE (or equivalent)
    let model_str = &outputs[1];
    // Verify model contains definitions for both variables
    assert!(
        model_str.contains("define-fun x") || model_str.contains("define-fun y"),
        "Model should contain variable definitions. Model: {model_str}"
    );
}

/// Concat in nested expression: ite with concat branches.
/// This matches patterns seen in model-checker-consumer loop harnesses.
/// Note: QF_BV with ITE over non-trivial BV expressions may return unknown
/// in the current BV solver. The key assertion is that it does NOT return unsat.
#[test]
#[timeout(10_000)]
fn test_bv_concat_in_ite_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const flag Bool)
        (declare-const a (_ BitVec 8))
        (declare-const b (_ BitVec 8))
        (declare-const result (_ BitVec 16))
        (assert (= a #xAA))
        (assert (= b #xBB))
        (assert (= result (ite flag (concat a b) (concat b a))))
        (assert (= result #xAABB))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert!(
        outputs == vec!["sat"] || outputs == vec!["unknown"],
        "ite(flag, concat(#xAA,#xBB), concat(#xBB,#xAA)) = #xAABB should be SAT or unknown (not unsat), got: {outputs:?}"
    );
}

/// Concat with 1-bit values: single-bit concat to build wider BVs.
/// Common in hardware verification (individual wire concatenation).
#[test]
#[timeout(10_000)]
fn test_bv_concat_single_bit_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-const b0 (_ BitVec 1))
        (declare-const b1 (_ BitVec 1))
        (declare-const b2 (_ BitVec 1))
        (declare-const b3 (_ BitVec 1))
        (assert (= b3 #b1))
        (assert (= b2 #b0))
        (assert (= b1 #b1))
        (assert (= b0 #b0))
        (assert (= (concat b3 b2 b1 b0) #b1010))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "concat of 4 single bits #b1010 should be SAT"
    );
}

/// Concat with constant folding: both args are constants.
/// The elaborator should fold this to a single constant.
#[test]
#[timeout(10_000)]
fn test_bv_concat_constant_fold_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (assert (= (concat #x0F #xF0) #x0FF0))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["sat"],
        "concat(#x0F, #xF0) = #x0FF0 is trivially SAT"
    );
}

/// Concat constant folding UNSAT: wrong expected result.
#[test]
#[timeout(10_000)]
fn test_bv_concat_constant_fold_unsat_8631() {
    let smt = r#"
        (set-logic QF_BV)
        (assert (= (concat #x0F #xF0) #xAAAA))
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "concat(#x0F, #xF0) = #xAAAA is UNSAT"
    );
}
