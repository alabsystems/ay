// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for BV extract model validation (#5512).
//!
//! 6/50 QF_BV benchmarks return wrong answers because the model assigns
//! BV values that don't match Bool variables defined as extract bits.
//! Pattern: `(ite (= #x1 ((_ extract K K) x)) x_K (not x_K))` evaluates
//! to false in the model.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

fn solve_with_model(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
}

/// Solve with the legacy lenient `=`/`distinct` sort coercions ENABLED, which
/// restores the #5115 BitVec-width zero-extension. Default AY (z3 4.15.4
/// parity) rejects a `(= #x1 ((_ extract N N) x))` width mismatch as a sort
/// error; these MCMPC-family regressions intend the zero-extension, so they opt
/// in explicitly. See `solve_strict_err` for the strict-default twin.
fn solve_lenient(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    exec.context_mut().set_lenient_sort_coercions(true);
    exec.execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT2:\n{smt}"))
}

/// Execute under the STRICT default and return the elaboration error string,
/// asserting that a BitVec-width-mismatched `=`/`distinct` is rejected exactly
/// as z3 4.15.4 does (rather than silently zero-extended).
fn solve_strict_err(smt: &str) -> String {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    match exec.execute_all(&commands) {
        Ok(out) => panic!("expected a sort-mismatch rejection, got output: {out:?}\nSMT2:\n{smt}"),
        Err(err) => err.to_string(),
    }
}

/// Basic extract bit definition: Bool variable equals a single bit of a BV.
/// The ITE pattern is used in dualexecution/mean_buckets/wage benchmarks.
#[test]
#[timeout(60_000)]
fn test_bv_extract_bit_ite_definition_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun chosen () (_ BitVec 8))
        (declare-fun chosen_0 () Bool)
        (assert (ite (= #b1 ((_ extract 0 0) chosen)) chosen_0 (not chosen_0)))
        (assert chosen_0)
        (check-sat)
    "#;
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Multi-bit extract definition: several bits extracted and linked to Bool vars.
/// Mimics the full dualexecution benchmark pattern.
#[test]
#[timeout(60_000)]
fn test_bv_extract_multibit_ite_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun b0 () Bool)
        (declare-fun b1 () Bool)
        (declare-fun b7 () Bool)
        (assert (ite (= #b1 ((_ extract 0 0) x)) b0 (not b0)))
        (assert (ite (= #b1 ((_ extract 1 1) x)) b1 (not b1)))
        (assert (ite (= #b1 ((_ extract 7 7) x)) b7 (not b7)))
        (assert b0)
        (assert b7)
        (assert (not b1))
        (check-sat)
    "#;
    // SAT: x = 0b10000001 = #x81, b0=true, b1=false, b7=true
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Extract with additional BV constraints that force a specific value.
/// Tests that the BV model and Bool model stay consistent through
/// preprocessing and minimization.
#[test]
#[timeout(60_000)]
fn test_bv_extract_with_constraint_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun b5 () Bool)
        (assert (ite (= #b1 ((_ extract 5 5) x)) b5 (not b5)))
        (assert (= x #xAA))
        (check-sat)
        (get-value (x b5))
    "#;
    // x = 0xAA = 0b10101010, bit 5 = 1, so b5 = true
    let outputs = solve_with_model(smt);
    assert!(outputs[0] == "sat", "Expected sat, got: {outputs:?}");
}

/// Extract-based equality: direct comparison without ITE wrapper.
/// Tests evaluate_term extract handler.
#[test]
#[timeout(60_000)]
fn test_bv_extract_equality_direct_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 16))
        (declare-fun b10 () Bool)
        (assert (= b10 (= #b1 ((_ extract 10 10) x))))
        (assert b10)
        (assert (bvugt x #x0400))
        (check-sat)
    "#;
    // x > 0x0400 and bit 10 must be 1 → x >= 0x0400
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Mimics the actual dualexecution benchmark pattern more closely:
/// multiple bit-defined Bools with BV arithmetic constraints.
#[test]
#[timeout(60_000)]
fn test_bv_extract_dualexecution_pattern_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun chosen () (_ BitVec 8))
        (declare-fun chosen_0 () Bool)
        (declare-fun chosen_3 () Bool)
        (declare-fun chosen_7 () Bool)
        ; Bit definitions
        (assert (ite (= #b1 ((_ extract 0 0) chosen)) chosen_0 (not chosen_0)))
        (assert (ite (= #b1 ((_ extract 3 3) chosen)) chosen_3 (not chosen_3)))
        (assert (ite (= #b1 ((_ extract 7 7) chosen)) chosen_7 (not chosen_7)))
        ; Constraints
        (assert (not chosen_7))
        (assert chosen_0)
        (assert chosen_3)
        (assert (bvugt chosen #x08))
        (check-sat)
    "#;
    // chosen_7=false → bit 7=0, chosen_0=true → bit 0=1,
    // chosen_3=true → bit 3=1, chosen > 0x08
    // x = 0b0xxx1xx1 with x > 8 → e.g. 0b00001001 = 0x09
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// Core reproduction case for #5512: the minimizer changes a BV value
/// but the Bool variables (from SAT model) don't update, causing the
/// model output to be inconsistent.
/// The get-model output must have b5 = true when bit 5 of x is 1.
#[test]
#[timeout(60_000)]
fn test_bv_extract_model_consistency_after_minimization_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (set-option :produce-models true)
        (declare-fun x () (_ BitVec 8))
        (declare-fun b5 () Bool)
        (assert (ite (= #b1 ((_ extract 5 5) x)) b5 (not b5)))
        (assert b5)
        (assert (bvugt x #x00))
        (check-sat)
        (get-model)
    "#;
    let outputs = solve_with_model(smt);
    assert_eq!(outputs[0], "sat", "should be SAT");
    // The model must be consistent: b5 = true requires bit 5 of x = 1
    let model_str = &outputs[1];
    // If b5 is false in the model, the model is inconsistent
    assert!(
        !model_str.contains("b5 () Bool false"),
        "BUG #5512: model has b5=false but assertion requires b5=true. Model: {model_str}"
    );
}

/// Same test with larger BV — the original failing pattern from competition.
#[test]
#[timeout(60_000)]
fn test_bv_extract_model_64bit_consistency_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (set-option :produce-models true)
        (declare-fun chosen () (_ BitVec 64))
        (declare-fun chosen_10 () Bool)
        (declare-fun chosen_53 () Bool)
        (assert (ite (= #b1 ((_ extract 10 10) chosen)) chosen_10 (not chosen_10)))
        (assert (ite (= #b1 ((_ extract 53 53) chosen)) chosen_53 (not chosen_53)))
        (assert chosen_10)
        (assert (not chosen_53))
        (assert (bvugt chosen #x0000000000000000))
        (check-sat)
        (get-model)
    "#;
    let outputs = solve_with_model(smt);
    assert_eq!(outputs[0], "sat", "should be SAT");
    let model_str = &outputs[1];
    assert!(
        !model_str.contains("chosen_10 () Bool false"),
        "BUG #5512: model has chosen_10=false but assertion requires chosen_10=true. Model: {model_str}"
    );
}

/// UNSAT case: contradictory bit requirements.
#[test]
#[timeout(60_000)]
fn test_bv_extract_contradictory_bits_5512() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun b0 () Bool)
        (assert (ite (= #b1 ((_ extract 0 0) x)) b0 (not b0)))
        (assert b0)
        (assert (= ((_ extract 0 0) x) #b0))
        (check-sat)
    "#;
    // b0=true requires bit 0=1, but extract constraint says bit 0=0 → UNSAT
    let outputs = crate::common::solve_vec(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// #5115 regression: hex constant #x1 (BitVec4) compared against 1-bit extract.
/// MCMPC benchmarks use `(= #x1 ((_ extract N N) x))` — this is a BV width
/// mismatch that must be coerced via zero-extension at elaboration time.
#[test]
#[timeout(60_000)]
fn test_bv_hex_constant_width_coercion_5115() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (declare-fun b0 () Bool)
        (assert (= b0 (= #x1 ((_ extract 0 0) x))))
        (assert b0)
        (check-sat)
    "#;
    // #x1 is BitVec(4), extract produces BitVec(1) — elaboration should
    // zero-extend the extract to BitVec(4) before comparing.
    // SAT: x with bit 0 = 1, #x1 = 0001, zero_extend(extract(0,0,x)) = 0001
    let outputs = solve_lenient(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// #5115 strict-default twin: without the lenient flag, AY matches z3 4.15.4
/// and REJECTS the `(= #x1 ((_ extract 0 0) x))` width mismatch as a sort error
/// (`Sorts (_ BitVec 4) and (_ BitVec 1) are incompatible`).
#[test]
#[timeout(60_000)]
fn test_bv_hex_constant_width_mismatch_strict_rejects_5115() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (= #x1 ((_ extract 0 0) x)))
        (check-sat)
    "#;
    let err = solve_strict_err(smt);
    assert!(
        err.contains("sort mismatch") && err.contains("BitVec 4") && err.contains("BitVec 1"),
        "unexpected strict error: {err}"
    );
}

/// #5115: Full MCMPC pattern with multiple bit definitions using #x1.
#[test]
#[timeout(60_000)]
fn test_bv_mcmpc_pattern_hex_extract_5115() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun chosen () (_ BitVec 8))
        (declare-fun chosen_0 () Bool)
        (declare-fun chosen_3 () Bool)
        (declare-fun chosen_7 () Bool)
        (assert (= chosen_0 (= #x1 ((_ extract 0 0) chosen))))
        (assert (= chosen_3 (= #x1 ((_ extract 3 3) chosen))))
        (assert (= chosen_7 (= #x1 ((_ extract 7 7) chosen))))
        (assert chosen_0)
        (assert (not chosen_7))
        (assert chosen_3)
        (check-sat)
    "#;
    let outputs = solve_lenient(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// #5115: Verify that BV width coercion produces correct UNSAT.
#[test]
#[timeout(60_000)]
fn test_bv_hex_width_coercion_unsat_5115() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (= #x1 ((_ extract 0 0) x)))
        (assert (= ((_ extract 0 0) x) #b0))
        (check-sat)
    "#;
    // #x1 = 0001 (BitVec4), extract = 0 (BitVec1), zero_extend(0) = 0000
    // 0001 != 0000, so the first assert requires bit 0 = 1
    // Second assert says bit 0 = 0 → UNSAT
    let outputs = solve_lenient(smt);
    assert_eq!(outputs, vec!["unsat"]);
}

/// #5115: Distinct with BV width mismatch.
#[test]
#[timeout(60_000)]
fn test_bv_distinct_width_coercion_5115() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (distinct #x0 ((_ extract 0 0) x)))
        (check-sat)
    "#;
    // #x0 = 0000 (BitVec4), extract = BitVec(1)
    // After coercion: distinct(0000, zero_extend(extract)) → bit 0 must be 1
    let outputs = solve_lenient(smt);
    assert_eq!(outputs, vec!["sat"]);
}

/// #5115 strict-default twin for `distinct`: the width mismatch is a sort error
/// under the default (z3 4.15.4 parity), not a silent zero-extension.
#[test]
#[timeout(60_000)]
fn test_bv_distinct_width_mismatch_strict_rejects_5115() {
    let smt = r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (distinct #x0 ((_ extract 0 0) x)))
        (check-sat)
    "#;
    let err = solve_strict_err(smt);
    assert!(
        err.contains("sort mismatch") && err.contains("BitVec 4") && err.contains("BitVec 1"),
        "unexpected strict error: {err}"
    );
}
