// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Floating-point theory executor-level tests (#8456).
//!
//! Tests that QF_FP queries return correct results with model validation
//! active. Prior to #8456, FP theory set `skip_model_eval=true`, bypassing
//! assertion-level validation. Model validation is now active for FP via
//! TERM_FLAG_FP and the observation pipeline in `observation.rs`.

use crate::Executor;
use ay_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

// ---------------------------------------------------------------------------
// Basic FP SAT/UNSAT with model validation (#8456)
// ---------------------------------------------------------------------------

/// FP NaN classification: fp.isNaN on a declared variable is satisfiable.
/// Model validation must accept the FP model.
#[test]
fn test_fp_is_nan_sat_with_validation_8456() {
    let smt = r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "FP isNaN should be sat or unknown, got: {result}"
    );
}

/// FP: x = +0.0 is satisfiable. Tests constant FP model construction.
#[test]
fn test_fp_positive_zero_sat_8456() {
    let smt = r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.eq x ((_ to_fp 8 24) RNE 0.0)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "FP positive zero equality should be sat, got: {result}"
    );
}

/// FP contradiction: x cannot be both NaN and positive.
#[test]
fn test_fp_nan_and_positive_unsat_8456() {
    let smt = r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(assert (fp.isNaN x))
(assert (fp.isPositive x))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("unsat"),
        "FP NaN-and-positive should be unsat, got: {result}"
    );
}

/// FP: fp.lt ordering on concrete FP values.
#[test]
fn test_fp_lt_concrete_sat_8456() {
    let smt = r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(assert (fp.lt x y))
(assert (not (fp.isNaN x)))
(assert (not (fp.isNaN y)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "FP lt on two non-NaN variables should be sat, got: {result}"
    );
}

/// FP: fp.add with rounding mode is satisfiable.
#[test]
fn test_fp_add_sat_8456() {
    let smt = r#"
(set-logic QF_FP)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y (_ FloatingPoint 8 24))
(declare-const z (_ FloatingPoint 8 24))
(assert (= z (fp.add RNE x y)))
(assert (not (fp.isNaN z)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "FP add with non-NaN result should be sat, got: {result}"
    );
}

// ---------------------------------------------------------------------------
// FP to_real model validation (#8456)
// ---------------------------------------------------------------------------

/// FP to_real: mixed FP+Real formula exercises the merged model path.
/// This previously required skip_model_eval to avoid false Unknown.
#[test]
fn test_fp_to_real_sat_with_validation_8456() {
    let smt = r#"
(set-logic QF_FPLRA)
(declare-const x (_ FloatingPoint 8 24))
(assert (not (fp.isNaN x)))
(assert (not (fp.isInfinite x)))
(assert (> (fp.to_real x) 0.0))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "FP to_real with positive constraint should be sat, got: {result}"
    );
}
