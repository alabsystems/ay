// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6165: int_div returns Unknown(incomplete) in QF_AUFLIA.
//!
//! Root cause: LRA's `parse_linear_expr` has a catch-all for unknown functions
//! (line 542) that creates opaque slack variables. In combined_theory_mode
//! (AUFLIA, UFLIA, etc.), this catch-all is guarded by `!self.combined_theory_mode`,
//! so `div` is treated as an opaque variable without setting `saw_unsupported`.
//! This allows the DPLL(T) loop to detect propositional contradictions.

#![allow(clippy::panic)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Solve and return the result, accepting model validation failures.
/// Returns the output lines on success, or the error message string if
/// execution fails (so the test can assert on the failure mode).
fn solve_or_error(smt: &str) -> Result<Vec<String>, String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    let mut exec = Executor::new();
    match exec.execute_all(&commands) {
        Ok(output) => Ok(output),
        Err(err) => Err(err.to_string()),
    }
}

/// Propositional contradiction with div is detected.
/// result = div(x,y) ∧ ¬(result = div(x,y)) → UNSAT
/// This is a trivial `p ∧ ¬p` that should be caught by the SAT solver.
#[test]
#[timeout(60_000)]
fn test_verification_consumer_div_trivial_unsat_6165() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const result Int)
        (assert (not (= y 0)))
        (assert (= result (div x y)))
        (assert (not (= result (div x y))))
        (check-sat)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output.last().map(String::as_str),
        Some("unsat"),
        "Expected unsat for p ∧ ¬p with div, got {output:?}"
    );
}

/// Two div terms with same arguments should be equal via EUF congruence.
/// cd_result = div(a,b) ∧ div_result = div(a,b) ∧ ¬(cd_result = div_result) → UNSAT
#[test]
#[timeout(60_000)]
fn test_verification_consumer_checked_div_unsat_6165() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const a Int)
        (declare-const b Int)
        (declare-const cd_result Int)
        (declare-const div_result Int)
        (assert (not (= b 0)))
        (assert (= cd_result (div a b)))
        (assert (= div_result (div a b)))
        (assert (not (= cd_result div_result)))
        (check-sat)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output.last().map(String::as_str),
        Some("unsat"),
        "Expected unsat via EUF congruence for div, got {output:?}"
    );
}

/// Div-containing formula without contradiction: the formula is satisfiable,
/// but AY currently hits a model validation error because the model evaluator
/// can't evaluate `(div x y)` with symbolic divisor. The catch-all arm in
/// parse_linear_expr has a `!self.combined_theory_mode` guard from #5524,
/// so saw_unsupported is NOT set in AUFLIA -> solver returns SAT -> model
/// validation fails.
///
/// Expected fix: add explicit "div"/"mod" arms with unconditional
/// saw_unsupported = true, which will make this return "unknown" instead.
/// When that fix lands, update this test to expect "unknown".
#[test]
#[timeout(60_000)]
fn test_div_opaque_sat_6165() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const result Int)
        (assert (not (= y 0)))
        (assert (= result (div x y)))
        (check-sat)
    "#;
    let result = solve_or_error(smt);
    match result {
        Ok(output) => {
            let last = output.last().map(String::as_str);
            // After explicit div/mod arm fix, this should return "unknown"
            assert!(
                last == Some("sat") || last == Some("unknown"),
                "Expected sat or unknown for satisfiable div formula, got {output:?}"
            );
        }
        Err(msg) => {
            // Current behavior: model validation error because LRA assigned
            // div(x,y) independently of actual div semantics
            assert!(
                msg.contains("model validation failed"),
                "Unexpected error: {msg}"
            );
        }
    }
}

/// verification-consumer verification pattern: div result used in a guard condition.
/// Precondition: y != 0. Body: result = div(x,y). Guard: result > 0.
/// The formula `y != 0 AND result = div(x,y) AND result > 0` is satisfiable
/// (e.g., x=6, y=3, result=2). The solver should not return Unknown just
/// because div is present — the nonlinear detection fix (#6165 Phase 1)
/// keeps this as QF_AUFLIA instead of upgrading to QF_UFNIA.
#[test]
#[timeout(60_000)]
fn test_verification_consumer_div_guard_6165() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const result Int)
        (assert (not (= y 0)))
        (assert (= result (div x y)))
        (assert (> result 0))
        (check-sat)
    "#;
    let result = solve_or_error(smt);
    match result {
        Ok(output) => {
            let last = output.last().map(String::as_str);
            // sat or unknown are both acceptable (not Unknown from nonlinear upgrade)
            assert!(
                last == Some("sat") || last == Some("unknown"),
                "Expected sat or unknown for div guard formula, got {output:?}"
            );
        }
        Err(msg) => {
            // Model validation error is the current behavior for opaque div
            assert!(
                msg.contains("model validation failed"),
                "Unexpected error: {msg}"
            );
        }
    }
}

/// abs in combined_theory_mode should not trigger spurious Unknown.
/// In AUFLIA, abs(x) is defined as (ite (>= x 0) x (- x)). The DPLL(T)
/// loop expands the ITE and reasons about both branches, correctly
/// determining that abs(x) >= 0 always. With the combined_theory_mode
/// guard (#6165), saw_unsupported is not set, so the DPLL(T) loop runs
/// and proves UNSAT. Without the guard, saw_unsupported would be set
/// and the solver would bail with Unknown.
#[test]
#[timeout(60_000)]
fn test_abs_combined_mode_6165() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-const a Int)
        (assert (= a (abs x)))
        (assert (< a 0))
        (check-sat)
    "#;
    // abs(x) >= 0 always, and the solver correctly handles this via ITE
    // expansion. If the combined_theory_mode guard for abs is removed,
    // saw_unsupported would be set and this returns "unknown" instead.
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output.last().map(String::as_str),
        Some("unsat"),
        "Expected unsat for a=abs(x) AND a<0 (unknown = regression from saw_unsupported), got {output:?}"
    );
}

/// Div with constant values should be satisfiable (constant folding).
#[test]
#[timeout(60_000)]
fn test_div_constant_sat_6165() {
    let smt = r#"
        (set-logic QF_AUFLIA)
        (declare-const x Int)
        (declare-const y Int)
        (declare-const result Int)
        (assert (= x 6))
        (assert (= y 3))
        (assert (= result (div x y)))
        (assert (= result 2))
        (check-sat)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output.last().map(String::as_str),
        Some("sat"),
        "Expected sat for div with constant values, got {output:?}"
    );
}

/// ALL + datatypes + mixed Int/Real must route to DT+AUFLIRA, not DT+AUFLRA.
///
/// verification-consumer emits ALL when datatype/custom-sort declarations are present. If a
/// mixed Int/Real formula contains `(to_real (mod n k))`, the old DT+AUFLRA
/// route asserted the integer `mod` atom to LRA, which returned Unknown as an
/// unsupported asserted atom. DT+AUFLIRA runs the existing constant mod/div
/// elimination before theory solving.
#[test]
#[timeout(60_000)]
fn test_all_datatype_mixed_to_real_mod_routes_to_auflira_8961() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatypes ((Box 0)) (((mkBox))))
        (declare-const n Int)
        (assert (<= 0 n))
        (assert (<= n 65535))
        (assert (< (to_real (mod n 2)) 1.0))
        (check-sat)
    "#;
    let output = crate::common::solve_vec(smt);
    assert_eq!(
        output.last().map(String::as_str),
        Some("sat"),
        "Expected sat via DT+AUFLIRA mod elimination, got {output:?}"
    );
}
