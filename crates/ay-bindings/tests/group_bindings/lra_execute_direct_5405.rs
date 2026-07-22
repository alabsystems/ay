// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Regression tests for ay#5405: QF_LRA through execute_direct.
//!
//! Root cause: `program.set_logic("QF_LRA")` stored the logic as metadata,
//! but `parse_logic()` only scanned `Constraint::SetLogic` commands. This
//! caused QF_LRA programs to silently default to QF_AUFBV, producing model
//! validation failures (Unknown("internal-error")).
//!
//! Fix: `parse_logic()` now checks `program.get_logic()` metadata first.
#![cfg(feature = "direct")]

use ay_bindings::execute_direct::{execute, ExecuteResult};
use ay_bindings::expr::Expr;
use ay_bindings::program::AYProgram;
use ay_bindings::sort::Sort;

/// SAT regression: x >= 1 AND x <= 5 must return Counterexample, not Unknown.
#[test]
fn test_qf_lra_sat_execute_direct_5405() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    program.assert(x.clone().real_ge(Expr::real(1)));
    program.assert(x.clone().real_le(Expr::real(5)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match &result {
        ExecuteResult::Counterexample { .. } => {}
        ExecuteResult::Verified => {
            panic!("x >= 1 AND x <= 5 should be SAT, not UNSAT");
        }
        ExecuteResult::Unknown(reason) => {
            panic!("BUG #5405: x >= 1 AND x <= 5 returned Unknown({})", reason);
        }
        ExecuteResult::NeedsFallback(reason) => {
            panic!("Unexpected fallback: {}", reason);
        }
        other => panic!("Unexpected ExecuteResult variant: {:?}", other),
    }
}

/// UNSAT regression: x in [-10,10] AND (x < -10 OR x > 10) must return Verified.
#[test]
fn test_qf_lra_unsat_execute_direct_5405() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    program.assert(x.clone().real_ge(Expr::real(-10)));
    program.assert(x.clone().real_le(Expr::real(10)));
    let disj = x
        .clone()
        .real_lt(Expr::real(-10))
        .or(x.clone().real_gt(Expr::real(10)));
    program.assert(disj);
    program.check_sat();

    let result = execute(&program).unwrap();
    match &result {
        ExecuteResult::Verified => {}
        ExecuteResult::Unknown(reason) => {
            panic!("BUG #5405: UNSAT formula returned Unknown({})", reason);
        }
        ExecuteResult::Counterexample { model, .. } => {
            panic!("BUG: UNSAT formula returned SAT with model: {:?}", model);
        }
        ExecuteResult::NeedsFallback(reason) => {
            panic!("Unexpected fallback: {}", reason);
        }
        other => panic!("Unexpected ExecuteResult variant: {:?}", other),
    }
}

/// Regression for #5605: real_mul with constant coefficients must not return Unknown.
///
/// optimization_consumer creates `(* x (/ 2000000 1000000))` which is linear (2x). The LRA solver
/// must recognize the constant divisor, fold to a rational, and treat the
/// multiplication as linear — not flag `saw_unsupported`.
#[test]
fn test_qf_lra_real_mul_constant_coefficient_5605() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());

    // x in [-5, 5]
    program.assert(x.clone().real_ge(Expr::real(-5)));
    program.assert(x.clone().real_le(Expr::real(5)));

    // output = 2x + 1
    let coeff = Expr::real(2000000).real_div(Expr::real(1000000)); // 2.0
    let offset = Expr::real(1000000).real_div(Expr::real(1000000)); // 1.0
    let output = x.clone().real_mul(coeff).real_add(offset);

    // Assert output outside [-9, 11] — should be UNSAT
    let lo = Expr::real(-9000000).real_div(Expr::real(1000000)); // -9.0
    let hi = Expr::real(11000000).real_div(Expr::real(1000000)); // 11.0
    let disj = output.clone().real_lt(lo).or(output.real_gt(hi));
    program.assert(disj);
    program.check_sat();

    let result = execute(&program).unwrap();
    match &result {
        ExecuteResult::Verified => {}
        ExecuteResult::Unknown(reason) => {
            panic!(
                "BUG #5605: real_mul with constant coefficient returned Unknown({})",
                reason
            );
        }
        ExecuteResult::Counterexample { model, .. } => {
            panic!("BUG: UNSAT formula returned SAT with model: {:?}", model);
        }
        ExecuteResult::NeedsFallback(reason) => {
            panic!("BUG: real_mul should not need fallback: {}", reason);
        }
        other => panic!("Unexpected ExecuteResult variant: {:?}", other),
    }
}

/// SAT variant of #5605: real_mul with constant coefficient, satisfiable.
///
/// output = 3x, x in [0, 10], assert output > 20 → SAT (x > 6.67)
#[test]
fn test_qf_lra_real_mul_constant_coefficient_sat_5605() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());

    program.assert(x.clone().real_ge(Expr::real(0)));
    program.assert(x.clone().real_le(Expr::real(10)));

    let output = x.real_mul(Expr::real(3));
    program.assert(output.real_gt(Expr::real(20)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match &result {
        ExecuteResult::Counterexample { .. } => {}
        ExecuteResult::Verified => {
            panic!("BUG: 3x > 20 with x in [0,10] should be SAT");
        }
        ExecuteResult::Unknown(reason) => {
            panic!(
                "BUG #5605: real_mul with integer constant returned Unknown({})",
                reason
            );
        }
        ExecuteResult::NeedsFallback(reason) => {
            panic!("BUG: real_mul should not need fallback: {}", reason);
        }
        other => panic!("Unexpected ExecuteResult variant: {:?}", other),
    }
}

/// UNSAT regression: strict inequality contradiction (x > y AND y > x).
#[test]
fn test_qf_lra_strict_contradiction_execute_direct_5405() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    let y = program.declare_const("y", Sort::real());
    program.assert(x.clone().real_gt(y.clone()));
    program.assert(y.real_gt(x));
    program.check_sat();

    let result = execute(&program).unwrap();
    match &result {
        ExecuteResult::Verified => {}
        ExecuteResult::Counterexample { model, .. } => {
            panic!(
                "BUG: Contradiction (x > y AND y > x) returned SAT with model: {:?}",
                model
            );
        }
        ExecuteResult::Unknown(_) | ExecuteResult::NeedsFallback(_) => {
            // Acceptable (ay may return Unknown for some valid reasons)
        }
        other => panic!("Unexpected ExecuteResult variant: {:?}", other),
    }
}
