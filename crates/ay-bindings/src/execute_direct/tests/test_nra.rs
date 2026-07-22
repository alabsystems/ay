// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! NRA and UF+NRA tests for ay-direct execution (#6769, #6752, #6753).

use super::*;

/// QF_NRA logic string parsing: verify set_logic("QF_NRA") dispatches to the
/// NRA solver and produces a result (SAT/UNSAT/Unknown) rather than erroring.
/// Uses a simple bounded linear formula under the NRA logic label to exercise
/// the logic-string parse path without depending on NRA solver completeness.
#[test]
fn test_qf_nra_logic_dispatch() {
    let mut program = AYProgram::new();
    program.set_logic("QF_NRA");
    let x = program.declare_const("x", Sort::real());

    // x > 0 AND x < 1 is SAT (linear, but under QF_NRA logic)
    program.assert(x.clone().real_gt(Expr::real(0)));
    program.assert(x.real_lt(Expr::real(1)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { .. } => {
            // Correct — SAT with a model for x in (0, 1)
        }
        other => panic!(
            "Expected Counterexample (SAT) for 0 < x < 1 under QF_NRA, got {:?}",
            other
        ),
    }
}

/// QF_NRA UNSAT: contradictory linear bounds under QF_NRA logic string.
/// Exercises that QF_NRA dispatches correctly and can prove unsatisfiability.
#[test]
fn test_qf_nra_contradictory_bounds_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_NRA");
    let x = program.declare_const("x", Sort::real());

    // x > 5 AND x < 3 is UNSAT
    program.assert(x.clone().real_gt(Expr::real(5)));
    program.assert(x.real_lt(Expr::real(3)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Verified => {
            // Correct — UNSAT, no real x satisfies x > 5 AND x < 3
        }
        other => panic!(
            "Expected Verified (UNSAT) for x > 5 AND x < 3 under QF_NRA, got {:?}",
            other
        ),
    }
}

/// QF_NRA nonlinear contradiction: symbolic multiplication should stay on the
/// real-only nonlinear path instead of degrading into mixed NIRA handling.
#[test]
fn test_qf_nra_symbolic_square_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_NRA");
    let x = program.declare_const("x", Sort::real());
    let x_sq = Expr::real_mul(x.clone(), x);

    program.assert(x_sq.real_lt(Expr::real(0)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Verified => {
            // Correct — x*x is always non-negative over the reals.
        }
        other => panic!(
            "Expected Verified (UNSAT) for x*x < 0 under QF_NRA, got {:?}",
            other
        ),
    }
}

/// optimization_consumer #4399 regression: a convex combination of non-negative real losses
/// must not surface as a trusted SAT counterexample when the candidate model
/// makes the violation false.
#[test]
fn test_qf_nra_label_smoothing_nonnegative_no_false_counterexample() {
    let mut program = AYProgram::new();
    program.set_logic("QF_NRA");
    let eps = program.declare_const("eps", Sort::real());
    let ce_onehot = program.declare_const("ce_onehot", Sort::real());
    let ce_uniform = program.declare_const("ce_uniform", Sort::real());
    let zero = Expr::real(0);
    let one = Expr::real(1);

    program.assert(eps.clone().real_gt(zero.clone()));
    program.assert(eps.clone().real_lt(one.clone()));
    program.assert(ce_onehot.clone().real_ge(zero.clone()));
    program.assert(ce_uniform.clone().real_ge(zero.clone()));

    let smoothed = one
        .real_sub(eps.clone())
        .real_mul(ce_onehot)
        .real_add(eps.real_mul(ce_uniform));
    program.assert(smoothed.real_lt(zero));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Verified | ExecuteResult::Unknown(_) => {}
        other => panic!("expected Verified or Unknown, not false counterexample: {other:?}"),
    }
}

/// optimization_consumer #4399 regression: `s * (1 - s) <= 0` under `0 < s < 1` is UNSAT.
/// The direct executor may be incomplete, but it must not return a model such
/// as `s = 1/2` as a trusted counterexample.
#[test]
fn test_qf_nra_softmax_jacobian_diag_no_false_counterexample() {
    let mut program = AYProgram::new();
    program.set_logic("QF_NRA");
    let s = program.declare_const("s_i", Sort::real());
    let zero = Expr::real(0);
    let one = Expr::real(1);

    program.assert(s.clone().real_gt(zero.clone()));
    program.assert(s.clone().real_lt(one.clone()));

    let jac_diag = s.clone().real_mul(one.real_sub(s));
    program.assert(jac_diag.real_le(zero));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Verified | ExecuteResult::Unknown(_) => {}
        other => panic!("expected Verified or Unknown, not false counterexample: {other:?}"),
    }
}

/// QF_UFNRA with range axiom: optimization_consumer-representative smoke test (#6769).
///
/// Declares UF `sin : Real -> Real` with range axiom -1 <= sin(x) <= 1,
/// then queries sin(x) > 2 which should be UNSAT. The direct UFNRA path may
/// still fail closed while full nonlinear/UF proof production is incomplete,
/// but it must not emit a trusted counterexample. This exercises:
/// - QF_UFNRA logic string parsing (Packet C0)
/// - FuncApp dispatch in execute_direct
/// - UF+NRA combined solving
#[test]
fn test_qf_ufnra_with_range_axiom() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UFNRA");

    // Declare UF: sin : Real -> Real
    program.declare_fun("sin", vec![Sort::real()], Sort::real());

    let x = program.declare_const("x", Sort::real());
    let sin_x = Expr::func_app_with_sort("sin", vec![x], Sort::real());

    // Range axiom: -1 <= sin(x) <= 1
    program.assert(sin_x.clone().real_ge(Expr::real(-1)));
    program.assert(sin_x.clone().real_le(Expr::real(1)));

    // Query: sin(x) > 2 (should be UNSAT given range axiom)
    program.assert(sin_x.real_gt(Expr::real(2)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Verified => {
            // Correct — UNSAT, sin(x) cannot exceed 2 given range [-1, 1]
        }
        ExecuteResult::Unknown(reason) => {
            assert!(
                reason.contains("incomplete") || reason.contains("semantic conflict verification"),
                "unexpected UFNRA fail-closed reason: {reason}"
            );
        }
        other => panic!(
            "Expected Verified or fail-closed Unknown for sin(x) > 2 with range [-1,1], got {:?}",
            other
        ),
    }
}

/// QF_NRA symbolic division UNSAT: (/ 1 x) >= 1 with x > 1 is unsatisfiable.
///
/// For x > 1, 1/x < 1, so (/ 1 x) >= 1 contradicts. Z3 returns unsat. The
/// direct executor may still be incomplete for symbolic division, but it must
/// fail closed rather than returning a trusted counterexample (#6811).
#[test]
fn test_qf_nra_symbolic_division_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_NRA");
    let x = program.declare_const("x", Sort::real());

    // x > 1
    program.assert(x.clone().real_gt(Expr::real(1)));
    // (/ 1 x) >= 1
    let one_over_x = Expr::real(1).real_div(x);
    program.assert(one_over_x.real_ge(Expr::real(1)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Verified => {
            // Correct — UNSAT: for x > 1, 1/x < 1
        }
        ExecuteResult::Unknown(reason) => {
            assert!(
                reason.contains("incomplete"),
                "unexpected symbolic-division fail-closed reason: {reason}"
            );
        }
        other => panic!(
            "Expected Verified or fail-closed Unknown for x > 1 AND 1/x >= 1 under QF_NRA, got {:?}",
            other
        ),
    }
}
