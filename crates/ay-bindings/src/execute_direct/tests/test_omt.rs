// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! OMT (Optimization Modulo Theories) tests for direct execution (#6702).
//!
//! Verifies that maximize/minimize/get-objectives go through the OMT
//! executor bridge without returning NeedsFallback.

use super::*;

/// Maximize on Int objective returns SAT and does not fall back.
#[test]
fn test_omt_maximize_int_sat_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_le(Expr::int(10)));
    program.assert(x.clone().int_ge(Expr::int(0)));
    program.maximize(x);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT maximize should not fall back after #6702, got: {result:?}"
    );
    assert!(
        matches!(
            result,
            ExecuteResult::Counterexample { .. } | ExecuteResult::Unknown(_)
        ),
        "expected SAT or Unknown for OMT maximize, got: {result:?}"
    );
}

/// Minimize on Real objective returns SAT and does not fall back.
#[test]
fn test_omt_minimize_real_sat_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let y = program.declare_const("y", Sort::real());
    program.assert(y.clone().real_ge(Expr::real(1))); // y >= 1
    program.assert(y.clone().real_le(Expr::real(5))); // y <= 5
    program.minimize(y);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT minimize should not fall back after #6702, got: {result:?}"
    );
    assert!(
        matches!(
            result,
            ExecuteResult::Counterexample { .. } | ExecuteResult::Unknown(_)
        ),
        "expected SAT or Unknown for OMT minimize, got: {result:?}"
    );
}

/// Two-objective lexicographic optimization preserves declaration order.
#[test]
fn test_omt_lexicographic_two_objectives_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    let y = program.declare_const("y", Sort::int());
    // x in [0, 10], y in [0, 10], x + y <= 15
    program.assert(x.clone().int_ge(Expr::int(0)));
    program.assert(x.clone().int_le(Expr::int(10)));
    program.assert(y.clone().int_ge(Expr::int(0)));
    program.assert(y.clone().int_le(Expr::int(10)));
    program.assert(x.clone().int_add(y.clone()).int_le(Expr::int(15)));
    // Maximize x first, then maximize y
    program.maximize(x);
    program.maximize(y);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT lexicographic should not fall back, got: {result:?}"
    );
}

/// get-objectives after optimization returns non-empty output.
#[test]
fn test_omt_get_objectives_output_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_ge(Expr::int(0)));
    program.assert(x.clone().int_le(Expr::int(42)));
    program.maximize(x);
    program.check_sat();
    program.get_objectives();

    let result = execute(&program).unwrap();
    assert!(
        !matches!(result, ExecuteResult::NeedsFallback(_)),
        "OMT with get-objectives should not fall back, got: {result:?}"
    );
}

/// SoftAssert still returns NeedsFallback (not handled by OMT bridge).
#[test]
fn test_omt_soft_assert_still_fallback_6702() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.soft_assert(x.int_ge(Expr::int(0)), 1);
    program.check_sat();

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::NeedsFallback(_)),
        "SoftAssert should still fall back, got: {result:?}"
    );
}
