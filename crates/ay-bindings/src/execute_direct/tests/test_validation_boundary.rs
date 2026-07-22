// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Consumer-boundary validation tests for `execute_direct` (#6852).

use super::*;

#[test]
fn test_validated_fp_sat_accepted_at_consumer_boundary_6852() {
    let mut program = AYProgram::new();
    program.set_logic("QF_FPLRA");

    let x = program.declare_const("x", Sort::fp(5, 11));
    let r = program.declare_const("r", Sort::real());
    program.assert(r.clone().eq(x.fp_to_real()));
    program.assert(r.real_gt(Expr::real(1)));
    program.check_sat();

    let details = execute_typed_with_details(&program).unwrap();
    match &details.result {
        ExecuteTypedResult::Counterexample(counterexample) => {
            assert!(
                counterexample.model.contains_key("r"),
                "expected validated FP/real model to contain r"
            );
        }
        other => {
            panic!("expected validated Counterexample at the consumer boundary, got {other:?}")
        }
    }
    assert!(
        details.degradation.is_none(),
        "validated SAT should not carry degradation metadata"
    );

    let solve_details = details
        .solve_details
        .as_ref()
        .expect("expected retained validated SAT solve details");
    assert_eq!(*solve_details.result.result(), SolveResult::Sat);
    assert!(
        solve_details.verification.sat_model_validated,
        "merged FP/real SAT model should be validated before crossing the consumer boundary"
    );
    assert!(details.assumption_solve_details.is_none());
}

#[test]
fn test_unknown_qf_logic_is_rejected_explicitly() {
    let mut program = AYProgram::new();
    program.set_logic("QF_FOO");

    let err = execute(&program).expect_err("unknown QF logic should not fall back");
    match err {
        ExecuteError::UnsupportedLogic(logic) => {
            assert_eq!(logic, "QF_FOO");
        }
        other => panic!("expected UnsupportedLogic for unknown QF family, got {other:?}"),
    }
}
