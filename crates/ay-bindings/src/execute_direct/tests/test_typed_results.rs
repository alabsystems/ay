// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Typed execute_direct result tests for #6311.

use super::*;
use num_bigint::BigInt;

#[test]
fn test_execute_typed_with_details_fallback_metadata_6708() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.soft_assert(x.int_gt(Expr::int(0)), 1);
    program.check_sat();

    let details = execute_typed_with_details(&program).unwrap();
    assert!(matches!(
        details.result,
        ExecuteTypedResult::NeedsFallback(_)
    ));
    assert!(details.solve_details.is_none());
    assert!(details.assumption_solve_details.is_none());

    let fallback = details.fallback.expect("expected fallback metadata");
    assert_eq!(fallback.kind, ExecuteFallbackKind::SoftAssertions);
    assert!(
        fallback.message.contains("soft assertions"),
        "unexpected fallback message: {}",
        fallback.message
    );
}

#[test]
fn test_execute_typed_int_counterexample_6311() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.assert(x.clone().int_lt(Expr::int(10)));
    program.check_sat();

    let result = execute_typed(&program).unwrap();
    match result {
        ExecuteTypedResult::Counterexample(counterexample) => match counterexample.model.get("x") {
            Some(ModelValue::Int(value)) => {
                assert!(
                    value >= &BigInt::from(1) && value < &BigInt::from(10),
                    "expected x in [1, 9], got {value}"
                );
            }
            other => panic!("expected typed int model value, got {other:?}"),
        },
        other => panic!("Expected typed Counterexample (SAT), got: {:?}", other),
    }
}

#[test]
fn test_execute_typed_with_details_model_failure_retains_sat_details_6708() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-models", "false"));
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.int_gt(Expr::int(0)));
    program.check_sat();

    let details = execute_typed_with_details(&program).unwrap();
    match details.result {
        ExecuteTypedResult::Unknown(reason) => {
            assert!(
                reason.contains("model extraction failed"),
                "expected model extraction unknown, got: {reason}"
            );
        }
        other => panic!("expected Unknown after model extraction failure, got {other:?}"),
    }

    let degradation = details.degradation.expect("expected degradation metadata");
    assert_eq!(
        degradation.kind,
        ExecuteDegradationKind::ModelExtractionFailure
    );
    assert!(
        degradation.message.contains("model extraction failed"),
        "unexpected degradation message: {}",
        degradation.message
    );

    let solve_details = details
        .solve_details
        .expect("SAT solve details should be retained");
    assert_eq!(*solve_details.result.result(), SolveResult::Sat);
    assert!(details.assumption_solve_details.is_none());
}

#[test]
fn test_execute_typed_bv_counterexample_6311() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let x = program.declare_const("x", Sort::bitvec(8));
    let zero = Expr::bitvec_const(0i64, 8);
    let lower_bound = Expr::bitvec_const(0x42i64, 8);
    program.assert(Expr::distinct(vec![x.clone(), zero]));
    program.assert(x.clone().bvuge(lower_bound));
    program.check_sat();

    let result = execute_typed(&program).unwrap();
    match result {
        ExecuteTypedResult::Counterexample(counterexample) => match counterexample.model.get("x") {
            Some(ModelValue::BitVec { value, width }) => {
                assert_eq!(*width, 8, "expected 8-bit model, got width {width}");
                assert!(
                    value >= &BigInt::from(0x42_u32) && value <= &BigInt::from(0xFF_u32),
                    "expected x in [0x42, 0xFF], got {value}"
                );
            }
            other => panic!("expected typed bitvector model value, got {other:?}"),
        },
        other => panic!("Expected typed Counterexample (SAT), got: {:?}", other),
    }
}

#[test]
fn test_execute_typed_get_value_returns_model_values_6311() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.assert(x.clone().int_lt(Expr::int(100)));
    program.check_sat();
    program.add_constraint(Constraint::GetValue(vec![x]));

    let result = execute_typed(&program).unwrap();
    match result {
        ExecuteTypedResult::Counterexample(counterexample) => {
            assert_eq!(
                counterexample.values.len(),
                1,
                "expected exactly one get-value result"
            );
            match counterexample.values.values().next() {
                Some(ModelValue::Int(value)) => {
                    assert!(
                        value >= &BigInt::from(1) && value < &BigInt::from(100),
                        "expected get-value result in [1, 99], got {value}"
                    );
                }
                other => panic!("expected typed int get-value result, got {other:?}"),
            }
        }
        other => panic!("Expected typed Counterexample (SAT), got: {:?}", other),
    }
}
