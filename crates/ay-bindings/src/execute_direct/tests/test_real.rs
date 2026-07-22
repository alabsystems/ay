// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Real arithmetic tests (#993).

use super::*;

#[test]
fn test_real_arithmetic_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    let y = program.declare_const("y", Sort::real());

    // x > y AND y > x is UNSAT
    program.assert(x.clone().real_gt(y.clone()));
    program.assert(y.real_gt(x));
    program.check_sat();

    let result = execute(&program).unwrap();
    // Must be Verified (UNSAT). The LRA strict inequality bug (#1654/#5405) is fixed.
    match result {
        ExecuteResult::Verified => {
            // Correct result - contradiction detected as UNSAT
        }
        other => {
            panic!(
                "Expected Verified (UNSAT) for contradictory QF_LRA formula, got {:?}",
                other
            );
        }
    }
}

#[test]
fn test_real_arithmetic_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    let y = program.declare_const("y", Sort::real());

    // x > y AND x + y = x (implies y = 0 and x > 0) is SAT
    program.assert(x.clone().real_gt(y.clone()));
    let sum = x.clone().real_add(y.clone());
    program.assert(sum.eq(x));
    program.check_sat();

    let result = execute(&program).unwrap();
    // Must be Counterexample (SAT). The LRA strict inequality bug (#1654/#5405) is fixed.
    match result {
        ExecuteResult::Counterexample { model, .. } => {
            // Validate that the model makes sense (y should be 0)
            if let Some(y_val) = model.get("y") {
                assert!(
                    y_val == "0" || y_val == "0.0",
                    "Expected y=0 or y=0.0 in model, got y={}",
                    y_val
                );
            }
        }
        other => {
            panic!(
                "Expected Counterexample (SAT) for satisfiable QF_LRA formula, got {:?}",
                other
            );
        }
    }
}

// #1044: Real comparison contradiction (x > y AND y > x) should NOT panic
// and must return UNSAT. Regression test for ay#1654 and ay#5405.
#[test]
fn test_real_comparison_contradiction_no_sat_issue_1044() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");
    let x = program.declare_const("x", Sort::real());
    let y = program.declare_const("y", Sort::real());

    // x > y AND y > x is a contradiction (logically UNSAT)
    program.assert(x.clone().real_gt(y.clone()));
    program.assert(y.real_gt(x));
    program.check_sat();

    let result = execute(&program).unwrap();

    // Must be Verified (UNSAT). The LRA strict inequality bug (#1654/#5405) is fixed.
    match result {
        ExecuteResult::Verified => {
            // Correct result - contradiction detected as UNSAT
        }
        other => {
            panic!(
                "Expected Verified (UNSAT) for contradictory QF_LRA formula, got {:?}",
                other
            );
        }
    }
}
