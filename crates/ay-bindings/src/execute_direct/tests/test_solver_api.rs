// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Solver API tests: check-sat-assuming, set-option, get-value.

use super::*;

// #5456: CheckSatAssuming now executes directly via the solver API.
// The implicit check_sat workaround (#2031) is handled internally.
#[test]
fn test_check_sat_assuming_direct_sat() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // x > 0
    program.assert(x.clone().int_gt(Expr::int(0)));

    // check-sat-assuming with x < 10 → SAT (x can be 1..9)
    let assumption = x.clone().int_lt(Expr::int(10));
    program.add_constraint(Constraint::CheckSatAssuming(vec![assumption]));

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { model, .. } => {
            // Verify model satisfies constraints: x > 0 AND x < 10
            let x_val: i64 = model
                .get("x")
                .unwrap_or_else(|| panic!("Model missing 'x': {:?}", model))
                .parse()
                .unwrap_or_else(|e| panic!("Cannot parse x value: {e}, model: {model:?}"));
            assert!(
                x_val > 0 && x_val < 10,
                "Model x={x_val} violates constraints (x > 0 AND x < 10)"
            );
        }
        other => panic!("Expected Counterexample (SAT), got: {:?}", other),
    }
}

// #5456: CheckSatAssuming with contradictory assumptions returns Verified (UNSAT).
#[test]
fn test_check_sat_assuming_direct_unsat() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // x > 5
    program.assert(x.clone().int_gt(Expr::int(5)));

    // check-sat-assuming with x < 3 → UNSAT (x > 5 AND x < 3 impossible)
    let assumption = x.clone().int_lt(Expr::int(3));
    program.add_constraint(Constraint::CheckSatAssuming(vec![assumption]));

    let result = execute(&program).unwrap();
    assert!(
        matches!(result, ExecuteResult::Verified),
        "Expected Verified (UNSAT) for contradictory assumptions, got: {:?}",
        result
    );
}

// #5456: CheckSatAssuming with BV logic (primary model-checker-consumer use case).
#[test]
fn test_check_sat_assuming_direct_bv_sat() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let x = program.declare_const("x", Sort::bitvec(8));

    // x != 0
    let zero = Expr::bitvec_const(0i64, 8);
    program.assert(Expr::distinct(vec![x.clone(), zero]));

    // check-sat-assuming with bvuge(x, 0x42) → SAT (x can be 0x42..0xFF)
    let bound = Expr::bitvec_const(0x42i64, 8);
    let assumption = x.clone().bvuge(bound);
    program.add_constraint(Constraint::CheckSatAssuming(vec![assumption]));

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { model, .. } => {
            // Verify model satisfies constraints: x != 0 AND bvuge(x, 0x42)
            // BV model values may be in hex (#x42) or decimal format.
            let x_str = model
                .get("x")
                .unwrap_or_else(|| panic!("Model missing 'x': {:?}", model));
            let x_val: u64 = if let Some(hex) = x_str.strip_prefix("#x") {
                u64::from_str_radix(hex, 16)
                    .unwrap_or_else(|e| panic!("Cannot parse BV hex '{x_str}': {e}"))
            } else if let Some(bin) = x_str.strip_prefix("#b") {
                u64::from_str_radix(bin, 2)
                    .unwrap_or_else(|e| panic!("Cannot parse BV bin '{x_str}': {e}"))
            } else {
                x_str
                    .parse()
                    .unwrap_or_else(|e| panic!("Cannot parse BV value '{x_str}': {e}"))
            };
            assert!(x_val != 0, "Model x=0 violates x != 0");
            assert!(
                x_val >= 0x42,
                "Model x=0x{x_val:02X} violates bvuge(x, 0x42)"
            );
            assert!(x_val <= 0xFF, "Model x=0x{x_val:02X} exceeds 8-bit range");
        }
        other => panic!(
            "Expected Counterexample (SAT) for BV check-sat-assuming, got: {:?}",
            other
        ),
    }
}

// #1977: CheckSatAssuming works correctly via direct API when preceded by check_sat
// This test verifies the ay-dpll API works correctly with the proper calling pattern.
#[test]
fn test_api_check_sat_assuming_works_after_check_sat() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort as ApiSort};

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver creation");
    let x = solver.declare_const("x", ApiSort::Int);

    // x > 5
    let five = solver.int_const(5);
    let x_gt_5 = solver.try_gt(x, five).expect("gt");
    solver.try_assert_term(x_gt_5).expect("assert");

    // First verify it's SAT without assumptions
    assert_eq!(solver.check_sat(), SolveResult::Sat, "x > 5 should be SAT");

    // Now check with assumption x < 3 - should be UNSAT
    let three = solver.int_const(3);
    let x_lt_3 = solver.try_lt(x, three).expect("lt");
    let result = solver.check_sat_assuming(&[x_lt_3]);
    assert_eq!(
        result,
        SolveResult::unsat(),
        "x > 5 AND x < 3 should be UNSAT"
    );
}

// #5504: Verify check_sat_assuming works as the FIRST solve call (no prior check_sat).
// If this passes, the redundant check_sat workaround in execute() is unnecessary.
#[test]
fn test_api_check_sat_assuming_first_call_no_prior_check_sat_5504() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort as ApiSort};

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver creation");
    let x = solver.declare_const("x", ApiSort::Int);

    // x > 5
    let five = solver.int_const(5);
    let x_gt_5 = solver.try_gt(x, five).expect("gt");
    solver.try_assert_term(x_gt_5).expect("assert");

    // NO prior check_sat() call — go straight to check_sat_assuming
    let three = solver.int_const(3);
    let x_lt_3 = solver.try_lt(x, three).expect("lt");
    let result = solver.check_sat_assuming(&[x_lt_3]);
    assert_eq!(
        result,
        SolveResult::unsat(),
        "x > 5 AND x < 3 should be UNSAT even without prior check_sat"
    );
}

// #8613: define-fun commands execute directly via the solver API and expand inline.
#[test]
fn test_define_fun_direct_execution_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    let n = Expr::var("n", Sort::int());
    program.define_fun(
        "inc",
        vec![("n".to_string(), Sort::int())],
        n.int_add(Expr::int(1)),
    );
    let inc_x = Expr::func_app_with_sort("inc", vec![x], Sort::int());
    program.assert(inc_x.eq(Expr::int(5)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { model, .. } => {
            let x_val: i64 = model
                .get("x")
                .unwrap_or_else(|| panic!("Model missing 'x': {:?}", model))
                .parse()
                .unwrap_or_else(|e| panic!("Cannot parse x value: {e}, model: {model:?}"));
            assert_eq!(x_val, 4);
        }
        other => panic!("Expected Counterexample (SAT), got: {:?}", other),
    }
}

// #5504: check_sat_assuming as first call returns SAT with valid model.
#[test]
fn test_api_check_sat_assuming_first_call_sat_5504() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort as ApiSort};

    let mut solver = Solver::try_new(Logic::QfLia).expect("solver creation");
    let x = solver.declare_const("x", ApiSort::Int);

    // x > 0
    let zero = solver.int_const(0);
    let x_gt_0 = solver.try_gt(x, zero).expect("gt");
    solver.try_assert_term(x_gt_0).expect("assert");

    // NO prior check_sat() — go straight to check_sat_assuming
    let hundred = solver.int_const(100);
    let x_lt_100 = solver.try_lt(x, hundred).expect("lt");
    let result = solver.check_sat_assuming(&[x_lt_100]);
    assert_eq!(
        result,
        SolveResult::Sat,
        "x > 0 AND x < 100 should be SAT without prior check_sat"
    );
}

// #5504: check_sat_assuming as first call with BV logic (model-checker-consumer primary use case).
#[test]
fn test_api_check_sat_assuming_first_call_bv_5504() {
    use ay_dpll::api::{Logic, SolveResult, Solver, Sort as ApiSort};

    let mut solver = Solver::try_new(Logic::QfBv).expect("solver creation");
    let x = solver.declare_const("x", ApiSort::BitVec(ay_dpll::api::BitVecSort { width: 32 }));

    // x != 0
    let zero = solver.try_bv_const(0i64, 32).expect("bv_const");
    let x_ne_0 = solver.try_distinct(&[x, zero]).expect("distinct");
    solver.try_assert_term(x_ne_0).expect("assert");

    // NO prior check_sat() — go straight to check_sat_assuming with x > 5
    let five = solver.try_bv_const(5i64, 32).expect("bv_const");
    let x_ugt_5 = solver.try_bvugt(x, five).expect("bvugt");
    let result = solver.check_sat_assuming(&[x_ugt_5]);
    assert_eq!(
        result,
        SolveResult::Sat,
        "BV32 x != 0 AND bvugt(x, 5) should be SAT without prior check_sat"
    );
}

// #5505: SetOption is forwarded to the solver via the direct API.
#[test]
fn test_set_option_forwarded_to_solver_5505() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    // Set produce-proofs before any declarations
    program.add_constraint(Constraint::set_option(":produce-proofs", "true"));
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());
    // x AND NOT x → UNSAT
    program.assert(x.clone());
    program.assert(x.not());
    program.check_sat();

    let result = execute(&program).unwrap();
    // Correctness: the option shouldn't break solving
    assert!(
        matches!(result, ExecuteResult::Verified),
        "Expected UNSAT with produce-proofs enabled, got: {:?}",
        result
    );
}

// #5505: SetOption with produce-models works through direct API.
#[test]
fn test_set_option_produce_models_5505() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-models", "true"));
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.assert(x.clone().int_lt(Expr::int(10)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { model, .. } => {
            assert!(model.contains_key("x"), "Model should contain x");
        }
        other => panic!("Expected Counterexample (SAT), got: {:?}", other),
    }
}

#[test]
fn test_execute_direct_empty_model_remains_counterexample_6311() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    program.assert(Expr::true_());
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { model, values } => {
            assert!(model.is_empty(), "expected empty model, got {model:?}");
            assert!(values.is_empty(), "expected empty values, got {values:?}");
        }
        other => panic!("Expected Counterexample with empty model, got: {:?}", other),
    }
}

#[test]
fn test_execute_direct_model_extraction_failure_returns_unknown_6311() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-models", "false"));
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Unknown(reason) => {
            assert!(
                reason.contains("model extraction failed"),
                "expected model extraction context, got: {reason}"
            );
            assert!(
                reason.contains("model generation is not enabled"),
                "expected executor error detail, got: {reason}"
            );
        }
        other => panic!(
            "Expected Unknown for model extraction failure, got: {:?}",
            other
        ),
    }
}

#[test]
fn test_execute_direct_get_value_extraction_failure_returns_unknown_6311() {
    use crate::constraint::Constraint;

    // When models are disabled, model extraction fails before get-value
    // extraction is attempted. The Unknown reason reflects the model failure.
    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-models", "false"));
    program.set_logic("QF_UF");
    program.assert(Expr::true_());
    program.check_sat();
    program.add_constraint(Constraint::GetValue(vec![Expr::bool_const(true)]));

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Unknown(reason) => {
            // Model extraction fails before get-value is attempted
            assert!(
                reason.contains("model extraction failed")
                    || reason.contains("get-value extraction failed"),
                "expected extraction failure context, got: {reason}"
            );
            assert!(
                reason.contains("model generation is not enabled"),
                "expected executor error detail, got: {reason}"
            );
        }
        other => panic!("Expected Unknown for extraction failure, got: {:?}", other),
    }
}

#[test]
fn test_execute_direct_empty_model_with_models_disabled_returns_unknown_6311() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-models", "false"));
    program.set_logic("QF_UF");
    program.assert(Expr::true_());
    program.check_sat();

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Unknown(reason) => {
            assert!(
                reason.contains("model extraction failed"),
                "expected model extraction context, got: {reason}"
            );
            assert!(
                reason.contains("model generation is not enabled"),
                "expected executor error detail, got: {reason}"
            );
        }
        other => panic!(
            "Expected Unknown for empty-model extraction failure, got: {:?}",
            other
        ),
    }
}

// #1977: GetValue is now supported via direct execution.
// Terms are collected during constraint processing and evaluated after check-sat.
#[test]
fn test_get_value_direct_execution() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // x > 0 AND x < 100 - a satisfiable constraint
    // Using inequality to avoid model validation issues with equality
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.assert(x.clone().int_lt(Expr::int(100)));

    program.check_sat();
    program.add_constraint(Constraint::GetValue(vec![x.clone()]));

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { model: _, values } => {
            // Check that we got a value for x
            assert!(!values.is_empty(), "Expected get-value to return values");
            // The expression format may vary, but we should have exactly one value
            assert_eq!(values.len(), 1, "Expected exactly one get-value result");
            // Verify the value is a valid integer in range [1, 99]
            let val = values.values().next().unwrap();
            let parsed: i64 = val
                .parse()
                .unwrap_or_else(|_| panic!("Expected integer value for x, got: '{}'", val));
            assert!(
                parsed >= 1 && parsed <= 99,
                "Expected x in [1, 99], got: {}",
                parsed
            );
        }
        other => panic!(
            "Expected Counterexample for trivially satisfiable QF_LIA, got: {:?}",
            other
        ),
    }
}

// #1977: Test get-value with multiple terms in a single call
#[test]
fn test_get_value_multiple_terms() {
    use crate::constraint::Constraint;

    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());
    let y = program.declare_const("y", Sort::int());

    // Two independent constraints
    program.assert(x.clone().int_gt(Expr::int(5)));
    program.assert(x.clone().int_lt(Expr::int(15)));
    program.assert(y.clone().int_gt(Expr::int(15)));
    program.assert(y.clone().int_lt(Expr::int(25)));

    program.check_sat();
    program.add_constraint(Constraint::GetValue(vec![x.clone(), y.clone()]));

    let result = execute(&program).unwrap();
    match result {
        ExecuteResult::Counterexample { model: _, values } => {
            assert_eq!(
                values.len(),
                2,
                "Expected two get-value results, got {}",
                values.len()
            );
            // Verify both values are valid integers in their expected ranges
            for (name, val) in &values {
                let parsed: i64 = val.parse().unwrap_or_else(|_| {
                    panic!("Expected integer value for {}, got: '{}'", name, val)
                });
                // x in [6, 14], y in [16, 24]
                assert!(
                    (parsed >= 6 && parsed <= 14) || (parsed >= 16 && parsed <= 24),
                    "Value {} = {} not in expected range",
                    name,
                    parsed
                );
            }
        }
        other => panic!(
            "Expected Counterexample for trivially satisfiable QF_LIA, got: {:?}",
            other
        ),
    }
}
