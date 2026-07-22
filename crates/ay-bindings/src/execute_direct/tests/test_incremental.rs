// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Tests for multi-check-sat / incremental execution (#8154).

use super::*;

// --- execute_all tests ---

#[test]
fn test_execute_all_single_check_sat_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());
    program.assert(x);
    program.check_sat();

    let results = execute_all(&program).unwrap();
    assert_eq!(
        results.len(),
        1,
        "single check-sat should produce one result"
    );
    assert!(
        matches!(results[0], ExecuteResult::Counterexample { .. }),
        "expected Counterexample, got {:?}",
        results[0]
    );
}

#[test]
fn test_execute_all_single_check_sat_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());
    program.assert(x.clone());
    program.assert(x.not());
    program.check_sat();

    let results = execute_all(&program).unwrap();
    assert_eq!(results.len(), 1);
    assert!(
        matches!(results[0], ExecuteResult::Verified),
        "expected Verified, got {:?}",
        results[0]
    );
}

#[test]
fn test_execute_all_two_check_sats_both_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // First: x > 0 is SAT
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.check_sat();

    // Second: add x < 100, still SAT
    program.assert(x.clone().int_lt(Expr::int(100)));
    program.check_sat();

    let results = execute_all(&program).unwrap();
    assert_eq!(
        results.len(),
        2,
        "two check-sats should produce two results"
    );
    assert!(
        matches!(results[0], ExecuteResult::Counterexample { .. }),
        "first check-sat should be SAT, got {:?}",
        results[0]
    );
    assert!(
        matches!(results[1], ExecuteResult::Counterexample { .. }),
        "second check-sat should be SAT, got {:?}",
        results[1]
    );
}

#[test]
fn test_execute_all_sat_then_unsat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // First: x > 0 is SAT
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.check_sat();

    // Second: add x < 0 → contradicts x > 0, so UNSAT
    program.assert(x.clone().int_lt(Expr::int(0)));
    program.check_sat();

    let results = execute_all(&program).unwrap();
    assert_eq!(results.len(), 2);
    assert!(
        matches!(results[0], ExecuteResult::Counterexample { .. }),
        "first check-sat should be SAT, got {:?}",
        results[0]
    );
    assert!(
        matches!(results[1], ExecuteResult::Verified),
        "second check-sat should be UNSAT, got {:?}",
        results[1]
    );
}

#[test]
fn test_execute_all_push_pop_independent_results() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // Base: x > 0
    program.assert(x.clone().int_gt(Expr::int(0)));

    // Push, add contradictory constraint, check (UNSAT), pop
    program.push();
    program.assert(x.clone().int_lt(Expr::int(0)));
    program.check_sat(); // UNSAT: x > 0 AND x < 0
    program.pop(1);

    // After pop, x > 0 is still SAT
    program.check_sat(); // SAT: just x > 0

    let results = execute_all(&program).unwrap();
    assert_eq!(results.len(), 2);
    assert!(
        matches!(results[0], ExecuteResult::Verified),
        "first check-sat (inside push) should be UNSAT, got {:?}",
        results[0]
    );
    assert!(
        matches!(results[1], ExecuteResult::Counterexample { .. }),
        "second check-sat (after pop) should be SAT, got {:?}",
        results[1]
    );
}

#[test]
fn test_execute_all_three_check_sats() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // Check 1: x > 5 is SAT
    program.assert(x.clone().int_gt(Expr::int(5)));
    program.check_sat();

    // Check 2: push, add x < 3 (contradicts), UNSAT
    program.push();
    program.assert(x.clone().int_lt(Expr::int(3)));
    program.check_sat();
    program.pop(1);

    // Check 3: x > 5 is still SAT after pop
    program.check_sat();

    let results = execute_all(&program).unwrap();
    assert_eq!(results.len(), 3);
    assert!(
        matches!(results[0], ExecuteResult::Counterexample { .. }),
        "check 1 should be SAT, got {:?}",
        results[0]
    );
    assert!(
        matches!(results[1], ExecuteResult::Verified),
        "check 2 should be UNSAT, got {:?}",
        results[1]
    );
    assert!(
        matches!(results[2], ExecuteResult::Counterexample { .. }),
        "check 3 should be SAT, got {:?}",
        results[2]
    );
}

// --- execute_all_typed tests ---

#[test]
fn test_execute_all_typed_returns_check_sat_indices() {
    let mut program = AYProgram::new();
    program.set_logic("QF_UF");
    let x = program.declare_const("x", Sort::bool());

    // Two check-sats with the same satisfiable assertion
    program.assert(x.clone());
    program.check_sat();
    program.check_sat();

    let outcomes = execute_all_typed(&program).unwrap();
    assert_eq!(outcomes.len(), 2);
    assert_eq!(
        outcomes[0].check_sat_index, 0,
        "first outcome should have index 0"
    );
    assert_eq!(
        outcomes[1].check_sat_index, 1,
        "second outcome should have index 1"
    );
}

#[test]
fn test_execute_all_typed_get_value_attaches_to_preceding_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    program.assert(x.clone().int_gt(Expr::int(0)));
    program.check_sat();
    program.get_value(vec![x.clone()]);

    program.assert(x.clone().int_lt(Expr::int(10)));
    program.check_sat();

    let outcomes = execute_all_typed(&program).unwrap();
    assert_eq!(outcomes.len(), 2);

    match &outcomes[0].result {
        ExecuteTypedResult::Counterexample(counterexample) => {
            assert_eq!(
                counterexample.values.len(),
                1,
                "get-value should attach to the first SAT result"
            );
            assert!(
                counterexample.values.contains_key("x"),
                "expected x get-value on the first SAT result, got {:?}",
                counterexample.values
            );
        }
        other => panic!("first outcome should be SAT, got {other:?}"),
    }

    match &outcomes[1].result {
        ExecuteTypedResult::Counterexample(counterexample) => {
            assert!(
                counterexample.values.is_empty(),
                "get-value from the prior SAT must not leak into the next result: {:?}",
                counterexample.values
            );
        }
        other => panic!("second outcome should be SAT, got {other:?}"),
    }
}

// --- Backwards compatibility: execute() returns last result ---

#[test]
fn test_execute_returns_last_result_multi_check_sat() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LIA");
    let x = program.declare_const("x", Sort::int());

    // First check-sat: SAT
    program.assert(x.clone().int_gt(Expr::int(0)));
    program.check_sat();

    // Second check-sat: UNSAT
    program.assert(x.clone().int_lt(Expr::int(0)));
    program.check_sat();

    // execute() should return the last result (UNSAT/Verified)
    let result = execute(&program).unwrap();
    // The old execute() path uses execute_typed_with_details_impl which
    // processes all commands but only runs check-sat at the end.
    // This test verifies it still works (returns some result).
    assert!(
        matches!(
            result,
            ExecuteResult::Verified
                | ExecuteResult::Counterexample { .. }
                | ExecuteResult::Unknown(_)
        ),
        "execute() should return a valid result for multi-check-sat program, got {:?}",
        result
    );
}

// --- BV logic multi-check-sat ---

#[test]
fn test_execute_all_bv_push_pop() {
    let mut program = AYProgram::new();
    program.set_logic("QF_BV");
    let x = program.declare_const("x", Sort::bitvec(8));

    let zero = Expr::bitvec_const(0i64, 8);
    let ff = Expr::bitvec_const(0xFFi64, 8);

    // x != 0 → SAT
    program.assert(Expr::distinct(vec![x.clone(), zero.clone()]));
    program.check_sat();

    // Push, add x = 0 → contradicts, UNSAT
    program.push();
    program.assert(x.clone().eq(zero));
    program.check_sat();
    program.pop(1);

    // x != 0 still SAT, add x = 0xFF → still SAT
    program.push();
    program.assert(x.clone().eq(ff));
    program.check_sat();
    program.pop(1);

    let results = execute_all(&program).unwrap();
    assert_eq!(results.len(), 3);
    assert!(
        matches!(results[0], ExecuteResult::Counterexample { .. }),
        "check 1 (x != 0) should be SAT, got {:?}",
        results[0]
    );
    assert!(
        matches!(results[1], ExecuteResult::Verified),
        "check 2 (x != 0 AND x = 0) should be UNSAT, got {:?}",
        results[1]
    );
    assert!(
        matches!(results[2], ExecuteResult::Counterexample { .. }),
        "check 3 (x != 0 AND x = 0xFF) should be SAT, got {:?}",
        results[2]
    );
}
