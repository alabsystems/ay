// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration tests for `execute_incremental()` (#8154 Phase 6c).

#![cfg(feature = "direct")]

use ay_bindings::execute_direct::{execute_incremental, ExecuteTypedResult};
use ay_bindings::{AYProgram, Expr, Sort};
use ntest::timeout;

#[test]
#[timeout(10_000)]
fn test_incremental_two_unsat_scopes() {
    let mut prog = AYProgram::qf_lia();
    let x = prog.declare_const("x", Sort::int());
    let y = prog.declare_const("y", Sort::int());

    prog.push();
    prog.assert(x.clone().int_gt(Expr::int(10)));
    prog.assert(x.clone().int_lt(Expr::int(5)));
    prog.check_sat();
    prog.pop(1);

    prog.push();
    prog.assert(y.clone().int_gt(Expr::int(20)));
    prog.assert(y.clone().int_lt(Expr::int(15)));
    prog.check_sat();
    prog.pop(1);

    let outcomes = execute_incremental(&prog).unwrap();
    assert_eq!(outcomes.len(), 2);
    assert!(matches!(outcomes[0].result, ExecuteTypedResult::Verified));
    assert!(matches!(outcomes[1].result, ExecuteTypedResult::Verified));
    assert_eq!(outcomes[0].check_sat_index, 0);
    assert_eq!(outcomes[1].check_sat_index, 1);
}

#[test]
#[timeout(10_000)]
fn test_incremental_sat_then_unsat() {
    let mut prog = AYProgram::qf_lia();
    let x = prog.declare_const("x", Sort::int());
    let y = prog.declare_const("y", Sort::int());

    prog.push();
    prog.assert(x.clone().int_gt(Expr::int(5)));
    prog.check_sat();
    prog.pop(1);

    prog.push();
    prog.assert(y.clone().int_gt(Expr::int(10)));
    prog.assert(y.clone().int_lt(Expr::int(5)));
    prog.check_sat();
    prog.pop(1);

    let outcomes = execute_incremental(&prog).unwrap();
    assert_eq!(outcomes.len(), 2);
    assert!(matches!(
        outcomes[0].result,
        ExecuteTypedResult::Counterexample(_)
    ));
    assert!(matches!(outcomes[1].result, ExecuteTypedResult::Verified));
}

#[test]
fn test_incremental_no_check_sat() {
    let mut prog = AYProgram::qf_lia();
    let _ = prog.declare_const("x", Sort::int());
    let outcomes = execute_incremental(&prog).unwrap();
    assert!(outcomes.is_empty());
}

#[test]
#[timeout(10_000)]
fn test_incremental_three_unsat_scopes() {
    let mut prog = AYProgram::qf_lia();
    let _ = prog.declare_const("a", Sort::int());
    let _ = prog.declare_const("b", Sort::int());
    let _ = prog.declare_const("c", Sort::int());

    for (name, lo, hi) in [("a", 10, 5), ("b", 20, 15), ("c", 30, 25)] {
        let v = Expr::var(name, Sort::int());
        prog.push();
        prog.assert(v.clone().int_gt(Expr::int(lo)));
        prog.assert(v.clone().int_lt(Expr::int(hi)));
        prog.check_sat();
        prog.pop(1);
    }

    let outcomes = execute_incremental(&prog).unwrap();
    assert_eq!(outcomes.len(), 3);
    for (i, o) in outcomes.iter().enumerate() {
        assert!(
            matches!(o.result, ExecuteTypedResult::Verified),
            "scope {i}"
        );
        assert!(o.solve_details.is_some(), "solve_details scope {i}");
    }
}

#[test]
#[timeout(10_000)]
fn test_incremental_get_value_stays_with_preceding_sat() {
    let mut prog = AYProgram::qf_lia();
    let x = prog.declare_const("x", Sort::int());

    prog.assert(x.clone().int_gt(Expr::int(0)));
    prog.check_sat();
    prog.get_value(vec![x.clone()]);

    prog.assert(x.clone().int_lt(Expr::int(10)));
    prog.check_sat();

    let outcomes = execute_incremental(&prog).unwrap();
    assert_eq!(outcomes.len(), 2);

    match &outcomes[0].result {
        ExecuteTypedResult::Counterexample(counterexample) => {
            assert_eq!(counterexample.values.len(), 1);
            assert!(counterexample.values.contains_key("x"));
        }
        other => panic!("first outcome should be SAT, got {other:?}"),
    }

    match &outcomes[1].result {
        ExecuteTypedResult::Counterexample(counterexample) => {
            assert!(
                counterexample.values.is_empty(),
                "first get-value must not leak into second SAT result: {:?}",
                counterexample.values
            );
        }
        other => panic!("second outcome should be SAT, got {other:?}"),
    }
}
