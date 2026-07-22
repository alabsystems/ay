// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Minimal native Rust API example: solve x + y = 7, x > 2, y < 4.

use ay_dpll::api::{Logic, SolveResult, Solver, Sort};

fn main() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA is supported");

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let seven = solver.int_const(7);
    let sum = solver.try_add(x, y).expect("integer addition");
    let sum_is_seven = solver.try_eq(sum, seven).expect("integer equality");
    solver
        .try_assert_term(sum_is_seven)
        .expect("Boolean assertion");

    let two = solver.int_const(2);
    let x_gt_two = solver.try_gt(x, two).expect("integer comparison");
    solver.try_assert_term(x_gt_two).expect("Boolean assertion");

    let four = solver.int_const(4);
    let y_lt_four = solver.try_lt(y, four).expect("integer comparison");
    solver
        .try_assert_term(y_lt_four)
        .expect("Boolean assertion");

    let details = solver.check_sat_with_details();
    match details.accept_for_consumer() {
        Ok(SolveResult::Sat) => {
            println!("sat: x={:?}, y={:?}", solver.value(x), solver.value(y));
        }
        Ok(SolveResult::Unsat(_)) => println!("unsat"),
        Ok(SolveResult::Unknown) | Err(_) => {
            println!("unknown: {:?}", details.unknown_reason);
        }
        Ok(_) => println!("unknown: unrecognized solver result"),
    }
}
