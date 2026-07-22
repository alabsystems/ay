// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{SetSolutionError, Solver};

#[test]
fn test_try_set_solution_returns_root_exported_error() {
    let mut solver = Solver::new(0);
    solver.new_var();
    solver.new_var();

    let short = solver
        .try_set_solution(&[true])
        .expect_err("short assignment should fail");
    assert_eq!(short, SetSolutionError::TooShort { got: 1, min: 2 });

    let long = solver
        .try_set_solution(&[true, false, true])
        .expect_err("long assignment should fail");
    assert_eq!(long, SetSolutionError::TooLong { got: 3, max: 2 });
}
