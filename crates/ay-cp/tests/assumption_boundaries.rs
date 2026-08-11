// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_cp::engine::CpSolveResult;
use ay_cp::{CpSatEngine, Domain};

#[test]
fn solve_under_assumptions_handles_maximum_integer() {
    let mut engine = CpSatEngine::new();
    let x = engine.new_int_var(Domain::singleton(i64::MAX), Some("x"));
    match engine.solve_under_assumptions(&[(x, i64::MAX)]) {
        CpSolveResult::Sat(assignment) => assert_eq!(
            assignment.iter().find(|(var, _)| *var == x),
            Some(&(x, i64::MAX)),
        ),
        other => panic!("expected SAT at i64::MAX, got {other:?}"),
    }
}
