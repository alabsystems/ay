// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! End-to-end integration tests over the MPS and LP fixtures.
//!
//! Each fixture pair (`simple`, `production`, `knapsack`) is parsed by both
//! parsers where applicable and solved via [`ay_lp::solve`]. We assert on the
//! optimum objective value (to ~1e-3 tolerance) and verify variable feasibility.

use std::fs;
use std::path::Path;

use ay_lp::{parse_lp, parse_mps, solve, Problem, RowKind, Sense, Solution};

fn fixture_path(name: &str) -> String {
    let dir = env!("CARGO_MANIFEST_DIR");
    format!("{dir}/tests/fixtures/{name}")
}

fn read(name: &str) -> String {
    let path = fixture_path(name);
    fs::read_to_string(Path::new(&path)).expect("fixture should exist")
}

fn check_feasible(problem: &Problem, solution: &Solution) {
    for c in &problem.constraints {
        let lhs: f64 = c.coeffs.iter().map(|&(i, a)| a * solution.values[i]).sum();
        match c.kind {
            RowKind::Le => assert!(
                lhs <= c.rhs + 1e-3,
                "constraint {} violated: {} !<= {}",
                c.name,
                lhs,
                c.rhs
            ),
            RowKind::Ge => assert!(
                lhs >= c.rhs - 1e-3,
                "constraint {} violated: {} !>= {}",
                c.name,
                lhs,
                c.rhs
            ),
            RowKind::Eq => assert!(
                (lhs - c.rhs).abs() <= 1e-3,
                "constraint {} violated: {} != {}",
                c.name,
                lhs,
                c.rhs
            ),
        }
    }
}

#[test]
fn test_simple_mps_round_trip() {
    let input = read("simple.mps");
    let problem = parse_mps(&input).expect("parse mps");
    assert_eq!(problem.sense, Sense::Min);
    assert_eq!(problem.variables.len(), 2);
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective - 4.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    check_feasible(&problem, &sol);
}

#[test]
fn test_production_mps_maximization() {
    let input = read("production.mps");
    let problem = parse_mps(&input).expect("parse mps");
    assert_eq!(problem.sense, Sense::Max);
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective - 21.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    check_feasible(&problem, &sol);
}

#[test]
fn test_knapsack_mps_binary() {
    let input = read("knapsack.mps");
    let problem = parse_mps(&input).expect("parse mps");
    assert!(problem.has_integer_vars());
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective - 9.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    for val in &sol.values {
        let rounded = val.round();
        assert!((val - rounded).abs() < 1e-3, "binary not integral: {val}");
        assert!((0.0..=1.0).contains(&rounded), "outside 0/1: {rounded}");
    }
    check_feasible(&problem, &sol);
}

#[test]
fn test_simple_lp_round_trip() {
    let input = read("simple.lp");
    let problem = parse_lp(&input).expect("parse lp");
    assert_eq!(problem.sense, Sense::Min);
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective - 4.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    check_feasible(&problem, &sol);
}

#[test]
fn test_production_lp_maximization() {
    let input = read("production.lp");
    let problem = parse_lp(&input).expect("parse lp");
    assert_eq!(problem.sense, Sense::Max);
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective - 21.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    check_feasible(&problem, &sol);
}

#[test]
fn test_knapsack_lp_binary() {
    let input = read("knapsack.lp");
    let problem = parse_lp(&input).expect("parse lp");
    assert!(problem.has_integer_vars());
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective - 9.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    check_feasible(&problem, &sol);
}

#[test]
fn test_mps_and_lp_give_same_optimum_on_simple() {
    let mps = parse_mps(&read("simple.mps")).expect("mps");
    let lp = parse_lp(&read("simple.lp")).expect("lp");
    let a = solve(&mps).expect("mps solve");
    let b = solve(&lp).expect("lp solve");
    assert!((a.objective - b.objective).abs() < 1e-3);
}

#[test]
fn test_lp_free_variable_solves() {
    let input = "\
Minimize
 x
Subject To
 lower: x >= -2
Bounds
 x free
End
";
    let problem = parse_lp(input).expect("parse lp");
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective + 2.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    assert!((sol.values[0] + 2.0).abs() < 1e-3, "x = {}", sol.values[0]);
    check_feasible(&problem, &sol);
}

#[test]
fn test_mps_free_variable_solves() {
    let input = "\
NAME FREE
ROWS
 N OBJ
 G LOWER
COLUMNS
    X OBJ 1.0 LOWER 1.0
RHS
    RHS LOWER -2.0
BOUNDS
 FR BND X
ENDATA
";
    let problem = parse_mps(input).expect("parse mps");
    let sol = solve(&problem).expect("solve");
    assert!(
        (sol.objective + 2.0).abs() < 1e-3,
        "obj = {}",
        sol.objective
    );
    assert!((sol.values[0] + 2.0).abs() < 1e-3, "x = {}", sol.values[0]);
    check_feasible(&problem, &sol);
}
