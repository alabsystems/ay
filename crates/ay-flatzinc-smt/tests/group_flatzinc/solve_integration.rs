// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end solve() integration tests for flatzinc-smt.
//!
//! These tests exercise the full pipeline through ay_flatzinc_smt::solve(),
//! which is the public API used by the fzn2smt binary. They validate DZN
//! output formatting, the optimization loop, and MiniZinc protocol
//! compliance (----------, ==========, etc.).
//!
//! Part of #319 (FlatZinc translation correctness), #273 (MiniZinc entry).

use ay_core::kani_compat::det_hash_map_new;
use ay_flatzinc_smt::{
    solve, solve_branching, translate, ObjectiveInfo, SearchAnnotation, SearchStrategy,
    SolverConfig, TranslationResult, ValChoice, VarChoice, VarDomain,
};

fn translate_fzn(input: &str) -> TranslationResult {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

fn make_config() -> SolverConfig {
    SolverConfig {
        timeout_ms: None,
        all_solutions: false,
        global_deadline: None,
    }
}

#[test]
fn solve_satisfaction_unsat() {
    let config = make_config();
    // bool_eq(false, true) is trivially unsat
    let fzn = "constraint bool_eq(false, true);\nsolve satisfy;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert_eq!(count, 0);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "expected UNSATISFIABLE, got: {output}"
    );
}

#[test]
fn solve_satisfaction_sat() {
    let config = make_config();
    // Simple: x in 1..5, x > 3, output x -> should find x=4 or x=5
    let fzn = "var 1..5: x :: output_var;\n\
               constraint int_gt(x, 3);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert_eq!(count, 1);
    assert!(
        output.contains("----------"),
        "expected solution separator, got: {output}"
    );
    assert!(
        output.contains("x = "),
        "expected DZN output with x, got: {output}"
    );
    // No optimality marker for satisfaction
    assert!(
        !output.contains("=========="),
        "satisfaction should not have optimality marker"
    );
}

#[test]
fn solve_satisfaction_set_union_mismatched_lower_bounds_sat() {
    let config = make_config();
    let fzn = "var set of 0..1: A;\n\
               var set of 0..1: B;\n\
               var set of 1..1: C;\n\
               constraint set_in(1, A);\n\
               constraint set_card(A, 1);\n\
               constraint set_card(B, 0);\n\
               constraint set_union(A, B, C);\n\
               constraint set_card(C, 1);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert_eq!(
        count, 1,
        "expected one satisfying assignment, got: {output}"
    );
    assert!(
        output.contains("----------"),
        "expected solution separator, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "mismatched set domains should stay satisfiable, got: {output}"
    );
}

#[test]
fn solve_optimization_maximize() {
    let config = make_config();
    // Maximize x where x in 1..5 -> optimal x=5
    let fzn = "var 1..5: x :: output_var;\n\
               solve maximize x;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert!(count >= 1, "should find at least one solution");
    assert!(
        output.contains("----------"),
        "expected solution separator, got: {output}"
    );
    assert!(
        output.contains("=========="),
        "expected optimality marker, got: {output}"
    );
    // The last solution before ========== should have x = 5
    let lines: Vec<&str> = output.lines().collect();
    let opt_idx = lines
        .iter()
        .position(|l| *l == "==========")
        .expect("no optimality marker");
    // Line before ========== is ----------
    // Line before that is the optimal solution's x value
    assert!(opt_idx >= 2, "not enough lines before ==========");
    let last_sol_line = lines[opt_idx - 2];
    assert!(
        last_sol_line.contains("x = 5"),
        "optimal should be x=5, got: {last_sol_line}"
    );
}

#[test]
fn solve_optimization_minimize() {
    let config = make_config();
    // Minimize x where x in 3..10, x >= 5 -> optimal x=5
    let fzn = "var 3..10: x :: output_var;\n\
               constraint int_ge(x, 5);\n\
               solve minimize x;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert!(count >= 1, "should find at least one solution");
    assert!(
        output.contains("=========="),
        "expected optimality marker, got: {output}"
    );
    // The last solution should have x = 5
    let lines: Vec<&str> = output.lines().collect();
    let opt_idx = lines
        .iter()
        .position(|l| *l == "==========")
        .expect("no optimality marker");
    assert!(opt_idx >= 2);
    let last_sol_line = lines[opt_idx - 2];
    assert!(
        last_sol_line.contains("x = 5"),
        "optimal should be x=5, got: {last_sol_line}"
    );
}

#[test]
fn solve_optimization_iterates_multiple_solutions() {
    let config = make_config();
    // Minimize x + y where x in 1..3, y in 1..3, x + y >= 3
    // Possible sums: 3, 4, 5, 6. Optimal is 3. Solver should find
    // an initial solution, then iteratively tighten to find 3.
    let fzn = "var 1..3: x :: output_var;\n\
               var 1..3: y :: output_var;\n\
               var int: obj :: output_var;\n\
               constraint int_lin_eq([1, 1, -1], [x, y, obj], 0);\n\
               constraint int_lin_le([-1, -1], [x, y], -3);\n\
               solve minimize obj;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert!(count >= 1, "should find at least one solution, got {count}");
    assert!(
        output.contains("=========="),
        "expected optimality marker, got: {output}"
    );

    // Count solution separators to verify at least one was printed
    let sep_count = output.lines().filter(|l| *l == "----------").count();
    assert!(
        sep_count >= 1,
        "should have at least 1 solution separator, got {sep_count}"
    );

    // Verify last solution has optimal obj = 3
    let lines: Vec<&str> = output.lines().collect();
    let opt_idx = lines
        .iter()
        .position(|l| *l == "==========")
        .expect("no optimality marker");
    // Find the obj line in the last solution block
    let last_sep_idx = lines[..opt_idx]
        .iter()
        .rposition(|l| *l == "----------")
        .expect("no separator before optimality");
    let solution_start = lines[..last_sep_idx]
        .iter()
        .rposition(|l| *l == "----------")
        .map(|i| i + 1)
        .unwrap_or(0);
    let last_solution: Vec<&&str> = lines[solution_start..last_sep_idx].iter().collect();
    let has_obj_3 = last_solution.iter().any(|l| l.contains("obj = 3"));
    assert!(
        has_obj_3,
        "optimal obj should be 3, last solution: {last_solution:?}\nfull output: {output}"
    );
}

#[test]
fn solve_optimization_unsat_from_start() {
    let config = make_config();
    // Minimize x where x > 5 AND x < 3 (unsat)
    let fzn = "var 1..10: x :: output_var;\n\
               constraint int_gt(x, 5);\n\
               constraint int_lt(x, 3);\n\
               solve minimize x;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert_eq!(count, 0, "unsat should yield 0 solutions");
    // MiniZinc protocol: optimization with 0 feasible solutions prints
    // =====UNSATISFIABLE===== (not ==========, which means "optimality proven").
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "unsat optimization should print =====UNSATISFIABLE=====: {output}"
    );
    assert!(
        !output.contains("----------"),
        "unsat should have no solution separators: {output}"
    );
}

/// Verify that branching_satisfaction outputs UNSATISFIABLE (not UNKNOWN)
/// when all branches are definitively UNSAT with no UNKNOWN encountered.
/// Regression test for #327: prior code returned bool, losing UNKNOWN vs UNSAT.
#[test]
fn branching_unsat_outputs_unsatisfiable_not_unknown() {
    let config = SolverConfig {
        timeout_ms: Some(5000),
        all_solutions: false,
        global_deadline: None,
    };
    // x must equal both 1 and 2 — definitively UNSAT.
    let fzn = "\
        var 1..2: x;\n\
        constraint int_eq(x, 1);\n\
        constraint int_eq(x, 2);\n\
        solve :: int_search([x], input_order, indomain_min) satisfy;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    solve_branching(&result, &config, &mut buf).expect("solve");
    let output = String::from_utf8(buf).unwrap();
    // Must say UNSATISFIABLE (not UNKNOWN) since all branches are UNSAT.
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "expected UNSATISFIABLE for definitively UNSAT model, got: {output}"
    );
    assert!(
        !output.contains("=====UNKNOWN====="),
        "should not output UNKNOWN when all branches are UNSAT"
    );
}

/// Verify that branching search outputs UNKNOWN (not UNSATISFIABLE)
/// when ay returns unknown for branches.
/// Counterpart to branching_unsat_outputs_unsatisfiable_not_unknown.
/// Regression test for #327: SearchOutcome::Unknown must propagate correctly.
///
/// Uses the solver API's specified zero-duration timeout, which deterministically
/// returns UNKNOWN before search. This does not depend on a particular theory
/// remaining incomplete as solver capabilities evolve.
#[test]
fn branching_unknown_outputs_unknown_not_unsatisfiable() {
    let config = SolverConfig {
        timeout_ms: Some(0),
        all_solutions: false,
        global_deadline: None,
    };
    // Construct TranslationResult directly so the test targets propagation of
    // the solver's UNKNOWN result through branching, not FlatZinc translation.
    let declarations = "\
        (set-logic QF_LIA)\n\
        (declare-fun x () Int)\n\
        (assert (>= x 1))\n\
        (assert (<= x 3))\n"
        .to_string();
    let result = TranslationResult {
        smtlib: String::new(),
        declarations,
        output_vars: vec![],
        objective: None,
        output_smt_names: vec![],
        smt_var_names: vec!["x".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["x".into()],
            var_choice: VarChoice::InputOrder,
            val_choice: ValChoice::IndomainMin,
            strategy: SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = det_hash_map_new();
            d.insert("x".into(), VarDomain::IntRange(1, 3));
            d
        },
    };
    let mut buf = Vec::new();
    let count = solve_branching(&result, &config, &mut buf).expect("solve");
    let output = String::from_utf8(buf).unwrap();

    assert_eq!(count, 0, "unknown should yield 0 solutions");
    // Must say UNKNOWN (not UNSATISFIABLE) since branches returned unknown.
    assert!(
        output.contains("=====UNKNOWN====="),
        "expected UNKNOWN when ay can't decide branches, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "should not output UNSATISFIABLE when branches returned UNKNOWN"
    );
}

/// Verify that branching optimization outputs UNKNOWN (not UNSATISFIABLE)
/// when ay returns unknown for all branches and no solutions were found.
/// Regression test for #327: optimization + hit_unknown + 0 solutions → UNKNOWN.
#[test]
fn branching_optimization_unknown_no_solutions_outputs_unknown() {
    let config = SolverConfig {
        timeout_ms: Some(0),
        all_solutions: false,
        global_deadline: None,
    };
    // Use the same deterministic zero-timeout route as the satisfaction test,
    // but add a minimize objective. The optimization loop must output UNKNOWN,
    // not UNSATISFIABLE (which would claim no feasible solution exists).
    let declarations = "\
        (set-logic QF_LIA)\n\
        (declare-fun x () Int)\n\
        (assert (>= x 1))\n\
        (assert (<= x 3))\n"
        .to_string();
    let result = TranslationResult {
        smtlib: String::new(),
        declarations,
        output_vars: vec![],
        objective: Some(ObjectiveInfo {
            minimize: true,
            smt_expr: "x".into(),
        }),
        output_smt_names: vec![],
        smt_var_names: vec!["x".into()],
        search_annotations: vec![SearchAnnotation::IntSearch {
            vars: vec!["x".into()],
            var_choice: VarChoice::InputOrder,
            val_choice: ValChoice::IndomainMin,
            strategy: SearchStrategy::Complete,
        }],
        var_domains: {
            let mut d = det_hash_map_new();
            d.insert("x".into(), VarDomain::IntRange(1, 3));
            d
        },
    };
    let mut buf = Vec::new();
    let count = solve_branching(&result, &config, &mut buf).expect("solve");
    let output = String::from_utf8(buf).unwrap();

    assert_eq!(count, 0, "unknown should yield 0 solutions");
    assert!(
        output.contains("=====UNKNOWN====="),
        "optimization with UNKNOWN + 0 solutions should output UNKNOWN, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "should not claim UNSATISFIABLE when branches returned UNKNOWN"
    );
    assert!(
        !output.contains("=========="),
        "should not claim optimality when branches returned UNKNOWN"
    );
}

#[test]
fn solve_satisfaction_protocol_format() {
    let config = make_config();
    // Verify exact MiniZinc protocol format:
    // <var> = <val>;\n----------\n (no ========== for satisfaction)
    let fzn = "var int: x :: output_var;\n\
               constraint int_eq(x, 42);\n\
               solve satisfy;\n";
    let result = translate_fzn(fzn);
    let mut buf = Vec::new();
    let count = solve(&result, &config, &mut buf).expect("solve failed");
    let output = String::from_utf8(buf).unwrap();

    assert_eq!(count, 1);
    let lines: Vec<&str> = output.lines().collect();
    assert_eq!(lines[0], "x = 42;", "first line should be DZN assignment");
    assert_eq!(lines[1], "----------", "second line should be separator");
    assert_eq!(lines.len(), 2, "satisfaction should have exactly 2 lines");
}
