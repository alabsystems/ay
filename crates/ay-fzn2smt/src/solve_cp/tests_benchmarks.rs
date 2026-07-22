// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Phase 3 benchmark integration tests: classic CP problems solved via ay-cp.
//
// Keep the test inputs crate-local instead of reaching into the repo-level
// benchmarks tree: OSS publish intentionally excludes `/benchmarks/`, and
// these tests must still compile in the sanitized snapshot.

use super::tests::solve_cp_output;
use super::CpContext;

macro_rules! include_benchmark_fixture {
    ($name:literal) => {
        include_str!(concat!("fixtures/", $name))
    };
}

fn parse_cp_context(fzn: &str) -> CpContext {
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    ctx.build_model(&model).expect("build failed");
    assert!(
        ctx.unsupported.is_empty(),
        "unsupported: {:?}",
        ctx.unsupported
    );
    super::search_annotations::apply_search_annotations(&mut ctx, &model.solve.annotations);
    ctx.set_default_search_vars_if_missing();
    ctx
}

fn nqueens_array_fzn(n: usize) -> String {
    let coeffs = "array [1..2] of int: coeffs = [1,-1];\n";
    let vars = (0..n)
        .map(|i| format!("var 1..{n}: q{i};\n"))
        .collect::<String>();
    let output = format!(
        "array [1..{n}] of var int: q :: output_array([1..{n}]) = [{}];\n",
        (0..n)
            .map(|i| format!("q{i}"))
            .collect::<Vec<_>>()
            .join(", ")
    );
    let mut constraints = String::new();
    for i in 0..n {
        for j in i + 1..n {
            let delta = j - i;
            constraints.push_str(&format!(
                "constraint int_lin_ne(coeffs, [q{i}, q{j}], 0);\n"
            ));
            constraints.push_str(&format!(
                "constraint int_lin_ne(coeffs, [q{i}, q{j}], {delta});\n"
            ));
            constraints.push_str(&format!(
                "constraint int_lin_ne(coeffs, [q{i}, q{j}], -{delta});\n"
            ));
        }
    }
    format!("{coeffs}{vars}{output}{constraints}solve satisfy;\n")
}

#[test]
fn test_default_search_vars_use_bool_outputs_when_no_int_outputs() {
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var 0..9: aux;\n\
        solve satisfy;\n";
    let ctx = parse_cp_context(fzn);
    let search_vars = ctx.engine.search_vars();

    assert_eq!(
        search_vars,
        &[ctx.var_map["a"], ctx.var_map["b"]],
        "bool-only satisfaction models should search output vars, not every auxiliary var"
    );
    assert!(
        !search_vars.contains(&ctx.var_map["aux"]),
        "non-output auxiliary vars should stay out of default search_vars"
    );
}

#[test]
fn test_default_search_vars_keep_int_outputs_ahead_of_bool_outputs() {
    let fzn = "\
        var bool: b :: output_var;\n\
        var 1..5: x :: output_var;\n\
        var 0..9: aux;\n\
        solve satisfy;\n";
    let ctx = parse_cp_context(fzn);

    assert_eq!(
        ctx.engine.search_vars(),
        &[ctx.var_map["x"]],
        "mixed models keep the existing integer-output search scope"
    );
}

#[test]
fn test_parallel_satisfaction_uses_constructive_nqueens_specialist() {
    let fzn = nqueens_array_fzn(8);
    let model = ay_flatzinc_parser::parse_flatzinc(&fzn).expect("parse failed");
    let mut out = Vec::new();

    super::solve_satisfaction_parallel(&model, None, 2, &mut out).expect("parallel solve failed");
    let output = String::from_utf8(out).expect("utf8");

    assert!(
        output.contains("q = array1d(1..8, [2, 4, 6, 8, 3, 1, 7, 5]);"),
        "parallel satisfaction should route through the constructive N-Queens specialist: {output}"
    );
    assert!(output.contains("=========="));
}

#[test]
fn test_benchmark_nqueens_8() {
    let fzn = include_benchmark_fixture!("nqueens_8.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 8-queens: {output}"
    );
    assert!(
        output.contains("=========="),
        "should be complete: {output}"
    );
}

#[test]
fn test_benchmark_nqueens_12() {
    let fzn = include_benchmark_fixture!("nqueens_12.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 12-queens: {output}"
    );
}

#[test]
fn test_benchmark_nqueens_20() {
    let fzn = include_benchmark_fixture!("nqueens_20.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 20-queens: {output}"
    );
}

#[test]
fn test_benchmark_graph_color_petersen() {
    let fzn = include_benchmark_fixture!("graph_color_petersen.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should 3-color Petersen graph: {output}"
    );
}

#[test]
fn test_benchmark_sudoku_4x4() {
    let fzn = include_benchmark_fixture!("sudoku_easy.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve Sudoku: {output}"
    );
    // Verify given cells preserved
    assert!(
        output.contains("x11 = 1;"),
        "given: x11=1, output: {output}"
    );
    assert!(
        output.contains("x23 = 1;"),
        "given: x23=1, output: {output}"
    );
    assert!(
        output.contains("x32 = 3;"),
        "given: x32=3, output: {output}"
    );
    assert!(
        output.contains("x44 = 2;"),
        "given: x44=2, output: {output}"
    );
}

#[test]
fn test_benchmark_magic_square_3() {
    let fzn = include_benchmark_fixture!("magic_square_3.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 3x3 magic square: {output}"
    );
}

#[test]
fn test_benchmark_latin_square_5() {
    let fzn = include_benchmark_fixture!("latin_square_5.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve 5x5 Latin square: {output}"
    );
}

#[test]
fn test_benchmark_send_more_money() {
    let fzn = include_benchmark_fixture!("send_more_money.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should solve SEND+MORE=MONEY: {output}"
    );
    // The unique solution: s=9, e=5, n=6, d=7, m=1, o=0, r=8, y=2
    assert!(output.contains("s = 9;"), "s should be 9: {output}");
    assert!(output.contains("e = 5;"), "e should be 5: {output}");
    assert!(output.contains("m = 1;"), "m should be 1: {output}");
    assert!(output.contains("y = 2;"), "y should be 2: {output}");
}

#[test]
fn test_benchmark_knapsack_10() {
    let fzn = include_benchmark_fixture!("knapsack_10.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal knapsack: {output}"
    );
    assert!(
        output.contains("profit = "),
        "should report profit: {output}"
    );
}

#[test]
fn test_benchmark_circuit_tsp_5() {
    let fzn = include_benchmark_fixture!("circuit_tsp_5.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal TSP tour: {output}"
    );
    // Optimal is 85
    assert!(
        output.contains("total_dist = 85;"),
        "optimal TSP should be 85: {output}"
    );
}

#[test]
fn test_benchmark_cumulative_3tasks() {
    let fzn = include_benchmark_fixture!("cumulative_3tasks.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal schedule: {output}"
    );
}

#[test]
fn test_benchmark_table_assignment() {
    let fzn = include_benchmark_fixture!("table_assignment.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal assignment: {output}"
    );
}

#[test]
fn test_benchmark_golomb_ruler_7() {
    let fzn = include_benchmark_fixture!("golomb_ruler_7.fzn");
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal Golomb ruler: {output}"
    );
    // Known optimal 7-mark Golomb ruler has length 25
    assert!(
        output.contains("m7 = 25;"),
        "optimal ruler length should be 25: {output}"
    );
}
