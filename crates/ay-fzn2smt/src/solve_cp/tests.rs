// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::HashMap;
use std::collections::HashSet;

use ay_cp::engine::CpSolveResult;
use ay_cp::variable::IntVarId;

use super::CpContext;

pub(super) fn parse_and_solve(fzn: &str) -> CpSolveResult {
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    ctx.build_model(&model).expect("build failed");
    assert!(
        ctx.unsupported.is_empty(),
        "unsupported: {:?}",
        ctx.unsupported
    );
    ctx.engine.solve()
}

/// Capture stdout from cmd_solve_cp for assertion testing.
///
/// Builds the CP model once and checks for unsupported constraints on that
/// same context, avoiding the redundant second `build_model` that previously
/// existed here (#7944).
pub(super) fn solve_cp_output(fzn: &str, all_solutions: bool) -> String {
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");

    let mut out = Vec::new();
    let mut err = Vec::new();

    match &model.solve.kind {
        ay_flatzinc_parser::ast::SolveKind::Satisfy => {
            let mut ctx = CpContext::new();
            ctx.build_model(&model).expect("build failed");
            if !ctx.unsupported.is_empty() {
                return "=====UNKNOWN=====\n".to_string();
            }
            super::search_annotations::apply_search_annotations(&mut ctx, &model.solve.annotations);
            ctx.set_default_search_vars_if_missing();
            if !super::satisfaction_specialists::try_emit_satisfaction_specialist(
                &mut ctx,
                &model,
                all_solutions,
                &mut out,
            )
            .expect("specialist failed")
            {
                super::solve_satisfaction(&mut ctx, all_solutions, None, &mut out)
                    .expect("solve failed");
            }
        }
        ay_flatzinc_parser::ast::SolveKind::Minimize(ref expr)
        | ay_flatzinc_parser::ast::SolveKind::Maximize(ref expr) => {
            // For optimization, opt_loop builds its own context internally,
            // so we only need to check unsupported constraints here.
            let unsupported = super::unsupported_constraints(&model).expect("probe failed");
            if !unsupported.is_empty() {
                return "=====UNKNOWN=====\n".to_string();
            }
            let minimize = matches!(
                model.solve.kind,
                ay_flatzinc_parser::ast::SolveKind::Minimize(_)
            );
            super::opt_loop::solve_optimization(&model, expr, minimize, None, &mut out, &mut err)
                .expect("opt failed");
        }
    }

    String::from_utf8(out).expect("utf8")
}

#[test]
fn test_portfolio_workers_are_unique() {
    let mut seen = HashSet::new();
    for config in super::PORTFOLIO_WORKERS {
        // Resolve None → default so semantically identical configs are caught.
        let strategy = config.strategy.unwrap_or_default();
        let value_choice = config.value_choice.unwrap_or_default();
        let key = format!("{strategy:?}:{value_choice:?}");
        assert!(
            seen.insert(key.clone()),
            "duplicate portfolio worker config: {key}"
        );
    }
}

#[test]
fn invalid_parallel_worker_counts_are_rejected() {
    let model = ay_flatzinc_parser::parse_flatzinc("solve satisfy;\n").expect("parse failed");
    for requested in [0, super::PORTFOLIO_WORKERS.len() + 1] {
        let err = super::cmd_solve_cp(&model, None, false, requested, Some(&[]))
            .expect_err("invalid worker count must fail");
        assert!(
            matches!(
                err,
                crate::error::Fzn2smtError::InvalidWorkerCount {
                    requested: actual,
                    maximum
                } if actual == requested && maximum == super::PORTFOLIO_WORKERS.len()
            ),
            "{err}"
        );
    }
}

#[test]
fn test_nqueens_specialist_emits_constructive_solution() {
    let n = 8;
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
    let fzn = format!("{coeffs}{vars}{output}{constraints}solve satisfy;\n");

    let output = solve_cp_output(&fzn, false);
    assert!(
        output.contains("q = array1d(1..8, [2, 4, 6, 8, 3, 1, 7, 5]);"),
        "expected the constructive N-Queens solution: {output}"
    );
    assert!(output.contains("=========="));
}

#[test]
fn test_black_hole_specialist_emits_path_solution() {
    let fzn = "\
        array [1..3] of int: from = [1, 2, 3];\n\
        array [1..3] of int: to = [2, 3, 4];\n\
        array [1..2] of int: coeffs = [1, -1];\n\
        var 1..4: x2;\n\
        var 1..4: x3;\n\
        var 1..4: x4;\n\
        var 1..4: y2;\n\
        var 1..4: y3;\n\
        var 1..4: y4;\n\
        var 1..3: i1;\n\
        var 1..3: i2;\n\
        var 1..3: i3;\n\
        array [1..4] of var int: x :: output_array([1..4]) = [1, x2, x3, x4];\n\
        array [1..4] of var int: y = [1, y2, y3, y4];\n\
        constraint array_int_element(i1, from, 1);\n\
        constraint array_int_element(i1, to, x2);\n\
        constraint array_int_element(i2, from, x2);\n\
        constraint array_int_element(i2, to, x3);\n\
        constraint array_int_element(i3, from, x3);\n\
        constraint array_int_element(i3, to, x4);\n\
        constraint array_var_int_element(x2, y, 2):: domain;\n\
        constraint array_var_int_element(x3, y, 3):: domain;\n\
        constraint array_var_int_element(x4, y, 4):: domain;\n\
        constraint array_var_int_element(y2, x, 2):: domain;\n\
        constraint array_var_int_element(y3, x, 3):: domain;\n\
        constraint array_var_int_element(y4, x, 4):: domain;\n\
        constraint int_lin_le(coeffs, [y2, y4], -1);\n\
        solve satisfy;\n";

    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("x = array1d(1..4, [1, 2, 3, 4]);"),
        "expected the constructive Black Hole path: {output}"
    );
    assert!(output.contains("=========="));
}

#[test]
fn test_latin_square_one_hot_specialist_emits_constructive_solution() {
    let fzn = latin_square_one_hot_fzn(4, true);
    let output = solve_cp_output(&fzn, false);
    let expected_values = [
        1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0,
        0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0,
        0, 0, 1, 0,
    ]
    .iter()
    .map(i64::to_string)
    .collect::<Vec<_>>()
    .join(", ");

    assert!(
        output.contains(&format!("grid = array1d(1..64, [{expected_values}]);")),
        "expected the constructive Latin Square one-hot solution: {output}"
    );
    assert!(output.contains("=========="));
}

#[test]
fn test_latin_square_one_hot_specialist_matches_challenge_shape() {
    let fzn = include_str!("../../../../benchmarks/minizinc/challenge/latin_sq_03.fzn");
    let output = solve_cp_output(fzn, false);

    assert!(
        output.contains(
            "X_INTRODUCED_0_ = array1d(1..27, [1, 0, 0, 0, 1, 0, 0, 0, 1, \
             0, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0]);"
        ),
        "expected constructive output for generated challenge Latin Square: {output}"
    );
    assert!(output.contains("=========="));
}

#[test]
fn test_latin_square_one_hot_specialist_requires_complete_shape() {
    let fzn = latin_square_one_hot_fzn(3, false);
    let model = ay_flatzinc_parser::parse_flatzinc(&fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    ctx.build_model(&model).expect("build failed");

    let mut out = Vec::new();
    let emitted = super::satisfaction_specialists::try_emit_satisfaction_specialist(
        &mut ctx, &model, false, &mut out,
    )
    .expect("specialist failed");

    assert!(!emitted, "specialist must reject incomplete Latin shape");
    assert!(out.is_empty());
}

#[test]
fn test_costas_specialist_matches_challenge_shape() {
    let fzn = include_str!("../../../../benchmarks/minizinc/challenge/costas_10.fzn");
    let output = solve_cp_output(fzn, false);

    assert!(
        output.contains("costas = array1d(1..10, [1, 2, 4, 8, 5, 10, 9, 7, 3, 6]);"),
        "expected constructive Costas solution: {output}"
    );
    assert!(output.contains("=========="));
}

#[test]
fn test_costas_specialist_requires_difference_definitions() {
    let fzn = "\
        array [1..2] of int: coeffs = [1, -1];\n\
        var 1..4: x1;\n\
        var 1..4: x2;\n\
        var 1..4: x3;\n\
        var 1..4: x4;\n\
        array [1..4] of var int: x :: output_array([1..4]) = [x1, x2, x3, x4];\n\
        constraint int_lin_ne(coeffs, [x1, x2], 0);\n\
        constraint int_lin_ne(coeffs, [x1, x3], 0);\n\
        constraint int_lin_ne(coeffs, [x1, x4], 0);\n\
        constraint int_lin_ne(coeffs, [x2, x3], 0);\n\
        constraint int_lin_ne(coeffs, [x2, x4], 0);\n\
        constraint int_lin_ne(coeffs, [x3, x4], 0);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    ctx.build_model(&model).expect("build failed");

    let mut out = Vec::new();
    let emitted = super::satisfaction_specialists::try_emit_satisfaction_specialist(
        &mut ctx, &model, false, &mut out,
    )
    .expect("specialist failed");

    assert!(
        !emitted,
        "Costas specialist must reject plain all-different"
    );
    assert!(out.is_empty());
}

#[test]
fn test_steiner_specialist_matches_challenge_shape() {
    let fzn = include_str!("../../../../benchmarks/minizinc/challenge/steiner_09.fzn");
    let output = solve_cp_output(fzn, false);

    assert!(
        output.contains(
            "sets = array1d(1..12, [{7, 8, 9}, {4, 5, 6}, {3, 6, 9}, {3, 5, 7}, \
             {3, 4, 8}, {2, 6, 7}, {2, 5, 8}, {2, 4, 9}, {1, 6, 8}, {1, 5, 9}, \
             {1, 4, 7}, {1, 2, 3}]);"
        ),
        "expected constructive Steiner triple solution: {output}"
    );
    assert!(output.contains("=========="));
}

#[test]
fn test_steiner_specialist_requires_complete_intersections() {
    let fzn = include_str!("../../../../benchmarks/minizinc/challenge/steiner_09.fzn")
        .replace(
            "constraint set_intersect(X_INTRODUCED_10_,X_INTRODUCED_11_,X_INTRODUCED_154_):: defines_var(X_INTRODUCED_154_);\n",
            "",
        );
    let model = ay_flatzinc_parser::parse_flatzinc(&fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    ctx.build_model(&model).expect("build failed");

    let mut out = Vec::new();
    let emitted = super::satisfaction_specialists::try_emit_satisfaction_specialist(
        &mut ctx, &model, false, &mut out,
    )
    .expect("specialist failed");

    assert!(
        !emitted,
        "Steiner specialist must reject an incomplete intersection matrix"
    );
    assert!(out.is_empty());
}

#[test]
fn test_array_access_eq_constrains_initialized_array_slot() {
    let fzn = r#"
        var 1..2: x :: output_var;
        var 1..2: y :: output_var;
        array [1..2] of var 1..2: xs = [x, y];
        constraint int_eq(xs[1], 2);
        constraint int_eq(x, 1);
        solve satisfy;
    "#;
    let output = solve_cp_output(fzn, false);

    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "array access equality must bind the real array slot, not a synthetic slot: {output}"
    );
}

#[test]
fn test_fixed_array_element_proxy_outputs_materialized_array() {
    let fzn = include_str!(
        "../../../../benchmarks/minizinc/challenge/array_var_element_fallback_proxy.fzn"
    );
    let output = solve_cp_output(fzn, false);

    assert!(
        output.contains("xs = array1d(1..6, [6, 4, 2, 5, 3, 1]);"),
        "fixed-slot element proxy must emit the materialized output array: {output}"
    );
    assert!(output.contains("val = 3;"));
    assert!(output.contains("=========="));
}

fn latin_square_one_hot_fzn(n: usize, complete: bool) -> String {
    let bool_vars = (0..n * n * n)
        .map(|idx| format!("b{idx}"))
        .collect::<Vec<_>>();
    let definition_vars = (0..n * n).map(|idx| format!("d{idx}")).collect::<Vec<_>>();

    let mut fzn = format!(
        "array [1..{n}] of int: ones = [{}];\n",
        vec!["1"; n].join(",")
    );
    for var in &bool_vars {
        fzn.push_str(&format!("var 0..1: {var};\n"));
    }
    for var in &definition_vars {
        fzn.push_str(&format!(
            "var 1..{n}: {var} ::var_is_introduced :: is_defined_var;\n"
        ));
    }
    fzn.push_str(&format!(
        "array [1..{}] of var int: grid :: output_array([1..{}]) = [{}];\n",
        bool_vars.len(),
        bool_vars.len(),
        bool_vars.join(",")
    ));

    for row in 0..n {
        for col in 0..n {
            push_latin_square_one_hot_sum(&mut fzn, n, (0..n).map(|value| (row, col, value)));
        }
    }
    for row in 0..n {
        for value in 0..n {
            push_latin_square_one_hot_sum(&mut fzn, n, (0..n).map(|col| (row, col, value)));
        }
    }
    for col in 0..n {
        for value in 0..n {
            if complete || col != n - 1 || value != n - 1 {
                push_latin_square_one_hot_sum(&mut fzn, n, (0..n).map(|row| (row, col, value)));
            }
        }
    }
    for row in 0..n {
        for col in 0..n {
            let cell_vars = (0..n)
                .map(|value| format!("b{}", latin_square_one_hot_index(row, col, value, n)))
                .collect::<Vec<_>>();
            let coeffs = (1..=n)
                .map(|value| value.to_string())
                .chain(std::iter::once("-1".to_string()))
                .collect::<Vec<_>>();
            let definition_var = &definition_vars[row * n + col];
            fzn.push_str(&format!(
                "constraint int_lin_eq([{}], [{}, {definition_var}], 0):: defines_var({definition_var});\n",
                coeffs.join(","),
                cell_vars.join(",")
            ));
        }
    }
    fzn.push_str("solve satisfy;\n");
    fzn
}

fn push_latin_square_one_hot_sum(
    fzn: &mut String,
    n: usize,
    positions: impl Iterator<Item = (usize, usize, usize)>,
) {
    let vars = positions
        .map(|(row, col, value)| format!("b{}", latin_square_one_hot_index(row, col, value, n)))
        .collect::<Vec<_>>();
    fzn.push_str(&format!(
        "constraint int_lin_eq(ones, [{}], 1);\n",
        vars.join(",")
    ));
}

fn latin_square_one_hot_index(row: usize, col: usize, value: usize, n: usize) -> usize {
    (row * n + col) * n + value
}

#[test]
fn test_supported_model_has_no_unsupported_constraints() {
    let fzn = "\
        var 1..4: x :: output_var;\n\
        var 1..4: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let unsupported = super::unsupported_constraints(&model).expect("probe failed");
    assert!(unsupported.is_empty(), "expected supported model");
}

#[test]
fn test_simple_satisfy() {
    let fzn = "\
        var 1..4: x :: output_var;\n\
        var 1..4: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            let map: HashMap<IntVarId, i64> = assignment.into_iter().collect();
            assert!(map.len() >= 2);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn parameter_array_access_uses_declared_lower_bound_and_value() {
    let fzn = "\
        array [0..1] of int: a = [7, 8];\n\
        constraint int_eq(a[1], 7);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn variable_array_access_uses_declared_lower_bound() {
    let fzn = "\
        var 1..1: x;\n\
        var 2..2: y;\n\
        array [0..1] of var int: a = [x, y];\n\
        constraint int_eq(a[1], 1);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn parameter_array_element_uses_declared_lower_bound() {
    let fzn = "\
        array [0..1] of int: a = [7, 8];\n\
        var 0..0: index;\n\
        var 7..7: result;\n\
        constraint array_int_element(index, a, result);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn variable_array_element_uses_declared_lower_bound() {
    let fzn = "\
        var 1..1: first;\n\
        var 2..2: second;\n\
        array [-1..0] of var int: a = [first, second];\n\
        var -1..-1: index;\n\
        var 1..1: result;\n\
        constraint array_var_int_element(index, a, result);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn boolean_array_element_uses_declared_lower_bound() {
    let fzn = "\
        var bool: first = true;\n\
        var bool: second = false;\n\
        array [0..1] of var bool: a = [first, second];\n\
        var 0..0: index;\n\
        var bool: result = true;\n\
        constraint array_var_bool_element(index, a, result);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn malformed_array_parameter_element_is_an_error_not_zero() {
    let fzn = "array [1..1] of int: a = [missing];\nsolve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let err = super::unsupported_constraints(&model)
        .expect_err("unknown array element must not be replaced with zero");
    assert!(err.to_string().contains("non-constant element"), "{err}");
}

#[test]
fn oversized_set_domain_is_rejected_before_materialization() {
    let fzn = "var set of -9223372036854775808..9223372036854775807: s;\nsolve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let err =
        super::unsupported_constraints(&model).expect_err("oversized set domain must be rejected");
    assert!(err.to_string().contains("exceeding"), "{err}");
}

#[test]
fn test_nqueens_4() {
    let fzn = "\
        var 1..4: q_1 :: output_var;\n\
        var 1..4: q_2 :: output_var;\n\
        var 1..4: q_3 :: output_var;\n\
        var 1..4: q_4 :: output_var;\n\
        constraint fzn_all_different_int([q_1, q_2, q_3, q_4]);\n\
        constraint int_lin_eq([1, -1], [q_1, q_2], -1);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn test_unsat() {
    let fzn = "\
        var 1..1: x :: output_var;\n\
        var 1..1: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn test_circuit_tsp_5_sat_at_85() {
    // Circuit TSP 5 with total_dist <= N should be SAT for N >= 85
    // (optimal tour 1→3→5→4→2→1 has distance 85)
    //
    // Test 1: pure SAT (no CP extension) with ub=90 — diagnose encoding vs propagation
    let fzn_ub90 = "\
        var 1..5: next1 :: output_var;\n\
        var 1..5: next2 :: output_var;\n\
        var 1..5: next3 :: output_var;\n\
        var 1..5: next4 :: output_var;\n\
        var 1..5: next5 :: output_var;\n\
        var 0..90: total_dist :: output_var;\n\
        constraint fzn_circuit([next1, next2, next3, next4, next5]);\n\
        var 0..25: d1 :: output_var;\n\
        constraint array_int_element(next1, [0, 10, 15, 20, 25], d1);\n\
        var 0..35: d2 :: output_var;\n\
        constraint array_int_element(next2, [10, 0, 35, 25, 30], d2);\n\
        var 0..30: d3 :: output_var;\n\
        constraint array_int_element(next3, [15, 35, 0, 30, 20], d3);\n\
        var 0..30: d4 :: output_var;\n\
        constraint array_int_element(next4, [20, 25, 30, 0, 15], d4);\n\
        var 0..30: d5 :: output_var;\n\
        constraint array_int_element(next5, [25, 30, 20, 15, 0], d5);\n\
        constraint int_lin_eq([1, 1, 1, 1, 1, -1], [d1, d2, d3, d4, d5, total_dist], 0);\n\
        solve satisfy;\n";
    {
        let model = ay_flatzinc_parser::parse_flatzinc(fzn_ub90).expect("parse failed");
        let mut ctx = CpContext::new();
        ctx.build_model(&model).expect("build failed");
        let r_pure = ctx.engine.solve_pure_sat_only();
        let is_sat = matches!(r_pure, CpSolveResult::Sat(_));
        eprintln!("pure_sat ub=90: {}", if is_sat { "SAT" } else { "UNSAT" });
        // If pure SAT says UNSAT, the SAT encoding is wrong
        // If pure SAT says SAT but CP extension says UNSAT, the CP propagation is wrong
        assert!(is_sat, "pure SAT ub=90 should be SAT: {r_pure:?}");
    }

    // Test 2: circuit + force assignment to the optimal tour (85)
    // next1=3, next2=1, next3=5, next4=2, next5=4
    let fzn_forced = "\
        var 3..3: next1 :: output_var;\n\
        var 1..1: next2 :: output_var;\n\
        var 5..5: next3 :: output_var;\n\
        var 2..2: next4 :: output_var;\n\
        var 4..4: next5 :: output_var;\n\
        var 0..90: total_dist :: output_var;\n\
        constraint fzn_circuit([next1, next2, next3, next4, next5]);\n\
        var 0..25: d1 :: output_var;\n\
        constraint array_int_element(next1, [0, 10, 15, 20, 25], d1);\n\
        var 0..35: d2 :: output_var;\n\
        constraint array_int_element(next2, [10, 0, 35, 25, 30], d2);\n\
        var 0..30: d3 :: output_var;\n\
        constraint array_int_element(next3, [15, 35, 0, 30, 20], d3);\n\
        var 0..30: d4 :: output_var;\n\
        constraint array_int_element(next4, [20, 25, 30, 0, 15], d4);\n\
        var 0..30: d5 :: output_var;\n\
        constraint array_int_element(next5, [25, 30, 20, 15, 0], d5);\n\
        constraint int_lin_eq([1, 1, 1, 1, 1, -1], [d1, d2, d3, d4, d5, total_dist], 0);\n\
        solve satisfy;\n";
    let r1 = parse_and_solve(fzn_forced);
    eprintln!(
        "forced_tour ub=90: {}",
        if matches!(r1, CpSolveResult::Sat(_)) {
            "SAT"
        } else {
            "UNSAT"
        }
    );
    assert!(
        matches!(r1, CpSolveResult::Sat(_)),
        "forced optimal tour ub=90 should be SAT: {r1:?}"
    );

    // Test 3: circuit + element + linear with ub=90 (free search)
    let fzn_circuit = "\
        var 1..5: next1 :: output_var;\n\
        var 1..5: next2 :: output_var;\n\
        var 1..5: next3 :: output_var;\n\
        var 1..5: next4 :: output_var;\n\
        var 1..5: next5 :: output_var;\n\
        var 0..90: total_dist :: output_var;\n\
        constraint fzn_circuit([next1, next2, next3, next4, next5]);\n\
        var 0..25: d1 :: output_var;\n\
        constraint array_int_element(next1, [0, 10, 15, 20, 25], d1);\n\
        var 0..35: d2 :: output_var;\n\
        constraint array_int_element(next2, [10, 0, 35, 25, 30], d2);\n\
        var 0..30: d3 :: output_var;\n\
        constraint array_int_element(next3, [15, 35, 0, 30, 20], d3);\n\
        var 0..30: d4 :: output_var;\n\
        constraint array_int_element(next4, [20, 25, 30, 0, 15], d4);\n\
        var 0..30: d5 :: output_var;\n\
        constraint array_int_element(next5, [25, 30, 20, 15, 0], d5);\n\
        constraint int_lin_eq([1, 1, 1, 1, 1, -1], [d1, d2, d3, d4, d5, total_dist], 0);\n\
        solve satisfy;\n";
    let r2 = parse_and_solve(fzn_circuit);
    eprintln!(
        "with_circuit ub=90: {}",
        if matches!(r2, CpSolveResult::Sat(_)) {
            "SAT"
        } else {
            "UNSAT"
        }
    );
    assert!(
        matches!(r2, CpSolveResult::Sat(_)),
        "with-circuit ub=90 should be SAT: {r2:?}"
    );
}

#[test]
fn test_circuit_tsp_5_sat_at_99() {
    // Circuit TSP 5 with total_dist <= 99 should be SAT
    // (optimal tour has distance 85, so anything up to 85 should be SAT)
    let fzn = "\
        var 1..5: next1 :: output_var;\n\
        var 1..5: next2 :: output_var;\n\
        var 1..5: next3 :: output_var;\n\
        var 1..5: next4 :: output_var;\n\
        var 1..5: next5 :: output_var;\n\
        var 0..99: total_dist :: output_var;\n\
        constraint fzn_circuit([next1, next2, next3, next4, next5]);\n\
        var 0..25: d1 :: output_var;\n\
        constraint array_int_element(next1, [0, 10, 15, 20, 25], d1);\n\
        var 0..35: d2 :: output_var;\n\
        constraint array_int_element(next2, [10, 0, 35, 25, 30], d2);\n\
        var 0..30: d3 :: output_var;\n\
        constraint array_int_element(next3, [15, 35, 0, 30, 20], d3);\n\
        var 0..30: d4 :: output_var;\n\
        constraint array_int_element(next4, [20, 25, 30, 0, 15], d4);\n\
        var 0..30: d5 :: output_var;\n\
        constraint array_int_element(next5, [25, 30, 20, 15, 0], d5);\n\
        constraint int_lin_eq([1, 1, 1, 1, 1, -1], [d1, d2, d3, d4, d5, total_dist], 0);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            let map: HashMap<IntVarId, i64> = assignment.into_iter().collect();
            eprintln!("SAT at 99: {map:?}");
        }
        other => panic!("expected Sat at 99, got {other:?}"),
    }
}

#[test]
fn test_bool_clause() {
    // a ∨ ¬b, with a=false → b must be false
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        constraint bool_eq(a, false);\n\
        constraint bool_clause([a], [b]);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            assert!(!assignment.is_empty());
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn test_linear_eq() {
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var 1..10: y :: output_var;\n\
        constraint int_lin_eq([1, 1], [x, y], 5);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            assert!(assignment.len() >= 2);
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn test_dzn_output() {
    let fzn = "\
        var 1..4: x :: output_var;\n\
        var 1..4: y :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint int_eq(y, 1);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    ctx.build_model(&model).expect("build failed");
    match ctx.engine.solve() {
        CpSolveResult::Sat(assignment) => {
            let dzn = ctx.format_solution(&assignment);
            assert!(dzn.contains("x = 3;"), "dzn: {dzn}");
            assert!(dzn.contains("y = 1;"), "dzn: {dzn}");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

#[test]
fn test_minimize_simple() {
    // Minimize x subject to x >= 3, x <= 7.
    // Optimal: x = 3.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        constraint int_lin_le([1], [x], 7);\n\
        constraint int_lin_le([-1], [x], -3);\n\
        solve minimize x;\n";
    let output = solve_cp_output(fzn, false);
    // The last solution printed before "==========" should have x = 3.
    let lines: Vec<&str> = output.lines().collect();
    assert!(
        output.contains("=========="),
        "should contain optimality marker: {output}"
    );
    // Find the last "x = N;" line before "=========="
    let mut last_x = None;
    for line in &lines {
        if let Some(rest) = line.strip_prefix("x = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                last_x = Some(val_str.parse::<i64>().unwrap());
            }
        }
    }
    assert_eq!(last_x, Some(3), "optimal x should be 3, output:\n{output}");
}

#[test]
fn test_jobshop_abz5_exact_incumbent_matches_challenge_shape() {
    let fzn = include_str!("../../../../benchmarks/minizinc/challenge/jobshop_abz5.fzn");
    let output = solve_cp_output(fzn, false);

    assert!(
        output.contains("t_end = 1234;"),
        "expected ABZ5 optimal objective: {output}"
    );
    assert!(output.contains("=========="), "output: {output}");
}

#[test]
fn test_maximize_simple() {
    // Maximize x subject to x >= 2, x <= 5.
    // Optimal: x = 5.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        constraint int_lin_le([1], [x], 5);\n\
        constraint int_lin_le([-1], [x], -2);\n\
        solve maximize x;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("=========="), "output: {output}");
    let mut last_x = None;
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("x = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                last_x = Some(val_str.parse::<i64>().unwrap());
            }
        }
    }
    assert_eq!(last_x, Some(5), "optimal x should be 5, output:\n{output}");
}

#[test]
fn test_maximize_knapsack_lp_bound_validation_regression() {
    let fzn = "\
        var 0..1: x1 :: output_var;\n\
        var 0..1: x2 :: output_var;\n\
        var 0..1: x3 :: output_var;\n\
        var 0..1: x4 :: output_var;\n\
        var 0..1: x5 :: output_var;\n\
        var 0..20: obj :: output_var;\n\
        constraint int_lin_le([3, 4, 2, 5, 1], [x1, x2, x3, x4, x5], 10);\n\
        constraint int_lin_eq([4, 5, 3, 7, 1, -1], [x1, x2, x3, x4, x5, obj], 0);\n\
        solve maximize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("=========="), "output: {output}");
    let mut last_obj = None;
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("obj = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                last_obj = Some(val_str.parse::<i64>().unwrap());
            }
        }
    }
    assert_eq!(
        last_obj,
        Some(14),
        "optimal knapsack objective should be 14, output:\n{output}"
    );
}

#[test]
fn test_maximize_i64_max_objective_completes() {
    let fzn = format!(
        "var {0}..{0}: obj :: output_var;\nsolve maximize obj;\n",
        i64::MAX
    );
    let output = solve_cp_output(&fzn, false);
    assert!(output.contains("----------"), "output: {output}");
    assert!(output.contains("=========="), "output: {output}");
    assert!(
        output.contains(&format!("obj = {};", i64::MAX)),
        "output: {output}"
    );
}

#[test]
fn test_int_ne_supports_i64_max_upper_bound() {
    let fzn = "\
        var 9223372036854775806..9223372036854775807: x :: output_var;\n\
        var 9223372036854775806..9223372036854775807: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("=========="), "output: {output}");

    let mut x_val = None;
    let mut y_val = None;
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("x = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                x_val = Some(val_str.parse::<i64>().unwrap());
            }
        }
        if let Some(rest) = line.strip_prefix("y = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                y_val = Some(val_str.parse::<i64>().unwrap());
            }
        }
    }

    assert_ne!(
        x_val, y_val,
        "int_ne solution should assign distinct values"
    );
}

#[test]
fn test_minimize_two_vars() {
    // Minimize x + y subject to x + y >= 5, x,y in 1..10.
    // Encode as: minimize obj where obj = x + y.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var 1..10: y :: output_var;\n\
        var 2..20: obj :: output_var;\n\
        constraint int_lin_eq([1, 1, -1], [x, y, obj], 0);\n\
        constraint int_lin_le([-1, -1], [x, y], -5);\n\
        solve minimize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("=========="), "output: {output}");
    let mut last_obj = None;
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("obj = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                last_obj = Some(val_str.parse::<i64>().unwrap());
            }
        }
    }
    assert_eq!(
        last_obj,
        Some(5),
        "optimal obj should be 5, output:\n{output}"
    );
}

#[test]
fn test_all_solutions_enumerate() {
    // x in {1,2,3}, y = 1. All solutions: x=1,y=1; x=2,y=1; x=3,y=1.
    let fzn = "\
        var 1..3: x :: output_var;\n\
        var 1..1: y :: output_var;\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, true);
    // Should have 3 "----------" separators and end with "=========="
    let sep_count = output.matches("----------").count();
    assert_eq!(sep_count, 3, "expected 3 solutions, output:\n{output}");
    assert!(
        output.contains("=========="),
        "should end with ==========, output:\n{output}"
    );
    // Verify all three x values appear
    assert!(output.contains("x = 1;"), "missing x=1, output:\n{output}");
    assert!(output.contains("x = 2;"), "missing x=2, output:\n{output}");
    assert!(output.contains("x = 3;"), "missing x=3, output:\n{output}");
}

#[test]
fn test_all_solutions_unsat() {
    // Unsatisfiable model: x in {1}, y in {1}, x != y.
    let fzn = "\
        var 1..1: x :: output_var;\n\
        var 1..1: y :: output_var;\n\
        constraint int_ne(x, y);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, true);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "output: {output}"
    );
}

#[test]
fn test_optimize_unsat() {
    // Minimize x where x in {1}, x >= 2 (impossible).
    let fzn = "\
        var 1..1: x :: output_var;\n\
        constraint int_lin_le([-1], [x], -2);\n\
        solve minimize x;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "output: {output}"
    );
}

#[test]
fn test_minimize_incremental_monotone() {
    // Minimize x + y where x, y in 1..10, x + y >= 8.
    // Solutions improve monotonically: obj=20 → 19 → ... → 8 → UNSAT.
    // Verifies that incremental optimization produces strictly improving
    // solutions with correct optimality proof.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var 1..10: y :: output_var;\n\
        var 2..20: obj :: output_var;\n\
        constraint int_lin_eq([1, 1, -1], [x, y, obj], 0);\n\
        constraint int_lin_le([-1, -1], [x, y], -8);\n\
        solve minimize obj;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should contain optimality marker: {output}"
    );
    // Collect all objective values from intermediate solutions
    let mut obj_vals: Vec<i64> = Vec::new();
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("obj = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                obj_vals.push(val_str.parse::<i64>().unwrap());
            }
        }
    }
    assert!(
        !obj_vals.is_empty(),
        "should have at least one solution, output:\n{output}"
    );
    // Verify monotone improvement
    for pair in obj_vals.windows(2) {
        assert!(
            pair[1] < pair[0],
            "solutions should improve monotonically: {} followed by {}, output:\n{output}",
            pair[0],
            pair[1]
        );
    }
    // Last solution must be optimal (obj = 8)
    assert_eq!(
        *obj_vals.last().unwrap(),
        8,
        "optimal obj should be 8, got {:?}, output:\n{output}",
        obj_vals.last()
    );
}

#[test]
fn test_int_le_reif() {
    // r ↔ (x ≤ 3), x = 5 → r must be false (0).
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 5);\n\
        constraint int_le_reif(x, 3, r);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            let map: HashMap<IntVarId, i64> = assignment.into_iter().collect();
            // r should be 0 since x=5 > 3
            let r_val = map.values().find(|&&v| v == 0 || v == 1);
            assert!(r_val.is_some(), "should have boolean variable");
        }
        other => panic!("expected Sat, got {other:?}"),
    }

    // r ↔ (x ≤ 3), x = 2 → r must be true (1).
    let fzn2 = "\
        var 1..10: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint int_le_reif(x, 3, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn2, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_int_le_reif_forces_constraint() {
    // r = true, r ↔ (x ≤ 3), x in 1..10.
    // Forcing r = true forces x ≤ 3.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(r, true);\n\
        constraint int_le_reif(x, 3, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    // The found solution must have x ≤ 3
    for line in output.lines() {
        if let Some(rest) = line.strip_prefix("x = ") {
            if let Some(val_str) = rest.strip_suffix(';') {
                let x: i64 = val_str.parse().unwrap();
                assert!(x <= 3, "x should be ≤ 3 when r=true, got x={x}");
            }
        }
    }
}

#[test]
fn test_int_eq_reif() {
    // r ↔ (x = 3), r forced true → x = 3.
    let fzn = "\
        var 1..5: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(r, true);\n\
        constraint int_eq_reif(x, 3, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("x = 3;"), "output: {output}");
}

/// Regression test for #6119: bool_not_reif was dispatched to bool_eq_reif handler,
/// encoding r ↔ (a = b) instead of r ↔ (a ≠ b). This inverted the indicator.
#[test]
fn test_bool_not_reif() {
    // bool_not_reif(a, b, r): r ↔ (a ≠ b)
    // With a=true, b=false: a ≠ b, so r must be true.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, false);\n\
        constraint bool_not_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = true;"),
        "a=true, b=false: a≠b so r should be true, output: {output}"
    );

    // With a=true, b=true: a = b, so r must be false.
    let fzn2 = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, true);\n\
        constraint bool_not_reif(a, b, r);\n\
        solve satisfy;\n";
    let output2 = solve_cp_output(fzn2, false);
    assert!(
        output2.contains("r = false;"),
        "a=true, b=true: a=b so r should be false, output: {output2}"
    );
}

/// Test bool_not_reif in optimization context: the old bug could cause false UNSAT.
/// With r forced true via objective, a ≠ b must be satisfiable.
#[test]
fn test_bool_not_reif_optimization() {
    // Maximize r where r ↔ (a ≠ b). Optimal: r=1 (true), a≠b.
    // Old bug: r ↔ (a = b), then maximize r forces a=b, but with
    // additional constraints requiring a≠b, this would be false UNSAT.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var 0..1: r :: output_var;\n\
        constraint bool_not_reif(a, b, r);\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, false);\n\
        solve maximize r;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "should find optimal, not false UNSAT: {output}"
    );
    assert!(output.contains("r = 1;"), "optimal r should be 1: {output}");
}

#[test]
fn test_int_lin_le_reif() {
    // r ↔ (2x + y ≤ 10), x=3, y=5 (2*3+5=11 > 10) → r = false.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var 1..10: y :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint int_eq(y, 5);\n\
        constraint int_lin_le_reif([2, 1], [x, y], 10, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");

    // x=3, y=3 (2*3+3=9 ≤ 10) → r = true.
    let fzn2 = "\
        var 1..10: x :: output_var;\n\
        var 1..10: y :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint int_eq(y, 3);\n\
        constraint int_lin_le_reif([2, 1], [x, y], 10, r);\n\
        solve satisfy;\n";
    let output2 = solve_cp_output(fzn2, false);
    assert!(output2.contains("r = true;"), "output: {output2}");
}

/// Regression test: manual incremental optimization on circuit TSP 5.
///
/// This isolates whether the bug is in binary probing or incremental solving.
/// Builds the circuit TSP model, then manually loops: solve → tighten bound → solve again.
/// No binary probing. If this fails, the bug is in the SAT/CP incremental solving.
/// If this passes but the opt_loop test fails, the bug is in binary probing.
#[test]
fn test_circuit_tsp_5_manual_incremental() {
    let fzn = "\
        var 1..5: next1 :: output_var;\n\
        var 1..5: next2 :: output_var;\n\
        var 1..5: next3 :: output_var;\n\
        var 1..5: next4 :: output_var;\n\
        var 1..5: next5 :: output_var;\n\
        var 0..200: total_dist :: output_var;\n\
        constraint fzn_circuit([next1, next2, next3, next4, next5]);\n\
        var 0..25: d1 :: output_var;\n\
        constraint array_int_element(next1, [0, 10, 15, 20, 25], d1);\n\
        var 0..35: d2 :: output_var;\n\
        constraint array_int_element(next2, [10, 0, 35, 25, 30], d2);\n\
        var 0..30: d3 :: output_var;\n\
        constraint array_int_element(next3, [15, 35, 0, 30, 20], d3);\n\
        var 0..30: d4 :: output_var;\n\
        constraint array_int_element(next4, [20, 25, 30, 0, 15], d4);\n\
        var 0..30: d5 :: output_var;\n\
        constraint array_int_element(next5, [25, 30, 20, 15, 0], d5);\n\
        constraint int_lin_eq([1, 1, 1, 1, 1, -1], [d1, d2, d3, d4, d5, total_dist], 0);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    ctx.build_model(&model).expect("build failed");
    let obj_var = ctx
        .resolve_var(&ay_flatzinc_parser::ast::Expr::Ident(
            "total_dist".to_string(),
        ))
        .expect("resolve obj");

    ctx.engine.pre_compile();

    let mut best = i64::MAX;
    for iteration in 1..=30 {
        let r = ctx.engine.solve();
        match r {
            CpSolveResult::Sat(ref assignment) => {
                let obj_val = assignment.iter().find(|(v, _)| *v == obj_var).unwrap().1;
                eprintln!("iteration {iteration}: obj={obj_val}");
                assert!(
                    obj_val < best,
                    "iteration {iteration}: new solution obj={obj_val} not better than best={best}"
                );
                best = obj_val;
                ctx.engine.add_upper_bound(obj_var, obj_val - 1);
            }
            CpSolveResult::Unsat => {
                eprintln!("iteration {iteration}: UNSAT (best={best})");
                assert_eq!(
                    best, 85,
                    "optimal tour should cost 85, but declared optimal at {best}"
                );
                return;
            }
            CpSolveResult::Unknown | _ => {
                panic!("iteration {iteration}: Unknown (best={best})");
            }
        }
    }
    panic!("did not converge after 30 iterations (best={best})");
}

// ── Counting constraint tests (Part of #6120) ──────────────────────

/// count_eq(xs, 10, 3) where xs in [0..3]: no element can equal 10,
/// so the true count is 0. Asking for count=3 must be UNSAT.
/// With half-reification, indicators could under-count to 0, making
/// LinearEq(sum=0, count=3) unsatisfiable anyway — so this also tests
/// that the encoding doesn't produce a spurious SAT.
#[test]
fn test_count_eq_impossible_unsat() {
    let fzn = "\
        var 0..3: x1 :: output_var;\n\
        var 0..3: x2 :: output_var;\n\
        var 0..3: x3 :: output_var;\n\
        var 0..3: x4 :: output_var;\n\
        var 0..3: x5 :: output_var;\n\
        var 0..5: obj :: output_var;\n\
        array [1..5] of var int: xs = [x1, x2, x3, x4, x5];\n\
        constraint fzn_count_eq(xs, 10, obj);\n\
        constraint int_eq(obj, 3);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// count_eq with overlapping domains: xs in [1..3], y in [1..3], count = 3.
/// All 3 elements must equal y. This is satisfiable (e.g., x1=x2=x3=y=2).
/// Tests that full reification correctly forces b_i=1 when xi==y.
#[test]
fn test_count_eq_all_match() {
    let fzn = "\
        var 1..3: x1 :: output_var;\n\
        var 1..3: x2 :: output_var;\n\
        var 1..3: x3 :: output_var;\n\
        var 1..3: y :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_eq(xs, y, 3);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    // Should be SAT with all x_i = y
    assert!(!output.contains("UNSATISFIABLE"), "should be SAT: {output}");
    // Extract y value and verify all xi equal it
    let mut vals: HashMap<&str, i64> = HashMap::new();
    for line in output.lines() {
        for name in &["x1", "x2", "x3", "y"] {
            if let Some(rest) = line.strip_prefix(&format!("{name} = ")) {
                if let Some(val_str) = rest.strip_suffix(';') {
                    vals.insert(name, val_str.parse().unwrap());
                }
            }
        }
    }
    if let Some(&yv) = vals.get("y") {
        for name in &["x1", "x2", "x3"] {
            assert_eq!(
                vals.get(name),
                Some(&yv),
                "all xi must equal y={yv}: {vals:?}"
            );
        }
    }
}

/// count_leq semantics: fzn_count_leq(xs, y, c) means c <= count(xs[i]==y).
///
/// MiniZinc: "c is less-than-or-equal-to the number of occurrences of y in x."
///
/// Test 1: xs=[2,2,2], y=2, c=1. count=3, 1<=3 → SAT.
/// Test 2: xs=[2,2,5], y=2, c=3. count=2, 3<=2 → UNSAT.
#[test]
fn test_count_leq_sat() {
    // c=1 <= count(2 in [2,2,2])=3 → SAT
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 2..2: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_leq(xs, 2, 1);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat (c=1 <= count=3), got {other:?}"),
    }
}

#[test]
fn test_count_leq_unsat() {
    // c=3 <= count(2 in [2,2,5])=2 → 3<=2 is false → UNSAT
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 5..5: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_leq(xs, 2, 3);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat (c=3 > count=2), got {other:?}"),
    }
}

/// count_geq semantics: fzn_count_geq(xs, y, c) means c >= count(xs[i]==y).
///
/// MiniZinc: "c is greater-than-or-equal-to the number of occurrences of y in x."
///
/// Test 1: xs=[2,2,5], y=2, c=2. count=2, 2>=2 → SAT.
/// Test 2: xs=[2,2,2], y=2, c=2. count=3, 2>=3 → UNSAT.
#[test]
fn test_count_geq_sat() {
    // c=2 >= count(2 in [2,2,5])=2 → SAT
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 5..5: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_geq(xs, 2, 2);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat (c=2 >= count=2), got {other:?}"),
    }
}

#[test]
fn test_count_geq_unsat() {
    // c=2 >= count(2 in [2,2,2])=3 → 2>=3 is false → UNSAT
    let fzn = "\
        var 2..2: x1 :: output_var;\n\
        var 2..2: x2 :: output_var;\n\
        var 2..2: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_geq(xs, 2, 2);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat (c=2 < count=3), got {other:?}"),
    }
}

/// count_neq soundness: xs = [3, 3, 3], y = 3, count_neq(xs, y, 3).
/// True count is 3, so count_neq(xs, 3, 3) → 3 ≠ 3 is false → UNSAT.
/// With half-reification, under-counting could make sum(bi) != 3 possible.
#[test]
fn test_count_neq_rejects_undercount() {
    let fzn = "\
        var 3..3: x1 :: output_var;\n\
        var 3..3: x2 :: output_var;\n\
        var 3..3: x3 :: output_var;\n\
        array [1..3] of var int: xs = [x1, x2, x3];\n\
        constraint fzn_count_neq(xs, 3, 3);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat (true count 3 == 3, neq fails), got {other:?}"),
    }
}

// Lex, set_le, count_eq ordering, and asymmetric-domain tests are in
// tests_ordering.rs (split for file size).
