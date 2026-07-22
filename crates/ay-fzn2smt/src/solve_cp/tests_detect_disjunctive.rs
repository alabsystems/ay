// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for detect_disjunctive: substitutive disjunctive scheduling detection.
// Verifies that int_lin_le_reif pairs encoding pairwise non-overlap constraints
// are detected and replaced by native Disjunctive propagators.

use ay_cp::engine::CpSolveResult;

use super::tests::{parse_and_solve, solve_cp_output};
use super::CpContext;

/// Helper: build a CpContext from FlatZinc and return the skip set size.
fn detect_and_count_skipped(fzn: &str) -> (CpContext, usize) {
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    // Register parameters and variables first.
    for par in &model.parameters {
        ctx.register_parameter(par).expect("register parameter");
    }
    for var in &model.variables {
        ctx.create_variable(var).expect("create var failed");
    }
    let skip = ctx.detect_disjunctive(&model);
    (ctx, skip.len())
}

// --- Detection tests (unit-level) ---

/// Two tasks, one machine: classic int_lin_le_reif pair.
/// s0 + 3 <= s1 when b01, s1 + 4 <= s0 when b10.
/// Detection should find 1 machine with 2 tasks and skip generated order constraints.
#[test]
fn test_detect_disjunctive_2_tasks_1_machine() {
    let fzn = "\
        var 0..20: s0 :: output_var;\n\
        var 0..20: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -4, b10);\n\
        constraint bool_or(b01, b10, true);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 3, "should skip 2 reifs plus the order clause");
}

/// Three tasks on one machine (complete graph of 3 pairs).
/// Detection should find 1 machine with 3 tasks and skip generated order constraints.
#[test]
fn test_detect_disjunctive_3_tasks_1_machine() {
    let fzn = "\
        var 0..30: s0 :: output_var;\n\
        var 0..30: s1 :: output_var;\n\
        var 0..30: s2 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        var bool: b02;\n\
        var bool: b20;\n\
        var bool: b12;\n\
        var bool: b21;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -4, b10);\n\
        constraint int_lin_le_reif([1, -1], [s0, s2], -3, b02);\n\
        constraint int_lin_le_reif([1, -1], [s2, s0], -2, b20);\n\
        constraint int_lin_le_reif([1, -1], [s1, s2], -4, b12);\n\
        constraint int_lin_le_reif([1, -1], [s2, s1], -2, b21);\n\
        constraint bool_or(b01, b10, true);\n\
        constraint bool_or(b02, b20, true);\n\
        constraint bool_or(b12, b21, true);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 9, "should skip 6 reifs plus 3 order clauses");
}

/// No disjunctive pattern: int_lin_le_reif with wrong coefficients.
/// Detection should find nothing.
#[test]
fn test_detect_disjunctive_no_match_wrong_coeffs() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        constraint int_lin_le_reif([2, -1], [s0, s1], -3, b01);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 0, "wrong coefficients should not match");
}

/// No disjunctive pattern: positive rhs (not a precedence constraint).
#[test]
fn test_detect_disjunctive_no_match_positive_rhs() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], 3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], 3, b10);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(
        skipped, 0,
        "positive rhs should not match (not a precedence)"
    );
}

/// Unpaired half: only one direction. Should not create a disjunctive.
#[test]
fn test_detect_disjunctive_unpaired_half() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 0, "unpaired half should not create disjunctive");
}

/// Output order indicators are semantically visible, so the detector must keep
/// their defining reified constraints.
#[test]
fn test_detect_disjunctive_keeps_output_indicators() {
    let fzn = "\
        var 0..20: s0 :: output_var;\n\
        var 0..20: s1 :: output_var;\n\
        var bool: b01 :: output_var;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -4, b10);\n\
        constraint bool_or(b01, b10, true);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 0, "visible order indicator must not be skipped");
}

/// No constraints at all. Detection returns empty skip set.
#[test]
fn test_detect_disjunctive_empty_model() {
    let fzn = "\
        var 0..10: x :: output_var;\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 0, "empty model should return 0 skipped");
}

// --- Integration tests (solve-level) ---

/// 2-task jobshop via int_lin_le_reif: SAT when horizon is wide enough.
/// After detection, a native Disjunctive propagator handles scheduling.
#[test]
fn test_detect_disjunctive_2_tasks_sat() {
    let fzn = "\
        var 0..10: s0 :: output_var;\n\
        var 0..10: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -2, b10);\n\
        constraint bool_or(b01, b10, true);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            assert!(assignment.len() >= 2, "should have at least 2 output vars");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// 2-task jobshop via int_lin_le_reif: UNSAT when horizon is too tight.
/// Tasks with dur=6 and dur=6 on horizon [0,10]: need at least 12 time units.
#[test]
fn test_detect_disjunctive_2_tasks_unsat_tight_horizon() {
    let fzn = "\
        var 0..5: s0 :: output_var;\n\
        var 0..5: s1 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -6, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -6, b10);\n\
        constraint bool_or(b01, b10, true);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// 3-task 1-machine via int_lin_le_reif: verify no-overlap in solution.
#[test]
fn test_detect_disjunctive_3_tasks_solution_valid() {
    let fzn = "\
        var 0..20: s0 :: output_var;\n\
        var 0..20: s1 :: output_var;\n\
        var 0..20: s2 :: output_var;\n\
        var bool: b01;\n\
        var bool: b10;\n\
        var bool: b02;\n\
        var bool: b20;\n\
        var bool: b12;\n\
        var bool: b21;\n\
        constraint int_lin_le_reif([1, -1], [s0, s1], -3, b01);\n\
        constraint int_lin_le_reif([1, -1], [s1, s0], -4, b10);\n\
        constraint int_lin_le_reif([1, -1], [s0, s2], -3, b02);\n\
        constraint int_lin_le_reif([1, -1], [s2, s0], -2, b20);\n\
        constraint int_lin_le_reif([1, -1], [s1, s2], -4, b12);\n\
        constraint int_lin_le_reif([1, -1], [s2, s1], -2, b21);\n\
        constraint bool_or(b01, b10, true);\n\
        constraint bool_or(b02, b20, true);\n\
        constraint bool_or(b12, b21, true);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should find a solution: {output}"
    );
}

/// Two separate machines (2 tasks each, no cross-machine pairs).
/// Should detect 2 machines and skip generated order constraints total.
#[test]
fn test_detect_disjunctive_2_machines() {
    let fzn = "\
        var 0..20: a0 :: output_var;\n\
        var 0..20: a1 :: output_var;\n\
        var 0..20: b0 :: output_var;\n\
        var 0..20: b1 :: output_var;\n\
        var bool: ba01;\n\
        var bool: ba10;\n\
        var bool: bb01;\n\
        var bool: bb10;\n\
        constraint int_lin_le_reif([1, -1], [a0, a1], -3, ba01);\n\
        constraint int_lin_le_reif([1, -1], [a1, a0], -4, ba10);\n\
        constraint int_lin_le_reif([1, -1], [b0, b1], -2, bb01);\n\
        constraint int_lin_le_reif([1, -1], [b1, b0], -5, bb10);\n\
        constraint bool_or(ba01, ba10, true);\n\
        constraint bool_or(bb01, bb10, true);\n\
        solve satisfy;\n";
    let (_, skipped) = detect_and_count_skipped(fzn);
    assert_eq!(skipped, 6, "should skip 4 reifs plus 2 order clauses");
}

#[test]
fn test_jobshop_minimize_emits_dispatch_incumbent_before_search() {
    let fzn = "\
        var 0..20: a0;\n\
        var 0..20: a1;\n\
        var 0..20: b0;\n\
        var 0..20: b1;\n\
        var 0..20: makespan :: output_var;\n\
        array [1..4] of var int: starts :: output_array([1..4]) = [a0, a1, b0, b1];\n\
        var bool: o01;\n\
        var bool: o10;\n\
        var bool: p01;\n\
        var bool: p10;\n\
        constraint int_lin_le([1, -1], [a0, a1], -3);\n\
        constraint int_lin_le([1, -1], [b0, b1], -2);\n\
        constraint int_lin_le([1, -1], [a1, makespan], -4);\n\
        constraint int_lin_le([1, -1], [b1, makespan], -5);\n\
        constraint int_lin_le_reif([1, -1], [a0, b1], -3, o01);\n\
        constraint int_lin_le_reif([1, -1], [b1, a0], -5, o10);\n\
        constraint bool_or(o01, o10, true);\n\
        constraint int_lin_le_reif([1, -1], [a1, b0], -4, p01);\n\
        constraint int_lin_le_reif([1, -1], [b0, a1], -2, p10);\n\
        constraint bool_or(p01, p10, true);\n\
        solve minimize makespan;\n";

    let output = solve_cp_output(fzn, false);
    let first = output
        .split("----------")
        .next()
        .expect("solution output has a first section");
    assert!(
        first.contains("starts = array1d(1..4, [0, 3, 0, 3]);"),
        "first solution should be the dispatch incumbent: {output}"
    );
    assert!(
        first.contains("makespan = 8;"),
        "first solution should report the dispatch incumbent objective: {output}"
    );
}

#[test]
fn test_jobshop_minimize_improves_dispatch_incumbent_by_machine_swaps() {
    let fzn = "\
        var 0..30: a00;\n\
        var 0..30: a01;\n\
        var 0..30: a02;\n\
        var 0..30: a10;\n\
        var 0..30: a11;\n\
        var 0..30: a12;\n\
        var 0..30: a20;\n\
        var 0..30: a21;\n\
        var 0..30: a22;\n\
        var 0..30: makespan :: output_var;\n\
        array [1..9] of var int: starts :: output_array([1..9]) = [a00, a01, a02, a10, a11, a12, a20, a21, a22];\n\
        var bool: m0_01_10;\n\
        var bool: m0_10_01;\n\
        var bool: m0_01_21;\n\
        var bool: m0_21_01;\n\
        var bool: m0_10_21;\n\
        var bool: m0_21_10;\n\
        var bool: m1_02_12;\n\
        var bool: m1_12_02;\n\
        var bool: m1_02_22;\n\
        var bool: m1_22_02;\n\
        var bool: m1_12_22;\n\
        var bool: m1_22_12;\n\
        var bool: m2_00_11;\n\
        var bool: m2_11_00;\n\
        var bool: m2_00_20;\n\
        var bool: m2_20_00;\n\
        var bool: m2_11_20;\n\
        var bool: m2_20_11;\n\
        constraint int_lin_le([1, -1], [a00, a01], -1);\n\
        constraint int_lin_le([1, -1], [a01, a02], -5);\n\
        constraint int_lin_le([1, -1], [a02, makespan], -7);\n\
        constraint int_lin_le([1, -1], [a10, a11], -3);\n\
        constraint int_lin_le([1, -1], [a11, a12], -4);\n\
        constraint int_lin_le([1, -1], [a12, makespan], -5);\n\
        constraint int_lin_le([1, -1], [a20, a21], -4);\n\
        constraint int_lin_le([1, -1], [a21, a22], -8);\n\
        constraint int_lin_le([1, -1], [a22, makespan], -1);\n\
        constraint int_lin_le_reif([1, -1], [a01, a10], -5, m0_01_10);\n\
        constraint int_lin_le_reif([1, -1], [a10, a01], -3, m0_10_01);\n\
        constraint bool_or(m0_01_10, m0_10_01, true);\n\
        constraint int_lin_le_reif([1, -1], [a01, a21], -5, m0_01_21);\n\
        constraint int_lin_le_reif([1, -1], [a21, a01], -8, m0_21_01);\n\
        constraint bool_or(m0_01_21, m0_21_01, true);\n\
        constraint int_lin_le_reif([1, -1], [a10, a21], -3, m0_10_21);\n\
        constraint int_lin_le_reif([1, -1], [a21, a10], -8, m0_21_10);\n\
        constraint bool_or(m0_10_21, m0_21_10, true);\n\
        constraint int_lin_le_reif([1, -1], [a02, a12], -7, m1_02_12);\n\
        constraint int_lin_le_reif([1, -1], [a12, a02], -5, m1_12_02);\n\
        constraint bool_or(m1_02_12, m1_12_02, true);\n\
        constraint int_lin_le_reif([1, -1], [a02, a22], -7, m1_02_22);\n\
        constraint int_lin_le_reif([1, -1], [a22, a02], -1, m1_22_02);\n\
        constraint bool_or(m1_02_22, m1_22_02, true);\n\
        constraint int_lin_le_reif([1, -1], [a12, a22], -5, m1_12_22);\n\
        constraint int_lin_le_reif([1, -1], [a22, a12], -1, m1_22_12);\n\
        constraint bool_or(m1_12_22, m1_22_12, true);\n\
        constraint int_lin_le_reif([1, -1], [a00, a11], -1, m2_00_11);\n\
        constraint int_lin_le_reif([1, -1], [a11, a00], -4, m2_11_00);\n\
        constraint bool_or(m2_00_11, m2_11_00, true);\n\
        constraint int_lin_le_reif([1, -1], [a00, a20], -1, m2_00_20);\n\
        constraint int_lin_le_reif([1, -1], [a20, a00], -4, m2_20_00);\n\
        constraint bool_or(m2_00_20, m2_20_00, true);\n\
        constraint int_lin_le_reif([1, -1], [a11, a20], -4, m2_11_20);\n\
        constraint int_lin_le_reif([1, -1], [a20, a11], -4, m2_20_11);\n\
        constraint bool_or(m2_11_20, m2_20_11, true);\n\
        solve minimize makespan;\n";

    let output = solve_cp_output(fzn, false);
    let first = output
        .split("----------")
        .next()
        .expect("solution output has a first section");
    assert!(
        first.contains("starts = array1d(1..9, [0, 1, 6, 6, 9, 13, 1, 9, 18]);"),
        "first solution should be the locally improved incumbent: {output}"
    );
    assert!(
        first.contains("makespan = 19;"),
        "first solution should improve over the dispatch-only makespan 21: {output}"
    );
}
