// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for global and set constraints: set_in_reif, array_int_maximum,
// array_int_minimum, int_lin_ne_reif, variable RHS, bool_and_reif,
// bool_or_reif.

use std::collections::HashMap;

use ay_cp::engine::CpSolveResult;

use super::tests::{parse_and_solve, solve_cp_output};
use super::CpContext;

// --- nvalue tests ---

#[test]
fn test_nvalue_empty_array_rejects_nonzero_count() {
    let fzn = "\
        var 1..1: n;\n\
        constraint fzn_nvalue(n, []);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "nvalue(n, []) must enforce n=0, got: {output}"
    );
}

// --- set_ne tests ---

#[test]
fn test_set_ne_forced_equal_sets_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var 1..1: one;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_ne(s1, s2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_ne must reject equal forced sets, got: {output}"
    );
}

#[test]
fn test_set_ne_forced_different_sets_sat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_ne(s1, s2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "set_ne must allow different forced sets, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "set_ne different forced sets should be satisfiable, got: {output}"
    );
}

#[test]
fn test_set_relation_handles_distant_singleton_domains() {
    let fzn = "\
        var set of -9223372036854775808..-9223372036854775808: s1;\n\
        var set of 9223372036854775807..9223372036854775807: s2;\n\
        constraint set_ne(s1, s2);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn test_set_union_rejects_member_outside_result_domain() {
    let fzn = "\
        var set of 1..1: s1;\n\
        var set of 2..2: s2;\n\
        var set of 1..1: result;\n\
        var 2..2: two;\n\
        constraint set_card(s1, 0);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s2, 1);\n\
        constraint set_card(result, 0);\n\
        constraint set_union(s1, s2, result);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn test_set_intersect_rejects_member_outside_result_domain() {
    let fzn = "\
        var set of 2..2: s1;\n\
        var set of 2..2: s2;\n\
        var set of 1..1: result;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(result, 0);\n\
        constraint set_intersect(s1, s2, result);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn test_array_set_element_parameter_uses_declared_lower_bound() {
    let fzn = "\
        array [0..1] of set of int: sets = [{1}, {2}];\n\
        var 1..1: index;\n\
        var set of 1..2: result;\n\
        var 1..1: one;\n\
        constraint array_set_element(index, sets, result);\n\
        constraint set_in(one, result);\n\
        constraint set_card(result, 1);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn test_array_set_element_rejects_unrepresentable_constant_member() {
    let fzn = "\
        array [1..1] of set of int: sets = [{2}];\n\
        var 1..1: index;\n\
        var set of 1..1: result;\n\
        constraint array_set_element(index, sets, result);\n\
        constraint set_card(result, 0);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn test_array_set_element_variable_uses_declared_lower_bound() {
    let fzn = "\
        var set of 1..1: s0;\n\
        var set of 2..2: s1;\n\
        array [0..1] of var set of 1..2: sets = [s0, s1];\n\
        var 1..1: index;\n\
        var set of 1..2: result;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s0);\n\
        constraint set_in(two, s1);\n\
        constraint set_card(s0, 1);\n\
        constraint set_card(s1, 1);\n\
        constraint array_set_element(index, sets, result);\n\
        constraint set_in(one, result);\n\
        constraint set_card(result, 1);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

// --- set_lt tests ---

#[test]
fn test_set_order_uses_sorted_lists_not_subset() {
    let fzn = "\
        var set of 1..3: s1;\n\
        var set of 1..3: s2;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        var 3..3: three;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(three, s1);\n\
        constraint set_card(s1, 2);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s2, 1);\n\
        constraint set_lt(s1, s2);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn test_set_le_accepts_proper_sorted_list_prefix() {
    let fzn = "\
        var set of 1..2: prefix;\n\
        var set of 1..2: longer;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, prefix);\n\
        constraint set_card(prefix, 1);\n\
        constraint set_in(one, longer);\n\
        constraint set_in(two, longer);\n\
        constraint set_card(longer, 2);\n\
        constraint set_le(prefix, longer);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn test_reified_set_order_matches_nonreified_lex_order() {
    let fzn = "\
        var set of 1..3: s1;\n\
        var set of 1..3: s2;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        var 3..3: three;\n\
        var bool: le;\n\
        var bool: lt;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(three, s1);\n\
        constraint set_card(s1, 2);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s2, 1);\n\
        constraint set_le_reif(s1, s2, le);\n\
        constraint set_lt_reif(s1, s2, lt);\n\
        constraint bool_eq(le, true);\n\
        constraint bool_eq(lt, true);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn test_empty_set_is_strictly_less_than_nonempty_set() {
    let forward = "\
        var set of 1..0: empty;\n\
        var set of 1..1: nonempty;\n\
        var 1..1: one;\n\
        constraint set_in(one, nonempty);\n\
        constraint set_lt(empty, nonempty);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(forward), CpSolveResult::Sat(_)));

    let reverse = "\
        var set of 1..0: empty;\n\
        var set of 1..1: nonempty;\n\
        var 1..1: one;\n\
        constraint set_in(one, nonempty);\n\
        constraint set_lt(nonempty, empty);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(reverse), CpSolveResult::Unsat));
}

#[test]
fn test_set_lt_forced_proper_prefix_sat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_card(s1, 1);\n\
        constraint set_in(one, s2);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s2, 2);\n\
        constraint set_lt(s1, s2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=========="),
        "set_lt must allow a forced sorted-list prefix, got: {output}"
    );
    assert!(
        !output.contains("=====UNSATISFIABLE====="),
        "set_lt sorted-list prefix case should be satisfiable, got: {output}"
    );
}

#[test]
fn test_set_lt_forced_equal_sets_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var 1..1: one;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_lt(s1, s2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_lt must reject equal forced sets, got: {output}"
    );
}

#[test]
fn test_set_lt_forced_lexicographically_greater_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_card(s1, 1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s2, 1);\n\
        constraint set_lt(s1, s2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_lt must reject a lexicographically greater left set, got: {output}"
    );
}

// --- set_in with constant sets ---

#[test]
fn test_set_in_sparse_constant_set_prunes_to_allowed_values() {
    let fzn = "\
        var 1..5: x :: output_var;\n\
        constraint set_in(x, {2, 4});\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    let vals = parse_int_values(&output, &["x"]);
    assert_eq!(vals.len(), 1, "should output x, got: {output}");
    assert!(
        vals["x"] == 2 || vals["x"] == 4,
        "set_in must restrict x to {{2, 4}}, got: {output}"
    );
}

#[test]
fn test_set_in_named_sparse_constant_set_rejects_forbidden_value() {
    let fzn = "\
        set of int: S = {1, 3};\n\
        var 1..3: x;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in(x, S);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_in must enforce named sparse sets, got: {output}"
    );
}

#[test]
fn test_set_in_interval_constant_set_rejects_out_of_range_value() {
    let fzn = "\
        var 1..5: x;\n\
        constraint int_eq(x, 5);\n\
        constraint set_in(x, 2..4);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_in must enforce interval sets, got: {output}"
    );
}

#[test]
fn test_set_in_empty_constant_set_is_unsat() {
    let fzn = "\
        var 1..5: x;\n\
        constraint set_in(x, {});\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_in over empty set must be UNSAT, got: {output}"
    );
}

// --- set_eq_reif tests ---

#[test]
fn test_set_eq_reif_forced_equal_sets_true() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_eq_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = true;"),
        "set_eq_reif must be true for equal forced sets, got: {output}"
    );
}

#[test]
fn test_set_eq_reif_forced_different_sets_false() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_eq_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = false;"),
        "set_eq_reif must be false for different forced sets, got: {output}"
    );
}

#[test]
fn test_set_eq_reif_forced_equal_sets_false_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r;\n\
        var 1..1: one;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_eq_reif(s1, s2, r);\n\
        constraint bool_eq(r, false);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_eq_reif must reject false when forced sets are equal, got: {output}"
    );
}

// --- set_ne_reif tests ---

#[test]
fn test_set_ne_reif_forced_equal_sets_false() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_ne_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = false;"),
        "set_ne_reif must be false for equal forced sets, got: {output}"
    );
}

#[test]
fn test_set_ne_reif_forced_different_sets_true() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_ne_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = true;"),
        "set_ne_reif must be true for different forced sets, got: {output}"
    );
}

#[test]
fn test_set_ne_reif_forced_different_sets_false_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_ne_reif(s1, s2, r);\n\
        constraint bool_eq(r, false);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_ne_reif must reject false when forced sets differ, got: {output}"
    );
}

// --- set_subset_reif tests ---

#[test]
fn test_set_subset_reif_forced_subset_true() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 2);\n\
        constraint set_subset_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = true;"),
        "set_subset_reif must be true for a forced subset, got: {output}"
    );
}

#[test]
fn test_set_subset_reif_forced_non_subset_false() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_subset_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = false;"),
        "set_subset_reif must be false for a forced non-subset, got: {output}"
    );
}

#[test]
fn test_set_subset_reif_forced_non_subset_true_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_subset_reif(s1, s2, r);\n\
        constraint bool_eq(r, true);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_subset_reif must reject true for a forced non-subset, got: {output}"
    );
}

// --- set_superset_reif tests ---

#[test]
fn test_set_superset_reif_forced_superset_true() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 2);\n\
        constraint set_card(s2, 1);\n\
        constraint set_superset_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = true;"),
        "set_superset_reif must be true for a forced superset, got: {output}"
    );
}

#[test]
fn test_set_superset_reif_forced_non_superset_false() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_superset_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = false;"),
        "set_superset_reif must be false for a forced non-superset, got: {output}"
    );
}

#[test]
fn test_set_superset_reif_forced_non_superset_true_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_superset_reif(s1, s2, r);\n\
        constraint bool_eq(r, true);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_superset_reif must reject true for a forced non-superset, got: {output}"
    );
}

// --- set_le_reif tests ---

#[test]
fn test_set_le_reif_forced_proper_prefix_true() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 2);\n\
        constraint set_le_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = true;"),
        "set_le_reif must be true for a forced sorted-list prefix, got: {output}"
    );
}

#[test]
fn test_set_le_reif_forced_lexicographically_greater_false() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_le_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = false;"),
        "set_le_reif must be false for a lexicographically greater left set, got: {output}"
    );
}

#[test]
fn test_set_le_reif_forced_lexicographically_greater_true_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_le_reif(s1, s2, r);\n\
        constraint bool_eq(r, true);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_le_reif must reject true for a lexicographically greater left set, got: {output}"
    );
}

// --- set_lt_reif tests ---

#[test]
fn test_set_lt_reif_forced_proper_prefix_true() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 2);\n\
        constraint set_lt_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = true;"),
        "set_lt_reif must be true for a forced sorted-list prefix, got: {output}"
    );
}

#[test]
fn test_set_lt_reif_forced_proper_prefix_false_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_in(two, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 2);\n\
        constraint set_lt_reif(s1, s2, r);\n\
        constraint bool_eq(r, false);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_lt_reif must reject false for a forced sorted-list prefix, got: {output}"
    );
}

#[test]
fn test_set_lt_reif_forced_equal_sets_false() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        constraint set_in(one, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_lt_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = false;"),
        "set_lt_reif must be false for equal forced sets, got: {output}"
    );
}

#[test]
fn test_set_lt_reif_forced_lexicographically_greater_false() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r :: output_var;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_lt_reif(s1, s2, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("r = false;"),
        "set_lt_reif must be false for a lexicographically greater left set, got: {output}"
    );
}

#[test]
fn test_set_lt_reif_forced_lexicographically_greater_true_unsat() {
    let fzn = "\
        var set of 1..2: s1;\n\
        var set of 1..2: s2;\n\
        var bool: r;\n\
        var 1..1: one;\n\
        var 2..2: two;\n\
        constraint set_in(two, s1);\n\
        constraint set_in(one, s2);\n\
        constraint set_card(s1, 1);\n\
        constraint set_card(s2, 1);\n\
        constraint set_lt_reif(s1, s2, r);\n\
        constraint bool_eq(r, true);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "set_lt_reif must reject true for a lexicographically greater left set, got: {output}"
    );
}

// --- set_in_reif tests ---

#[test]
fn test_set_in_reif_sparse_true() {
    // r ↔ (x ∈ {1, 3}), x = 3 → r = true.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, {1, 3}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_sparse_false() {
    // r ↔ (x ∈ {1, 3}), x = 2 → r = false.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, {1, 3}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_interval_true() {
    // r ↔ (x ∈ 1..3), x = 2 → r = true.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, 1..3, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_interval_false() {
    // r ↔ (x ∈ 1..3), x = 5 → r = false.
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 5);\n\
        constraint set_in_reif(x, 1..3, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_interval_with_minimum_lower_bound() {
    let fzn = "\
        var 0..0: x;\n\
        var bool: r;\n\
        constraint set_in_reif(x, -9223372036854775808..0, r);\n\
        constraint bool_eq(r, true);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn test_set_in_reif_variable_domain_is_bounded_before_table_allocation() {
    let fzn = "\
        var 0..1048576: x;\n\
        var set of 0..0: s;\n\
        var bool: r;\n\
        constraint set_in_reif(x, s, r);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    let err = ctx
        .build_model(&model)
        .expect_err("oversized element table must be rejected");
    assert!(err.to_string().contains("exceeding"), "{err}");
}

#[test]
fn test_set_in_reif_does_not_drop_nonconstant_set_elements() {
    let fzn = "\
        var 0..1: x;\n\
        var bool: r;\n\
        constraint set_in_reif(x, {missing}, r);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let mut ctx = CpContext::new();
    let err = ctx
        .build_model(&model)
        .expect_err("nonconstant set element must be rejected");
    assert!(err.to_string().contains("constant set element"), "{err}");
}

// --- set_in_reif with empty set ---

#[test]
fn test_set_in_reif_empty_set() {
    // r ↔ (x ∈ {}), x = 3 → r = false (empty set has no members).
    let fzn = "\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, {}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_empty_set() {
    // Named empty set parameter: S = {}, x = 3 → r = false.
    let fzn = "\
        set of int: S = {};\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

// --- set_in_reif with named set parameter (Ident resolution) ---

#[test]
fn test_set_in_reif_ident_sparse_true() {
    // Named set parameter: S = {1, 3}, x = 3 → r = true.
    let fzn = "\
        set of int: S = {1, 3};\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_sparse_false() {
    // Named set parameter: S = {1, 3}, x = 2 → r = false.
    let fzn = "\
        set of int: S = {1, 3};\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_range_true() {
    // Named set parameter: S = 1..3, x = 2 → r = true.
    let fzn = "\
        set of int: S = 1..3;\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 2);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_ident_range_false() {
    // Named set parameter: S = 1..3, x = 5 → r = false.
    let fzn = "\
        set of int: S = 1..3;\n\
        var 1..7: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 5);\n\
        constraint set_in_reif(x, S, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

// --- set_in_reif with large domain (indicator variable path) ---

#[test]
fn test_set_in_reif_large_domain_true() {
    // Domain > 10000 forces indicator variable path.
    // r ↔ (x ∈ {100, 500}), x = 500 → r = true.
    let fzn = "\
        var 1..20000: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 500);\n\
        constraint set_in_reif(x, {100, 500}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_set_in_reif_large_domain_false() {
    // Domain > 10000 forces indicator variable path.
    // r ↔ (x ∈ {100, 500}), x = 300 → r = false.
    let fzn = "\
        var 1..20000: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 300);\n\
        constraint set_in_reif(x, {100, 500}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_set_in_reif_large_domain_single_element() {
    // Single element in large domain: r ↔ (x ∈ {42}), x = 42 → r = true.
    let fzn = "\
        var 1..11000: x :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(x, 42);\n\
        constraint set_in_reif(x, {42}, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

// --- int_lin_ne_reif tests ---

#[test]
fn test_int_lin_ne_reif_true() {
    // r ↔ (x + y ≠ 0), x = 0, y = 1 → r = true.
    let fzn = "\
        var 0..0: x :: output_var;\n\
        var -1..1: y :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_eq(y, 1);\n\
        constraint int_lin_ne_reif([1, 1], [x, y], 0, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

#[test]
fn test_int_lin_ne_reif_false() {
    // r ↔ (x + y ≠ 0), x = 0, y = 0 → r = false.
    let fzn = "\
        var 0..0: x :: output_var;\n\
        var 0..0: y :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint int_lin_ne_reif([1, 1], [x, y], 0, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

// --- array_int_maximum tests ---

#[test]
fn test_array_int_maximum() {
    // r = max([a, b]), a = 3, b = 7 → r = 7.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 3);\n\
        constraint int_eq(b, 7);\n\
        constraint array_int_maximum(r, [a, b]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 7;"), "output: {output}");
}

#[test]
fn test_array_int_maximum_three() {
    // r = max([2, 8, 5]) → r = 8.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 2);\n\
        constraint int_eq(b, 8);\n\
        constraint int_eq(c, 5);\n\
        constraint array_int_maximum(r, [a, b, c]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 8;"), "output: {output}");
}

// --- array_int_minimum tests ---

#[test]
fn test_array_int_minimum() {
    // r = min([a, b]), a = 3, b = 7 → r = 3.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 3);\n\
        constraint int_eq(b, 7);\n\
        constraint array_int_minimum(r, [a, b]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 3;"), "output: {output}");
}

#[test]
fn test_array_int_minimum_three() {
    // r = min([9, 4, 6]) → r = 4.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        var 1..10: r :: output_var;\n\
        constraint int_eq(a, 9);\n\
        constraint int_eq(b, 4);\n\
        constraint int_eq(c, 6);\n\
        constraint array_int_minimum(r, [a, b, c]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = 4;"), "output: {output}");
}

// --- Variable RHS linear test ---

#[test]
fn test_linear_eq_variable_rhs() {
    // bool_lin_eq([-1, 2, 3], [x1, x2, x3], eq) where eq is a variable.
    let fzn = "\
        array [1..3] of int: cs = [-1, 2, 3];\n\
        var bool: x1 :: output_var;\n\
        var bool: x2 :: output_var;\n\
        var bool: x3 :: output_var;\n\
        var 1..3: eq :: output_var;\n\
        constraint bool_lin_eq(cs, [x1, x2, x3], eq);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    // Verify the equation holds: -1*x1 + 2*x2 + 3*x3 = eq
    let mut vals: HashMap<&str, i64> = HashMap::new();
    for line in output.lines() {
        for name in &["x1", "x2", "x3", "eq"] {
            if let Some(rest) = line.strip_prefix(&format!("{name} = ")) {
                if let Some(val_str) = rest.strip_suffix(';') {
                    let v = match val_str {
                        "true" => 1,
                        "false" => 0,
                        s => s.parse().unwrap(),
                    };
                    vals.insert(name, v);
                }
            }
        }
    }
    assert_eq!(vals.len(), 4, "should find all 4 values, output:\n{output}");
    let lhs = -vals["x1"] + 2 * vals["x2"] + 3 * vals["x3"];
    assert_eq!(
        lhs, vals["eq"],
        "equation should hold: {lhs} != {}",
        vals["eq"]
    );
}

// --- bool_and_reif tests ---

#[test]
fn test_bool_and_reif() {
    // r ↔ (a ∧ b), a = true, b = false → r = false.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, false);\n\
        constraint bool_and_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_bool_and_reif_true() {
    // r ↔ (a ∧ b), a = true, b = true → r = true.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, true);\n\
        constraint bool_and_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

// --- bool_or_reif tests ---

#[test]
fn test_bool_or_reif() {
    // r ↔ (a ∨ b), a = false, b = false → r = false.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, false);\n\
        constraint bool_eq(b, false);\n\
        constraint bool_or_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = false;"), "output: {output}");
}

#[test]
fn test_bool_or_reif_true() {
    // r ↔ (a ∨ b), a = false, b = true → r = true.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(a, false);\n\
        constraint bool_eq(b, true);\n\
        constraint bool_or_reif(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("r = true;"), "output: {output}");
}

// --- circuit tests ---

#[test]
fn singleton_circuit_requires_its_self_loop() {
    let fzn = "\
        var 1..2: successor;\n\
        constraint fzn_circuit([successor]);\n\
        constraint int_eq(successor, 2);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn declared_zero_based_circuit_uses_its_array_index_set() {
    let fzn = "\
        var 0..1: successor0;\n\
        var 0..1: successor1;\n\
        array [0..1] of var int: successors = [successor0, successor1];\n\
        constraint fzn_circuit(successors);\n\
        constraint int_eq(successor0, 1);\n\
        constraint int_eq(successor1, 0);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn inline_circuit_does_not_infer_node_ids_from_shifted_domains() {
    let fzn = "\
        var 2..3: successor1;\n\
        var 2..3: successor2;\n\
        constraint fzn_circuit([successor1, successor2]);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn extreme_successor_bounds_do_not_shift_the_circuit_index_set() {
    let fzn = "\
        var 9223372036854775807..9223372036854775807: x;\n\
        var 9223372036854775807..9223372036854775807: y;\n\
        constraint fzn_circuit([x, y]);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Unsat));
}

#[test]
fn quadratic_global_decompositions_have_a_checked_work_limit() {
    let fzn = "\
        array [1..1025] of var 1..1025: x;\n\
        array [1..1025] of var 1..1025: y;\n\
        array [1..1025] of var 1..1025: dx;\n\
        array [1..1025] of var 1..1025: dy;\n\
        constraint fzn_circuit(x);\n\
        constraint fzn_inverse(x, y);\n\
        constraint fzn_diffn(x, y, dx, dy);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let unsupported = super::unsupported_constraints(&model).expect("translation must fail closed");
    assert_eq!(unsupported, ["fzn_circuit", "fzn_inverse", "fzn_diffn"]);
}

#[test]
fn test_circuit_4() {
    // circuit([x1, x2, x3, x4]): Hamiltonian cycle on 4 nodes.
    let fzn = "\
        var 1..4: x1 :: output_var;\n\
        var 1..4: x2 :: output_var;\n\
        var 1..4: x3 :: output_var;\n\
        var 1..4: x4 :: output_var;\n\
        constraint fzn_circuit([x1, x2, x3, x4]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    // Parse the solution and verify it forms a single cycle
    let vals = parse_int_values(&output, &["x1", "x2", "x3", "x4"]);
    assert_eq!(vals.len(), 4, "should find all 4 values, output:\n{output}");
    // No self-loops
    for i in 0..4 {
        let name = &["x1", "x2", "x3", "x4"][i];
        assert_ne!(vals[name], (i + 1) as i64, "no self-loop at {name}");
    }
    // All different
    let mut seen: Vec<i64> = vals.values().copied().collect();
    seen.sort_unstable();
    assert_eq!(seen, [1, 2, 3, 4], "must be a permutation");
    // Verify single cycle: starting from node 1, follow successors, must visit all nodes
    let mut visited = [false; 4];
    let mut current = 0; // node 1 (0-indexed)
    for _ in 0..4 {
        assert!(!visited[current], "revisiting node {}", current + 1);
        visited[current] = true;
        let succ = vals[&["x1", "x2", "x3", "x4"][current]] as usize - 1;
        current = succ;
    }
    assert_eq!(current, 0, "cycle must return to node 1");
    assert!(visited.iter().all(|&v| v), "all nodes must be visited");
}

#[test]
fn test_circuit_no_subcycles() {
    // circuit([x1, x2, x3, x4]) with x1=2, x2=1 forced.
    // Without circuit, this allows subcycles {1,2} + {3,4}.
    // With circuit, nodes 3 and 4 must connect to/from the {1,2} chain.
    let fzn = "\
        var 1..4: x1 :: output_var;\n\
        var 1..4: x2 :: output_var;\n\
        var 1..4: x3 :: output_var;\n\
        var 1..4: x4 :: output_var;\n\
        constraint fzn_circuit([x1, x2, x3, x4]);\n\
        constraint int_eq(x1, 2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    let vals = parse_int_values(&output, &["x1", "x2", "x3", "x4"]);
    assert_eq!(vals["x1"], 2);
    // x2 cannot be 1 (would create subcycle {1,2}), must link to 3 or 4
    assert_ne!(vals["x2"], 1, "x2=1 would create subcycle {{1,2}}");
}

#[test]
fn test_circuit_rejects_out_of_range_successor() {
    // A circuit successor array is a permutation of its declared index set.
    // The MTZ element path constrains non-root successors, but the root
    // successor also needs an explicit range guard.
    let fzn = "\
        var 4..4: x1;\n\
        var 3..3: x2;\n\
        var 1..1: x3;\n\
        constraint fzn_circuit([x1, x2, x3]);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNSATISFIABLE====="),
        "out-of-range circuit successor should be UNSAT, got: {output}"
    );
}

// --- inverse tests ---

#[test]
fn declared_zero_based_inverse_uses_both_array_index_sets() {
    let fzn = "\
        var 1..1: x0;\n\
        var 0..0: x1;\n\
        var 1..1: y0;\n\
        var 0..0: y1;\n\
        array [0..1] of var int: x = [x0, x1];\n\
        array [0..1] of var int: y = [y0, y1];\n\
        constraint fzn_inverse(x, y);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn arbitrary_offset_inverse_channels_between_opposite_index_sets() {
    // x[5]=9, x[6]=8 is inverted by y[8]=6, y[9]=5.
    let fzn = "\
        var 9..9: x5;\n\
        var 8..8: x6;\n\
        var 6..6: y8;\n\
        var 5..5: y9;\n\
        array [5..6] of var int: x = [x5, x6];\n\
        array [8..9] of var int: y = [y8, y9];\n\
        constraint fzn_inverse(x, y);\n\
        solve satisfy;\n";
    assert!(matches!(parse_and_solve(fzn), CpSolveResult::Sat(_)));
}

#[test]
fn inverse_rejects_mismatched_array_cardinalities() {
    let fzn = "\
        var 1..2: x;\n\
        var 1..2: y1;\n\
        var 1..2: y2;\n\
        constraint fzn_inverse([x], [y1, y2]);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let err = super::unsupported_constraints(&model)
        .expect_err("inverse arrays of different lengths must be rejected");
    assert!(matches!(
        err,
        crate::error::Fzn2smtError::InverseArrayLengthMismatch { left: 1, right: 2 }
    ));
}

#[test]
fn test_inverse_3() {
    // inverse(x, y): x[y[i]] = i and y[x[i]] = i for all i.
    let fzn = "\
        var 1..3: x1 :: output_var;\n\
        var 1..3: x2 :: output_var;\n\
        var 1..3: x3 :: output_var;\n\
        var 1..3: y1 :: output_var;\n\
        var 1..3: y2 :: output_var;\n\
        var 1..3: y3 :: output_var;\n\
        constraint fzn_inverse([x1, x2, x3], [y1, y2, y3]);\n\
        constraint int_eq(x1, 3);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    let vals = parse_int_values(&output, &["x1", "x2", "x3", "y1", "y2", "y3"]);
    assert_eq!(vals.len(), 6, "should find all 6 values, output:\n{output}");
    assert_eq!(vals["x1"], 3);
    // Verify inverse property: x[y[i]] = i
    let x = [vals["x1"], vals["x2"], vals["x3"]];
    let y = [vals["y1"], vals["y2"], vals["y3"]];
    for i in 0..3usize {
        let expected = (i + 1) as i64;
        let yi = y[i] as usize - 1;
        assert_eq!(
            x[yi],
            expected,
            "x[y[{}]] = {} (expected {})",
            i + 1,
            x[yi],
            expected
        );
        let xi = x[i] as usize - 1;
        assert_eq!(
            y[xi],
            expected,
            "y[x[{}]] = {} (expected {})",
            i + 1,
            y[xi],
            expected
        );
    }
}

/// Parse integer values from DZN output.
fn parse_int_values<'a>(output: &str, names: &'a [&'a str]) -> HashMap<&'a str, i64> {
    let mut vals = HashMap::new();
    for line in output.lines() {
        for &name in names {
            if let Some(rest) = line.strip_prefix(&format!("{name} = ")) {
                if let Some(val_str) = rest.strip_suffix(';') {
                    let v: i64 = val_str.parse().unwrap_or_else(|_| match val_str {
                        "true" => 1,
                        "false" => 0,
                        _ => panic!("cannot parse {val_str}"),
                    });
                    vals.insert(name, v);
                }
            }
        }
    }
    vals
}
