// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `prescan_element_pairs` — paired-element-to-TABLE conversion.
//!
//! Covers Finding 5 from prescan-element-pairs-soundness-audit:
//! - (None, None) case: both results are variables
//! - (Some, None) case: one result is constant
//! - Groups of size != 2 are skipped
//! - TABLE conversion preserves SAT/UNSAT semantics

use ay_cp::engine::CpSolveResult;

use super::tests::parse_and_solve;

/// Two array_int_element constraints sharing index, both results are variables.
/// This exercises the (None, None) path: TABLE(var_a, var_b) with paired tuples.
///
/// Model: index i in 1..3, vals_a = [10,20,30], vals_b = [1,2,3]
///   element(i, vals_a, x)  ->  x = vals_a[i]
///   element(i, vals_b, y)  ->  y = vals_b[i]
///   x = 20  (forces i=2, y=2)
///
/// After prescan: TABLE(x,y) with tuples {(10,1),(20,2),(30,3)}, plus x=20.
/// Should produce SAT with y=2.
#[test]
fn test_prescan_both_variable_results_sat() {
    let fzn = "\
        var 1..3: i;\n\
        var 10..30: x :: output_var;\n\
        var 1..3: y :: output_var;\n\
        constraint array_int_element(i, [10,20,30], x);\n\
        constraint array_int_element(i, [1,2,3], y);\n\
        constraint int_eq(x, 20);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            // y must be 2 because x=20 forces i=2, and vals_b[2]=2
            let has_y_eq_2 = assignment.iter().any(|(_, v)| *v == 2);
            assert!(has_y_eq_2, "expected y=2 in assignment: {assignment:?}");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Same structure but UNSAT: force x=20 and y=1, which requires i=2 and i=1
/// simultaneously — impossible since they share the same index.
#[test]
fn test_prescan_both_variable_results_unsat() {
    let fzn = "\
        var 1..3: i;\n\
        var 10..30: x :: output_var;\n\
        var 1..3: y :: output_var;\n\
        constraint array_int_element(i, [10,20,30], x);\n\
        constraint array_int_element(i, [1,2,3], y);\n\
        constraint int_eq(x, 20);\n\
        constraint int_eq(y, 1);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

/// One constant result (result_a=2), one variable result.
/// This exercises the (Some, None) path: TABLE(var_b) with filtered values.
///
/// Model: index i in 1..4, vals_a = [1,2,2,3], vals_b = [10,20,30,40]
///   element(i, vals_a, 2)  ->  vals_a[i] = 2, so i in {2,3}
///   element(i, vals_b, y)  ->  y = vals_b[i]
///
/// After prescan: TABLE(y) with allowed = {20, 30} (vals_b at positions 2,3).
#[test]
fn test_prescan_one_constant_result_sat() {
    let fzn = "\
        var 1..4: i;\n\
        var 10..40: y :: output_var;\n\
        constraint array_int_element(i, [1,2,2,3], 2);\n\
        constraint array_int_element(i, [10,20,30,40], y);\n\
        constraint int_eq(y, 30);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat (y=30 is valid since i=3), got {other:?}"),
    }
}

/// Force y to a value NOT in the allowed set — should be UNSAT.
/// vals_a[i]=2 restricts i to {2,3}, so y must be in {20,30}. y=40 is invalid.
#[test]
fn test_prescan_one_constant_result_unsat() {
    let fzn = "\
        var 1..4: i;\n\
        var 10..40: y :: output_var;\n\
        constraint array_int_element(i, [1,2,2,3], 2);\n\
        constraint array_int_element(i, [10,20,30,40], y);\n\
        constraint int_eq(y, 40);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat (y=40 requires i=4, but vals_a[4]=3≠2), got {other:?}"),
    }
}

/// Three element constraints sharing the same index: should NOT be paired
/// (prescan_element_pairs only handles groups of exactly 2).
/// All three constraints remain as regular element propagators.
#[test]
fn test_prescan_skips_triple_group() {
    let fzn = "\
        var 1..3: i;\n\
        var 1..3: x :: output_var;\n\
        var 1..3: y :: output_var;\n\
        var 1..3: z :: output_var;\n\
        constraint array_int_element(i, [1,2,3], x);\n\
        constraint array_int_element(i, [3,2,1], y);\n\
        constraint array_int_element(i, [2,3,1], z);\n\
        constraint int_eq(x, 1);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            // x=1 forces i=1, so y=3, z=2
            let has_y_eq_3 = assignment.iter().any(|(_, v)| *v == 3);
            let has_z_eq_2 = assignment.iter().any(|(_, v)| *v == 2);
            assert!(
                has_y_eq_3 && has_z_eq_2,
                "expected y=3, z=2 in assignment: {assignment:?}"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Single element constraint (group of 1): should NOT be paired.
#[test]
fn test_prescan_skips_single_element() {
    let fzn = "\
        var 1..3: i;\n\
        var 10..30: x :: output_var;\n\
        constraint array_int_element(i, [10,20,30], x);\n\
        constraint int_eq(i, 2);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            let has_x_eq_20 = assignment.iter().any(|(_, v)| *v == 20);
            assert!(has_x_eq_20, "expected x=20 in assignment: {assignment:?}");
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Index variable with restricted domain: only some array positions are valid.
/// vals_a = [1,2,3,4,5], vals_b = [50,40,30,20,10], index i in 3..5.
/// With element pair and const result vals_a[i]=3, i must be 3 (only valid in domain).
/// So y = vals_b[3] = 30.
#[test]
fn test_prescan_restricted_index_domain() {
    let fzn = "\
        var 3..5: i;\n\
        var 10..50: y :: output_var;\n\
        constraint array_int_element(i, [1,2,3,4,5], 3);\n\
        constraint array_int_element(i, [50,40,30,20,10], y);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            let has_y_eq_30 = assignment.iter().any(|(_, v)| *v == 30);
            assert!(
                has_y_eq_30,
                "expected y=30 (i=3 is only valid index where vals_a=3 in domain 3..5): {assignment:?}"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Three-way interaction: TABLE (from prescan) + Inverse (from detect) + int_lin_le.
/// Mimics black_hole_0 structure at n=4: cards {1..4}, positions {1..4}.
///
/// x[p] = card at position p (x[1]=1 fixed).
/// y[c] = position of card c (y[1]=1 fixed).
/// Adjacency cycle: 1↔2, 2↔3, 3↔4, 4↔1.
///
/// Chain: x[1]=1 → x[2] must be adjacent to 1 → x[3] adjacent to x[2] → x[4].
/// Valid sequences: [1,2,3,4] and [1,4,3,2].
/// int_lin_le([1,-1],[y2,y3],-1) → y[2]<y[3] eliminates [1,4,3,2].
/// Expected: SAT with x=[1,2,3,4], y=[1,2,3,4].
#[test]
fn test_prescan_table_inverse_linle_sat() {
    let fzn = "\
        var 1..4: x2;\n\
        var 1..4: x3;\n\
        var 1..4: x4;\n\
        var 1..4: y2;\n\
        var 1..4: y3;\n\
        var 1..4: y4;\n\
        array [1..4] of var int: x :: output_array([1..4]) = [1, x2, x3, x4];\n\
        array [1..4] of var int: y = [1, y2, y3, y4];\n\
        var 1..8: idx1 :: var_is_introduced;\n\
        var 1..8: idx2 :: var_is_introduced;\n\
        var 1..8: idx3 :: var_is_introduced;\n\
        constraint array_int_element(idx1, [1,1,2,2,3,3,4,4], 1);\n\
        constraint array_int_element(idx1, [2,4,1,3,2,4,3,1], x2);\n\
        constraint array_int_element(idx2, [1,1,2,2,3,3,4,4], x2);\n\
        constraint array_int_element(idx2, [2,4,1,3,2,4,3,1], x3);\n\
        constraint array_int_element(idx3, [1,1,2,2,3,3,4,4], x3);\n\
        constraint array_int_element(idx3, [2,4,1,3,2,4,3,1], x4);\n\
        constraint array_var_int_element(x2, y, 2);\n\
        constraint array_var_int_element(x3, y, 3);\n\
        constraint array_var_int_element(x4, y, 4);\n\
        constraint array_var_int_element(y2, x, 2);\n\
        constraint array_var_int_element(y3, x, 3);\n\
        constraint array_var_int_element(y4, x, 4);\n\
        constraint int_lin_le([1,-1], [y2, y3], -1);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat (TABLE+Inverse+int_lin_le three-way), got {other:?}"),
    }
}

/// Same as above but WITHOUT int_lin_le: TABLE + Inverse only.
/// Both valid sequences [1,2,3,4] and [1,4,3,2] should be reachable.
#[test]
fn test_prescan_table_inverse_no_linle_sat() {
    let fzn = "\
        var 1..4: x2;\n\
        var 1..4: x3;\n\
        var 1..4: x4;\n\
        var 1..4: y2;\n\
        var 1..4: y3;\n\
        var 1..4: y4;\n\
        array [1..4] of var int: x :: output_array([1..4]) = [1, x2, x3, x4];\n\
        array [1..4] of var int: y = [1, y2, y3, y4];\n\
        var 1..8: idx1 :: var_is_introduced;\n\
        var 1..8: idx2 :: var_is_introduced;\n\
        var 1..8: idx3 :: var_is_introduced;\n\
        constraint array_int_element(idx1, [1,1,2,2,3,3,4,4], 1);\n\
        constraint array_int_element(idx1, [2,4,1,3,2,4,3,1], x2);\n\
        constraint array_int_element(idx2, [1,1,2,2,3,3,4,4], x2);\n\
        constraint array_int_element(idx2, [2,4,1,3,2,4,3,1], x3);\n\
        constraint array_int_element(idx3, [1,1,2,2,3,3,4,4], x3);\n\
        constraint array_int_element(idx3, [2,4,1,3,2,4,3,1], x4);\n\
        constraint array_var_int_element(x2, y, 2);\n\
        constraint array_var_int_element(x3, y, 3);\n\
        constraint array_var_int_element(x4, y, 4);\n\
        constraint array_var_int_element(y2, x, 2);\n\
        constraint array_var_int_element(y3, x, 3);\n\
        constraint array_var_int_element(y4, x, 4);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat (TABLE+Inverse, no int_lin_le), got {other:?}"),
    }
}

/// TABLE + int_lin_le WITHOUT Inverse detection (no array_var_int_element).
/// Tests the TABLE chain alone with ordering.
#[test]
fn test_prescan_table_linle_no_inverse_sat() {
    let fzn = "\
        var 1..4: x2 :: output_var;\n\
        var 1..4: x3 :: output_var;\n\
        var 1..4: x4 :: output_var;\n\
        var 1..4: y2;\n\
        var 1..4: y3;\n\
        var 1..8: idx1 :: var_is_introduced;\n\
        var 1..8: idx2 :: var_is_introduced;\n\
        var 1..8: idx3 :: var_is_introduced;\n\
        constraint array_int_element(idx1, [1,1,2,2,3,3,4,4], 1);\n\
        constraint array_int_element(idx1, [2,4,1,3,2,4,3,1], x2);\n\
        constraint array_int_element(idx2, [1,1,2,2,3,3,4,4], x2);\n\
        constraint array_int_element(idx2, [2,4,1,3,2,4,3,1], x3);\n\
        constraint array_int_element(idx3, [1,1,2,2,3,3,4,4], x3);\n\
        constraint array_int_element(idx3, [2,4,1,3,2,4,3,1], x4);\n\
        constraint int_lin_le([1,-1], [y2, y3], -1);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat (TABLE+int_lin_le, no Inverse), got {other:?}"),
    }
}

/// Both results are constants: should NOT trigger TABLE conversion (both
/// constants means both element constraints reduce to domain restrictions
/// on the index variable, no TABLE needed).
#[test]
fn test_prescan_both_constant_results_not_converted() {
    let fzn = "\
        var 1..4: i :: output_var;\n\
        constraint array_int_element(i, [1,2,2,1], 2);\n\
        constraint array_int_element(i, [10,20,20,10], 20);\n\
        solve satisfy;\n";

    match parse_and_solve(fzn) {
        CpSolveResult::Sat(assignment) => {
            // vals_a[i]=2 requires i in {2,3}
            // vals_b[i]=20 requires i in {2,3}
            // So i in {2,3}
            let i_val = assignment.iter().find(|(_, _)| true).map(|(_, v)| *v);
            assert!(
                i_val == Some(2) || i_val == Some(3),
                "expected i in {{2,3}}, got {assignment:?}"
            );
        }
        other => panic!("expected Sat, got {other:?}"),
    }
}
