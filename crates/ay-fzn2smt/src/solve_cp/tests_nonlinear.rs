// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Tests for nonlinear, table-based, and Big-M encoded constraints.
// Split from tests.rs to stay under the 1000-line file limit.

use ay_cp::engine::CpSolveResult;

use super::tests::{parse_and_solve, solve_cp_output};

#[test]
fn oversized_nonlinear_big_m_is_a_typed_error() {
    let fzn = "\
        var -9223372036854775808..0: x;\n\
        var 0..9223372036854775807: absolute;\n\
        constraint int_abs(x, absolute);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let err = super::unsupported_constraints(&model)
        .expect_err("an unrepresentable nonlinear Big-M coefficient must be rejected");
    assert!(
        matches!(
            err,
            crate::error::Fzn2smtError::LinearEncodingOverflow { .. }
                | crate::error::Fzn2smtError::InvalidCpIntegerDomain { .. }
        ),
        "unexpected error: {err}"
    );
}

#[test]
fn oversized_reified_linear_encoding_is_a_typed_error() {
    let fzn = "\
        var -9223372036854775808..9223372036854775807: x;\n\
        var -9223372036854775808..9223372036854775807: y;\n\
        var bool: r;\n\
        constraint int_le_reif(x, y, r);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let err = super::unsupported_constraints(&model)
        .expect_err("an unrepresentable reified linear encoding must be rejected");
    assert!(
        matches!(
            err,
            crate::error::Fzn2smtError::LinearEncodingOverflow { .. }
                | crate::error::Fzn2smtError::InvalidCpIntegerDomain { .. }
        ),
        "unexpected error: {err}"
    );
}

#[test]
fn wide_table_domain_is_rejected_without_overflow() {
    let fzn = "\
        var -9223372036854775808..9223372036854775807: x;\n\
        var -9223372036854775808..9223372036854775807: q;\n\
        constraint int_div(x, 2, q);\n\
        solve satisfy;\n";
    let model = ay_flatzinc_parser::parse_flatzinc(fzn).expect("parse failed");
    let error = super::unsupported_constraints(&model)
        .expect_err("an unrepresentable CP domain must fail closed");
    assert!(matches!(
        error,
        crate::error::Fzn2smtError::InvalidCpIntegerDomain { .. }
    ));
}

// --- int_times tests ---

#[test]
fn test_int_times_const() {
    // c = 3 * x, x = 4 → c = 12.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var 1..30: c :: output_var;\n\
        constraint int_eq(x, 4);\n\
        constraint int_times(3, x, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 12;"), "output: {output}");
}

#[test]
fn test_int_times_var() {
    // c = x * y, x = 3, y = 5 → c = 15.
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var 1..10: y :: output_var;\n\
        var 1..100: c :: output_var;\n\
        constraint int_eq(x, 3);\n\
        constraint int_eq(y, 5);\n\
        constraint int_times(x, y, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 15;"), "output: {output}");
}

// --- int_abs tests ---

#[test]
fn test_int_abs_positive() {
    // c = |a|, a = 5 → c = 5.
    let fzn = "\
        var -10..10: a :: output_var;\n\
        var 0..10: c :: output_var;\n\
        constraint int_eq(a, 5);\n\
        constraint int_abs(a, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 5;"), "output: {output}");
}

#[test]
fn test_int_abs_negative() {
    // c = |a|, a = -7 → c = 7.
    let fzn = "\
        var -10..10: a :: output_var;\n\
        var 0..10: c :: output_var;\n\
        constraint int_eq(a, -7);\n\
        constraint int_abs(a, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 7;"), "output: {output}");
}

// --- int_min tests ---

#[test]
fn test_int_min() {
    // c = min(a, b), a = 3, b = 7 → c = 3.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        constraint int_eq(a, 3);\n\
        constraint int_eq(b, 7);\n\
        constraint int_min(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 3;"), "output: {output}");
}

#[test]
fn test_int_min_reversed() {
    // c = min(a, b), a = 8, b = 2 → c = 2.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        constraint int_eq(a, 8);\n\
        constraint int_eq(b, 2);\n\
        constraint int_min(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 2;"), "output: {output}");
}

// --- int_max tests ---

#[test]
fn test_int_max() {
    // c = max(a, b), a = 3, b = 7 → c = 7.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        constraint int_eq(a, 3);\n\
        constraint int_eq(b, 7);\n\
        constraint int_max(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 7;"), "output: {output}");
}

#[test]
fn test_int_max_reversed() {
    // c = max(a, b), a = 9, b = 4 → c = 9.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 1..10: c :: output_var;\n\
        constraint int_eq(a, 9);\n\
        constraint int_eq(b, 4);\n\
        constraint int_max(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 9;"), "output: {output}");
}

// --- int_lin_ne tests ---

#[test]
fn test_int_lin_ne() {
    // x != 5, x in 5..5 → UNSAT.
    let fzn = "\
        var 5..5: x :: output_var;\n\
        constraint int_lin_ne([1], [x], 5);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Unsat => {}
        other => panic!("expected Unsat, got {other:?}"),
    }
}

#[test]
fn test_int_lin_ne_sat() {
    // x + y != 10, x=3, y in 1..10 → y != 7.
    let fzn = "\
        var 3..3: x :: output_var;\n\
        var 1..10: y :: output_var;\n\
        constraint int_lin_ne([1, 1], [x, y], 10);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    // y should not be 7
    assert!(
        !output.contains("y = 7;"),
        "y should not be 7, output: {output}"
    );
}

// --- bool_xor tests ---

#[test]
fn test_bool_xor() {
    // c = a XOR b, a = true, b = false → c = true.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: c :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, false);\n\
        constraint bool_xor(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = true;"), "output: {output}");
}

// --- int_div tests ---

#[test]
fn test_int_div_const_divisor() {
    // c = a div 3, a = 10 → c = 3.
    let fzn = "\
        var 1..20: a :: output_var;\n\
        var 0..20: c :: output_var;\n\
        constraint int_eq(a, 10);\n\
        constraint int_div(a, 3, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 3;"), "output: {output}");
}

#[test]
fn test_int_div_identity() {
    // c = a div 1, a = 7 → c = 7.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: c :: output_var;\n\
        constraint int_eq(a, 7);\n\
        constraint int_div(a, 1, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 7;"), "output: {output}");
}

#[test]
fn test_int_div_negate() {
    // c = a div (-1), a = 5 → c = -5.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var -10..10: c :: output_var;\n\
        constraint int_eq(a, 5);\n\
        constraint int_div(a, -1, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = -5;"), "output: {output}");
}

#[test]
fn test_int_div_var() {
    // c = a div b, a = 7, b = 2 → c = 3.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 0..10: c :: output_var;\n\
        constraint int_eq(a, 7);\n\
        constraint int_eq(b, 2);\n\
        constraint int_div(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 3;"), "output: {output}");
}

#[test]
fn test_int_div_negative() {
    // c = a div b, a = -7, b = 2 → c = -3 (truncation towards zero).
    let fzn = "\
        var -10..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var -10..10: c :: output_var;\n\
        constraint int_eq(a, -7);\n\
        constraint int_eq(b, 2);\n\
        constraint int_div(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = -3;"), "output: {output}");
}

// --- int_mod tests ---

#[test]
fn test_int_mod_const() {
    // c = a mod 3, a = 10 → c = 1.
    let fzn = "\
        var 1..20: a :: output_var;\n\
        var 0..20: c :: output_var;\n\
        constraint int_eq(a, 10);\n\
        constraint int_mod(a, 3, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 1;"), "output: {output}");
}

#[test]
fn test_int_mod_var() {
    // c = a mod b, a = 10, b = 4 → c = 2.
    let fzn = "\
        var 1..20: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 0..10: c :: output_var;\n\
        constraint int_eq(a, 10);\n\
        constraint int_eq(b, 4);\n\
        constraint int_mod(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 2;"), "output: {output}");
}

#[test]
fn test_int_mod_negative() {
    // c = a mod b, a = -7, b = 3 → c = -1 (truncation remainder).
    let fzn = "\
        var -10..10: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var -10..10: c :: output_var;\n\
        constraint int_eq(a, -7);\n\
        constraint int_eq(b, 3);\n\
        constraint int_mod(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = -1;"), "output: {output}");
}

#[test]
fn test_int_mod_exact() {
    // c = a mod b, a = 9, b = 3 → c = 0.
    let fzn = "\
        var 1..20: a :: output_var;\n\
        var 1..10: b :: output_var;\n\
        var 0..10: c :: output_var;\n\
        constraint int_eq(a, 9);\n\
        constraint int_eq(b, 3);\n\
        constraint int_mod(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 0;"), "output: {output}");
}

// --- int_pow tests ---

#[test]
fn test_int_pow_const_exp() {
    // c = a^2, a = 5 → c = 25.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 0..100: c :: output_var;\n\
        constraint int_eq(a, 5);\n\
        constraint int_pow(a, 2, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 25;"), "output: {output}");
}

#[test]
fn test_int_pow_zero_exp() {
    // c = a^0, a = 7 → c = 1.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 0..10: c :: output_var;\n\
        constraint int_eq(a, 7);\n\
        constraint int_pow(a, 0, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 1;"), "output: {output}");
}

#[test]
fn test_int_pow_one_exp() {
    // c = a^1, a = 6 → c = 6.
    let fzn = "\
        var 1..10: a :: output_var;\n\
        var 0..10: c :: output_var;\n\
        constraint int_eq(a, 6);\n\
        constraint int_pow(a, 1, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 6;"), "output: {output}");
}

#[test]
fn test_int_pow_var() {
    // c = a^b, a = 2, b = 3 → c = 8.
    let fzn = "\
        var 1..5: a :: output_var;\n\
        var 0..5: b :: output_var;\n\
        var 0..200: c :: output_var;\n\
        constraint int_eq(a, 2);\n\
        constraint int_eq(b, 3);\n\
        constraint int_pow(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 8;"), "output: {output}");
}

#[test]
fn test_int_pow_cube() {
    // c = a^3, a = 3 → c = 27.
    let fzn = "\
        var 1..5: a :: output_var;\n\
        var 0..200: c :: output_var;\n\
        constraint int_eq(a, 3);\n\
        constraint int_pow(a, 3, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 27;"), "output: {output}");
}

#[test]
fn test_bool_xor_same() {
    // c = a XOR b, a = true, b = true → c = false.
    let fzn = "\
        var bool: a :: output_var;\n\
        var bool: b :: output_var;\n\
        var bool: c :: output_var;\n\
        constraint bool_eq(a, true);\n\
        constraint bool_eq(b, true);\n\
        constraint bool_xor(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = false;"), "output: {output}");
}

// --- Checked arithmetic overflow tests (#5467) ---

/// int_times with negative operands near domain boundaries.
/// Verifies that checked_mul skips overflow tuples instead of panicking.
#[test]
fn test_int_times_negative_operands() {
    // c = x * y, x = -3, y = -4 -> c = 12.
    let fzn = "\
        var -5..5: x :: output_var;\n\
        var -5..5: y :: output_var;\n\
        var -25..25: c :: output_var;\n\
        constraint int_eq(x, -3);\n\
        constraint int_eq(y, -4);\n\
        constraint int_times(x, y, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 12;"), "output: {output}");
}

/// int_div with -128 / -1 = 128 (small-scale analogue of i64::MIN / -1).
#[test]
fn test_int_div_min_neg1_no_panic() {
    let fzn = "\
        var -128..127: a :: output_var;\n\
        var -1..-1: b :: output_var;\n\
        var -128..128: c :: output_var;\n\
        constraint int_eq(a, -128);\n\
        constraint int_div(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 128;"), "output: {output}");
}

/// int_mod with negative dividend and divisor uses checked_rem.
#[test]
fn test_int_mod_negative_dividend_and_divisor() {
    // -7 % -3 = -1 (truncation remainder).
    let fzn = "\
        var -10..10: a :: output_var;\n\
        var -5..-1: b :: output_var;\n\
        var -10..10: c :: output_var;\n\
        constraint int_eq(a, -7);\n\
        constraint int_eq(b, -3);\n\
        constraint int_mod(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = -1;"), "output: {output}");
}

// --- Edge case tests for #5468: int_times, int_div, int_mod ---

/// int_times with zero: 0 * x = 0.
#[test]
fn test_int_times_zero_left() {
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var -10..10: c :: output_var;\n\
        constraint int_eq(x, 7);\n\
        constraint int_times(0, x, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 0;"), "output: {output}");
}

/// int_times with zero: x * 0 = 0.
#[test]
fn test_int_times_zero_right() {
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var -10..10: c :: output_var;\n\
        constraint int_eq(x, 5);\n\
        constraint int_times(x, 0, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 0;"), "output: {output}");
}

/// int_times with identity: 1 * x = x.
#[test]
fn test_int_times_identity() {
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var 1..10: c :: output_var;\n\
        constraint int_eq(x, 8);\n\
        constraint int_times(1, x, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 8;"), "output: {output}");
}

/// int_times negative constant: (-3) * 5 = -15.
#[test]
fn test_int_times_neg_const() {
    let fzn = "\
        var 1..10: x :: output_var;\n\
        var -30..30: c :: output_var;\n\
        constraint int_eq(x, 5);\n\
        constraint int_times(-3, x, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = -15;"), "output: {output}");
}

/// int_times: large domain falls back to mark_unsupported → UNKNOWN.
#[test]
fn test_int_times_large_domain_unsupported() {
    // Both vars have domain 200, cross-product = 200*200 = 40000 > 10000.
    let fzn = "\
        var 1..200: x :: output_var;\n\
        var 1..200: y :: output_var;\n\
        var 1..40000: c :: output_var;\n\
        constraint int_times(x, y, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("=====UNKNOWN====="),
        "should be UNKNOWN for large domain, output: {output}"
    );
}

/// int_div: 0 / x = 0.
#[test]
fn test_int_div_zero_dividend() {
    let fzn = "\
        var -5..5: a :: output_var;\n\
        var 1..5: b :: output_var;\n\
        var -5..5: c :: output_var;\n\
        constraint int_eq(a, 0);\n\
        constraint int_eq(b, 3);\n\
        constraint int_div(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 0;"), "output: {output}");
}

/// int_div: both negative: -10 / -3 = 3 (truncation towards zero).
#[test]
fn test_int_div_both_negative() {
    let fzn = "\
        var -10..-1: a :: output_var;\n\
        var -5..-1: b :: output_var;\n\
        var -10..10: c :: output_var;\n\
        constraint int_eq(a, -10);\n\
        constraint int_eq(b, -3);\n\
        constraint int_div(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 3;"), "output: {output}");
}

/// int_mod: x % 1 = 0 for any x.
#[test]
fn test_int_mod_by_one() {
    let fzn = "\
        var 1..20: a :: output_var;\n\
        var -5..5: c :: output_var;\n\
        constraint int_eq(a, 13);\n\
        constraint int_mod(a, 1, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 0;"), "output: {output}");
}

/// int_mod: 0 % x = 0 for any nonzero x.
#[test]
fn test_int_mod_zero_dividend() {
    let fzn = "\
        var -5..5: a :: output_var;\n\
        var 1..5: b :: output_var;\n\
        var -5..5: c :: output_var;\n\
        constraint int_eq(a, 0);\n\
        constraint int_eq(b, 4);\n\
        constraint int_mod(a, b, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 0;"), "output: {output}");
}

/// Table constraint with negative values: multiplication of negative numbers.
#[test]
fn test_int_times_table_negatives() {
    // x in [-3..3], y in [-3..3], c = x * y.
    // Check specific values: (-2) * (-3) = 6, (-2) * 3 = -6.
    let fzn = "\
        var -3..3: x :: output_var;\n\
        var -3..3: y :: output_var;\n\
        var -9..9: c :: output_var;\n\
        constraint int_eq(x, -2);\n\
        constraint int_eq(y, -3);\n\
        constraint int_times(x, y, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 6;"), "output: {output}");
}

/// Table constraint: single valid tuple (tight constraint).
#[test]
fn test_int_times_single_tuple() {
    // x=3, y=3 → c must be 9. Only one valid assignment.
    let fzn = "\
        var 3..3: x :: output_var;\n\
        var 3..3: y :: output_var;\n\
        var 9..9: c :: output_var;\n\
        constraint int_times(x, y, c);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(output.contains("c = 9;"), "output: {output}");
}

// --- Regression tests for #5685: Big-M soundness ---

/// int_lin_ne with rhs below sum range must be trivially SAT (#5685).
/// Before the fix, M = sum_max - sum_min + 1 was too small when rhs < sum_min,
/// causing the Big-M relaxation to overconstrain and produce false UNSAT.
#[test]
fn test_int_lin_ne_rhs_below_range() {
    // x in [5..10], constraint x != 3. Trivially SAT since 3 < 5.
    let fzn = "\
        var 5..10: x :: output_var;\n\
        constraint int_lin_ne([1], [x], 3);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// int_lin_ne with rhs above sum range must be trivially SAT (#5685).
#[test]
fn test_int_lin_ne_rhs_above_range() {
    // x in [1..5], constraint x != 100. Trivially SAT since 100 > 5.
    let fzn = "\
        var 1..5: x :: output_var;\n\
        constraint int_lin_ne([1], [x], 100);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Multi-variable int_lin_ne with rhs outside sum range (#5685).
/// 2*x + y, with x in [5..10], y in [1..3]: sum range is [11..23].
/// Constraint sum != 5 is trivially SAT since 5 < 11.
#[test]
fn test_int_lin_ne_multivar_rhs_below() {
    let fzn = "\
        var 5..10: x :: output_var;\n\
        var 1..3: y :: output_var;\n\
        constraint int_lin_ne([2, 1], [x, y], 5);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat, got {other:?}"),
    }
}

/// Ensure int_lin_ne still correctly excludes in-range values.
/// x in [1..3], constraint x != 2 → must produce x=1 or x=3.
#[test]
fn test_int_lin_ne_excludes_inrange() {
    let fzn = "\
        var 1..3: x :: output_var;\n\
        constraint int_lin_ne([1], [x], 2);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        !output.contains("x = 2;"),
        "x should not be 2, output: {output}"
    );
    assert!(
        output.contains("----------"),
        "should find a solution, output: {output}"
    );
}

/// int_ne_imp(a, b, r): r → (a ≠ b) regression test.
/// When r is forced to 1 and a,b have overlapping domains,
/// the encoding must force a ≠ b.
#[test]
fn test_int_ne_imp_forces_ne() {
    // r=1, a in [1..3], b in [1..3]: must have a ≠ b.
    let fzn = "\
        var 1..3: a :: output_var;\n\
        var 1..3: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(r, true);\n\
        constraint int_ne_imp(a, b, r);\n\
        solve satisfy;\n";
    let output = solve_cp_output(fzn, false);
    assert!(
        output.contains("----------"),
        "should find solution, output: {output}"
    );
    // Check that a and b are not equal
    for v in 1..=3 {
        let a_eq = output.contains(&format!("a = {v};"));
        let b_eq = output.contains(&format!("b = {v};"));
        assert!(!(a_eq && b_eq), "a and b should differ, output: {output}");
    }
}

/// int_ne_imp with r=0: should not constrain a,b at all.
#[test]
fn test_int_ne_imp_inactive() {
    // r=0, a=b=2: should be SAT (implication inactive).
    let fzn = "\
        var 2..2: a :: output_var;\n\
        var 2..2: b :: output_var;\n\
        var bool: r :: output_var;\n\
        constraint bool_eq(r, false);\n\
        constraint int_ne_imp(a, b, r);\n\
        solve satisfy;\n";
    match parse_and_solve(fzn) {
        CpSolveResult::Sat(_) => {}
        other => panic!("expected Sat (r=0 should not constrain), got {other:?}"),
    }
}
