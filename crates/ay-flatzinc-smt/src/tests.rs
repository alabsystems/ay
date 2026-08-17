// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
// Core tests for FlatZinc-to-SMT translation.
// Extended constraint coverage in tests_extended.rs.
// TranslateError tests in tests_error.rs.

use super::*;

fn translate_fzn(input: &str) -> TranslationResult {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect("translate failed")
}

fn translate_fzn_err(input: &str) -> TranslateError {
    let model = ay_flatzinc_parser::parse_flatzinc(input).expect("parse failed");
    translate(&model).expect_err("translation should fail")
}

// --- Variable declaration tests ---

#[test]
fn test_declare_bool_var() {
    let r = translate_fzn("var bool: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Bool)"));
}

#[test]
fn test_declare_int_var() {
    let r = translate_fzn("var int: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Int)"));
}

#[test]
fn test_declare_int_range_var() {
    let r = translate_fzn("var 1..10: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Int)"));
    assert!(r.smtlib.contains("(assert (>= x 1))"));
    assert!(r.smtlib.contains("(assert (<= x 10))"));
}

#[test]
fn test_declare_int_set_var() {
    let r = translate_fzn("var {1, 3, 5}: x;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const x Int)"));
    assert!(r.smtlib.contains("(assert (or (= x 1) (= x 3) (= x 5)))"));
}

#[test]
fn test_declare_array_var() {
    let r = translate_fzn("array [1..3] of var 1..5: q;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(declare-const q_1 Int)"));
    assert!(r.smtlib.contains("(declare-const q_2 Int)"));
    assert!(r.smtlib.contains("(declare-const q_3 Int)"));
    assert!(r.smtlib.contains("(assert (>= q_1 1))"));
    assert!(r.smtlib.contains("(assert (<= q_1 5))"));
}

#[test]
fn test_array_parameter_length_must_match_index_range() {
    let err = translate_fzn_err("array [1..2] of int: a = [10];\nsolve satisfy;\n");
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref message)
            if message.contains("array a") && message.contains("has 1 initializer elements")),
        "{err}"
    );
}

#[test]
fn test_array_variable_initializer_length_must_match_index_range() {
    let err =
        translate_fzn_err("var int: x;\narray [1..1] of var int: a = [x, x];\nsolve satisfy;\n");
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref message)
            if message.contains("array a") && message.contains("has 2 initializer elements")),
        "{err}"
    );
}

#[test]
fn test_set_array_variable_initializer_length_must_match_index_range() {
    let err = translate_fzn_err(
        "var set of 1..2: s;\n\
         array [1..2] of var set of 1..2: a = [s];\n\
         solve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref message)
            if message.contains("array a") && message.contains("has 1 initializer elements")),
        "{err}"
    );
}

#[test]
fn test_integer_element_uses_named_array_lower_bound() {
    let r = translate_fzn(
        "array [0..1] of int: a = [7, 8];\n\
         var 0..1: index;\n\
         var 7..8: value;\n\
         constraint array_int_element(index, a, value);\n\
         solve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (and (>= index 0) (<= index 1)))"));
    assert!(r.smtlib.contains("(ite (= index 0) 7 8)"));
}

#[test]
fn test_boolean_element_uses_named_array_lower_bound() {
    let r = translate_fzn(
        "var bool: a;\n\
         var bool: b;\n\
         array [-1..0] of var bool: values = [a, b];\n\
         var -1..0: index;\n\
         var bool: value;\n\
         constraint array_var_bool_element(index, values, value);\n\
         solve satisfy;\n",
    );
    assert!(r
        .smtlib
        .contains("(assert (and (>= index (- 1)) (<= index 0)))"));
    assert!(r.smtlib.contains("(ite (= index (- 1)) values_-1"));
}

#[test]
fn test_array_variable_access_checks_declared_bounds() {
    let err = translate_fzn_err(
        "array [1..2] of var int: a;\nconstraint int_eq(a[3], 0);\nsolve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::ArrayIndexOutOfBounds { ref name, index }
            if name == "a" && index == 3),
        "{err}"
    );
}

#[test]
fn test_materialized_array_range_is_bounded_before_expansion() {
    let err = translate_fzn_err(
        "array [-9223372036854775808..9223372036854775807] of var int: a;\nsolve satisfy;\n",
    );
    assert!(
        matches!(err, TranslateError::UnsupportedType(ref message)
            if message.contains("array index range") && message.contains("exceeding")),
        "{err}"
    );
}

#[test]
fn test_var_with_fixed_value() {
    let r = translate_fzn("var bool: x = true;\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(assert (= x true))"));
}

// Regression test for ay#5355: interleaved declare/assert causes ay hang.
// All (declare-const) must come before all (assert) bound statements.
#[test]
fn test_deferred_bounds_ordering() {
    let r = translate_fzn(
        "var 1..10: x;\nvar 1..10: y;\nvar 1..10: z;\n\
         constraint int_ne(x, y);\nsolve satisfy;\n",
    );
    let lines: Vec<&str> = r.smtlib.lines().collect();
    let last_declare = lines
        .iter()
        .rposition(|l| l.starts_with("(declare-const"))
        .expect("no declare-const found");
    let first_assert = lines
        .iter()
        .position(|l| l.starts_with("(assert"))
        .expect("no assert found");
    assert!(
        last_declare < first_assert,
        "declare-const at line {last_declare} comes after assert at line {first_assert}\n\
         Output:\n{}",
        r.smtlib
    );
}

// Stress test: many variables to verify deferred-bounds holds at scale.
// For n variables, all n declare-const lines must precede all n bound assertions.
#[test]
fn test_deferred_bounds_ordering_many_vars() {
    let mut fzn = String::new();
    for i in 0..20 {
        fzn.push_str(&format!("var 1..100: v{i};\n"));
    }
    // Add constraints that reference multiple variables
    fzn.push_str("constraint int_ne(v0, v1);\n");
    fzn.push_str("constraint int_le(v2, v3);\n");
    fzn.push_str("solve satisfy;\n");

    let r = translate_fzn(&fzn);
    let lines: Vec<&str> = r.smtlib.lines().collect();
    let last_declare = lines
        .iter()
        .rposition(|l| l.starts_with("(declare-const"))
        .expect("no declare-const found");
    let first_assert = lines
        .iter()
        .position(|l| l.starts_with("(assert"))
        .expect("no assert found");
    assert!(
        last_declare < first_assert,
        "With 20 variables: declare-const at line {} comes after assert at line {}\n\
         First 30 lines:\n{}",
        last_declare,
        first_assert,
        lines
            .iter()
            .take(30)
            .copied()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// Verify alldifferent pairwise encoding produces exactly n*(n-1)/2 assertions.
// Documents the O(n^2) encoding cost from globals.rs.
#[test]
fn test_alldifferent_pairwise_count() {
    let r = translate_fzn(
        "array [1..5] of var 1..5: x;\n\
         constraint fzn_all_different_int(x);\nsolve satisfy;\n",
    );
    let neq_count = r
        .smtlib
        .lines()
        .filter(|l| l.contains("(assert (not (= x_"))
        .count();
    // 5 variables -> 5*4/2 = 10 pairwise assertions
    assert_eq!(
        neq_count, 10,
        "Expected 10 pairwise != assertions for 5 variables, got {neq_count}"
    );
}

#[test]
fn test_parameter_inlining() {
    let r = translate_fzn("int: n = 42;\nvar int: x;\nconstraint int_eq(x, n);\nsolve satisfy;\n");
    assert!(r.smtlib.contains("(assert (= x 42))"));
}

// --- Basic constraint tests ---

#[test]
fn test_int_eq() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_eq(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= x y))"));
}

#[test]
fn test_int_ne() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_ne(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= x y)))"));
}

#[test]
fn test_int_lt() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lt(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (< x y))"));
}

#[test]
fn test_int_le() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_le(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (<= x y))"));
}

// --- Boolean constraint tests ---

#[test]
fn test_bool_and() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_and(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (and a b)))"));
    assert!(r.smtlib.contains("(assert (=> (and a b) r))"));
}

#[test]
fn test_bool_or() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: r;\n\
         constraint bool_or(a, b, r);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> r (or a b)))"));
    assert!(r.smtlib.contains("(assert (=> (or a b) r))"));
}

#[test]
fn test_bool_not() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\n\
         constraint bool_not(a, b);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (=> b (not a)))"));
    assert!(r.smtlib.contains("(assert (=> (not a) b))"));
}

#[test]
fn test_bool_clause() {
    let r = translate_fzn(
        "var bool: a;\nvar bool: b;\nvar bool: c;\n\
         constraint bool_clause([a, b], [c]);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (or a b (not c)))"));
}

// --- Arithmetic constraint tests ---

#[test]
fn test_int_plus() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_plus(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (+ x y)))"));
}

#[test]
fn test_int_times() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\nvar int: z;\n\
         constraint int_times(x, y, z);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= z (* x y)))"));
}

#[test]
fn test_int_abs() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_abs(x, y);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= y (ite (>= x 0) x (- x))))"));
}

#[test]
fn test_int_min() {
    let r = translate_fzn(
        "var int: a;\nvar int: b;\nvar int: c;\n\
         constraint int_min(a, b, c);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= c (ite (<= a b) a b)))"));
}

#[test]
fn test_int_max() {
    let r = translate_fzn(
        "var int: a;\nvar int: b;\nvar int: c;\n\
         constraint int_max(a, b, c);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= c (ite (>= a b) a b)))"));
}

// --- Linear constraint tests ---

#[test]
fn test_int_lin_eq() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_eq([1, -1], [x, y], 0);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= (+ x (- y)) 0))"));
}

#[test]
fn test_int_lin_le() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_le([2, 3], [x, y], 10);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (<= (+ (* 2 x) (* 3 y)) 10))"));
}

#[test]
fn test_int_lin_ne() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_lin_ne([1, 1], [x, y], 5);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (not (= (+ x y) 5)))"));
}

#[test]
fn test_int_lin_with_param_coefficients() {
    let r = translate_fzn(
        "array [1..2] of int: cs = [3, 4];\n\
         var int: x;\nvar int: y;\n\
         constraint int_lin_eq(cs, [x, y], 12);\nsolve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert (= (+ (* 3 x) (* 4 y)) 12))"));
}

include!("tests/array_elements.rs");

include!("tests/conversions_objectives_and_regressions.rs");
