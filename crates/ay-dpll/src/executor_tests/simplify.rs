// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term simplification tests - boolean, arithmetic, ITE, equality simplification

use crate::Executor;
use ay_frontend::parse;

#[test]
fn test_simplify_boolean_and_true() {
    // (and true x) should simplify to x
    let input = r#"
        (declare-const x Bool)
        (simplify (and true x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_boolean_and_false() {
    // (and false x) should simplify to false
    let input = r#"
        (declare-const x Bool)
        (simplify (and false x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_boolean_or_true() {
    // (or true x) should simplify to true
    let input = r#"
        (declare-const x Bool)
        (simplify (or true x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_boolean_or_false() {
    // (or false x) should simplify to x
    let input = r#"
        (declare-const x Bool)
        (simplify (or false x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_double_negation() {
    // (not (not x)) should simplify to x
    let input = r#"
        (declare-const x Bool)
        (simplify (not (not x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_de_morgan_not_and() {
    // (not (and x y)) should simplify to (or (not x) (not y))
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (not (and x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].contains("(or"));
    assert!(outputs[0].contains("(not x)"));
    assert!(outputs[0].contains("(not y)"));
}

#[test]
fn test_simplify_de_morgan_not_or() {
    // (not (or x y)) should simplify to (and (not x) (not y))
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (not (or x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(outputs[0].contains("(and"));
    assert!(outputs[0].contains("(not x)"));
    assert!(outputs[0].contains("(not y)"));
}

#[test]
fn test_simplify_de_morgan_enables_complement_simplification() {
    // (and x (not (or x y))) -> false
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (and x (not (or x y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].trim(), "false");
}

#[test]
fn test_simplify_ite_true_condition() {
    // (ite true a b) should simplify to a
    let input = r#"
        (declare-const a Int)
        (declare-const b Int)
        (simplify (ite true a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "a");
}

#[test]
fn test_simplify_ite_false_condition() {
    // (ite false a b) should simplify to b
    let input = r#"
        (declare-const a Int)
        (declare-const b Int)
        (simplify (ite false a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "b");
}

#[test]
fn test_simplify_equality_same() {
    // (= x x) should simplify to true
    let input = r#"
        (declare-const x Int)
        (simplify (= x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_constant() {
    // Constants should remain unchanged
    let input = r#"
        (simplify true)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

// =======================================================================
// Arithmetic constant folding tests via simplify
// =======================================================================

#[test]
fn test_simplify_int_addition() {
    // (+ 2 3) should simplify to 5
    let input = r#"
        (simplify (+ 2 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "5");
}

#[test]
fn test_simplify_int_subtraction() {
    // (- 10 4) should simplify to 6
    let input = r#"
        (simplify (- 10 4))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "6");
}

#[test]
fn test_simplify_int_multiplication() {
    // (* 3 4) should simplify to 12
    let input = r#"
        (simplify (* 3 4))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "12");
}

#[test]
fn test_simplify_int_div() {
    // (div 7 3) should simplify to 2
    let input = r#"
        (simplify (div 7 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "2");
}

#[test]
fn test_simplify_int_mod() {
    // (mod 7 3) should simplify to 1
    let input = r#"
        (simplify (mod 7 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "1");
}

#[test]
fn test_simplify_unary_minus() {
    // (- 5) should simplify to a constant -5, rendered in SMT-LIB unary-minus form
    let input = r#"
        (simplify (- 5))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Constant folding evaluates (- 5) to a negative constant, printed as `(- 5)`.
    assert_eq!(outputs[0], "(- 5)");
}

#[test]
fn test_simplify_nested_arithmetic() {
    // (+ 1 (+ 2 3)) should simplify to 6
    let input = r#"
        (simplify (+ 1 (+ 2 3)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "6");
}

#[test]
fn test_simplify_add_zero_identity() {
    // (+ x 0) should simplify to x
    let input = r#"
        (declare-const x Int)
        (simplify (+ x 0))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // The second output should be "x"
    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_mul_one_identity() {
    // (* x 1) should simplify to x
    let input = r#"
        (declare-const x Int)
        (simplify (* x 1))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_mul_zero_annihilation() {
    // (* x 0) should simplify to 0
    let input = r#"
        (declare-const x Int)
        (simplify (* x 0))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "0");
}

#[test]
fn test_simplify_sub_self() {
    // (- x x) should simplify to 0
    let input = r#"
        (declare-const x Int)
        (simplify (- x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "0");
}

#[test]
fn test_simplify_abs() {
    // (abs (- 5)) should simplify to 5
    let input = r#"
        (simplify (abs (- 5)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "5");
}

// =======================================================================
// Comparison simplification tests
// =======================================================================

#[test]
fn test_simplify_less_than_constants() {
    // (< 2 3) should simplify to true
    let input = r#"
        (simplify (< 2 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_chained_less_than_constants() {
    // (< 1 2 3) is syntactic sugar for (and (< 1 2) (< 2 3)) and should simplify to true
    let input = r#"
        (simplify (< 1 2 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_less_than_false() {
    // (< 5 3) should simplify to false
    let input = r#"
        (simplify (< 5 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_less_equal_constants() {
    // (<= 3 3) should simplify to true
    let input = r#"
        (simplify (<= 3 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_chained_less_equal_constants() {
    // (<= 1 1 2) is syntactic sugar for (and (<= 1 1) (<= 1 2)) and should simplify to true
    let input = r#"
        (simplify (<= 1 1 2))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_greater_than_constants() {
    // (> 5 3) should simplify to true
    let input = r#"
        (simplify (> 5 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_chained_greater_than_constants() {
    // (> 3 2 1) is syntactic sugar for (and (> 3 2) (> 2 1)) and should simplify to true
    let input = r#"
        (simplify (> 3 2 1))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_greater_equal_constants() {
    // (>= 3 5) should simplify to false
    let input = r#"
        (simplify (>= 3 5))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_chained_comparison_reflexive_short_circuit() {
    // (< x x y) is (and (< x x) (< x y)) and should simplify to false due to reflexive (< x x)
    let input = r#"
        (declare-const x Int)
        (declare-const y Int)
        (simplify (< x x y))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_less_than_reflexive() {
    // (< x x) should simplify to false
    let input = r#"
        (declare-const x Int)
        (simplify (< x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_less_equal_reflexive() {
    // (<= x x) should simplify to true
    let input = r#"
        (declare-const x Int)
        (simplify (<= x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_greater_than_reflexive() {
    // (> x x) should simplify to false
    let input = r#"
        (declare-const x Int)
        (simplify (> x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_greater_equal_reflexive() {
    // (>= x x) should simplify to true
    let input = r#"
        (declare-const x Int)
        (simplify (>= x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_comparison_non_constant() {
    // (< x y) should not simplify when x and y are different variables
    let input = r#"
        (declare-const x Int)
        (declare-const y Int)
        (simplify (< x y))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should produce (< x y) since it can't simplify non-constants
    assert!(outputs[0].contains('<') || outputs[0].contains('x'));
}

#[test]
fn test_simplify_nested_comparison() {
    // (and (< 1 2) (> 3 2)) should simplify to true
    let input = r#"
        (simplify (and (< 1 2) (> 3 2)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

// =======================================================================
// Equality constant folding tests
// =======================================================================

#[test]
fn test_simplify_eq_different_int_constants() {
    // (= 1 2) should simplify to false
    let input = r#"
        (simplify (= 1 2))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_eq_same_int_constants() {
    // (= 42 42) should simplify to true
    let input = r#"
        (simplify (= 42 42))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_eq_different_bool_constants() {
    // (= true false) should simplify to false
    let input = r#"
        (simplify (= true false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_eq_different_string_constants() {
    // (= "hello" "world") should simplify to false
    let input = r#"
        (simplify (= "hello" "world"))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

// =======================================================================
// Distinct simplification tests
// =======================================================================

#[test]
fn test_simplify_distinct_duplicate_vars() {
    // (distinct x x) should simplify to false
    let input = r#"
        (declare-const x Int)
        (simplify (distinct x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_distinct_constants() {
    // (distinct 1 2 3) should simplify to true
    let input = r#"
        (simplify (distinct 1 2 3))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_distinct_duplicate_constants() {
    // (distinct 1 2 1) should simplify to false
    let input = r#"
        (simplify (distinct 1 2 1))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_distinct_same_constants() {
    // (distinct 5 5) should simplify to false
    let input = r#"
        (simplify (distinct 5 5))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

// =======================================================================
// ITE Boolean branch simplification tests
// =======================================================================

#[test]
fn test_simplify_ite_true_false_branches() {
    // (ite c true false) should simplify to c
    let input = r#"
        (declare-const c Bool)
        (simplify (ite c true false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "c");
}

#[test]
fn test_simplify_ite_false_true_branches() {
    // (ite c false true) should simplify to (not c)
    let input = r#"
        (declare-const c Bool)
        (simplify (ite c false true))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(not c)");
}

#[test]
fn test_simplify_ite_cond_as_then_branch() {
    // (ite c c false) should simplify to c
    let input = r#"
        (declare-const c Bool)
        (simplify (ite c c false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "c");
}

#[test]
fn test_simplify_ite_true_then_cond_else() {
    // (ite c true c) should simplify to c
    let input = r#"
        (declare-const c Bool)
        (simplify (ite c true c))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "c");
}

#[test]
fn test_simplify_ite_x_false_to_and() {
    // (ite c x false) should simplify to (and c x)
    let input = r#"
        (declare-const c Bool)
        (declare-const x Bool)
        (simplify (ite c x false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(and c x)");
}

#[test]
fn test_simplify_ite_true_x_to_or() {
    // (ite c true x) should simplify to (or c x)
    let input = r#"
        (declare-const c Bool)
        (declare-const x Bool)
        (simplify (ite c true x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(or c x)");
}

#[test]
fn test_simplify_ite_false_x_to_and_not() {
    // (ite c false x) should simplify to (and (not c) x)
    let input = r#"
        (declare-const c Bool)
        (declare-const x Bool)
        (simplify (ite c false x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (and (not c) x) or equivalent
    let result = &outputs[0];
    assert!(
        result.contains("and") && result.contains("not"),
        "Expected (and (not c) x), got: {result}"
    );
}

#[test]
fn test_simplify_ite_x_true_to_or_not() {
    // (ite c x true) should simplify to (or (not c) x)
    let input = r#"
        (declare-const c Bool)
        (declare-const x Bool)
        (simplify (ite c x true))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (or (not c) x) or equivalent
    let result = &outputs[0];
    assert!(
        result.contains("or") && result.contains("not"),
        "Expected (or (not c) x), got: {result}"
    );
}

#[test]
fn test_simplify_nested_ite_same_condition() {
    // (ite c (ite c x y) z) should simplify to (ite c x z)
    let input = r#"
        (declare-const c Bool)
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (ite c (ite c x y) z))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should simplify - the y variable shouldn't appear
    let result = &outputs[0];
    assert!(
        !result.contains('y'),
        "Expected y to be eliminated, got: {result}"
    );
}

#[test]
fn test_simplify_ite_non_bool_no_and_or() {
    // (ite c x 0) with Int x should NOT simplify to (and c x)
    let input = r#"
        (declare-const c Bool)
        (declare-const x Int)
        (simplify (ite c x 0))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should remain as ite, not become and
    let result = &outputs[0];
    assert!(
        result.contains("ite") || result.contains('x'),
        "Expected ite for Int branches, got: {result}"
    );
    assert!(
        !result.contains("and"),
        "Should not simplify Int ite to and, got: {result}"
    );
}

// =======================================================================
// ITE negated condition normalization tests
// =======================================================================

#[test]
fn test_simplify_ite_negated_condition() {
    // (ite (not c) a b) -> (ite c b a)
    let input = r#"
        (declare-const c Bool)
        (declare-const a Int)
        (declare-const b Int)
        (simplify (ite (not c) a b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should produce (ite c b a), with condition c (not negated) and branches swapped
    let result = &outputs[0];
    assert!(
        result.contains("ite"),
        "Expected ite in result, got: {result}"
    );
    // The condition should be just "c", not "(not c)"
    // Check that (not c) does NOT appear in the output
    assert!(
        !result.contains("not"),
        "Expected positive condition (c), not (not c), got: {result}"
    );
}

#[test]
fn test_simplify_ite_negated_condition_bool_true_false() {
    // (ite (not c) true false) -> (ite c false true) -> (not c)
    let input = r#"
        (declare-const c Bool)
        (simplify (ite (not c) true false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should simplify to (not c)
    let result = &outputs[0];
    assert!(
        result.contains("not") && result.contains('c'),
        "Expected (not c), got: {result}"
    );
}

#[test]
fn test_simplify_ite_negated_condition_with_sat() {
    // Test that ITE with negated condition works correctly in SAT solving
    // (ite (not c) 1 2) = 1 with c = false should be SAT
    let input = r#"
        (declare-const c Bool)
        (assert (= (ite (not c) 1 2) 1))
        (assert (not c))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "sat");
}

// =======================================================================
// Comparison normalization tests
// =======================================================================

#[test]
fn test_simplify_gt_normalizes_to_lt() {
    // (> x y) should normalize to (< y x)
    let input = r#"
        (declare-const x Int)
        (declare-const y Int)
        (simplify (> x y))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should produce (< y x), not (> x y)
    let result = &outputs[0];
    assert!(
        result.contains('<') && !result.contains('>'),
        "Expected < operator after normalization, got: {result}"
    );
    // Check that y comes before x in the output (< y x)
    let y_pos = result.find('y').unwrap_or(usize::MAX);
    let x_pos = result.find('x').unwrap_or(usize::MAX);
    assert!(
        y_pos < x_pos,
        "Expected (< y x) after normalizing (> x y), got: {result}"
    );
}

#[test]
fn test_simplify_ge_normalizes_to_le() {
    // (>= x y) should normalize to (<= y x)
    let input = r#"
        (declare-const x Int)
        (declare-const y Int)
        (simplify (>= x y))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should produce (<= y x), not (>= x y)
    let result = &outputs[0];
    assert!(
        result.contains("<=") && !result.contains(">="),
        "Expected <= operator after normalization, got: {result}"
    );
    // Check that y comes before x in the output (<= y x)
    let y_pos = result.find('y').unwrap_or(usize::MAX);
    let x_pos = result.find('x').unwrap_or(usize::MAX);
    assert!(
        y_pos < x_pos,
        "Expected (<= y x) after normalizing (>= x y), got: {result}"
    );
}

#[test]
fn test_simplify_gt_and_lt_same_result() {
    // (> x y) and (< y x) should produce identical output
    let input1 = r#"
        (declare-const a Int)
        (declare-const b Int)
        (simplify (> a b))
    "#;

    let input2 = r#"
        (declare-const a Int)
        (declare-const b Int)
        (simplify (< b a))
    "#;

    let commands1 = parse(input1).unwrap();
    let mut exec1 = Executor::new();
    let outputs1 = exec1.execute_all(&commands1).unwrap();

    let commands2 = parse(input2).unwrap();
    let mut exec2 = Executor::new();
    let outputs2 = exec2.execute_all(&commands2).unwrap();

    assert_eq!(outputs1.len(), 1);
    assert_eq!(outputs2.len(), 1);
    assert_eq!(
        outputs1[0], outputs2[0],
        "(> a b) and (< b a) should produce identical output"
    );
}

#[test]
fn test_simplify_ge_and_le_same_result() {
    // (>= x y) and (<= y x) should produce identical output
    let input1 = r#"
        (declare-const a Int)
        (declare-const b Int)
        (simplify (>= a b))
    "#;

    let input2 = r#"
        (declare-const a Int)
        (declare-const b Int)
        (simplify (<= b a))
    "#;

    let commands1 = parse(input1).unwrap();
    let mut exec1 = Executor::new();
    let outputs1 = exec1.execute_all(&commands1).unwrap();

    let commands2 = parse(input2).unwrap();
    let mut exec2 = Executor::new();
    let outputs2 = exec2.execute_all(&commands2).unwrap();

    assert_eq!(outputs1.len(), 1);
    assert_eq!(outputs2.len(), 1);
    assert_eq!(
        outputs1[0], outputs2[0],
        "(>= a b) and (<= b a) should produce identical output"
    );
}

// =======================================================================
// Boolean equality (iff) simplification tests
// =======================================================================

#[test]
fn test_simplify_eq_bool_with_true() {
    // (= x true) should simplify to x
    let input = r#"
        (declare-const x Bool)
        (simplify (= x true))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_eq_true_with_bool() {
    // (= true x) should simplify to x
    let input = r#"
        (declare-const x Bool)
        (simplify (= true x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_eq_bool_with_false() {
    // (= x false) should simplify to (not x)
    let input = r#"
        (declare-const x Bool)
        (simplify (= x false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(not x)");
}

#[test]
fn test_simplify_eq_false_with_bool() {
    // (= false x) should simplify to (not x)
    let input = r#"
        (declare-const x Bool)
        (simplify (= false x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(not x)");
}

#[test]
fn test_simplify_eq_compound_bool_with_true() {
    // (= (and x y) true) should simplify to (and x y)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (= (and x y) true))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(and x y)");
}

#[test]
fn test_simplify_eq_compound_bool_with_false() {
    // (= (or x y) false) should simplify to (not (or x y)), which normalizes via De Morgan
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (= (or x y) false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(and (not x) (not y))");
}

#[test]
fn test_simplify_eq_complement_detection() {
    // (= x (not x)) should simplify to false
    let input = r#"
        (declare-const x Bool)
        (simplify (= x (not x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_eq_complement_detection_reversed() {
    // (= (not x) x) should simplify to false
    let input = r#"
        (declare-const x Bool)
        (simplify (= (not x) x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_eq_complement_predicate() {
    // (= (p a) (not (p a))) should simplify to false
    let input = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-fun p (U) Bool)
        (simplify (= (p a) (not (p a))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_eq_negation_lifting() {
    // (= (not x) (not y)) simplifies: lift negations → mk_eq(x,y).
    // After #6869 (commit 2e12dd3b3), Bool-Bool eq returns App("=")
    // instead of ITE encoding — the ITE normalization was removed because
    // it broke EUF congruence closure through alias chains.
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (= (not x) (not y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(= x y)");
}

#[test]
fn test_simplify_eq_negation_lifting_predicates() {
    // (= (not (p a)) (not (q b))) simplifies: lift negations → mk_eq on Bool.
    // After #6869 (commit 2e12dd3b3), Bool-Bool eq returns App("=")
    // instead of ITE encoding.
    let input = r#"
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-fun p (U) Bool)
        (declare-fun q (U) Bool)
        (simplify (= (not (p a)) (not (q b))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "(= (p a) (q b))");
}

#[test]
fn test_simplify_eq_reflexive_negation() {
    // (= (not x) (not x)) should simplify to true
    let input = r#"
        (declare-const x Bool)
        (simplify (= (not x) (not x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

// =======================================================================
// ITE-equality simplification tests
// =======================================================================

#[test]
fn test_simplify_eq_ite_then_branch() {
    // (= (ite c a b) a) -> (or c (= b a))
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (= (ite c a b) a))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (or c (= a b)) with canonical ordering
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains('c'));
}

#[test]
fn test_simplify_eq_ite_else_branch() {
    // (= (ite c a b) b) -> (or (not c) (= a b))
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (= (ite c a b) b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (or (not c) (= a b)) with canonical ordering
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains("not"));
}

#[test]
fn test_simplify_eq_ite_symmetric() {
    // (= a (ite c a b)) -> (or c (= b a))
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (= a (ite c a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (or c (= a b)) with canonical ordering
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains('c'));
}

#[test]
fn test_simplify_eq_ite_same_condition() {
    // (= (ite c a b) (ite c x y)) -> (ite c (= a x) (= b y))
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (= (ite c a b) (ite c x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (ite c (= a x) (= b y)) or simplified form
    assert!(outputs[0].contains("ite") || outputs[0].contains('='));
}

#[test]
fn test_simplify_eq_ite_with_constants() {
    // (= (ite c true false) true) -> c
    let input = r#"
        (declare-const c Bool)
        (simplify (= (ite c true false) true))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // (ite c true false) simplifies to c, so (= c true) -> c
    assert_eq!(outputs[0], "c");
}

#[test]
fn test_simplify_eq_ite_reflexive() {
    // (= (ite c a a) a) -> true (via same-branch simplification)
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (simplify (= (ite c a a) a))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

// =======================================================================
// And/Or flattening tests
// =======================================================================

#[test]
fn test_simplify_and_flattening() {
    // (and a (and b c)) should flatten to (and a b c)
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (simplify (and a (and b c)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Output should be a flat and with a, b, c (canonically sorted)
    assert!(outputs[0].contains("and"));
    assert!(outputs[0].contains('a'));
    assert!(outputs[0].contains('b'));
    assert!(outputs[0].contains('c'));
    // Should NOT contain nested and
    assert_eq!(outputs[0].matches("and").count(), 1);
}

#[test]
fn test_simplify_or_flattening() {
    // (or a (or b c)) should flatten to (or a b c)
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (simplify (or a (or b c)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Output should be a flat or with a, b, c (canonically sorted)
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains('a'));
    assert!(outputs[0].contains('b'));
    assert!(outputs[0].contains('c'));
    // Should NOT contain nested or
    assert_eq!(outputs[0].matches("or").count(), 1);
}

#[test]
fn test_simplify_and_deep_flattening() {
    // (and (and a b) (and c d)) should flatten to (and a b c d)
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (declare-const d Bool)
        (simplify (and (and a b) (and c d)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Output should be a flat and with a, b, c, d
    assert!(outputs[0].contains("and"));
    assert!(outputs[0].contains('a'));
    assert!(outputs[0].contains('b'));
    assert!(outputs[0].contains('c'));
    assert!(outputs[0].contains('d'));
    // Should NOT contain nested and
    assert_eq!(outputs[0].matches("and").count(), 1);
}

#[test]
fn test_simplify_or_deep_flattening() {
    // (or (or a b) (or c d)) should flatten to (or a b c d)
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (declare-const d Bool)
        (simplify (or (or a b) (or c d)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Output should be a flat or with a, b, c, d
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains('a'));
    assert!(outputs[0].contains('b'));
    assert!(outputs[0].contains('c'));
    assert!(outputs[0].contains('d'));
    // Should NOT contain nested or
    assert_eq!(outputs[0].matches("or").count(), 1);
}

#[test]
fn test_simplify_and_flattening_with_dedup() {
    // (and a (and a b)) should flatten and dedup to (and a b)
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (and a (and a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Output should be (and a b)
    assert_eq!(outputs[0], "(and a b)");
}

#[test]
fn test_simplify_or_flattening_with_dedup() {
    // (or a (or a b)) should flatten and dedup to (or a b)
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (or a (or a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Output should be (or a b)
    assert_eq!(outputs[0], "(or a b)");
}

// =======================================================================
// Complement detection tests
// =======================================================================

#[test]
fn test_simplify_and_complement() {
    // (and x (not x)) should simplify to false
    let input = r#"
        (declare-const x Bool)
        (simplify (and x (not x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_or_complement() {
    // (or x (not x)) should simplify to true
    let input = r#"
        (declare-const x Bool)
        (simplify (or x (not x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_and_complement_with_others() {
    // (and x y (not x) z) should simplify to false
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (and x y (not x) z))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_or_complement_with_others() {
    // (or x y (not x) z) should simplify to true
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (or x y (not x) z))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_and_complement_nested() {
    // (and (and a b) (not a)) should simplify to false
    // after flattening: (and a b (not a)) contains complement
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (and (and a b) (not a)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_or_complement_nested() {
    // (or (or a b) (not a)) should simplify to true
    // after flattening: (or a b (not a)) contains complement
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (or (or a b) (not a)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_and_no_complement() {
    // (and x (not y)) should NOT simplify to false (no complement)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (and x (not y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should remain as an and term
    assert!(outputs[0].contains("and"));
    assert!(outputs[0].contains('x'));
    assert!(outputs[0].contains("not"));
    assert!(outputs[0].contains('y'));
}

#[test]
fn test_simplify_or_no_complement() {
    // (or x (not y)) should NOT simplify to true (no complement)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (or x (not y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should remain as an or term
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains('x'));
    assert!(outputs[0].contains("not"));
    assert!(outputs[0].contains('y'));
}

// =======================================================================
// Absorption law tests
// =======================================================================

#[test]
fn test_simplify_and_absorption_basic() {
    // (and x (or x y)) = x
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (and x (or x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_or_absorption_basic() {
    // (or x (and x y)) = x
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (or x (and x y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_and_absorption_order_independent() {
    // (and (or x y) x) = x (order shouldn't matter)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (and (or x y) x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_or_absorption_order_independent() {
    // (or (and x y) x) = x (order shouldn't matter)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (or (and x y) x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_and_absorption_multiple_vars() {
    // (and x (or x y z)) = x
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (and x (or x y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_or_absorption_multiple_vars() {
    // (or x (and x y z)) = x
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (or x (and x y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_and_no_absorption() {
    // (and x (or y z)) should NOT simplify - x is not in (or y z)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (and x (or y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should remain as an and term
    assert!(outputs[0].contains("and"));
    assert!(outputs[0].contains("or"));
}

#[test]
fn test_simplify_or_no_absorption() {
    // (or x (and y z)) should NOT simplify - x is not in (and y z)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (or x (and y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should remain as an or term
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains("and"));
}

// =======================================================================
// Negation-through absorption tests via simplify
// =======================================================================

#[test]
fn test_simplify_and_negation_through_absorption() {
    // (and x (or (not x) y)) should simplify to (and x y)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (and x (or (not x) y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (and x y)
    assert!(outputs[0].contains("and"));
    assert!(outputs[0].contains('x'));
    assert!(outputs[0].contains('y'));
    // Should NOT contain "or" or "not"
    assert!(!outputs[0].contains("or"));
    assert!(!outputs[0].contains("not"));
}

#[test]
fn test_simplify_or_negation_through_absorption() {
    // (or x (and (not x) y)) should simplify to (or x y)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (or x (and (not x) y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (or x y)
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains('x'));
    assert!(outputs[0].contains('y'));
    // Should NOT contain "and" or "not"
    assert!(!outputs[0].contains("and"));
    assert!(!outputs[0].contains("not"));
}

#[test]
fn test_simplify_and_negation_through_multiple() {
    // (and x (or (not x) y z)) should simplify to (and x (or y z))
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (and x (or (not x) y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (and x (or y z))
    assert!(outputs[0].contains("and"));
    assert!(outputs[0].contains("or"));
    // Should NOT contain "not" - the (not x) was removed
    assert!(!outputs[0].contains("not"));
}

#[test]
fn test_simplify_or_negation_through_multiple() {
    // (or x (and (not x) y z)) should simplify to (or x (and y z))
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (or x (and (not x) y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (or x (and y z))
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains("and"));
    // Should NOT contain "not" - the (not x) was removed
    assert!(!outputs[0].contains("not"));
}

#[test]
fn test_simplify_and_negation_through_removes_inner() {
    // Duplicate elimination keeps the input valid SMT-LIB while exercising
    // the same inner collapse:
    // (and x (or (not x) (not x))) simplifies:
    // First (or (not x) (not x)) = (not x)
    // Then (and x (not x)) = false (complement)
    let input = r#"
        (declare-const x Bool)
        (simplify (and x (or (not x) (not x))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].trim(), "false");
}

#[test]
fn test_simplify_or_negation_through_removes_inner() {
    // Duplicate elimination keeps the input valid SMT-LIB while exercising
    // the same inner collapse:
    // (or x (and (not x) (not x))) simplifies:
    // First (and (not x) (not x)) = (not x)
    // Then (or x (not x)) = true (complement)
    let input = r#"
        (declare-const x Bool)
        (simplify (or x (and (not x) (not x))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0].trim(), "true");
}

#[test]
fn test_simplify_and_negation_through_no_false_positive() {
    // (and x (or y z)) should NOT simplify - no (not x) in the or
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (and x (or y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should remain as (and x (or y z))
    assert!(outputs[0].contains("and"));
    assert!(outputs[0].contains("or"));
}

#[test]
fn test_simplify_or_negation_through_no_false_positive() {
    // (or x (and y z)) should NOT simplify - no (not x) in the and
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (declare-const z Bool)
        (simplify (or x (and y z)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should remain as (or x (and y z))
    assert!(outputs[0].contains("or"));
    assert!(outputs[0].contains("and"));
}

// ========================================================================
// ITE Negation Normalization Tests
// ========================================================================

#[test]
fn test_simplify_not_ite_basic() {
    // (not (ite c a b)) -> (ite c (not a) (not b))
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (not (ite c a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Result should be (ite c (not a) (not b))
    assert!(
        outputs[0].contains("ite"),
        "Expected ite in result, got: {}",
        outputs[0]
    );
    // Both branches should have not
    let not_count = outputs[0].matches("not").count();
    assert_eq!(
        not_count, 2,
        "Expected exactly 2 'not' in result, got {}: {}",
        not_count, outputs[0]
    );
}

#[test]
fn test_simplify_not_ite_with_true_branch() {
    // (not (ite c true a)) = (not (or c a)) = (and (not c) (not a))
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (simplify (not (ite c true a)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should simplify to (and (not c) (not a))
    assert!(
        outputs[0].contains("and"),
        "Expected and in result, got: {}",
        outputs[0]
    );
    let not_count = outputs[0].matches("not").count();
    assert_eq!(
        not_count, 2,
        "Expected exactly 2 'not' in result, got {}: {}",
        not_count, outputs[0]
    );
}

#[test]
fn test_simplify_not_ite_with_false_branch() {
    // (not (ite c a false)) = (not (and c a)) = (or (not c) (not a))
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (simplify (not (ite c a false)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should simplify to (or (not c) (not a))
    assert!(
        outputs[0].contains("or"),
        "Expected or in result, got: {}",
        outputs[0]
    );
    let not_count = outputs[0].matches("not").count();
    assert_eq!(
        not_count, 2,
        "Expected exactly 2 'not' in result, got {}: {}",
        not_count, outputs[0]
    );
}

#[test]
fn test_simplify_not_ite_true_false_branches() {
    // (not (ite c true false)) = (not c)
    // Because (ite c true false) = c
    let input = r#"
        (declare-const c Bool)
        (simplify (not (ite c true false)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should simplify to (not c)
    assert_eq!(
        outputs[0].trim(),
        "(not c)",
        "Expected (not c), got: {}",
        outputs[0]
    );
}

#[test]
fn test_simplify_not_ite_false_true_branches() {
    // (not (ite c false true)) = c
    // Because (ite c false true) = (not c), and (not (not c)) = c
    let input = r#"
        (declare-const c Bool)
        (simplify (not (ite c false true)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should simplify to c
    assert_eq!(outputs[0].trim(), "c", "Expected c, got: {}", outputs[0]);
}

#[test]
fn test_simplify_not_ite_nested() {
    // (not (ite c1 (ite c2 a b) false))
    // = (not (and c1 (ite c2 a b)))
    // = (or (not c1) (not (ite c2 a b)))
    // = (or (not c1) (ite c2 (not a) (not b)))
    let input = r#"
        (declare-const c1 Bool)
        (declare-const c2 Bool)
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (not (ite c1 (ite c2 a b) false)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should have or with (not c1) and ite
    assert!(
        outputs[0].contains("or"),
        "Expected or in result, got: {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains("ite"),
        "Expected ite in result, got: {}",
        outputs[0]
    );
}

#[test]
fn test_simplify_double_not_ite() {
    // (not (not (ite c a b))) = (ite c a b)
    let input = r#"
        (declare-const c Bool)
        (declare-const a Bool)
        (declare-const b Bool)
        (simplify (not (not (ite c a b))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (ite c a b)
    assert!(
        outputs[0].contains("ite"),
        "Expected ite in result, got: {}",
        outputs[0]
    );
    // Should not have any 'not'
    assert!(
        !outputs[0].contains("not"),
        "Should not contain 'not', got: {}",
        outputs[0]
    );
}

// =========================================================================
// XOR simplification tests (SMT-LIB integration)
// =========================================================================

#[test]
fn test_simplify_xor_same_operand() {
    // (xor x x) = false
    let input = r#"
        (declare-const x Bool)
        (simplify (xor x x))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "false");
}

#[test]
fn test_simplify_xor_with_true() {
    // (xor x true) = (not x)
    let input = r#"
        (declare-const x Bool)
        (simplify (xor x true))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("not"),
        "Expected (not x), got: {}",
        outputs[0]
    );
}

#[test]
fn test_simplify_xor_with_false() {
    // (xor x false) = x
    let input = r#"
        (declare-const x Bool)
        (simplify (xor x false))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "x");
}

#[test]
fn test_simplify_xor_complement() {
    // (xor x (not x)) = true
    let input = r#"
        (declare-const x Bool)
        (simplify (xor x (not x)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "true");
}

#[test]
fn test_simplify_xor_double_negation_lifting() {
    // (xor (not x) (not y)) = (xor x y)
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (simplify (xor (not x) (not y)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should be (xor x y) - no 'not' in the result
    assert!(
        !outputs[0].contains("not"),
        "Should not contain 'not' after double negation lifting, got: {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains("xor"),
        "Expected xor in result, got: {}",
        outputs[0]
    );
}

#[test]
fn test_xor_sat_formula() {
    // Test a satisfiable formula using xor
    // (xor x y) and (xor x true) - should be sat with y = true
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (assert (xor x y))
        (assert (xor x true))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "sat");
}

// ============================================
// QF_AX (Array) Tests
// ============================================
