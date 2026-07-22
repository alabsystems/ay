// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========== Regression tests for #352 ==========

#[test]
fn test_regression_352_unknown_function_errors() {
    // #352: Unknown functions should produce parse error, not Bool(true)
    let input = r#"
            (set-logic HORN)
            (declare-fun Inv (Int) Bool)
            (declare-var x Int)
            (assert (forall ((x Int)) (=> (= (unknown_func x) 0) (Inv x))))
            (check-sat)
        "#;

    let result = ChcParser::parse(input);
    assert!(
        result.is_err(),
        "Unknown function 'unknown_func' should cause parse error"
    );
    let err_msg = result.expect_err("test should fail").to_string();
    assert!(
        err_msg.contains("Unknown function application") && err_msg.contains("unknown_func"),
        "Error should mention 'Unknown function application' and 'unknown_func': {err_msg}"
    );
}

#[test]
fn test_regression_352_non_bool_declare_fun_errors() {
    // #352: Non-Bool declare-fun should produce parse error
    let input = r#"
            (set-logic HORN)
            (declare-fun f (Int) Int)
            (declare-fun Inv (Int) Bool)
            (check-sat)
        "#;

    let result = ChcParser::parse(input);
    assert!(
        result.is_err(),
        "Non-Bool declare-fun 'f' should cause parse error"
    );
    let err_msg = result.expect_err("test should fail").to_string();
    assert!(
        err_msg.contains("Non-predicate function declaration"),
        "Error should mention 'Non-predicate function declaration': {err_msg}"
    );
}

// ========== N-ary equality tests ==========

#[test]
fn test_nary_equality_chainable() {
    // SMT-LIB 2.6: (= a b c) should parse as (and (= a b) (= b c))
    // Issue #380
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("y".to_string(), ChcSort::Int);
    parser.variables.insert("z".to_string(), ChcSort::Int);

    // Binary equality (= x y) should still work
    parser.input = "(= x y)".to_string();
    parser.pos = 0;
    let binary = parser.parse_expr().expect("test should succeed");
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    assert_eq!(binary, ChcExpr::eq(x.clone(), y.clone()));

    // Ternary equality (= x y z) should expand to (and (= x y) (= y z))
    parser.input = "(= x y z)".to_string();
    parser.pos = 0;
    let ternary = parser.parse_expr().expect("test should succeed");
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let expected = ChcExpr::and(ChcExpr::eq(x, y.clone()), ChcExpr::eq(y, z));
    assert_eq!(ternary, expected);
}

#[test]
fn test_nary_equality_four_args() {
    // Test (= a b c d) = (and (= a b) (= b c) (= c d))
    // Issue #380 - ensure 4+ args also work
    let mut parser = ChcParser::new();
    parser.variables.insert("a".to_string(), ChcSort::Int);
    parser.variables.insert("b".to_string(), ChcSort::Int);
    parser.variables.insert("c".to_string(), ChcSort::Int);
    parser.variables.insert("d".to_string(), ChcSort::Int);

    parser.input = "(= a b c d)".to_string();
    parser.pos = 0;
    let result = parser.parse_expr().expect("test should succeed");

    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Int));
    let d = ChcExpr::var(ChcVar::new("d", ChcSort::Int));

    // Should be (and (and (= a b) (= b c)) (= c d))
    let eq_ab = ChcExpr::eq(a, b.clone());
    let eq_bc = ChcExpr::eq(b, c.clone());
    let eq_cd = ChcExpr::eq(c, d);
    let expected = ChcExpr::and(ChcExpr::and(eq_ab, eq_bc), eq_cd);
    assert_eq!(result, expected);
}

#[test]
fn test_nary_equality_too_few_args() {
    // (= x) with only one argument should be an error
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(= x)".to_string();
    parser.pos = 0;
    let result = parser.parse_expr();
    assert!(result.is_err(), "(= x) should require at least 2 arguments");
    let err_msg = result.expect_err("test should fail").to_string();
    assert!(
        err_msg.contains("at least 2 arguments"),
        "Error message should mention 'at least 2 arguments': {err_msg}"
    );
}

// ========== Chainable comparison tests ==========

#[test]
fn test_chainable_less_than() {
    // SMT-LIB 2.6: (< a b c) should parse as (and (< a b) (< b c))
    // Issue #1843
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("y".to_string(), ChcSort::Int);
    parser.variables.insert("z".to_string(), ChcSort::Int);

    // Binary (< x y) should still work
    parser.input = "(< x y)".to_string();
    parser.pos = 0;
    let binary = parser.parse_expr().expect("test should succeed");
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    assert_eq!(binary, ChcExpr::lt(x.clone(), y.clone()));

    // Ternary (< x y z) should expand to (and (< x y) (< y z))
    parser.input = "(< x y z)".to_string();
    parser.pos = 0;
    let ternary = parser.parse_expr().expect("test should succeed");
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let expected = ChcExpr::and(ChcExpr::lt(x, y.clone()), ChcExpr::lt(y, z));
    assert_eq!(ternary, expected);
}

#[test]
fn test_chainable_less_equal() {
    // SMT-LIB 2.6: (<= a b c) should parse as (and (<= a b) (<= b c))
    // Issue #1843
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("y".to_string(), ChcSort::Int);
    parser.variables.insert("z".to_string(), ChcSort::Int);

    // Binary (<= x y) should still work
    parser.input = "(<= x y)".to_string();
    parser.pos = 0;
    let binary = parser.parse_expr().expect("test should succeed");
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    assert_eq!(binary, ChcExpr::le(x.clone(), y.clone()));

    // Ternary (<= x y z) should expand to (and (<= x y) (<= y z))
    parser.input = "(<= x y z)".to_string();
    parser.pos = 0;
    let ternary = parser.parse_expr().expect("test should succeed");
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let expected = ChcExpr::and(ChcExpr::le(x, y.clone()), ChcExpr::le(y, z));
    assert_eq!(ternary, expected);
}

#[test]
fn test_chainable_greater_than() {
    // SMT-LIB 2.6: (> a b c) should parse as (and (> a b) (> b c))
    // Issue #1843
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("y".to_string(), ChcSort::Int);
    parser.variables.insert("z".to_string(), ChcSort::Int);

    // Binary (> x y) should still work
    parser.input = "(> x y)".to_string();
    parser.pos = 0;
    let binary = parser.parse_expr().expect("test should succeed");
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    assert_eq!(binary, ChcExpr::gt(x.clone(), y.clone()));

    // Ternary (> x y z) should expand to (and (> x y) (> y z))
    parser.input = "(> x y z)".to_string();
    parser.pos = 0;
    let ternary = parser.parse_expr().expect("test should succeed");
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let expected = ChcExpr::and(ChcExpr::gt(x, y.clone()), ChcExpr::gt(y, z));
    assert_eq!(ternary, expected);
}

#[test]
fn test_chainable_greater_equal() {
    // SMT-LIB 2.6: (>= a b c) should parse as (and (>= a b) (>= b c))
    // Issue #1843
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("y".to_string(), ChcSort::Int);
    parser.variables.insert("z".to_string(), ChcSort::Int);

    // Binary (>= x y) should still work
    parser.input = "(>= x y)".to_string();
    parser.pos = 0;
    let binary = parser.parse_expr().expect("test should succeed");
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    assert_eq!(binary, ChcExpr::ge(x.clone(), y.clone()));

    // Ternary (>= x y z) should expand to (and (>= x y) (>= y z))
    parser.input = "(>= x y z)".to_string();
    parser.pos = 0;
    let ternary = parser.parse_expr().expect("test should succeed");
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let expected = ChcExpr::and(ChcExpr::ge(x, y.clone()), ChcExpr::ge(y, z));
    assert_eq!(ternary, expected);
}

#[test]
fn test_chainable_comparison_error_too_few_args() {
    // Test that all comparison operators require at least 2 arguments
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    for op in &["<", "<=", ">", ">="] {
        parser.input = format!("({op} x)");
        parser.pos = 0;
        let result = parser.parse_expr();
        assert!(
            result.is_err(),
            "({op} x) should require at least 2 arguments"
        );
        let err_msg = result.expect_err("test should fail").to_string();
        assert!(
            err_msg.contains("at least 2 arguments"),
            "'{op}' error message should mention 'at least 2 arguments': {err_msg}"
        );
    }
}

#[test]
fn test_chainable_comparison_four_args() {
    // Test 4-arg case for <= to ensure chaining works beyond 3 args
    // (<= a b c d) should expand to (and (and (<= a b) (<= b c)) (<= c d))
    let mut parser = ChcParser::new();
    parser.variables.insert("a".to_string(), ChcSort::Int);
    parser.variables.insert("b".to_string(), ChcSort::Int);
    parser.variables.insert("c".to_string(), ChcSort::Int);
    parser.variables.insert("d".to_string(), ChcSort::Int);

    parser.input = "(<= a b c d)".to_string();
    parser.pos = 0;
    let result = parser.parse_expr().expect("test should succeed");

    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Int));
    let d = ChcExpr::var(ChcVar::new("d", ChcSort::Int));

    // (and (and (<= a b) (<= b c)) (<= c d))
    let le_ab = ChcExpr::le(a, b.clone());
    let le_bc = ChcExpr::le(b, c.clone());
    let le_cd = ChcExpr::le(c, d);
    let expected = ChcExpr::and(ChcExpr::and(le_ab, le_bc), le_cd);
    assert_eq!(result, expected);
}

// ========== N-ary distinct tests ==========

#[test]
fn test_nary_distinct() {
    // SMT-LIB 2.6: (distinct x y z) should parse as
    // (and (and (distinct x y) (distinct x z)) (distinct y z))
    // Issue #1844
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);
    parser.variables.insert("y".to_string(), ChcSort::Int);
    parser.variables.insert("z".to_string(), ChcSort::Int);

    // Binary distinct (distinct x y) should still work
    parser.input = "(distinct x y)".to_string();
    parser.pos = 0;
    let binary = parser.parse_expr().expect("test should succeed");
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    assert_eq!(binary, ChcExpr::ne(x.clone(), y.clone()));

    // Ternary distinct (distinct x y z) should expand to pairwise inequalities
    // (and (and (distinct x y) (distinct x z)) (distinct y z))
    parser.input = "(distinct x y z)".to_string();
    parser.pos = 0;
    let ternary = parser.parse_expr().expect("test should succeed");
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    let expected = ChcExpr::and(
        ChcExpr::and(ChcExpr::ne(x.clone(), y.clone()), ChcExpr::ne(x, z.clone())),
        ChcExpr::ne(y, z),
    );
    assert_eq!(ternary, expected);
}

#[test]
fn test_nary_distinct_four_args() {
    // Test (distinct a b c d) generates all 6 pairwise inequalities:
    // (a!=b), (a!=c), (a!=d), (b!=c), (b!=d), (c!=d)
    // Issue #1844
    let mut parser = ChcParser::new();
    parser.variables.insert("a".to_string(), ChcSort::Int);
    parser.variables.insert("b".to_string(), ChcSort::Int);
    parser.variables.insert("c".to_string(), ChcSort::Int);
    parser.variables.insert("d".to_string(), ChcSort::Int);

    parser.input = "(distinct a b c d)".to_string();
    parser.pos = 0;
    let result = parser.parse_expr().expect("test should succeed");

    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Int));
    let d = ChcExpr::var(ChcVar::new("d", ChcSort::Int));

    // Should produce 6 inequalities conjuncted together
    // Order: (a!=b), (a!=c), (a!=d), (b!=c), (b!=d), (c!=d)
    let ne_ab = ChcExpr::ne(a.clone(), b.clone());
    let ne_ac = ChcExpr::ne(a.clone(), c.clone());
    let ne_ad = ChcExpr::ne(a, d.clone());
    let ne_bc = ChcExpr::ne(b.clone(), c.clone());
    let ne_bd = ChcExpr::ne(b, d.clone());
    let ne_cd = ChcExpr::ne(c, d);

    // Build expected tree from reduce pattern:
    // ((((ne_ab & ne_ac) & ne_ad) & ne_bc) & ne_bd) & ne_cd
    let expected = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::and(ChcExpr::and(ChcExpr::and(ne_ab, ne_ac), ne_ad), ne_bc),
            ne_bd,
        ),
        ne_cd,
    );
    assert_eq!(result, expected);
}

#[test]
fn test_nary_distinct_too_few_args() {
    // (distinct x) with only one argument should be an error
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(distinct x)".to_string();
    parser.pos = 0;
    let result = parser.parse_expr();
    assert!(
        result.is_err(),
        "(distinct x) should require at least 2 arguments"
    );
    let err_msg = result.expect_err("test should fail").to_string();
    assert!(
        err_msg.contains("at least 2 arguments"),
        "Error message should mention 'at least 2 arguments': {err_msg}"
    );
}
