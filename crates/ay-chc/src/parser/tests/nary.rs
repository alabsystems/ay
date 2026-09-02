// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{engines, BmcConfig, SmtContext, SmtResult};

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

fn solve_only_constraint(input: &str) -> SmtResult {
    let problem = ChcParser::parse(input).expect("UF fixture should parse");
    assert_eq!(problem.clauses().len(), 1, "fixture must have one rule");
    let constraint = problem.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("fixture rule must have a background-theory constraint");
    SmtContext::new().check_sat(constraint)
}

#[test]
fn test_scalar_return_declare_fun_has_euf_congruence() {
    for input in [
        r#"
                (set-logic HORN)
                (declare-fun f (Int) Int)
                (declare-fun g (Int) Int)
                (declare-var x Int)
                (declare-var y Int)
                (rule (=> (and (= x y) (distinct (f (g x)) (f (g y)))) false))
            "#,
        r#"
                (set-logic HORN)
                (declare-fun f ((_ BitVec 8)) (_ BitVec 16))
                (declare-var x (_ BitVec 8))
                (declare-var y (_ BitVec 8))
                (rule (=> (and (= x y) (distinct (f x) (f y))) false))
            "#,
    ] {
        let result = solve_only_constraint(input);
        assert!(
            result.is_unsat(),
            "x = y must imply f(x) = f(y), got {result:?}"
        );
    }
}

#[test]
fn test_scalar_return_declare_fun_keeps_distinct_applications_independent() {
    let input = r#"
            (set-logic HORN)
            (declare-fun f (Int) Int)
            (declare-var x Int)
            (declare-var y Int)
            (rule (=> (and (distinct x y) (distinct (f x) (f y))) false))
        "#;

    let result = solve_only_constraint(input);
    assert!(
        result.is_sat(),
        "different UF arguments may have different results, got {result:?}"
    );
}

#[test]
fn test_scalar_return_nullary_declare_fun_parses_as_stable_constant() {
    let input = r#"
            (set-logic HORN)
            (declare-fun c () Int)
            (declare-var x Int)
            (rule (=> (and (= x c) (distinct x c)) false))
        "#;

    let result = solve_only_constraint(input);
    assert!(
        result.is_unsat(),
        "two occurrences of one nullary UF must denote the same value, got {result:?}"
    );
}

#[test]
fn test_local_binding_shadows_scalar_nullary_uf() {
    for local_formula in ["(= (let ((c 0)) c) 0)", "(exists ((c Int)) (= c 0))"] {
        let input = format!(
            "(set-logic HORN)\n\
             (declare-fun c () Int)\n\
             (rule (=> (and (= c 1) {local_formula}) false))"
        );
        let result = solve_only_constraint(&input);
        assert!(
            result.is_sat(),
            "the local c must shadow global c; otherwise c=1 and c=0 become contradictory: \
             {local_formula}, got {result:?}"
        );
    }
}

#[test]
fn test_non_horn_nested_relation_fails_validation_before_query_slicing() {
    let problem = ChcParser::parse(
        r#"
            (set-logic HORN)
            (declare-rel P ())
            (declare-var x Int)
            (rule P)
            (query (or P (= x 0)))
        "#,
    )
    .expect("the surface parser retains the non-Horn Boolean shape for validation");

    assert!(
        matches!(problem.validate(), Err(crate::ChcError::Verification(_))),
        "a relation nested in a background constraint must not reach dependency slicing"
    );
}

#[test]
fn test_scalar_return_uf_congruence_is_shared_across_horn_rules() {
    let input = r#"
            (set-logic HORN)
            (declare-fun f (Int) Int)
            (declare-rel P (Int))
            (declare-var x Int)
            (rule (P (f 0)))
            (rule (=> (and (P x) (distinct x (f 0))) false))
        "#;
    let problem = ChcParser::parse(input).expect("cross-rule UF fixture should parse");
    let result = engines::solve_bmc_only(
        problem,
        BmcConfig {
            max_depth: 4,
            acyclic_safe: true,
            prefer_exact_acyclic_first: true,
            ..BmcConfig::default()
        },
    );
    assert!(
        result.is_safe(),
        "one UF symbol must keep its interpretation across a derivation: got {result:?}"
    );
}

#[test]
fn test_parameterized_int_uf_reaches_end_to_end_unsafe() {
    let problem = ChcParser::parse(
        r#"
            (set-logic HORN)
            (declare-fun f (Int) Int)
            (declare-rel P (Int))
            (declare-var x Int)
            (rule (P (f 0)))
            (rule (=> (and (P x) (= (f 0) 7)) false))
        "#,
    )
    .expect("Int UF unsafe fixture should parse");
    let result = engines::solve_bmc_only(
        problem,
        BmcConfig {
            max_depth: 4,
            ..BmcConfig::default()
        },
    );
    assert!(
        result.is_unsafe(),
        "a concrete finite interpretation f(0)=7 witnesses Unsafe: {result:?}"
    );
}

#[test]
fn test_parameterized_bv_uf_reaches_end_to_end_unsafe() {
    let problem = ChcParser::parse(
        r#"
            (set-logic HORN)
            (declare-fun f ((_ BitVec 8)) (_ BitVec 16))
            (declare-rel P ((_ BitVec 16)))
            (declare-var x (_ BitVec 16))
            (rule (P (f #x03)))
            (rule (=> (and (P x) (= (f #x03) #x1234)) false))
        "#,
    )
    .expect("BV UF unsafe fixture should parse");
    let result = engines::solve_bmc_only(
        problem,
        BmcConfig {
            max_depth: 4,
            ..BmcConfig::default()
        },
    );
    assert!(
        result.is_unsafe(),
        "a concrete finite interpretation f(#x03)=#x1234 witnesses Unsafe: {result:?}"
    );
}

#[test]
fn test_parameterized_uf_multi_premise_query_ground_replays_unsafe() {
    let problem = ChcParser::parse(
        r#"
            (set-logic HORN)
            (declare-fun f (Int) Int)
            (declare-rel P (Int))
            (declare-rel Q (Int))
            (declare-var x Int)
            (declare-var y Int)
            (rule (P (f 0)))
            (rule (Q (f 0)))
            (rule (=> (and (P x) (Q y) (= x y) (= (f 0) 7)) false))
        "#,
    )
    .expect("multi-premise UF unsafe fixture should parse");
    let result = engines::solve_bmc_only(
        problem,
        BmcConfig {
            max_depth: 4,
            ..BmcConfig::default()
        },
    );
    assert!(
        result.is_unsafe(),
        "finite UF observations must survive pure multi-premise ground replay: {result:?}"
    );
}

#[test]
fn test_scalar_return_declare_fun_checks_application_signature() {
    for (application, expected) in [
        ("(f x x)", "expects 1 arguments, got 2"),
        ("(f b)", "expected argument sort Int, got Bool"),
    ] {
        let input = format!(
            "(set-logic HORN)\n\
             (declare-fun f (Int) Int)\n\
             (declare-var x Int)\n\
             (declare-var b Bool)\n\
             (rule (=> (= {application} 0) false))"
        );
        let error = ChcParser::parse(&input).expect_err("invalid UF call must fail closed");
        assert!(
            error.to_string().contains(expected),
            "expected {expected:?} in error, got {error}"
        );
    }
}

#[test]
fn test_scalar_return_declare_fun_rejects_symbol_collisions() {
    for input in [
        "(declare-fun f (Int) Int) (declare-fun f (Int) Int)",
        "(declare-fun f (Int) Int) (declare-fun f (Bool) Int)",
        "(declare-fun f (Int) Int) (declare-rel f (Int))",
        "(declare-rel f (Int)) (declare-fun f (Int) Int)",
        "(declare-fun f (Int) Int) (declare-var f Int)",
        "(declare-var f Int) (declare-fun f (Int) Int)",
        "(declare-fun f (Int) Int) (declare-datatype T ((f)))",
        "(declare-datatype T ((f))) (declare-fun f (Int) Int)",
    ] {
        let error = ChcParser::parse(input).expect_err("symbol collision must fail closed");
        assert!(
            error.to_string().contains("already declared"),
            "collision error should identify the existing declaration: {error}"
        );
    }
}

#[test]
fn test_scalar_return_declare_fun_rejects_non_scalar_boundary() {
    for input in [
        "(declare-fun f (Int) (Array Int Int))",
        "(declare-fun f ((Array Int Int)) Int)",
        "(declare-fun select (Int) Int)",
        "(declare-fun as (Int) Int)",
        "(declare-fun const (Int) Int)",
        "(declare-fun let (Int) Int)",
        "(declare-datatype T ((as)))",
    ] {
        let error = ChcParser::parse(input).expect_err("out-of-scope UF must fail closed");
        let message = error.to_string();
        assert!(
            message.contains("non-scalar") || message.contains("active logic"),
            "error should describe the bounded UF boundary: {message}"
        );
    }
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
