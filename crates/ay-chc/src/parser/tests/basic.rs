// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_simple_chc() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
}

#[test]
fn test_parse_sort() {
    let mut parser = ChcParser::new();
    parser.input = "Int".to_string();
    parser.pos = 0;
    let sort = parser.parse_sort().expect("test should succeed");
    assert_eq!(sort, ChcSort::Int);

    parser.input = "Bool".to_string();
    parser.pos = 0;
    let sort = parser.parse_sort().expect("test should succeed");
    assert_eq!(sort, ChcSort::Bool);

    parser.input = "(_ BitVec 32)".to_string();
    parser.pos = 0;
    let sort = parser.parse_sort().expect("test should succeed");
    assert_eq!(sort, ChcSort::BitVec(32));
}

#[test]
fn test_parse_expr_literal() {
    let mut parser = ChcParser::new();

    parser.input = "42".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert_eq!(expr, ChcExpr::int(42));

    parser.input = "-10".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert_eq!(expr, ChcExpr::int(-10));

    parser.input = "true".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert_eq!(expr, ChcExpr::Bool(true));
}

#[test]
fn test_parse_expr_arithmetic() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(+ x 1)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    // Just check it parses without error
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Add, _)));

    parser.input = "(- x 5)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Sub, _)));
}

#[test]
fn test_parse_expr_comparison() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(< x 10)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Lt, _)));

    parser.input = "(= x 0)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Eq, _)));
}

#[test]
fn test_parse_expr_boolean() {
    let mut parser = ChcParser::new();
    parser.variables.insert("a".to_string(), ChcSort::Bool);
    parser.variables.insert("b".to_string(), ChcSort::Bool);

    parser.input = "(and a b)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::And, _)));

    parser.input = "(or a b)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Or, _)));

    parser.input = "(not a)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Not, _)));
}

#[test]
fn test_parse_expr_implication() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Int);

    parser.input = "(=> (= x 0) (< x 10))".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Implies, _)));
}

#[test]
fn test_parse_let_expr() {
    let mut parser = ChcParser::new();

    parser.input = "(let ((x 5)) (+ x 1))".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    // After substitution, should be (+ 5 1)
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Add, _)));
}

#[test]
fn test_parse_forall_expr() {
    let mut parser = ChcParser::new();

    parser.input = "(forall ((x Int)) (>= x 0))".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("test should succeed");
    // Forall is stripped for CHC, just returns body
    assert!(matches!(expr, ChcExpr::Op(ChcOp::Ge, _)));
}

#[test]
fn test_parse_chc_with_rule() {
    let input = r#"
            (set-logic HORN)
            (declare-rel Inv (Int))
            (declare-var x Int)
            (rule (=> (= x 0) (Inv x)))
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
    // Rule should be added
    assert!(!problem.clauses().is_empty());
}

#[test]
fn test_parse_comments() {
    let input = r#"
            ; This is a comment
            (set-logic HORN) ; inline comment
            (declare-rel Inv (Int)) ; another comment
        "#;

    let problem = ChcParser::parse(input).expect("test should succeed");
    assert_eq!(problem.predicates().len(), 1);
}
