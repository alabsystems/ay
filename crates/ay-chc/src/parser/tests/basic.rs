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

/// Quantifier stripping is polarity-dependent. A `forall` in a rule BODY is
/// hoisted into the flat clause scope, which turns `forall i. (B(i) -> H)`
/// into `(exists i. B(i)) -> H` -- a WEAKENED antecedent that can fabricate a
/// counterexample. It must be recorded so the verdict can be downgraded.
///
/// Regression for the wrong-answer witness: on this shape ay used to answer
/// `sat` where z3 4.16.0 answers `unsat`.
#[test]
fn body_position_forall_is_flagged_as_overapproximation() {
    let input = r#"
        (set-logic HORN)
        (declare-var a (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-var b (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-rel P ((Array (_ BitVec 64) (_ BitVec 64))))
        (declare-rel bad ())
        (rule (=> (forall ((i (_ BitVec 64))) (= (select b i) #x0000000000000007)) (P b)))
        (rule (=> (and (P a) (not (= (select a #x0000000000000005) #x0000000000000007))) bad))
        (query bad)
    "#;
    let problem = ChcParser::parse(input).expect("body-forall must still parse");
    assert!(
        problem.has_stripped_body_forall(),
        "a body-position forall must be flagged as an over-approximation"
    );
}

/// A `forall` at POSITIVE polarity is the legitimate implicit-universal
/// wrapper; stripping it is equivalence-preserving and must NOT flag.
#[test]
fn positive_position_forall_is_not_flagged() {
    let input = r#"
        (set-logic HORN)
        (declare-var x Int)
        (declare-rel Inv (Int))
        (rule (=> (= x 0) (Inv x)))
        (query (and (Inv x) (< x 0)))
    "#;
    let problem = ChcParser::parse(input).expect("plain rule must parse");
    assert!(
        !problem.has_stripped_body_forall(),
        "no body-position forall here, so nothing may be flagged"
    );
}

/// An `exists` in a HEAD would be STRENGTHENED to `forall` by stripping,
/// making facts derivable that the input never entailed -- a false-proof
/// route. No verdict downgrade can repair that, so it must be rejected.
#[test]
fn head_position_exists_is_rejected() {
    let input = r#"
        (set-logic HORN)
        (declare-rel Q ((_ BitVec 8)))
        (rule (=> true (exists ((y (_ BitVec 8))) (Q y))))
    "#;
    let err = ChcParser::parse(input).expect_err("head-exists must be rejected, not mis-parsed");
    let msg = format!("{err}");
    assert!(
        msg.contains("exists") && msg.contains("STRENGTHENED"),
        "error should explain the strengthening risk, got: {msg}"
    );
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
