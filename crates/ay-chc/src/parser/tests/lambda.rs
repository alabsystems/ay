// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn expression(text: &str) -> ChcExpr {
    let mut parser = ChcParser::new();
    parser.input = text.into();
    let value = parser
        .parse_expr()
        .expect("well-typed array lambda must parse");
    parser.skip_whitespace_and_comments();
    assert_eq!(parser.pos, parser.input.len());
    value
}

#[test]
fn closed_array_lambda_has_no_free_binder() {
    let value = expression("(lambda ((i Int)) (+ i 1))");
    assert_eq!(
        value.sort(),
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
    );
    assert!(
        value.vars().is_empty(),
        "the lambda binder is not a clause variable"
    );
}

#[test]
fn bitvector_array_lambda_keeps_only_outer_free_variables() {
    let mut parser = ChcParser::new();
    parser.variables.insert("base".into(), ChcSort::BitVec(64));
    parser.input = "(lambda ((i (_ BitVec 64))) (bvadd i base))".into();
    let value = parser.parse_expr().expect("typed bitvector lambda");
    let variables = value.vars();
    assert_eq!(variables.len(), 1);
    assert_eq!(variables[0].name, "base");
    assert_eq!(
        value.sort(),
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(64)),)
    );
}

#[test]
fn nested_array_lambda_shadowing_restores_outer_scope() {
    let value = expression("(lambda ((x Int)) (+ x (select (lambda ((x Int)) (+ x 2)) 3)))");
    assert!(value.vars().is_empty());
}

#[test]
fn malformed_or_multivariable_array_lambdas_are_rejected() {
    for input in [
        "(lambda () 1)",
        "(lambda ((x Int) (y Int)) (+ x y))",
        "(lambda ((x)) x)",
        "(lambda ((x (_ BitVec 0))) x)",
    ] {
        let mut parser = ChcParser::new();
        parser.input = input.into();
        assert!(
            parser.parse_expr().is_err(),
            "unexpectedly accepted {input}"
        );
    }
}

#[test]
fn array_lambda_let_and_binder_scopes_do_not_capture() {
    let cases = [
        ("(let ((x 11)) (select (lambda ((x Int)) (+ x 1)) 2))", 3),
        ("(let ((x 11)) (select (lambda ((i Int)) (+ i x)) 2))", 13),
        ("(select (lambda ((x Int)) (let ((x 7)) (+ x 1))) 2)", 8),
        (
            "(select (lambda ((x Int)) (+ x (select (lambda ((x Int)) (+ x 2)) 3))) 5)",
            10,
        ),
    ];
    for (text, expected) in cases {
        let expression = expression(text);
        assert_eq!(
            crate::expr::evaluate_expr(&expression, &Default::default()),
            Some(crate::smt::SmtValue::Int(expected)),
            "{text}"
        );
    }
}

#[test]
fn array_lambda_quantifiers_fail_without_hoisting() {
    for text in [
        "(lambda ((x Int)) (forall ((y Int)) (= y x)))",
        "(lambda ((x Int)) (exists ((y Int)) (= y x)))",
    ] {
        let mut parser = ChcParser::new();
        parser.input = text.into();
        assert!(parser.parse_expr().is_err());
        assert!(
            parser.variables.is_empty(),
            "lambda scope must be restored on error"
        );
        assert!(parser.active_renames.is_empty());
        assert_eq!(parser.lambda_depth, 0);
    }
}

#[test]
fn array_lambda_serialization_roundtrips_lexical_scopes() {
    let original = expression(
        "(let ((offset 9)) (lambda ((x Int)) (+ x (select (lambda ((x Int)) (+ offset x)) 2))))",
    );
    let rendered = crate::InvariantModel::expr_to_smtlib(&original);
    let restored = expression(&rendered);
    assert_eq!(original, restored, "{rendered}");
    assert!(restored.vars().is_empty());
}
