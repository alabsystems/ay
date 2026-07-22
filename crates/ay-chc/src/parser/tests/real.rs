// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parse_decimal_real_literals() {
    let mut parser = ChcParser::new();

    parser.input = "12.3400".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("decimal real should parse");
    assert_eq!(expr, ChcExpr::Real(617, 50));

    parser.input = "-0.125".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("negative decimal real should parse");
    assert_eq!(expr, ChcExpr::Real(-1, 8));
}

#[test]
fn test_parse_constant_real_division() {
    let mut parser = ChcParser::new();

    parser.input = "(/ 3 4)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("integer real division should parse");
    assert_eq!(expr, ChcExpr::Real(3, 4));

    parser.input = "(/ 1.5 0.5)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("decimal real division should parse");
    assert_eq!(expr, ChcExpr::Real(3, 1));
}

#[test]
fn test_parse_symbolic_real_division_by_constant_as_scaled_term() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Real);

    parser.input = "(/ x 2)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("real division by constant should parse");

    let ChcExpr::Op(ChcOp::Mul, args) = &expr else {
        panic!("expected division by constant to become multiplication, got {expr:?}");
    };
    assert_eq!(args.len(), 2);
    assert_eq!(args[0].as_ref(), &ChcExpr::Real(1, 2));
    assert!(matches!(
        args[1].as_ref(),
        ChcExpr::Var(v) if v.name == "x" && v.sort == ChcSort::Real
    ));
}

#[test]
fn test_parse_symbolic_real_division_by_symbolic_denominator() {
    let mut parser = ChcParser::new();
    parser.variables.insert("x".to_string(), ChcSort::Real);
    parser.variables.insert("y".to_string(), ChcSort::Real);

    parser.input = "(/ x y)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("symbolic real division should parse");

    let ChcExpr::Op(ChcOp::Div, args) = &expr else {
        panic!("expected symbolic division to remain a division term, got {expr:?}");
    };
    assert_eq!(args.len(), 2);
    assert!(matches!(args[0].as_ref(), ChcExpr::Var(v) if v.name == "x"));
    assert!(matches!(args[1].as_ref(), ChcExpr::Var(v) if v.name == "y"));
}

#[test]
fn test_parse_real_predicate_application_coerces_int_literal() {
    let mut parser = ChcParser::new();
    parser.predicates.insert(
        "P".to_string(),
        (crate::PredicateId::new(0), vec![ChcSort::Real]),
    );

    parser.input = "(P 0)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("Real predicate argument should coerce Int literal");

    let ChcExpr::PredicateApp(_, _, args) = &expr else {
        panic!("expected predicate app");
    };
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].as_ref(), &ChcExpr::Real(0, 1));
}

#[test]
fn test_parse_real_predicate_preserves_mixed_arithmetic_shape() {
    let mut parser = ChcParser::new();
    parser.variables.insert("i".to_string(), ChcSort::Int);
    parser.variables.insert("r".to_string(), ChcSort::Real);
    parser.predicates.insert(
        "P".to_string(),
        (crate::PredicateId::new(0), vec![ChcSort::Real]),
    );

    parser.input = "(P (+ i r))".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("mixed Int/Real arithmetic should satisfy a Real predicate argument");

    let ChcExpr::PredicateApp(_, _, args) = &expr else {
        panic!("expected predicate app");
    };
    assert_eq!(args.len(), 1);
    assert!(
        matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Add, add_args)
            if matches!(add_args[0].as_ref(), ChcExpr::Var(v) if v.name == "i")
                && matches!(add_args[1].as_ref(), ChcExpr::Var(v) if v.name == "r")),
        "mixed arithmetic should not be wrapped in whole-expression to_real: {expr:?}"
    );
}

#[test]
fn test_parse_int_real_conversion_ops() {
    let mut parser = ChcParser::new();
    parser.variables.insert("b".to_string(), ChcSort::Bool);
    parser.variables.insert("i".to_string(), ChcSort::Int);
    parser.variables.insert("r".to_string(), ChcSort::Real);

    parser.input = "(to_real 7)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("constant to_real should parse");
    assert_eq!(expr, ChcExpr::Real(7, 1));

    parser.input = "(to_real i)".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("symbolic Int to_real should parse");
    assert!(matches!(
        expr,
        ChcExpr::FuncApp(ref name, ChcSort::Real, ref args)
            if name == "to_real" && args.len() == 1
    ));

    parser.input = "(to_real r)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("Real to_real should parse");
    assert!(matches!(&expr, ChcExpr::Var(v) if v.name == "r" && v.sort == ChcSort::Real));

    parser.input = "(to_real (ite b 1 2.5))".to_string();
    parser.pos = 0;
    let expr = parser
        .parse_expr()
        .expect("numeric ITE to_real should parse");
    let ChcExpr::Op(ChcOp::Ite, args) = &expr else {
        panic!("expected to_real over numeric ITE to stay an ITE, got {expr:?}");
    };
    assert_eq!(args[1].as_ref(), &ChcExpr::Real(1, 1));
    assert_eq!(args[2].as_ref(), &ChcExpr::Real(5, 2));

    parser.input = "(to_int r)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("to_int should parse");
    assert!(matches!(
        expr,
        ChcExpr::FuncApp(ref name, ChcSort::Int, ref args)
            if name == "to_int" && args.len() == 1
    ));

    parser.input = "(is_int r)".to_string();
    parser.pos = 0;
    let expr = parser.parse_expr().expect("is_int should parse");
    assert!(matches!(
        expr,
        ChcExpr::FuncApp(ref name, ChcSort::Bool, ref args)
            if name == "is_int" && args.len() == 1
    ));
}

#[test]
fn test_parse_predicate_rejects_mismatched_ite_branch_sorts() {
    let mut parser = ChcParser::new();
    parser.variables.insert("b".to_string(), ChcSort::Bool);
    parser.variables.insert("i".to_string(), ChcSort::Int);
    parser.predicates.insert(
        "PInt".to_string(),
        (crate::PredicateId::new(0), vec![ChcSort::Int]),
    );
    parser.predicates.insert(
        "PBool".to_string(),
        (crate::PredicateId::new(1), vec![ChcSort::Bool]),
    );

    for input in ["(PInt (ite b i false))", "(PBool (ite b true 0))"] {
        parser.input = input.to_string();
        parser.pos = 0;
        let err = parser
            .parse_expr()
            .expect_err("mismatched ITE branches should not satisfy predicate sort checks")
            .to_string();
        assert!(
            err.contains("ITE branch sort mismatch"),
            "unexpected error for {input}: {err}"
        );
    }
}

#[test]
fn test_parse_div_mod_reject_real_operands() {
    let mut parser = ChcParser::new();
    parser.variables.insert("i".to_string(), ChcSort::Int);
    parser.variables.insert("r".to_string(), ChcSort::Real);

    for (op, input) in [
        ("div", "(div 3.5 2)"),
        ("div", "(div i r)"),
        ("mod", "(mod 3 2.5)"),
        ("mod", "(mod r i)"),
    ] {
        parser.input = input.to_string();
        parser.pos = 0;
        let err = parser
            .parse_expr()
            .expect_err("Real operand to Int div/mod should fail")
            .to_string();
        assert!(
            err.contains(&format!("'{op}' requires Int arguments")),
            "unexpected error for {input}: {err}"
        );
        assert!(
            err.contains("Real"),
            "error should mention Real sort for {input}: {err}"
        );
    }
}

#[test]
fn test_parse_int_predicate_rejects_mixed_int_real_arithmetic_argument() {
    let mut parser = ChcParser::new();
    parser.variables.insert("i".to_string(), ChcSort::Int);
    parser.variables.insert("r".to_string(), ChcSort::Real);
    parser.predicates.insert(
        "P".to_string(),
        (crate::PredicateId::new(0), vec![ChcSort::Int]),
    );

    for input in ["(P (+ i r))", "(P (* i 1.5))", "(P (- i r))"] {
        parser.input = input.to_string();
        parser.pos = 0;
        let err = parser
            .parse_expr()
            .expect_err("mixed Int/Real arithmetic should not satisfy an Int predicate argument")
            .to_string();
        assert!(
            err.contains("Predicate 'P' expected argument sort Int, got Real"),
            "unexpected error for {input}: {err}"
        );
    }
}
