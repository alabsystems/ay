// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::{ChcDtConstructor, ChcDtSelector, ChcOp};
use std::sync::Arc;
#[test]
fn parse_define_fun_basic_model_entry() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
; comment
(define-fun inv ((x Int)) Bool
  (and (>= x 0) (<= x 10)))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).expect("missing inv interpretation");

    assert_eq!(interp.vars, vec![ChcVar::new("x", ChcSort::Int)]);
    assert_eq!(
        interp.formula,
        ChcExpr::and(
            ChcExpr::ge(
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::int(0)
            ),
            ChcExpr::le(
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::int(10)
            ),
        )
    );
}

#[test]
fn parse_spacer_wrapper_multiple_definitions() {
    let mut problem = ChcProblem::new();
    let inv0 = problem.declare_predicate("inv0", vec![ChcSort::Int]);
    let inv1 = problem.declare_predicate("inv1", vec![ChcSort::Int]);

    let input = r#"
(
  (define-fun inv0 ((x Int)) Bool (>= x 0))
  (define-fun inv1 ((y Int)) Bool (<= y 10))
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    assert_eq!(
        model.len(),
        2,
        "model should contain exactly 2 predicate interpretations"
    );

    let interp0 = model.get(&inv0).expect("model must contain inv0");
    assert_eq!(interp0.vars, vec![ChcVar::new("x", ChcSort::Int)]);
    assert_eq!(
        interp0.formula,
        ChcExpr::ge(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(0)
        )
    );

    let interp1 = model.get(&inv1).expect("model must contain inv1");
    assert_eq!(interp1.vars, vec![ChcVar::new("y", ChcSort::Int)]);
    assert_eq!(
        interp1.formula,
        ChcExpr::le(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::int(10)
        )
    );
}

#[test]
fn parse_z3_recursive_datatype_model_selectors_and_testers() {
    let list_sort = ChcSort::Datatype {
        name: "listOfInt".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "conslistOfInt".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "headlistOfInt".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "taillistOfInt".to_string(),
                        sort: ChcSort::Uninterpreted("listOfInt".to_string()),
                    },
                ],
            },
            ChcDtConstructor {
                name: "nillistOfInt".to_string(),
                selectors: vec![],
            },
        ]),
    };
    let mut problem = ChcProblem::new();
    problem.add_datatype_def(
        "listOfInt".to_string(),
        vec![
            (
                "conslistOfInt".to_string(),
                vec![
                    ("headlistOfInt".to_string(), ChcSort::Int),
                    ("taillistOfInt".to_string(), list_sort.clone()),
                ],
            ),
            ("nillistOfInt".to_string(), vec![]),
        ],
    );
    let inv = problem.declare_predicate("Inv", vec![list_sort]);

    let input = r#"
(
  (define-fun Inv ((x!0 listOfInt)) Bool
    (let ((a!1 ((_ is nillistOfInt) (taillistOfInt x!0))))
      (or a!1 (= x!0 nillistOfInt) (>= (headlistOfInt x!0) 0))))
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).expect("Inv interpretation should parse");
    assert!(matches!(
        &interp.vars[0].sort,
        ChcSort::Datatype { name, .. } if name == "listOfInt"
    ));
    assert!(
        format!("{:?}", interp.formula).contains("is-nillistOfInt"),
        "Z3 indexed datatype tester should be parsed as a Bool function application: {:?}",
        interp.formula
    );
    assert!(
        format!("{:?}", interp.formula).contains("headlistOfInt"),
        "datatype selector applications should be preserved: {:?}",
        interp.formula
    );
}

#[test]
fn parse_quoted_predicate_and_var_names() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("my inv", vec![ChcSort::Int]);

    let input = r#"(define-fun |my inv| ((|my var| Int)) Bool (>= |my var| 0))"#;
    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    assert_eq!(interp.vars, vec![ChcVar::new("my var", ChcSort::Int)]);
}

#[test]
fn parse_define_fun_skips_unknown_predicates() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
(define-fun unknown ((x Int)) Bool true)
(define-fun inv ((x Int)) Bool true)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    assert_eq!(model.len(), 1, "only known predicates should be in model");
    let interp = model.get(&inv).expect("model must contain inv");
    assert_eq!(
        interp.formula,
        ChcExpr::Bool(true),
        "inv body should be true"
    );
}

#[test]
fn parse_define_fun_param_count_mismatch_errors() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    let input = r#"(define-fun inv ((x Int)) Bool true)"#;
    let err = InvariantModel::parse_smtlib(input, &problem).unwrap_err();
    assert!(matches!(err, ChcError::Parse(_)));
}

#[test]
fn parse_define_fun_return_type_must_be_bool() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"(define-fun inv ((x Int)) Int 0)"#;
    let err = InvariantModel::parse_smtlib(input, &problem).unwrap_err();
    assert!(matches!(err, ChcError::Parse(_)));
}

#[test]
fn parse_array_sorts_select_store_and_const_arrays() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate(
        "inv",
        vec![
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
            ChcSort::Int,
        ],
    );

    let input = r#"
(define-fun inv ((arr (Array Int Int)) (i Int)) Bool
  (and
(= (select arr i) 0)
(= (store arr i 1) ((as const (Array Int Int)) 0))
  )
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    assert_eq!(interp.vars.len(), 2);
    assert_eq!(
        interp.vars[0].sort,
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
    );
    assert_eq!(interp.vars[1].sort, ChcSort::Int);
}

#[test]
fn parse_nary_distinct_and_chained_comparisons() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let input = r#"
(define-fun inv ((a Int) (b Int) (c Int)) Bool
  (and
(distinct a b c)
(< a b c)
  )
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model
        .get(&inv)
        .expect("model must contain parsed interpretation for inv");

    assert_eq!(
        interp.vars,
        vec![
            ChcVar::new("a", ChcSort::Int),
            ChcVar::new("b", ChcSort::Int),
            ChcVar::new("c", ChcSort::Int),
        ]
    );

    let atoms = match &interp.formula {
        ChcExpr::Op(ChcOp::And, args) => args.iter().map(|arg| arg.as_ref().clone()).collect(),
        other => vec![other.clone()],
    };

    // distinct(a,b,c) expands to 3 pairwise != constraints.
    // (< a b c) expands to 2 chained < constraints.
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Int));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Int));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Int));
    let expected_atoms = vec![
        ChcExpr::ne(a.clone(), b.clone()),
        ChcExpr::ne(a.clone(), c.clone()),
        ChcExpr::ne(b.clone(), c.clone()),
        ChcExpr::lt(a, b.clone()),
        ChcExpr::lt(b, c),
    ];
    assert_eq!(
        atoms.len(),
        expected_atoms.len(),
        "expected exactly 5 conjunctive atoms after n-ary expansion"
    );
    for expected in expected_atoms {
        assert!(
            atoms.iter().any(|actual| actual == &expected),
            "missing expanded atom: {expected:?}"
        );
    }
}

#[test]
fn parse_real_division_accepts_explicit_unary_negation() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
(define-fun inv ((x Int)) Bool
  (= (/ (- 3) 4) (/ -3 4))
)
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    // Both sides should parse as the same Real(-3,4) after normalization.
    match &interp.formula {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            assert_eq!(args[0].as_ref(), args[1].as_ref());
            assert!(matches!(args[0].as_ref(), ChcExpr::Real(-3, 4)));
        }
        other => panic!("expected equality, got {other:?}"),
    }
}

#[test]
fn parse_let_expressions_substitutes_bindings() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Golem-style let bindings
    let input = r#"
(define-fun inv ((x Int) (y Int)) Bool
  (let ((sum (+ x y)))
(let ((bound (<= sum 10)))
  bound)))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    // After substitution: (<= (+ x y) 10)
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expected = ChcExpr::le(
        ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
        ChcExpr::int(10),
    );
    assert_eq!(interp.formula, expected);
}

#[test]
fn parse_nested_let_with_multiple_bindings() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"
(define-fun inv ((x Int)) Bool
  (let ((a (+ x 1)) (b (+ x 2)))
(and (>= a 0) (>= b 0))))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    // After substitution: (and (>= (+ x 1) 0) (>= (+ x 2) 0))
    let x = ChcVar::new("x", ChcSort::Int);
    let expected = ChcExpr::and(
        ChcExpr::ge(
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ChcExpr::int(0),
        ),
        ChcExpr::ge(
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
            ChcExpr::int(0),
        ),
    );
    assert_eq!(interp.formula, expected);
}

#[test]
fn parse_unbalanced_parens_errors() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("inv", vec![ChcSort::Int]);

    // Missing closing paren
    let input = r#"(define-fun inv ((x Int)) Bool (>= x 0)"#;
    let err = InvariantModel::parse_smtlib(input, &problem).unwrap_err();
    assert!(matches!(err, ChcError::Parse(_)));
}

#[test]
fn parse_nested_ite() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    // Nested ITE: (ite (>= x 5) 1 (ite (>= x 0) 0 (- 1)))
    // Represents: if x >= 5 then 1 elif x >= 0 then 0 else -1
    let input = r#"
(define-fun inv ((x Int)) Bool
  (>= (ite (>= x 5) 1 (ite (>= x 0) 0 (- 1))) 0))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).expect("model must contain inv");

    assert_eq!(interp.vars, vec![ChcVar::new("x", ChcSort::Int)]);

    let x = ChcVar::new("x", ChcSort::Int);
    let inner_ite = ChcExpr::ite(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::int(0),
        ChcExpr::neg(ChcExpr::int(1)),
    );
    let outer_ite = ChcExpr::ite(
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5)),
        ChcExpr::int(1),
        inner_ite,
    );
    let expected = ChcExpr::ge(outer_ite, ChcExpr::int(0));
    assert_eq!(
        interp.formula, expected,
        "nested ITE structure must be preserved"
    );
}

#[test]
fn parse_implies_binary_operator() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let input = r#"(define-fun inv ((x Int)) Bool (=> (>= x 0) (<= x 10)))"#;
    let model = InvariantModel::parse_smtlib(input, &problem).unwrap();
    let interp = model.get(&inv).unwrap();

    let x = ChcVar::new("x", ChcSort::Int);
    let expected = ChcExpr::implies(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10)),
    );
    assert_eq!(interp.formula, expected);
}

#[test]
fn bitvector_model_output_round_trips_as_typed_chc_ops() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Bool, ChcSort::BitVec(64)]);
    let input = r#"
(define-fun Inv ((flag Bool) (count (_ BitVec 64))) Bool
  (and
    (or flag (not (= ((_ extract 0 0) count) (_ bv1 1))))
    (= (bvand (bvsub count (_ bv1 64)) (_ bv1 64)) (_ bv1 64))))
"#;

    let model = InvariantModel::parse_smtlib(input, &problem).expect("BV model should parse");
    let interpretation = model.get(&inv).expect("Inv interpretation");
    let formula_debug = format!("{:?}", interpretation.formula);
    assert!(formula_debug.contains("BvExtract(0, 0)"));
    assert!(formula_debug.contains("BvAnd"));
    assert!(formula_debug.contains("BvSub"));

    let canonical = model.to_smtlib(&problem);
    let reparsed = InvariantModel::parse_smtlib(&canonical, &problem)
        .expect("AY's emitted BV model must parse back");
    assert_eq!(reparsed.to_smtlib(&problem), canonical);
}

#[test]
fn emitted_bitvector_operator_vocabulary_round_trips() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(8)]);
    let bodies = [
        ("(= (bvadd x (_ bv1 8)) (_ bv2 8))", ChcOp::BvAdd),
        ("(= (bvsub x (_ bv1 8)) (_ bv0 8))", ChcOp::BvSub),
        ("(= (bvmul x (_ bv2 8)) (_ bv4 8))", ChcOp::BvMul),
        ("(= (bvudiv x (_ bv2 8)) (_ bv1 8))", ChcOp::BvUDiv),
        ("(= (bvurem x (_ bv2 8)) (_ bv0 8))", ChcOp::BvURem),
        ("(= (bvsdiv x (_ bv2 8)) (_ bv1 8))", ChcOp::BvSDiv),
        ("(= (bvsrem x (_ bv2 8)) (_ bv0 8))", ChcOp::BvSRem),
        ("(= (bvsmod x (_ bv2 8)) (_ bv0 8))", ChcOp::BvSMod),
        ("(= (bvand x (_ bv1 8)) (_ bv1 8))", ChcOp::BvAnd),
        ("(= (bvor x (_ bv1 8)) (_ bv1 8))", ChcOp::BvOr),
        ("(= (bvxor x (_ bv1 8)) (_ bv0 8))", ChcOp::BvXor),
        ("(= (bvnand x (_ bv1 8)) (_ bv254 8))", ChcOp::BvNand),
        ("(= (bvnor x (_ bv1 8)) (_ bv0 8))", ChcOp::BvNor),
        ("(= (bvxnor x (_ bv1 8)) (_ bv255 8))", ChcOp::BvXnor),
        ("(= (bvnot x) (_ bv0 8))", ChcOp::BvNot),
        ("(= (bvneg x) (_ bv0 8))", ChcOp::BvNeg),
        ("(= (bvshl x (_ bv1 8)) (_ bv0 8))", ChcOp::BvShl),
        ("(= (bvlshr x (_ bv1 8)) (_ bv0 8))", ChcOp::BvLShr),
        ("(= (bvashr x (_ bv1 8)) (_ bv0 8))", ChcOp::BvAShr),
        ("(bvult x (_ bv1 8))", ChcOp::BvULt),
        ("(bvule x (_ bv1 8))", ChcOp::BvULe),
        ("(bvugt x (_ bv1 8))", ChcOp::BvUGt),
        ("(bvuge x (_ bv1 8))", ChcOp::BvUGe),
        ("(bvslt x (_ bv1 8))", ChcOp::BvSLt),
        ("(bvsle x (_ bv1 8))", ChcOp::BvSLe),
        ("(bvsgt x (_ bv1 8))", ChcOp::BvSGt),
        ("(bvsge x (_ bv1 8))", ChcOp::BvSGe),
        ("(= (bvcomp x (_ bv1 8)) (_ bv1 1))", ChcOp::BvComp),
        ("(= (concat x x) (_ bv0 16))", ChcOp::BvConcat),
        ("(= (bv2nat x) 1)", ChcOp::Bv2Nat),
        ("(= ((_ extract 3 0) x) (_ bv0 4))", ChcOp::BvExtract(3, 0)),
        (
            "(= ((_ zero_extend 8) x) (_ bv0 16))",
            ChcOp::BvZeroExtend(8),
        ),
        (
            "(= ((_ sign_extend 8) x) (_ bv0 16))",
            ChcOp::BvSignExtend(8),
        ),
        (
            "(= ((_ rotate_left 1) x) (_ bv0 8))",
            ChcOp::BvRotateLeft(1),
        ),
        (
            "(= ((_ rotate_right 1) x) (_ bv0 8))",
            ChcOp::BvRotateRight(1),
        ),
        ("(= ((_ repeat 2) x) (_ bv0 16))", ChcOp::BvRepeat(2)),
        ("(= ((_ int2bv 8) 1) (_ bv1 8))", ChcOp::Int2Bv(8)),
    ];

    for (body, expected_op) in bodies {
        let source = format!("(define-fun Inv ((x (_ BitVec 8))) Bool {body})");
        let model = InvariantModel::parse_smtlib(&source, &problem)
            .unwrap_or_else(|error| panic!("operator body `{body}` failed: {error}"));
        let interpretation = model.get(&inv).expect("Inv interpretation");
        assert!(
            expression_contains_op(&interpretation.formula, expected_op),
            "body `{body}` did not parse as {expected_op:?}: {:?}",
            interpretation.formula
        );
        let canonical = model.to_smtlib(&problem);
        let reparsed = InvariantModel::parse_smtlib(&canonical, &problem)
            .unwrap_or_else(|error| panic!("canonical body `{body}` failed: {error}"));
        assert_eq!(reparsed.to_smtlib(&problem), canonical, "body `{body}`");
    }
}

fn expression_contains_op(expression: &ChcExpr, expected: ChcOp) -> bool {
    match expression {
        ChcExpr::Op(actual, args) => {
            *actual == expected
                || args
                    .iter()
                    .any(|argument| expression_contains_op(argument, expected))
        }
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => args
            .iter()
            .any(|argument| expression_contains_op(argument, expected)),
        ChcExpr::ConstArray(_, value) => expression_contains_op(value, expected),
        _ => false,
    }
}

#[test]
fn malformed_or_unbounded_bitvector_indices_fail_closed() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate("Inv", vec![ChcSort::BitVec(8)]);
    let invalid_bodies = [
        "(= ((_ extract 0 1) x) (_ bv0 1))",
        "(= ((_ repeat 0) x) (_ bv0 8))",
        "(= ((_ int2bv 0) 1) (_ bv0 1))",
        "(= ((_ zero_extend 1048577) x) (_ bv0 8))",
        "(= (_ bv0 0) (_ bv0 8))",
        "(= (_ bv256 8) (_ bv0 8))",
    ];

    for body in invalid_bodies {
        let source = format!("(define-fun Inv ((x (_ BitVec 8))) Bool {body})");
        assert!(
            InvariantModel::parse_smtlib(&source, &problem).is_err(),
            "malformed body `{body}` must fail closed"
        );
    }

    for width in ["0", "1048577", "4294967297"] {
        let source = format!("(define-fun Inv ((x (_ BitVec {width}))) Bool true)");
        assert!(
            InvariantModel::parse_smtlib(&source, &problem).is_err(),
            "unsupported width `{width}` must fail closed"
        );
    }
}
