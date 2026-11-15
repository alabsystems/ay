// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

use super::*;

#[test]
fn existing_singleton_rule_must_not_share_an_inner_existential_witness() {
    // For every Boolean-array cell there exists its Boolean value, even for a
    // nonconstant array. Rewriting this to a=const(j) would be strictly stronger.
    for body in [
        "(exists ((j Bool)) (= (select a i) j))",
        "(forall ((j Bool)) (= (select a i) j))",
        "(let ((v (exists ((j Bool)) (= (select a i) j)))) v)",
    ] {
        let parser = parse_body(body, "(i (_ BitVec 64))", -1);
        assert!(parser.problem.has_stripped_body_forall(), "{body}");
        assert!(parser.quantifier_seen);
    }
    let mut env = Map::default();
    env.insert("a".into(), array(1, [false, true]));
    let cell_equality = op(ChcOp::Eq, vec![read("a", 1), var("j", ChcSort::Bool)]);
    for index in 0..2 {
        env.insert("i".into(), SmtValue::BitVec(index, 1));
        assert!([false, true].into_iter().any(|witness| {
            env.insert("j".into(), SmtValue::Bool(witness));
            evaluate_expr(&cell_equality, &env) == Some(SmtValue::Bool(true))
        }));
    }
    let incorrectly_shared = op(
        ChcOp::Eq,
        vec![
            var("a", array_sort(1)),
            ChcExpr::ConstArray(ChcSort::BitVec(1), Arc::new(var("j", ChcSort::Bool))),
        ],
    );
    let ChcExpr::Op(ChcOp::Eq, operands) = &incorrectly_shared else {
        unreachable!("the proposed incorrect rewrite is an array equality")
    };
    for witness in [false, true] {
        env.insert("j".into(), SmtValue::Bool(witness));
        // The generic value oracle may abstain on differing array defaults.
        // Evaluate both concrete indices instead: one scalar disagreement is
        // an exact extensional counterexample to this shared array equality.
        let pointwise = [0, 1].map(|index| {
            let reads = operands
                .iter()
                .map(|operand| {
                    Arc::new(ChcExpr::Op(
                        ChcOp::Select,
                        vec![operand.clone(), Arc::new(ChcExpr::BitVec(index, 1))],
                    ))
                })
                .collect();
            evaluate_expr(&ChcExpr::Op(ChcOp::Eq, reads), &env)
        });
        assert!(pointwise
            .iter()
            .all(|value| matches!(value, Some(SmtValue::Bool(_)))));
        assert!(pointwise.contains(&Some(SmtValue::Bool(false))));
    }
}

#[test]
fn finite_expansion_must_not_share_an_inner_binder_between_indices() {
    for body in [
        "(=> (bvult i (_ bv2 64)) (exists ((j Bool)) (= (select a i) j)))",
        "(=> (and (bvult i (_ bv2 64)) (forall ((j (_ BitVec 64))) (= i j))) (= (select a i) true))",
        "(=> (bvult i (_ bv2 64)) (let ((v (exists ((j Bool)) (= (select a i) j)))) v))",
    ] {
        assert!(parse_body(body, "(i (_ BitVec 64))", -1).problem.has_stripped_body_forall(), "{body}");
    }
}

#[test]
fn exact_hooks_report_completion_to_parents_and_keep_preexisting_marks() {
    for inner in [
        "(forall ((j (_ BitVec 64))) (= (select b j) true))",
        "(forall ((j (_ BitVec 64))) (=> (bvult j (_ bv2 64)) (= (select b j) true)))",
    ] {
        // A preceding inner exact rewrite still marks a completed quantifier;
        // an erased let binding must not make the outer hook forget it.
        let body =
            format!("(let ((unused {inner})) (=> (bvult i (_ bv2 64)) (= (select a i) true)))");
        assert!(parse_body(&body, "(i (_ BitVec 64))", -1)
            .problem
            .has_stripped_body_forall());
    }
    let mut parser = ChcParser::new();
    parser.polarity = -1;
    parser.variables.insert("a".into(), array_sort(64));
    parser.problem.mark_stripped_body_forall();
    parser.input =
        "(forall ((i (_ BitVec 64))) (=> (bvult i (_ bv2 64)) (= (select a i) true)))".into();
    parser.parse_expr().unwrap();
    assert!(parser.problem.has_stripped_body_forall());
}

#[test]
fn declaration_and_sibling_binder_shadowing_remain_lexical() {
    let input = r#"(set-logic HORN)
        (declare-var a (Array (_ BitVec 64) Bool))
        (declare-var i Bool)
        (declare-rel P ((Array (_ BitVec 64) Bool) Bool))
        (rule (=> (and i
            (forall ((i (_ BitVec 64))) (=> (bvult i (_ bv2 64)) (= (select a i) true)))
            (forall ((i (_ BitVec 64))) (=> (bvult i (_ bv1 64)) (= (select a i) true))))
          (P a i)))
        (query P)"#;
    let problem = ChcParser::parse(input).unwrap();
    assert!(!problem.has_stripped_body_forall());
    let constraint = problem.clauses()[0].body.constraint.as_ref().unwrap();
    let vars = constraint.vars();
    assert!(vars
        .iter()
        .any(|v| v.name == "i" && v.sort == ChcSort::Bool));
    assert!(!vars.iter().any(|v| matches!(v.sort, ChcSort::BitVec(_))));
    let mut env = environment(2, 0b1111, 0, false);
    env.insert("a".into(), array(64, [true, true]));
    for flag in [false, true] {
        env.insert("i".into(), SmtValue::Bool(flag));
        assert_eq!(evaluate_expr(constraint, &env), Some(SmtValue::Bool(flag)));
    }
}
