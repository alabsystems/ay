// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn simultaneous_let_rhs_captures_the_old_environment() {
    let problem = parsed(
        "(declare-var x (_ BitVec 8))
        (declare-rel P ((_ BitVec 8)))
        (declare-rel error ())
        (rule (let ((x #x01) (saved x)) (=> (= saved x) (P saved))))
        (query error)",
    );
    let clause = &problem.source_problem().clauses()[0];
    let ClauseHead::Predicate(_, args) = &clause.head else {
        panic!("P head")
    };
    assert!(matches!(&args[0], ChcExpr::Var(var) if var.name == "x"));
    let Some(ChcExpr::Op(ChcOp::Eq, equality)) = clause.body.constraint.as_ref() else {
        panic!("raw equality")
    };
    assert_eq!(equality[0].as_ref(), &args[0]);
    assert_eq!(equality[1].as_ref(), &ChcExpr::BitVec(1, 8));
}

#[test]
fn resolved_alias_survives_later_same_name_universal_shadowing() {
    let problem = parsed(
        "(set-logic HORN)(declare-fun P ((_ BitVec 8)) Bool)
        (assert (forall ((x (_ BitVec 8)))
          (let ((saved x)) (forall ((x (_ BitVec 8)))
            (=> (= saved #x01) (P x))))))
        (assert (=> (P #x00) false))
        (check-sat)",
    );
    let clause = &problem.source_problem().clauses()[0];
    let ClauseHead::Predicate(_, args) = &clause.head else {
        panic!("P head")
    };
    let ChcExpr::Var(inner) = &args[0] else {
        panic!("inner variable")
    };
    let Some(ChcExpr::Op(ChcOp::Eq, equality)) = clause.body.constraint.as_ref() else {
        panic!("outer variable constraint")
    };
    let ChcExpr::Var(outer) = equality[0].as_ref() else {
        panic!("saved outer")
    };
    assert_ne!(outer.name, inner.name);
    assert_eq!(outer.sort, inner.sort);
}

#[test]
fn whole_forall_and_relation_aliases_retain_their_horn_roles() {
    let problem = parsed(
        "(declare-var a (Array (_ BitVec 2) Bool))
        (declare-var n (_ BitVec 2))
        (declare-rel P ((Array (_ BitVec 2) Bool)))
        (declare-rel error ())
        (rule (let ((all (forall ((i (_ BitVec 2)))
                     (=> (bvult i n) (select a i)))))
                 (=> (and all all) (P a))))
        (rule (let ((pred (P a))) (=> (and pred false) error)))
        (query error)",
    );
    assert_eq!(problem.premises()[0].len(), 2);
    assert_eq!(
        problem.premises()[0][0].matrix(),
        problem.premises()[0][1].matrix()
    );
    assert_eq!(
        problem.source_problem().clauses()[1].body.predicates.len(),
        1
    );
    assert_eq!(
        problem.source_problem().clauses()[1]
            .body
            .constraint
            .as_ref(),
        Some(&ChcExpr::Bool(false))
    );
    assert_eq!(problem.source_problem().clauses().len(), 3);
}

#[test]
fn matrix_binder_does_not_capture_a_resolved_outer_alias() {
    let problem = parsed(
        "(declare-fun P () Bool)
        (assert (forall ((i (_ BitVec 2)) (a (Array (_ BitVec 2) Bool)))
          (let ((saved i))
            (=> (forall ((i (_ BitVec 2)))
                  (=> (= i saved) (select a i))) P))))
        (assert (=> P false))
        (check-sat)",
    );
    let premise = &problem.premises()[0][0];
    let ChcExpr::Op(ChcOp::Implies, implication) = premise.matrix() else {
        panic!("original implication")
    };
    let ChcExpr::Op(ChcOp::Eq, equality) = implication[0].as_ref() else {
        panic!("original guard")
    };
    let (ChcExpr::Var(bound), ChcExpr::Var(saved)) = (equality[0].as_ref(), equality[1].as_ref())
    else {
        panic!("two lexical variables")
    };
    assert_eq!(bound, premise.binder());
    assert_ne!(bound.name, saved.name);
}

#[test]
fn explicit_binders_avoid_source_variable_and_predicate_names() {
    let problem = parsed(
        "(declare-var ay!source!0 (_ BitVec 8))
        (declare-rel P ((_ BitVec 8) (_ BitVec 8)))
        (declare-rel ay!source!1 ())
        (rule (forall ((x (_ BitVec 8))) (P x ay!source!0)))
        (query ay!source!1)",
    );
    let ClauseHead::Predicate(_, args) = &problem.source_problem().clauses()[0].head else {
        panic!("P head")
    };
    assert!(matches!(&args[0], ChcExpr::Var(var) if var.name == "ay!source!2"));
    assert!(matches!(&args[1], ChcExpr::Var(var) if var.name == "ay!source!0"));
}

#[test]
fn relational_equality_is_not_substituted_out_of_the_source() {
    let problem = parsed(
        "(declare-var x (_ BitVec 8))
        (declare-var next (_ BitVec 8))
        (declare-rel P ((_ BitVec 8)))
        (declare-rel error ())
        (rule (=> (and (P x) (= next (bvadd x #x01))) (P next)))
        (query error)",
    );
    let clause = &problem.source_problem().clauses()[0];
    let ClauseHead::Predicate(id, args) = &clause.head else {
        panic!("P head")
    };
    assert!(matches!(&args[0], ChcExpr::Var(var) if var.name == "next"));
    assert_eq!(clause.body.predicates[0].0, *id);
    let Some(ChcExpr::Op(ChcOp::Eq, equality)) = &clause.body.constraint else {
        panic!("retained relational equality")
    };
    assert_eq!(equality[0].as_ref(), &args[0]);
    let ChcExpr::Op(ChcOp::BvAdd, sum) = equality[1].as_ref() else {
        panic!("retained successor expression")
    };
    assert_eq!(sum[0].as_ref(), &clause.body.predicates[0].1[0]);
    assert_eq!(sum[1].as_ref(), &ChcExpr::BitVec(1, 8));
}
