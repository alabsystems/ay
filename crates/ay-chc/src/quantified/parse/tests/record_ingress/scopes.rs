// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn record_let_alias_survives_outer_forall_shadowing_and_preserves_raw_equality() {
    let problem = parsed(&format!(
        "{}
        (declare-fun P (Vec) Bool)
        (assert (forall ((v Vec)) (let ((saved v))
          (forall ((v Vec)) (=> (= (fld_len saved) (fld_len v)) (P v))))))
        (assert (forall ((v Vec)) (=> (P v) false))) (check-sat)",
        fixtures::record()
    ));
    let clause = &problem.source_problem().clauses()[0];
    let ClauseHead::Predicate(_, args) = &clause.head else {
        panic!("P head")
    };
    let ChcExpr::Var(inner) = &args[0] else {
        panic!("inner record")
    };
    let Some(ChcExpr::Op(ChcOp::Eq, equality)) = &clause.body.constraint else {
        panic!("raw equality")
    };
    let ChcExpr::FuncApp(_, _, left) = equality[0].as_ref() else {
        panic!("saved selector")
    };
    let ChcExpr::FuncApp(_, _, right) = equality[1].as_ref() else {
        panic!("inner selector")
    };
    let ChcExpr::Var(outer) = left[0].as_ref() else {
        panic!("saved record")
    };
    assert_ne!(outer.name, inner.name);
    assert_eq!(outer.sort, inner.sort);
    assert_eq!(right[0].as_ref(), &args[0]);
}

#[test]
fn record_names_are_reserved_for_fresh_binders_and_lexical_function_shadowing_refuses() {
    let declarations = "(declare-datatype ay!source!0 ((ay!source!1 (ay!source!2 Bool))))";
    let problem = parsed(&format!(
        "{declarations}
        (declare-fun P (ay!source!0) Bool)
        (assert (forall ((v ay!source!0)) (P v)))
        (assert false)(check-sat)"
    ));
    let ClauseHead::Predicate(_, args) = &problem.source_problem().clauses()[0].head else {
        panic!("P")
    };
    assert!(matches!(&args[0], ChcExpr::Var(var) if var.name == "ay!source!3"));
    for expression in [
        "(let ((fld_len #x00)) (= (fld_len v) (_ bv0 64)))",
        "(let ((mkVec true)) (= v (mkVec (_ bv0 64) (_ bv0 64) (_ bv0 64) (fld_data v))))",
        "(let ((mkVec true)) (= v ((as mkVec Vec) (_ bv0 64) (_ bv0 64) (_ bv0 64) (fld_data v))))",
    ] {
        fixtures::refuses(&format!(
            "{}(declare-var v Vec)(declare-rel error ())
            (rule (=> {expression} error))(query error)",
            fixtures::record()
        ));
    }
}
