// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;

#[test]
fn vec_record_symbolic_resize_keeps_all_fields_guards_and_original_premise() {
    // Synthetic scalar-leaf projection of MODEL_CHECKER_CONSUMER's four-field Vec layout;
    // deliberately retains symbolic bounds and the source array selector.
    let mut problem = declarations("Vec_u8");
    let record = Registry::new(&problem)
        .unwrap()
        .lookup("Vec_u8")
        .unwrap()
        .clone();
    let p = problem.declare_predicate("P", vec![record.clone(), bv(64), bv(8)]);
    let value = var("v", record.clone());
    let index = var("i", bv(64));
    let old = app("fld_len", bv(64), vec![value.clone()]);
    let data = app("fld_data", array(), vec![value.clone()]);
    let guard = op(
        ChcOp::And,
        vec![
            op(ChcOp::BvUGe, vec![index.clone(), old]),
            op(ChcOp::BvULt, vec![index.clone(), var("new", bv(64))]),
        ],
    );
    let matrix = op(
        ChcOp::Implies,
        vec![
            guard,
            op(
                ChcOp::Eq,
                vec![op(ChcOp::Select, vec![data, index]), var("fill", bv(8))],
            ),
        ],
    );
    let premise = UniversalPremise::new(ChcVar::new("i", bv(64)), matrix.clone());
    let body = ClauseBody::new(
        vec![(p, vec![value, var("new", bv(64)), var("fill", bv(8))])],
        Some(ChcExpr::Bool(true)),
    );
    let source = QuantifiedChcProblem::new(
        problem,
        vec![QuantifiedHornClause::new(
            HornClause::query(body),
            vec![premise],
        )],
    )
    .unwrap();
    assert_eq!(source.premises()[0][0].matrix(), &matrix);
    let text = source.source_smtlib();
    assert!(text.contains("(declare-fun P (Vec_u8 (_ BitVec 64) (_ BitVec 8)) Bool)"));
    assert!(text.contains("(P v new fill)"));
    assert!(text.contains("(forall ((i (_ BitVec 64))) (=> (and (bvuge i (fld_len v)) (bvult i new)) (= (select (fld_data v) i) fill)))"));
    for name in ["fld_ptr", "fld_len", "fld_cap", "fld_data"] {
        assert!(text.contains(name));
    }
    assert!(!source.source_problem().has_stripped_body_forall());
}

#[test]
fn constructors_record_equality_and_ite_keep_full_typed_syntax() {
    let mut problem = declarations("Vec record");
    let record = Registry::new(&problem)
        .unwrap()
        .lookup("Vec record")
        .unwrap()
        .clone();
    problem.declare_predicate("unused record predicate", vec![record.clone()]);
    let construct = app(
        "mk_vec",
        record.clone(),
        vec![
            ChcExpr::BitVec(7, 64),
            ChcExpr::BitVec(2, 64),
            ChcExpr::BitVec(9, 64),
            var("data", array()),
        ],
    );
    let choice = op(
        ChcOp::Ite,
        vec![
            var("choose", ChcSort::Bool),
            construct,
            var("v", record.clone()),
        ],
    );
    let formula = op(ChcOp::Ne, vec![choice, var("w", record)]);
    let source = query(problem, formula.clone(), vec![]).unwrap();
    assert_eq!(
        source.source_problem().clauses()[0]
            .body
            .constraint
            .as_ref(),
        Some(&formula)
    );
    let text = source.source_smtlib();
    assert!(text.contains("(|Vec record| 0)"));
    assert!(text.contains("(declare-fun |unused record predicate| (|Vec record|) Bool)"));
    assert!(text.contains("(v |Vec record|)"));
    assert!(text.contains("(w |Vec record|)"));
    assert!(text.contains("((as mk_vec |Vec record|) (_ bv7 64) (_ bv2 64) (_ bv9 64) data)"));
    assert!(text.contains("(distinct (ite choose"));
}

#[test]
fn malformed_record_uses_do_not_acquire_ordinary_uf_authority() {
    let problem = declarations("Vec_u8");
    let registry = Registry::new(&problem).unwrap();
    let record = registry.lookup("Vec_u8").unwrap().clone();
    let value = var("v", record.clone());
    let malformed = vec![
        app("fld_data", ChcSort::Bool, vec![value.clone()]),
        app("fld_ptr", bv(64), vec![var("v", array())]),
        app("mk_vec", record.clone(), vec![ChcExpr::BitVec(0, 64)]),
        app("is-mk_vec", ChcSort::Bool, vec![value.clone()]),
        app("uf", ChcSort::Bool, vec![value.clone()]),
    ];
    for expression in malformed {
        let formula = op(ChcOp::Eq, vec![expression.clone(), expression]);
        assert!(query(declarations("Vec_u8"), formula, vec![]).is_err());
    }
    let ChcSort::Datatype { name, constructors } = record else {
        panic!("record");
    };
    let mut changed = constructors.to_vec();
    changed[0].selectors[3].sort = ChcSort::Bool;
    let forged = ChcSort::Datatype {
        name,
        constructors: crate::ChcDtConstructors::new(changed),
    };
    let value = var("v", forged);
    assert!(query(problem, op(ChcOp::Eq, vec![value.clone(), value]), vec![]).is_err());
}

#[test]
fn unused_record_operations_cannot_be_captured_by_any_source_binder() {
    for name in ["mk_vec", "fld_data"] {
        assert!(query(declarations("Vec_u8"), var(name, ChcSort::Bool), vec![]).is_err());
        let unused = UniversalPremise::new(ChcVar::new(name, bv(64)), ChcExpr::Bool(true));
        assert!(query(declarations("Vec_u8"), ChcExpr::Bool(true), vec![unused]).is_err());
        let mut problem = declarations("Vec_u8");
        problem.declare_predicate(name, vec![]);
        assert!(query(problem, ChcExpr::Bool(false), vec![]).is_err());
    }
}

#[test]
fn repeated_large_record_metadata_is_precharged_before_source_sort_clones() {
    let mut problem = ChcProblem::new();
    problem.add_datatype_def(
        "R".into(),
        vec![("mk".into(), vec![("field".repeat(3000), ChcSort::Bool)])],
    );
    let record = Registry::new(&problem)
        .unwrap()
        .lookup("R")
        .unwrap()
        .clone();
    let equality = Arc::new(op(
        ChcOp::Eq,
        vec![var("x", record.clone()), var("y", record)],
    ));
    let formula = ChcExpr::Op(ChcOp::And, vec![equality; 100]);
    assert!(query(problem, formula, vec![]).is_err());
}
