// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;
use crate::quantified::{QuantifiedChcProblem, QuantifiedHornClause, UniversalPremise};
use crate::{ChcExpr, ChcOp, ChcVar, ClauseBody, HornClause};
use std::sync::Arc;

mod arrays;
mod nested;
mod source;
mod wide;

fn bv(width: u32) -> ChcSort {
    ChcSort::BitVec(width)
}
fn array() -> ChcSort {
    ChcSort::Array(Box::new(bv(64)), Box::new(bv(8)))
}
fn fields() -> Vec<(String, ChcSort)> {
    vec![
        ("fld_ptr".into(), bv(64)),
        ("fld_len".into(), bv(64)),
        ("fld_cap".into(), bv(64)),
        ("fld_data".into(), array()),
    ]
}
fn declarations(name: &str) -> ChcProblem {
    let mut problem = ChcProblem::new();
    problem.add_datatype_def(name.into(), vec![("mk_vec".into(), fields())]);
    problem
}
fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}
fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}
fn app(name: &str, sort: ChcSort, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::FuncApp(name.into(), sort, args.into_iter().map(Arc::new).collect())
}
fn query(
    problem: ChcProblem,
    expr: ChcExpr,
    premises: Vec<UniversalPremise>,
) -> ChcResult<QuantifiedChcProblem> {
    QuantifiedChcProblem::new(
        problem,
        vec![QuantifiedHornClause::new(
            HornClause::query(ClauseBody::constraint(expr)),
            premises,
        )],
    )
}

#[test]
fn registry_authenticates_complete_ordered_constructor_and_selector_metadata() {
    let problem = declarations("Vec_u8");
    let registry = Registry::new(&problem).unwrap();
    let sort = registry.lookup("Vec_u8").unwrap();
    registry.validate_sort(sort).unwrap();
    assert_eq!(
        registry
            .application("mk_vec", &[bv(64), bv(64), bv(64), array()])
            .unwrap(),
        *sort
    );
    assert_eq!(
        registry
            .application("fld_data", std::slice::from_ref(sort))
            .unwrap(),
        array()
    );
    assert!(registry.application("mk_vec", &[bv(64)]).is_err());
    assert!(registry.application("fld_data", &[array()]).is_err());
    assert!(registry.application("arbitrary_uf", &[bv(64)]).is_err());
    let ChcSort::Datatype { name, constructors } = sort else {
        panic!("record");
    };
    let mut changed = constructors.to_vec();
    changed[0].selectors.swap(0, 1);
    let forged = ChcSort::Datatype {
        name: name.clone(),
        constructors: crate::ChcDtConstructors::new(changed),
    };
    assert!(supported_sort(&forged));
    assert!(registry.validate_sort(&forged).is_err());
    assert!(registry.application("fld_data", &[forged]).is_err());
    let names: Vec<_> = registry.term_names().collect();
    assert_eq!(
        names,
        vec!["fld_cap", "fld_data", "fld_len", "fld_ptr", "mk_vec"]
    );
}

#[test]
fn selector_overloads_resolve_by_exact_record_not_name_alone() {
    let mut problem = declarations("Vec_u8");
    let other_fields = vec![
        ("fld_ptr".into(), bv(32)),
        ("fld_data".into(), ChcSort::Bool),
    ];
    problem.add_datatype_def("Other".into(), vec![("mk_other".into(), other_fields)]);
    let registry = Registry::new(&problem).unwrap();
    let first = registry.lookup("Vec_u8").unwrap().clone();
    let second = registry.lookup("Other").unwrap().clone();
    assert_eq!(registry.application("fld_ptr", &[first]).unwrap(), bv(64));
    assert_eq!(registry.application("fld_ptr", &[second]).unwrap(), bv(32));
    // Same constructor spelling with indistinguishable argument signatures is
    // not guessed. Selector overloads above remain unambiguous by input sort.
    problem.add_datatype_def("Twin".into(), vec![("mk_vec".into(), fields())]);
    let registry = Registry::new(&problem).unwrap();
    assert!(registry
        .application("mk_vec", &[bv(64), bv(64), bv(64), array()])
        .is_err());
}

#[test]
fn record_shape_refuses_enums_placeholders_and_malformed_fields() {
    let cases = vec![
        vec![],
        vec![("mk".into(), vec![])],
        vec![
            ("one".into(), vec![("a".into(), ChcSort::Bool)]),
            ("two".into(), vec![("b".into(), ChcSort::Bool)]),
        ],
        vec![(
            "mk".into(),
            vec![("x".into(), ChcSort::Uninterpreted("R".into()))],
        )],
        vec![(
            "mk".into(),
            vec![(
                "x".into(),
                ChcSort::Array(
                    Box::new(bv(8)),
                    Box::new(ChcSort::Array(Box::new(bv(8)), Box::new(array()))),
                ),
            )],
        )],
        vec![("mk".into(), vec![("x".into(), ChcSort::Int)])],
        vec![("mk".into(), vec![("x".into(), bv(0))])],
        vec![("mk".into(), vec![("x".into(), bv(u32::MAX))])],
        vec![("mk".into(), vec![("x".into(), bv(8)), ("x".into(), bv(8))])],
        vec![("mk".into(), vec![("mk".into(), bv(8))])],
    ];
    for constructors in cases {
        let mut problem = ChcProblem::new();
        problem.add_datatype_def("R".into(), constructors);
        assert!(registry_bytes(&problem).is_none());
        assert!(Registry::new(&problem).is_err());
    }
}

#[test]
fn borrowed_limits_refuse_before_metadata_cloning_or_formatting() {
    for name in [
        "select".to_owned(),
        "forall".to_owned(),
        "a|b".to_owned(),
        "a\\b".to_owned(),
        "x".repeat(MAX_NAME_BYTES + 1),
    ] {
        assert!(Registry::new(&declarations(&name)).is_err());
    }
    let mut many = ChcProblem::new();
    for index in 0..=MAX_RECORDS {
        many.add_datatype_def(
            format!("R{index}"),
            vec![(format!("mk{index}"), vec![("f".into(), ChcSort::Bool)])],
        );
    }
    assert!(registry_bytes(&many).is_none());
    let mut wide = ChcProblem::new();
    wide.add_datatype_def(
        "R".into(),
        vec![(
            "mk".into(),
            (0..=MAX_FIELDS)
                .map(|n| (format!("f{n}"), ChcSort::Bool))
                .collect(),
        )],
    );
    assert!(registry_bytes(&wide).is_none());
    let mut names = ChcProblem::new();
    names.add_datatype_def(
        "R".into(),
        vec![(
            "mk".into(),
            (0..MAX_FIELDS)
                .map(|n| {
                    (
                        format!("{n:02}{}", "x".repeat(MAX_NAME_BYTES - 2)),
                        ChcSort::Bool,
                    )
                })
                .collect(),
        )],
    );
    assert!(registry_bytes(&names).is_none());
}

#[test]
fn every_unused_record_declaration_is_retained_in_canonical_identity() {
    let empty = query(ChcProblem::new(), ChcExpr::Bool(false), vec![]).unwrap();
    let first = query(declarations("Vec_u8"), ChcExpr::Bool(false), vec![]).unwrap();
    assert_ne!(empty.source_smtlib(), first.source_smtlib());
    assert!(first
        .source_smtlib()
        .contains("(fld_data (Array (_ BitVec 64) (_ BitVec 8)))"));
    let mut a = declarations("Vec_u8");
    a.add_datatype_def(
        "Unused".into(),
        vec![("mk_unused".into(), vec![("flag".into(), ChcSort::Bool)])],
    );
    let mut b = ChcProblem::new();
    b.add_datatype_def(
        "Unused".into(),
        vec![("mk_unused".into(), vec![("flag".into(), ChcSort::Bool)])],
    );
    b.add_datatype_def("Vec_u8".into(), vec![("mk_vec".into(), fields())]);
    let second = query(a, ChcExpr::Bool(false), vec![]).unwrap();
    assert_ne!(first.source_smtlib(), second.source_smtlib());
    assert_eq!(
        second.source_smtlib(),
        query(b, ChcExpr::Bool(false), vec![])
            .unwrap()
            .source_smtlib()
    );
    assert_eq!(second.source_problem().datatype_defs().len(), 2);
}
