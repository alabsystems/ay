// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use super::*;

mod limits;

fn record(name: &str, ctor: &str, fields: Vec<(&str, ChcSort)>) -> ChcSort {
    ChcSort::Datatype {
        name: name.into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: ctor.into(),
            selectors: fields
                .into_iter()
                .map(|(name, sort)| ChcDtSelector {
                    name: name.into(),
                    sort,
                })
                .collect(),
        }]),
    }
}

fn add(problem: &mut ChcProblem, sort: &ChcSort) {
    let ChcSort::Datatype { name, constructors } = sort else {
        panic!("record");
    };
    problem.add_datatype_def(
        name.clone(),
        constructors
            .iter()
            .map(|ctor| {
                (
                    ctor.name.clone(),
                    ctor.selectors
                        .iter()
                        .map(|field| (field.name.clone(), field.sort.clone()))
                        .collect(),
                )
            })
            .collect(),
    );
}

fn nested() -> (ChcProblem, ChcSort, ChcSort) {
    let mut problem = declarations("Vec_u8");
    let inner = Registry::new(&problem)
        .unwrap()
        .lookup("Vec_u8")
        .unwrap()
        .clone();
    let outer = record(
        "VecIntoIter_u8",
        "mk_iter",
        vec![("fld_vec", inner.clone()), ("fld_pos", bv(64))],
    );
    add(&mut problem, &outer);
    (problem, inner, outer)
}

#[test]
fn nested_vec_into_iter_authenticates_each_operation_kind_and_full_source() {
    // Exact logical layout from MODEL_CHECKER_CONSUMER 22278991c4, names/sort_constructors.rs
    // vec_into_iter_fields and CHC stubs_iterators_vec::make_vec_into_iter_chc.
    let (problem, inner, outer) = nested();
    let registry = Registry::new(&problem).unwrap();
    let ctor = registry
        .resolve_application("mk_iter", &[inner.clone(), bv(64)])
        .unwrap();
    assert_eq!(ctor.kind, OperationKind::Constructor);
    assert_eq!(ctor.sort, &outer);
    let selector = registry
        .resolve_application("fld_vec", std::slice::from_ref(&outer))
        .unwrap();
    assert_eq!(selector.kind, OperationKind::Selector { field: 0 });
    assert_eq!(selector.sort, &inner);
    let value = app("fld_vec", inner, vec![var("it", outer)]);
    let data = app("fld_data", array(), vec![value]);
    let index = var("i", bv(64));
    let matrix = op(
        ChcOp::Implies,
        vec![
            op(ChcOp::BvULt, vec![index.clone(), var("len", bv(64))]),
            op(
                ChcOp::Eq,
                vec![op(ChcOp::Select, vec![data, index]), var("fill", bv(8))],
            ),
        ],
    );
    let source = query(
        problem,
        ChcExpr::Bool(false),
        vec![UniversalPremise::new(
            ChcVar::new("i", bv(64)),
            matrix.clone(),
        )],
    )
    .unwrap();
    assert_eq!(source.premises()[0][0].matrix(), &matrix);
    assert!(source.source_smtlib().contains("(fld_vec Vec_u8)"));
    assert!(source
        .source_smtlib()
        .contains("(select (fld_data ((as fld_vec Vec_u8) it)) i)"));
    assert_eq!(registry.record_sorts().count(), 2);
}

#[test]
fn nested_disagreement_missing_declarations_and_placeholder_cycles_refuse() {
    let (problem, inner, outer) = nested();
    let registry = Registry::new(&problem).unwrap();
    let wrong_inner = record("Vec_u8", "mk_vec", vec![("wrong", ChcSort::Bool)]);
    let wrong_outer = record(
        "VecIntoIter_u8",
        "mk_iter",
        vec![("fld_vec", wrong_inner), ("fld_pos", bv(64))],
    );
    assert!(sort_bytes(&wrong_outer).is_some());
    assert!(registry.validate_sort(&wrong_outer).is_err());
    assert!(registry
        .application("fld_vec", &[wrong_outer.clone()])
        .is_err());
    let mut mismatch = declarations("Vec_u8");
    add(&mut mismatch, &wrong_outer);
    assert!(Registry::new(&mismatch).is_err());
    let mut missing = ChcProblem::new();
    add(&mut missing, &outer);
    assert!(Registry::new(&missing).is_err());
    let recursive = record(
        "A",
        "mk_a",
        vec![("next", ChcSort::Uninterpreted("A".into()))],
    );
    let mut problem = ChcProblem::new();
    add(&mut problem, &recursive);
    assert!(Registry::new(&problem).is_err());
    let mut array_of_record = ChcProblem::new();
    add(
        &mut array_of_record,
        &record(
            "Bad",
            "mk_bad",
            vec![("a", ChcSort::Array(Box::new(bv(8)), Box::new(inner)))],
        ),
    );
    assert!(Registry::new(&array_of_record).is_err());
}

#[test]
fn recursive_name_graph_cannot_be_authenticated_by_truncated_metadata() {
    let leaf_a = record("A", "mk_a", vec![("leaf", ChcSort::Bool)]);
    let b = record("B", "mk_b", vec![("a", leaf_a)]);
    let a = record("A", "mk_a", vec![("b", b.clone())]);
    let mut problem = ChcProblem::new();
    add(&mut problem, &a);
    add(&mut problem, &b);
    assert!(registry_bytes(&problem).is_some());
    assert!(Registry::new(&problem).is_err());
}

#[test]
fn duplicate_shared_nested_fields_keep_positions_and_unused_identity() {
    let (_, inner, _) = nested();
    let outer = record(
        "Pair",
        "mk_pair",
        vec![("left", inner.clone()), ("right", inner.clone())],
    );
    let mut problem = declarations("Vec_u8");
    add(&mut problem, &outer);
    let registry = Registry::new(&problem).unwrap();
    assert_eq!(
        registry
            .resolve_application("left", std::slice::from_ref(&outer))
            .unwrap()
            .kind,
        OperationKind::Selector { field: 0 }
    );
    assert_eq!(
        registry
            .resolve_application("right", std::slice::from_ref(&outer))
            .unwrap()
            .kind,
        OperationKind::Selector { field: 1 }
    );
    let first = query(problem, ChcExpr::Bool(false), vec![]).unwrap();
    let mut changed = declarations("Vec_u8");
    add(
        &mut changed,
        &record(
            "Pair",
            "mk_pair",
            vec![("right", inner.clone()), ("left", inner)],
        ),
    );
    let second = query(changed, ChcExpr::Bool(false), vec![]).unwrap();
    assert_ne!(first.source_smtlib(), second.source_smtlib());
    assert_eq!(first.source_problem().datatype_defs().len(), 2);
}

#[test]
fn equal_result_sorts_do_not_disambiguate_distinct_operation_identities() {
    let (_, inner, _) = nested();
    let pair = record(
        "Pair",
        "mk_pair",
        vec![("left", inner.clone()), ("right", inner)],
    );
    let mut problem = declarations("Vec_u8");
    add(&mut problem, &pair);
    let mut registry = Registry::new(&problem).unwrap();
    // A private-map fault injection exercises the defensive identity check;
    // public declaration admission already prohibits duplicate field names.
    let record = registry.names["Pair"];
    registry.functions.get_mut("left").unwrap().push(Signature {
        record,
        field: Some(1),
    });
    assert!(registry
        .resolve_application("left", std::slice::from_ref(&pair))
        .is_err());
    assert!(registry.application("left", &[pair]).is_err());
}
