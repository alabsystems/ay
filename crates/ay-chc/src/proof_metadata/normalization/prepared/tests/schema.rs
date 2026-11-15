// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The prepared datatype-free cohort and reference-based ordinary serializer
//! must agree on bytes, their exact digest and the schema actually emitted.

use super::*;
use crate::{ChcDtConstructor, ChcDtConstructors, ChcDtSelector};
use sha2::{Digest, Sha256};

fn assert_identity(problem: &ChcProblem, schema: &'static str) -> String {
    let ordinary = crate::normalized_chc_input(problem);
    let generic = super::super::super::text::normalized_input(
        problem,
        &mut super::super::super::AlwaysContinue,
    )
    .unwrap();
    assert_eq!(ordinary, generic);
    assert_eq!(
        crate::normalized_chc_input_schema_of(&ordinary),
        Some(schema)
    );
    let digest = format!("{:x}", Sha256::digest(ordinary.as_bytes()));
    assert_eq!(crate::normalized_chc_input_sha256(problem), digest);
    assert_eq!(
        super::super::super::normalized_chc_input_identity_with_progress(problem, &mut || true),
        Ok((schema, digest)),
    );
    ordinary
}

fn refuses_prepared(problem: &ChcProblem) {
    let original = quiet_owner();
    let result = original.with_work(|work| {
        prepare_normalized_chc_input_with_work(problem, work)?
            .with_input(|_, _, _| panic!("datatype input must not reach a prepared-input consumer"))
    });
    assert_eq!(
        result,
        Err(OriginalAdmissionError::Query(QueryError::Invalid(
            "datatype-bearing normalized input is unsupported",
        )))
    );
    assert!(original.check().is_err());
}

fn nested_datatype() -> ChcSort {
    let mut sort = ChcSort::BitVec(32);
    for level in 0..4 {
        sort = ChcSort::Datatype {
            name: format!("D{level}"),
            constructors: ChcDtConstructors::new(vec![ChcDtConstructor {
                name: format!("mk{level}"),
                selectors: vec![
                    ChcDtSelector {
                        name: "a".into(),
                        sort: sort.clone(),
                    },
                    ChcDtSelector {
                        name: "b".into(),
                        sort,
                    },
                ],
            }]),
        };
    }
    sort
}

#[test]
fn successful_prepared_bytes_hash_and_schema_match_the_public_v1_identity() {
    for problem in [ChcProblem::new(), fixture()] {
        let expected = assert_identity(&problem, crate::NORMALIZED_CHC_INPUT_SCHEMA);
        quiet_owner()
            .with_work(|work| {
                prepare_normalized_chc_input_with_work(&problem, work)?.with_sha256(
                    |source, bytes, digest, _| {
                        assert!(std::ptr::eq(source, &problem));
                        assert_eq!(bytes, expected);
                        assert_eq!(digest, crate::normalized_chc_input_sha256(source));
                        Ok(())
                    },
                )
            })
            .unwrap();
    }
}

#[test]
fn unused_datatype_registry_fallback_uses_the_schema_its_sorts_actually_require() {
    for sort in [ChcSort::Int, nested_datatype()] {
        let referenced = matches!(&sort, ChcSort::Datatype { .. });
        let mut problem = ChcProblem::new();
        problem.add_datatype_def(
            "Unused".into(),
            vec![("mk".into(), vec![("v".into(), sort)])],
        );
        refuses_prepared(&problem);
        let schema = if referenced {
            crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA
        } else {
            crate::NORMALIZED_CHC_INPUT_SCHEMA
        };
        let text = assert_identity(&problem, schema);
        assert_eq!(
            text.lines()
                .filter(|line| line.starts_with("constructors @"))
                .count(),
            if referenced { 4 } else { 0 }
        );
    }
}

#[test]
fn datatype_sorts_hidden_in_all_expression_positions_refuse_without_v1_mislabeling() {
    let sort = nested_datatype();
    let array = ChcSort::Array(Box::new(sort.clone()), Box::new(ChcSort::Int));
    let expressions = [
        ChcExpr::FuncApp("hidden".into(), array.clone(), Vec::new()),
        ChcExpr::FuncApp(
            "outer".into(),
            ChcSort::Bool,
            vec![Arc::new(ChcExpr::var(ChcVar::new("x", array.clone())))],
        ),
        ChcExpr::ConstArrayMarker(array),
        ChcExpr::ConstArray(sort.clone(), Arc::new(ChcExpr::Int(0))),
        ChcExpr::ConstArray(ChcSort::Int, Arc::new(ChcExpr::var(ChcVar::new("x", sort)))),
    ];
    for hidden in expressions {
        let mut problem = ChcProblem::new();
        // Keep the raw unchosen branch: normalization is source identity,
        // not an evaluator allowed to erase an apparently unreachable sort.
        raw(
            &mut problem,
            HornClause::query(ClauseBody::constraint(ChcExpr::Op(
                ChcOp::Ite,
                vec![
                    Arc::new(ChcExpr::Bool(true)),
                    Arc::new(ChcExpr::Bool(true)),
                    Arc::new(hidden),
                ],
            ))),
        );
        refuses_prepared(&problem);
        let text = assert_identity(
            &problem,
            crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA,
        );
        assert_eq!(
            text.lines()
                .filter(|line| line.starts_with("constructors @"))
                .count(),
            4
        );
    }
}

#[test]
fn datatype_hidden_under_predicate_array_sort_uses_the_reference_identity() {
    let mut problem = ChcProblem::new();
    problem.declare_predicate(
        "P",
        vec![ChcSort::Array(
            Box::new(ChcSort::Int),
            Box::new(nested_datatype()),
        )],
    );
    refuses_prepared(&problem);
    assert_identity(
        &problem,
        crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA,
    );
}
