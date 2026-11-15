// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::{CancellationToken, ChcDtConstructor, ChcDtSelector, ClauseHead};
use std::time::Duration;

fn arr(value: ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(bv(64)), Box::new(value))
}

fn cell() -> ChcSort {
    ChcSort::Datatype {
        name: "Cell record".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "mk cell".into(),
            selectors: vec![ChcDtSelector {
                name: "data".into(),
                sort: arr(bv(8)),
            }],
        }]),
    }
}

fn declarations() -> ChcProblem {
    let mut result = ChcProblem::new();
    result.add_datatype_def(
        "Cell record".into(),
        vec![("mk cell".into(), vec![("data".into(), arr(bv(8)))])],
    );
    result
}

fn function(name: &str, sort: ChcSort, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::FuncApp(name.into(), sort, args.into_iter().map(Arc::new).collect())
}

#[test]
fn exact_nested_source_keeps_joint_axes_and_quoted_constant_record_arrays() {
    let records = var("records", arr(cell()));
    let row = op(ChcOp::Select, vec![records.clone(), var("r", bv(64))]);
    let data = function("data", arr(bv(8)), vec![row]);
    let matrix = op(
        ChcOp::Eq,
        vec![
            op(ChcOp::Select, vec![data, var("c", bv(64))]),
            var("fill", bv(8)),
        ],
    );
    let default = function(
        "mk cell",
        cell(),
        vec![ChcExpr::ConstArray(bv(64), Arc::new(var("fill", bv(8))))],
    );
    let constant = ChcExpr::ConstArray(bv(64), Arc::new(default));
    let constraint = op(ChcOp::Eq, vec![records, constant]);
    let group = UniversalPremise::with_binders(
        vec![ChcVar::new("r", bv(64)), ChcVar::new("c", bv(64))],
        matrix.clone(),
    )
    .unwrap();
    let source = QuantifiedChcProblem::new(
        declarations(),
        vec![query(constraint.clone(), vec![group.clone()])],
    )
    .unwrap();
    assert_eq!(
        source.source_problem().clauses()[0]
            .body
            .constraint
            .as_ref(),
        Some(&constraint)
    );
    assert_eq!(source.premises()[0][0].matrix(), &matrix);
    let text = source.source_smtlib();
    assert!(text.contains("(records (Array (_ BitVec 64) |Cell record|))"));
    assert!(text.contains("((as const (Array (_ BitVec 64) |Cell record|))"));
    assert!(text.contains("(forall ((r (_ BitVec 64)) (c (_ BitVec 64)))"));
    assert!(text.contains("(select (data (select records r)) c)"));
    let rows = source
        .query_obligations(Duration::from_secs(60), &CancellationToken::new())
        .unwrap();
    assert_eq!(rows[0].problem().source_smtlib(), text);
    assert_eq!(
        rows[0].problem().premises()[0][0]
            .binders()
            .collect::<Vec<_>>(),
        group.binders().collect::<Vec<_>>()
    );
}

#[test]
fn nested_array_operations_authenticate_complete_argument_and_result_sorts() {
    let nested = arr(arr(bv(8)));
    let a = var("a", nested.clone());
    let row = var("row", arr(bv(8)));
    let index = ChcExpr::BitVec(33, 64);
    let updated = op(ChcOp::Store, vec![a.clone(), index.clone(), row.clone()]);
    let chosen = op(
        ChcOp::Ite,
        vec![var("condition", ChcSort::Bool), a.clone(), updated.clone()],
    );
    let valid = op(
        ChcOp::Eq,
        vec![op(ChcOp::Select, vec![chosen, index.clone()]), row],
    );
    assert!(standalone(vec![premise("unused", 64, valid)]).is_ok());
    for bad in [
        op(
            ChcOp::Store,
            vec![a.clone(), ChcExpr::BitVec(33, 8), var("row", arr(bv(8)))],
        ),
        op(
            ChcOp::Store,
            vec![a.clone(), index.clone(), var("row", arr(bv(16)))],
        ),
        op(
            ChcOp::Ite,
            vec![ChcExpr::Bool(true), a.clone(), var("other", arr(bv(8)))],
        ),
        op(ChcOp::Eq, vec![a, var("other", arr(arr(bv(16))))]),
    ] {
        assert!(standalone(vec![premise(
            "unused",
            64,
            op(ChcOp::Eq, vec![bad.clone(), bad])
        )])
        .is_err());
    }
    assert!(matches!(updated, ChcExpr::Op(ChcOp::Store, _)));
}

#[test]
fn record_cells_are_authenticated_even_under_unused_declarations_and_false_queries() {
    let mut declared = declarations();
    let invalid = arr(arr(cell())); // Cell itself already contains one array.
    declared.declare_predicate("unused", vec![invalid]);
    assert!(
        QuantifiedChcProblem::new(declared, vec![query(ChcExpr::Bool(false), vec![])]).is_err()
    );
    let mut missing = ChcProblem::new();
    let p = missing.declare_predicate("P", vec![arr(cell())]);
    assert!(QuantifiedChcProblem::new(
        missing,
        vec![QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody::new(vec![(p, vec![var("a", arr(cell()))])], None),
                ClauseHead::False
            ),
            vec![]
        )]
    )
    .is_err());
}
