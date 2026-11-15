// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedChcFunction;
use crate::ChcOp;
use std::sync::Arc;

enum Order {
    Original,
    Reversed,
}

fn source(unused_width: u32, order: Order) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let mut functions = vec![
        QuantifiedChcFunction::new(
            "uf_range".into(),
            vec![ChcSort::Bool, ChcSort::BitVec(64), ChcSort::BitVec(64)],
            ChcSort::BitVec(1),
        ),
        QuantifiedChcFunction::new(
            "unused".into(),
            vec![ChcSort::BitVec(unused_width)],
            ChcSort::BitVec(unused_width),
        ),
    ];
    if matches!(order, Order::Reversed) {
        functions.reverse();
    }
    let row = ChcVar::new("row", ChcSort::BitVec(64));
    let column = ChcVar::new("column", ChcSort::BitVec(64));
    let call = ChcExpr::FuncApp(
        "uf_range".into(),
        ChcSort::BitVec(1),
        vec![
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::Var(row.clone())),
            Arc::new(ChcExpr::Var(column.clone())),
        ],
    );
    let matrix = ChcExpr::Op(
        ChcOp::Eq,
        vec![Arc::new(call), Arc::new(ChcExpr::BitVec(1, 1))],
    );
    let premise = UniversalPremise::with_binders(vec![row, column], matrix).unwrap();
    let mut clauses = vec![QuantifiedHornClause::new(
        HornClause::fact(ChcExpr::Bool(true), p, vec![]),
        vec![premise],
    )];
    for enabled in [false, true] {
        clauses.push(QuantifiedHornClause::new(
            HornClause::query(ClauseBody::new(
                vec![(p, vec![])],
                Some(ChcExpr::Bool(enabled)),
            )),
            vec![],
        ));
    }
    QuantifiedChcProblem::new_with_functions(declarations, functions, clauses).unwrap()
}

#[test]
fn every_query_slice_keeps_unused_function_declarations_and_complete_premise_scope() {
    let source = source(8, Order::Original);
    let rows = source
        .query_obligations(Duration::from_secs(30), &CancellationToken::new())
        .unwrap();
    assert_eq!(rows.len(), 2);
    for (index, row) in rows.iter().enumerate() {
        assert_eq!(row.id().source_query_ordinal(), index);
        assert_eq!(row.id().query_clause_index(), index + 1);
        assert_eq!(row.id().defining_clause_index(), None);
        assert_eq!(row.id().aggregate_source_sha256(), source.source_sha256());
        let slice = row.problem();
        assert_eq!(
            slice.function_declarations(),
            source.function_declarations()
        );
        assert_eq!(slice.source_problem().clauses().len(), 2);
        assert_eq!(slice.premises()[0].len(), 1);
        let expected = &source.premises()[0][0];
        let actual = &slice.premises()[0][0];
        assert_eq!(actual.matrix(), expected.matrix());
        assert_eq!(
            actual.binders().collect::<Vec<_>>(),
            expected.binders().collect::<Vec<_>>()
        );
        assert_eq!(
            slice.source_problem().clauses()[1].body.constraint,
            Some(ChcExpr::Bool(index == 1))
        );
        assert_eq!(row.id().content_sha256(), slice.source_sha256());
        assert_eq!(
            slice
                .source_smtlib()
                .matches("(declare-fun unused ")
                .count(),
            1
        );
    }
    assert_ne!(rows[0].id(), rows[1].id());
}

#[test]
fn unused_signature_changes_and_declaration_order_are_bound_in_every_row_identity() {
    let token = CancellationToken::new();
    let original = source(8, Order::Original);
    let rows = original
        .query_obligations(Duration::from_secs(30), &token)
        .unwrap();
    for changed in [source(16, Order::Original), source(8, Order::Reversed)] {
        assert_ne!(changed.source_sha256(), original.source_sha256());
        let changed_rows = changed
            .query_obligations(Duration::from_secs(30), &token)
            .unwrap();
        assert_eq!(changed_rows.len(), rows.len());
        for (before, after) in rows.iter().zip(&changed_rows) {
            assert_eq!(
                before.id().source_query_ordinal(),
                after.id().source_query_ordinal()
            );
            assert_eq!(
                before.id().query_clause_index(),
                after.id().query_clause_index()
            );
            assert_ne!(
                before.id().aggregate_source_sha256(),
                after.id().aggregate_source_sha256()
            );
            assert_ne!(before.id().content_sha256(), after.id().content_sha256());
        }
    }
    let repeated = source(8, Order::Original)
        .query_obligations(Duration::from_secs(30), &token)
        .unwrap();
    assert_eq!(rows[0].id(), repeated[0].id());
    assert_eq!(rows[1].id(), repeated[1].id());
}

#[test]
fn unused_wide_function_signatures_consume_the_actual_shared_slice_copy_allowance() {
    let token = CancellationToken::new();
    let source = source(8, Order::Original);
    let measured = control(&token);
    let expected = enumerate_checked(&source, &measured).unwrap();
    assert_eq!(expected.len(), 2);
    let bytes = measured.bytes_used();
    assert!(bytes > source.source_smtlib().len());
    let exact = Control::with_limits(&token, 8_000_000, bytes);
    assert_eq!(enumerate_checked(&source, &exact).unwrap().len(), 2);
    let short = Control::with_limits(&token, 8_000_000, bytes - 1);
    assert!(enumerate_checked(&source, &short).is_err());
    assert!(short.poll().is_err());
    assert!(enumerate_checked(&source, &short).is_err());
    let fresh = enumerate_checked(&source, &control(&token)).unwrap();
    assert_eq!(fresh[0].id(), expected[0].id());
    assert_eq!(fresh[1].id(), expected[1].id());

    let wider = self::source(1024, Order::Original);
    for (left, right) in source
        .source_problem()
        .clauses()
        .iter()
        .zip(wider.source_problem().clauses())
    {
        assert_eq!(left.body.constraint, right.body.constraint);
        assert_eq!(left.body.predicates, right.body.predicates);
    }
    assert_eq!(
        source.premises()[0][0].matrix(),
        wider.premises()[0][0].matrix()
    );
    let wide_control = control(&token);
    assert_eq!(enumerate_checked(&wider, &wide_control).unwrap().len(), 2);
    assert!(wide_control.bytes_used() > bytes);
}
