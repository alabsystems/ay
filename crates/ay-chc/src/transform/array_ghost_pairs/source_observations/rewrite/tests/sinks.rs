// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn nullary_and_scalar_heads_keep_actual_wide_and_narrow_query_indices() {
    for width in [72, 136] {
        let table = variable("table", array(width, bv(8)));
        let data = variable("data", array(64, bv(8)));
        let key = variable("key", bv(width));
        let index = variable("index", bv(64));
        let constraint = ChcExpr::and_all([
            ChcExpr::ne(
                ChcExpr::select(table.clone(), key.clone()),
                ChcExpr::BitVec(0, 8),
            ),
            ChcExpr::ne(
                ChcExpr::select(data.clone(), index.clone()),
                ChcExpr::BitVec(0, 8),
            ),
        ]);
        for head in [vec![], vec![variable("flag", ChcSort::Bool)]] {
            let source = fixture_with_constraint(
                vec![table.clone(), data.clone()],
                head,
                vec![],
                Some(constraint.clone()),
            );
            let token = CancellationToken::new();
            let control = control(&token);
            let layout = Layout::analyze(&source, &control).unwrap();
            assert!(layout.axes(PredicateId::new(1)).unwrap().is_empty());
            let raw = problem(&source, &layout, &control).unwrap();
            let clause = &raw.clauses()[0];
            assert!(matches!(clause.head, ClauseHead::Predicate(..)));
            let actuals = &clause.body.predicates[0].1;
            assert_eq!(&actuals[2..4], &[key.clone(), index.clone()]);
            assert_eq!(actuals[4], ChcExpr::select(table.clone(), key.clone()));
            assert_eq!(actuals[5], ChcExpr::select(data.clone(), index.clone()));
            assert_eq!(clause.body.constraint.as_ref(), Some(&constraint));
        }
    }
}

#[test]
fn absent_or_conflicting_sink_read_indices_keep_the_typed_zero_fallback() {
    let table = variable("table", array(136, bv(8)));
    let key = variable("key", bv(136));
    let other = variable("other", bv(136));
    let conflict = ChcExpr::ne(
        ChcExpr::select(table.clone(), key),
        ChcExpr::select(table.clone(), other),
    );
    for constraint in [None, Some(conflict)] {
        let source = fixture_with_constraint(vec![table.clone()], vec![], vec![], constraint);
        let token = CancellationToken::new();
        let control = control(&token);
        let layout = Layout::analyze(&source, &control).unwrap();
        let original = &source.source_problem().clauses()[0];
        if let Some(constraint) = &original.body.constraint {
            assert!(super::super::super::candidate::query_axes(
                constraint,
                &original.body.predicates[0].1,
                PredicateId::new(0),
                &layout,
                &control,
            )
            .is_none());
        }
        let raw = problem(&source, &layout, &control).unwrap();
        assert_eq!(
            raw.clauses()[0].body.predicates[0].1[1],
            ChcExpr::BitVec(0, 136)
        );
        assert!(control.poll().is_some());
    }
}
