// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedHornClause;
use crate::{CancellationToken, ChcDtConstructor, ChcDtSelector};
use std::time::Duration;

mod fixtures;
mod sinks;
use fixtures::*;

#[test]
fn reordering_preserves_exact_array_owners_at_equal_and_mixed_widths() {
    for (left_width, right_width) in [(4, 4), (2, 5), (72, 64), (136, 64)] {
        let a = variable("a", array(left_width, bv(8)));
        let b = variable("b", array(right_width, bv(8)));
        let source = fixture(vec![a.clone(), b.clone()], vec![b, a], vec![]);
        let token = CancellationToken::new();
        let control = control(&token);
        let layout = Layout::analyze(&source, &control).unwrap();
        assert_eq!(mapping(&source, &layout, &control), vec![Some(1), Some(0)]);
        let raw = problem(&source, &layout, &control).unwrap();
        let clause = &raw.clauses()[0];
        let ClauseHead::Predicate(_, head) = &clause.head else {
            panic!("head")
        };
        let body = &clause.body.predicates[0].1;
        assert_eq!(body[2], head[3]);
        assert_eq!(body[3], head[2]);
        assert_ne!(body[2], body[3]);
        assert_eq!(body[4], head[5]);
        assert_eq!(body[5], head[4]);
        assert_eq!(
            &body[..2],
            &source.source_problem().clauses()[0].body.predicates[0].1
        );
    }
}

#[test]
fn record_field_ordinals_keep_equal_width_sibling_axes_independent() {
    let record = record(
        "Pair",
        vec![("left", array(4, bv(8))), ("right", array(4, bv(8)))],
    );
    let pair = variable("pair", record.clone());
    let other = variable("other", array(4, bv(8)));
    let source = fixture(
        vec![pair.clone(), other.clone()],
        vec![other, pair],
        vec![record],
    );
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    assert_eq!(
        mapping(&source, &layout, &control),
        vec![Some(1), Some(2), Some(0)]
    );
    let raw = problem(&source, &layout, &control).unwrap();
    let clause = &raw.clauses()[0];
    let ClauseHead::Predicate(_, head) = &clause.head else {
        panic!("head")
    };
    let body = &clause.body.predicates[0].1;
    assert_eq!(
        &body[2..5],
        &[head[3].clone(), head[4].clone(), head[2].clone()]
    );
    assert_eq!(
        &body[5..8],
        &[head[6].clone(), head[7].clone(), head[5].clone()]
    );
    assert_ne!(body[2], body[3]);
    assert_ne!(body[5], body[6]);
}

#[test]
fn nested_record_paths_preserve_outer_ancestry_and_distinct_inner_axes() {
    let row = record(
        "Row",
        vec![("first", array(5, bv(8))), ("second", array(5, bv(8)))],
    );
    let grid = record("Grid", vec![("rows", array(3, row.clone()))]);
    let matrix = variable("matrix", grid.clone());
    let other = variable("other", array(3, bv(8)));
    let source = fixture(
        vec![matrix.clone(), other.clone()],
        vec![other, matrix],
        vec![row, grid],
    );
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    assert_eq!(
        mapping(&source, &layout, &control),
        vec![Some(1), Some(2), Some(3), Some(0)]
    );
    let raw = problem(&source, &layout, &control).unwrap();
    let clause = &raw.clauses()[0];
    let ClauseHead::Predicate(_, head) = &clause.head else {
        panic!("head")
    };
    let body = &clause.body.predicates[0].1;
    assert_eq!(
        &body[2..6],
        &[
            head[3].clone(),
            head[4].clone(),
            head[5].clone(),
            head[2].clone()
        ]
    );
    assert_eq!(body[6], head[7]);
    assert_eq!(body[7], head[8]);
    assert_ne!(body[3], body[4]);
}

#[test]
fn unmatched_and_store_owners_cannot_steal_an_exactly_transported_axis() {
    let sort = array(4, bv(8));
    let a = variable("a", sort.clone());
    let b = variable("b", sort.clone());
    let c = variable("c", sort);
    let updated = ChcExpr::store(a.clone(), ChcExpr::BitVec(1, 4), ChcExpr::BitVec(7, 8));
    for replacement in [c, updated] {
        let source = fixture(
            vec![a.clone(), b.clone()],
            vec![b.clone(), replacement],
            vec![],
        );
        let token = CancellationToken::new();
        let control = control(&token);
        let layout = Layout::analyze(&source, &control).unwrap();
        assert_eq!(mapping(&source, &layout, &control), vec![None, Some(0)]);
        let raw = problem(&source, &layout, &control).unwrap();
        let clause = &raw.clauses()[0];
        let ClauseHead::Predicate(_, head) = &clause.head else {
            panic!("head")
        };
        let body = &clause.body.predicates[0].1;
        assert_eq!(body[2], ChcExpr::BitVec(0, 4));
        assert_eq!(body[3], head[2]);
        assert_ne!(body[2], body[3]);
    }
}

#[test]
fn repeated_source_arguments_do_not_merge_independently_owned_axes() {
    let a = variable("a", array(4, bv(8)));
    for (body, head, expected) in [
        (
            vec![a.clone(), a.clone()],
            vec![a.clone()],
            vec![None, None],
        ),
        (vec![a.clone()], vec![a.clone(), a], vec![None]),
    ] {
        let source = fixture(body, head, vec![]);
        let token = CancellationToken::new();
        let control = control(&token);
        let layout = Layout::analyze(&source, &control).unwrap();
        assert_eq!(mapping(&source, &layout, &control), expected);
        assert!(problem(&source, &layout, &control).is_some());
    }
}

#[test]
fn different_owners_do_not_gain_transport_but_keep_typed_positional_fallback() {
    for (head_width, expected_zero) in [(4, false), (5, true)] {
        let a = variable("a", array(4, bv(8)));
        let b = variable("b", array(head_width, bv(8)));
        let source = fixture(vec![a], vec![b], vec![]);
        let token = CancellationToken::new();
        let control = control(&token);
        let layout = Layout::analyze(&source, &control).unwrap();
        assert_eq!(mapping(&source, &layout, &control), vec![None]);
        let raw = problem(&source, &layout, &control).unwrap();
        let clause = &raw.clauses()[0];
        let ClauseHead::Predicate(_, head) = &clause.head else {
            panic!("head")
        };
        let axis = &clause.body.predicates[0].1[1];
        if expected_zero {
            assert_eq!(axis, &ChcExpr::BitVec(0, 4));
        } else {
            assert_eq!(axis, &head[1]);
        }
    }
}

#[test]
fn observed_cancel_and_expiry_refuse_transport_before_later_retries() {
    let source = simple();
    let token = CancellationToken::new();
    let layout = Layout::analyze(&source, &control(&token)).unwrap();
    let stopped = control(&token);
    token.cancel();
    assert!(try_mapping(&source, &layout, &stopped).is_none());
    token.reset();
    assert!(try_mapping(&source, &layout, &stopped).is_none());
    assert!(try_mapping(&source, &layout, &control(&token)).is_some());
    let expired = SourceControl::new(Instant::now(), &token);
    assert!(try_mapping(&source, &layout, &expired).is_none());
}

#[test]
fn complete_source_name_and_comparison_cost_refuses_before_copy() {
    let a = variable(&"a".repeat(4096), array(4, bv(8)));
    let b = variable("b", array(4, bv(8)));
    let source = fixture(vec![a.clone(), b.clone()], vec![b, a], vec![]);
    let token = CancellationToken::new();
    let layout = Layout::analyze(&source, &control(&token)).unwrap();
    let limited = control(&token);
    limited.bytes(64 * 1024 * 1024 - 4096).unwrap();
    assert!(try_mapping(&source, &layout, &limited).is_none());
    assert!(limited.poll().is_none());
    assert!(try_mapping(&source, &layout, &limited).is_none());
    assert_eq!(
        mapping(&source, &layout, &control(&token)),
        vec![Some(1), Some(0)]
    );
}
