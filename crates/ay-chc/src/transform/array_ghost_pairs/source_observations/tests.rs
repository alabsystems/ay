// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

mod fixtures;
mod synthesis;

use super::*;
use crate::{CancellationToken, ChcExpr, ChcSort, ClauseHead, PredicateId};
use fixtures::*;
use std::sync::Arc;

#[test]
fn layout_keeps_one_shared_outer_axis_and_an_independent_inner_axis() {
    let source = fixture("a", false);
    let token = CancellationToken::new();
    let control = control(&token);
    assert_eq!(requires_observations(&source, &control), Some(true));
    let layout = Layout::analyze(&source, &control).unwrap();
    let id = PredicateId::new(0);
    assert_eq!(layout.axes(id).unwrap(), &[bv(64), bv(64)]);
    let vars = layout.canonical(id).unwrap();
    assert_eq!(vars.len(), 6); // originals, row/column, len/cell.
    assert_eq!(vars[4].sort, bv(64));
    assert_eq!(vars[5].sort, bv(8));
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("fact")
    };
    let axes = [ChcExpr::BitVec(33, 64), ChcExpr::BitVec(65, 64)];
    let actuals = layout.actuals(id, args, &axes, &control).unwrap();
    assert_eq!(&actuals[..2], args);
    assert_eq!(&actuals[2..4], &axes);
    assert_eq!(actuals[4], length(args[0].clone(), axes[0].clone()));
    assert_eq!(
        actuals[5],
        read(args[0].clone(), axes[0].clone(), axes[1].clone())
    );
    assert_ne!(
        actuals[5],
        read(args[0].clone(), axes[1].clone(), axes[0].clone())
    );
}

#[test]
fn canonical_names_avoid_source_variables_and_actuals_refuse_wrong_tuple_metadata() {
    let source = fixture("ay!observation!0!0", false);
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    let id = PredicateId::new(0);
    assert_ne!(layout.canonical(id).unwrap()[0].name, "ay!observation!0!0");
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("fact")
    };
    assert!(layout
        .actuals(id, args, &[ChcExpr::BitVec(0, 64)], &control)
        .is_none());
    assert!(layout
        .actuals(
            id,
            args,
            &[ChcExpr::BitVec(0, 64), ChcExpr::BitVec(0, 8)],
            &control
        )
        .is_none());
    assert!(layout
        .actuals(
            id,
            &args[..1],
            &[ChcExpr::BitVec(0, 64), ChcExpr::BitVec(0, 64)],
            &control
        )
        .is_none());
    assert!(!layout.matches_source(&fixture("different", false), &control));
}

#[test]
fn observation_paths_share_copied_composite_roots_and_axis_terms() {
    let source = fixture("a", false);
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    let id = PredicateId::new(0);
    let array = layout.original_sorts(id).unwrap()[0].clone();
    let original = crate::ChcExpr::ite(
        variable("choose", ChcSort::Bool),
        variable("left", array.clone()),
        variable("right", array),
    );
    let actuals = layout
        .actuals(
            id,
            &[original, ChcExpr::BitVec(7, 8)],
            &[ChcExpr::BitVec(33, 64), ChcExpr::BitVec(65, 64)],
            &control,
        )
        .unwrap();
    let ChcExpr::FuncApp(_, _, len) = &actuals[4] else {
        panic!("len")
    };
    let ChcExpr::Op(_, len_read) = len[0].as_ref() else {
        panic!("row")
    };
    let ChcExpr::Op(_, cell) = &actuals[5] else {
        panic!("cell")
    };
    let ChcExpr::FuncApp(_, _, data) = cell[0].as_ref() else {
        panic!("data")
    };
    let ChcExpr::Op(_, data_read) = data[0].as_ref() else {
        panic!("row")
    };
    assert!(Arc::ptr_eq(&len_read[0], &data_read[0]));
    assert!(Arc::ptr_eq(&len_read[1], &data_read[1]));
    assert!(!Arc::ptr_eq(&len_read[1], &cell[1]));
}

#[test]
fn actuals_resource_refusal_is_atomic_sticky_and_fresh_retry_succeeds() {
    let source = fixture("a", false);
    let token = CancellationToken::new();
    let layout = Layout::analyze(&source, &control(&token)).unwrap();
    let id = PredicateId::new(0);
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("fact")
    };
    let axes = [ChcExpr::BitVec(33, 64), ChcExpr::BitVec(65, 64)];
    let stopped = control(&token);
    stopped.bytes(64 * 1024 * 1024 - 128).unwrap();
    assert!(layout.actuals(id, args, &axes, &stopped).is_none());
    assert!(stopped.poll().is_none());
    assert!(layout.actuals(id, args, &axes, &stopped).is_none());
    assert!(layout.actuals(id, args, &axes, &control(&token)).is_some());
}
