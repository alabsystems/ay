// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcParser, ChcVar};

#[path = "tests/candidates.rs"]
mod candidates;

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn array(key: ChcSort, value: ChcSort) -> ChcExpr {
    var("array", ChcSort::Array(Box::new(key), Box::new(value)))
}

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

fn normalized(expression: &ChcExpr) -> Option<ChcExpr> {
    normalize(expression, &mut 1_000_000, &mut || false).map(Cow::into_owned)
}

#[test]
fn bare_reads_remain_borrowed_and_stops_never_return_a_partial_normalization() {
    let a = array(ChcSort::Int, ChcSort::Int);
    let bare = ChcExpr::select(a.clone(), ChcExpr::Int(0));
    assert!(matches!(
        normalize(&bare, &mut 100, &mut || false),
        Some(Cow::Borrowed(original)) if std::ptr::eq(original, &bare)
    ));
    let stored = ChcExpr::select(
        ChcExpr::store(a, ChcExpr::Int(0), ChcExpr::Int(1)),
        ChcExpr::Int(1),
    );
    assert!(normalize(&stored, &mut 1000, &mut || true).is_none());
    let before = stored.clone();
    let mut polls = 0;
    assert!(normalize(&stored, &mut 1000, &mut || {
        polls += 1;
        polls == 20
    })
    .is_none());
    assert_eq!(
        polls, 20,
        "stop must occur inside real traversal/construction"
    );
    assert_eq!(stored, before);
    assert!(normalized(&stored).is_some());
}

#[test]
fn typed_keys_and_cells_keep_newest_store_outermost_without_constant_folding() {
    for (key, value, old, new) in [
        (
            ChcSort::Int,
            ChcSort::Bool,
            ChcExpr::Bool(false),
            ChcExpr::Bool(true),
        ),
        (
            ChcSort::BitVec(32),
            ChcSort::Bool,
            ChcExpr::Bool(false),
            ChcExpr::Bool(true),
        ),
        (
            ChcSort::BitVec(64),
            ChcSort::BitVec(8),
            ChcExpr::BitVec(0, 8),
            ChcExpr::BitVec(7, 8),
        ),
    ] {
        let a = array(key.clone(), value);
        let i = var("i", key.clone());
        let j = var("j", key);
        let read = ChcExpr::select(
            ChcExpr::store(
                ChcExpr::store(a.clone(), i.clone(), old.clone()),
                i.clone(),
                new.clone(),
            ),
            j.clone(),
        );
        let expected = op(
            ChcOp::Ite,
            vec![
                ChcExpr::eq(i.clone(), j.clone()),
                new,
                op(
                    ChcOp::Ite,
                    vec![ChcExpr::eq(i, j.clone()), old, ChcExpr::select(a, j)],
                ),
            ],
        );
        assert_eq!(normalized(&read), Some(expected));
    }
}

#[test]
fn malformed_original_operands_and_unsupported_key_sorts_fail_closed() {
    let a = array(ChcSort::BitVec(2), ChcSort::BitVec(8));
    let key = ChcExpr::BitVec(1, 2);
    let good = ChcExpr::BitVec(7, 8);
    let malformed_value = op(
        ChcOp::Ite,
        vec![ChcExpr::Bool(true), good.clone(), ChcExpr::Bool(false)],
    );
    let malformed_index = op(ChcOp::BvAdd, vec![key.clone(), ChcExpr::Bool(false)]);
    let stored = ChcExpr::store(a.clone(), key.clone(), good.clone());
    for malformed_select in [
        op(ChcOp::Select, vec![stored.clone()]),
        op(ChcOp::Select, vec![stored, key.clone(), key.clone()]),
    ] {
        assert!(normalized(&malformed_select).is_none());
    }
    for store in [
        op(ChcOp::Store, vec![a.clone(), key.clone()]),
        op(
            ChcOp::Store,
            vec![a.clone(), key.clone(), good.clone(), good.clone()],
        ),
        ChcExpr::store(a.clone(), ChcExpr::BitVec(1, 3), good.clone()),
        ChcExpr::store(a.clone(), key.clone(), ChcExpr::BitVec(7, 7)),
        ChcExpr::store(a.clone(), key.clone(), malformed_value),
        ChcExpr::store(a.clone(), malformed_index, good.clone()),
        ChcExpr::store(a.clone(), key.clone(), ChcExpr::BitVec(256, 8)),
        ChcExpr::store(a, key.clone(), ChcExpr::BitVec(0, 0)),
    ] {
        assert!(normalized(&ChcExpr::select(store, key.clone())).is_none());
    }
    for (sort, index) in [
        (ChcSort::Bool, ChcExpr::Bool(false)),
        (ChcSort::BitVec(65), ChcExpr::BitVec(1, 65)),
    ] {
        let stored = ChcExpr::store(array(sort, ChcSort::BitVec(8)), index.clone(), good.clone());
        assert!(normalized(&ChcExpr::select(stored, index)).is_none());
    }
}

#[test]
fn expanded_index_occurrences_and_depth_are_bounded_before_publication() {
    let a = array(ChcSort::BitVec(8), ChcSort::BitVec(8));
    let mut index = Arc::new(ChcExpr::BitVec(1, 8));
    for _ in 0..6 {
        index = Arc::new(ChcExpr::Op(
            ChcOp::BvAdd,
            vec![Arc::clone(&index), Arc::clone(&index)],
        ));
    }
    let mut stored = a;
    for i in 0..8 {
        stored = ChcExpr::store(stored, ChcExpr::BitVec(i, 8), ChcExpr::BitVec(7, 8));
    }
    let expression = ChcExpr::Op(ChcOp::Select, vec![Arc::new(stored), index]);
    let mut source_budget = 4096;
    assert_eq!(
        contains_read_over_write(
            &expression,
            &mut Meter {
                remaining: &mut source_budget,
                stopped: &mut || false
            },
        ),
        Some(true)
    );
    assert!(source_budget > 0, "the source itself fits this allowance");
    let mut budget = 4096;
    assert!(normalize(&expression, &mut budget, &mut || false).is_none());
    assert_eq!(
        budget, 0,
        "expanded, not merely unique Arc, work exhausts the meter"
    );
    assert!(normalized(&expression).is_some());

    let mut deep = ChcExpr::Bool(false);
    for _ in 0..MAX_EXPR_RECURSION_DEPTH {
        deep = op(ChcOp::Not, vec![deep]);
    }
    assert!(normalized(&deep).is_none());
}
