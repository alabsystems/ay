// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![cfg(test)]

mod nesting;

use super::*;
use crate::ChcParser;

fn guarded(guard: ChcExpr, value: ChcExpr) -> ChcExpr {
    op(
        ChcOp::Implies,
        vec![guard, op(ChcOp::Eq, vec![read("a", 64), value])],
    )
}

fn parse_body(body: &str, binders: &str, polarity: i8) -> ChcParser {
    let mut parser = ChcParser::new();
    parser.polarity = polarity;
    parser.variables.insert("a".into(), array_sort(64));
    parser.variables.insert("b".into(), array_sort(64));
    parser.variables.insert("n".into(), ChcSort::BitVec(64));
    parser.input = format!("(forall ({binders}) {body})");
    parser.parse_expr().unwrap();
    parser
}

#[test]
fn parser_near_misses_keep_existing_downgrade_marker() {
    for body in [
        "(=> (bvult i n) (= (select a i) true))",
        "(=> (bvslt i (_ bv2 64)) (= (select a i) true))",
        "(=> (bvult (bvadd i (_ bv1 64)) (_ bv2 64)) (= (select a i) true))",
        "(=> (or (bvult i (_ bv2 64)) (bvuge i (_ bv5 64))) (= (select a i) true))",
        "(=> (bvult i (_ bv65536 64)) (= (select a i) true))",
        "(=> (bvult i (_ bv18446744073709551616 64)) (= (select a i) true))",
    ] {
        assert!(
            parse_body(body, "(i (_ BitVec 64))", -1)
                .problem
                .has_stripped_body_forall(),
            "{body}"
        );
    }
    let body = "(=> (bvult i (_ bv2 64)) (= (select a i) true))";
    assert!(parse_body(body, "(i (_ BitVec 64)) (j Bool)", -1)
        .problem
        .has_stripped_body_forall());
    assert!(parse_body(body, "(i (_ BitVec 64))", 0)
        .problem
        .has_stripped_body_forall());
    assert!(!parse_body(body, "(i (_ BitVec 64))", 1)
        .problem
        .has_stripped_body_forall());
}

#[test]
fn empty_support_still_rejects_later_malformed_guard_and_consequent() {
    let empty = compare(ChcOp::BvULt, 0, 64);
    let malformed = op(
        ChcOp::BvULt,
        vec![var("i", ChcSort::Bool), ChcExpr::BitVec(2, 64)],
    );
    let hidden = op(ChcOp::And, vec![empty.clone(), malformed]);
    assert!(eliminate(
        &guarded(hidden, ChcExpr::Bool(true)),
        "i",
        &ChcSort::BitVec(64)
    )
    .is_none());
    for value in [
        var("i", ChcSort::Bool),
        ChcExpr::ConstArrayMarker(ChcSort::Bool),
        ChcExpr::IsTesterMarker("C".into()),
        ChcExpr::FuncApp("f".into(), ChcSort::Bool, Vec::new()),
        ChcExpr::PredicateApp("P".into(), crate::PredicateId(0), Vec::new()),
        op(ChcOp::Not, vec![ChcExpr::Bool(false)]),
    ] {
        assert!(eliminate(&guarded(empty.clone(), value), "i", &ChcSort::BitVec(64)).is_none());
    }
    let good = guarded(empty, ChcExpr::Bool(true));
    assert_eq!(
        eliminate(&good, "i", &ChcSort::BitVec(64)),
        Some(ChcExpr::Bool(true))
    );
    let bad_tail = op(ChcOp::And, vec![good, ChcExpr::Bool(false)]);
    assert!(eliminate(&bad_tail, "i", &ChcSort::BitVec(64)).is_none());
}

#[test]
fn raw_width_and_sort_mismatches_never_receive_exact_elimination() {
    let equality = op(ChcOp::Eq, vec![read("a", 2), ChcExpr::Bool(true)]);
    for guard in [
        compare(ChcOp::BvULt, 4, 2),
        op(
            ChcOp::BvULt,
            vec![var("i", ChcSort::BitVec(3)), ChcExpr::BitVec(2, 2)],
        ),
        op(
            ChcOp::BvULt,
            vec![var("i", ChcSort::BitVec(2)), ChcExpr::BitVec(2, 3)],
        ),
    ] {
        assert!(eliminate(
            &op(ChcOp::Implies, vec![guard, equality.clone()]),
            "i",
            &ChcSort::BitVec(2)
        )
        .is_none());
    }
    for width in [0, 65, u32::MAX] {
        assert!(eliminate(&resize(0, 1, width, true), "i", &ChcSort::BitVec(width)).is_none());
    }
    let arr = var(
        "bv",
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(2))),
    );
    let lhs = op(ChcOp::Select, vec![arr, var("i", ChcSort::BitVec(64))]);
    for rhs in [
        ChcExpr::BitVec(4, 2),
        ChcExpr::BitVec(1, 3),
        ChcExpr::Bool(true),
    ] {
        let body = op(
            ChcOp::Implies,
            vec![
                compare(ChcOp::BvULt, 0, 64),
                op(ChcOp::Eq, vec![lhs.clone(), rhs]),
            ],
        );
        assert!(eliminate(&body, "i", &ChcSort::BitVec(64)).is_none());
    }
}

#[test]
fn shared_inspection_and_output_allowance_has_a_complete_boundary() {
    // This exact fixture uses 23 inspection units and 11 per emitted instance.
    let accepted = (MAX_SINGLETON_FORALL_INSPECTION_NODES - 23) / 11;
    let result = eliminate(
        &resize(accepted as u128, 0, 64, false),
        "i",
        &ChcSort::BitVec(64),
    )
    .unwrap();
    assert!(matches!(&result, ChcExpr::Op(ChcOp::And, args) if args.len() == accepted));
    assert!(eliminate(
        &resize(accepted as u128 + 1, 0, 64, false),
        "i",
        &ChcSort::BitVec(64)
    )
    .is_none());
    let half = resize((accepted / 2 + 1) as u128, 0, 64, false);
    assert!(eliminate(
        &op(ChcOp::And, vec![half.clone(), half]),
        "i",
        &ChcSort::BitVec(64)
    )
    .is_none());
}

#[test]
fn depth_width_and_names_are_bounded_even_when_every_support_is_empty() {
    let leaf = resize(0, 0, 64, false);
    let mut deep = leaf.clone();
    for _ in 0..=MAX_DEPTH {
        deep = op(ChcOp::And, vec![deep]);
    }
    assert!(eliminate(&deep, "i", &ChcSort::BitVec(64)).is_none());
    #[expect(
        clippy::rc_clone_in_vec_init,
        reason = "the node-cap fixture intentionally shares one immutable leaf instead of materializing width nodes"
    )]
    let wide = ChcExpr::Op(
        ChcOp::And,
        vec![Arc::new(leaf); MAX_SINGLETON_FORALL_INSPECTION_NODES],
    );
    assert!(eliminate(&wide, "i", &ChcSort::BitVec(64)).is_none());
    let huge_name = "n".repeat(MAX_SINGLETON_FORALL_BINDER_NAME_BYTES + 1);
    let bad_name = guarded(compare(ChcOp::BvULt, 0, 64), var(&huge_name, ChcSort::Bool));
    assert!(eliminate(&bad_name, "i", &ChcSort::BitVec(64)).is_none());
    let mut deep_sort = ChcSort::Bool;
    for _ in 0..128 {
        deep_sort = ChcSort::Array(Box::new(ChcSort::Bool), Box::new(deep_sort));
    }
    let bad_sort = guarded(compare(ChcOp::BvULt, 0, 64), var("x", deep_sort));
    assert!(eliminate(&bad_sort, "i", &ChcSort::BitVec(64)).is_none());
}
