// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `transition_check` on a domain with an empty range: crossed bounds empty an
//! Int range, and the exhaustive enumeration used to walk every assignment of
//! the ranges before it (2026-10-31, Trust's verification of ay-sat: PDR
//! workers sat in it for hours). On that date a lone bound beyond ±100 emptied
//! a range too; since 2026-11-01 such a range is anchored inside its bounds
//! (`window_tests.rs`), so these instances cross their bounds instead, which
//! gives the same `150..=100` and `-100..=-150` ranges.

use super::*;
use std::sync::mpsc;
use std::time::Duration;

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(int_var(name))
}

fn and(args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(ChcOp::And, args.into_iter().map(Arc::new).collect())
}

/// Query variables `v0..v{n}` in that order of appearance (so in that order in
/// `transition_check`'s ranges), with `v{empty_at}` bounded by `bound` in the
/// body and every other variable unbounded (default range `-50..=50`). The query
/// pins every variable to a value; the empty variable's value is `pinned` (one
/// side of its crossed bounds, outside its empty range).
fn instance(n: usize, empty_at: usize, bound: ChcExpr, pinned: i64) -> (ChcExpr, ChcExpr) {
    let body = bound;
    let query = and((0..n)
        .map(|i| {
            let value = if i == empty_at { pinned } else { 0 };
            ChcExpr::eq(var(&format!("v{i}")), ChcExpr::int(value))
        })
        .collect());
    (body, query)
}

/// `v >= 150 /\ v <= 100`: the range `150..=100`.
fn above(name: &str) -> ChcExpr {
    and(vec![
        ChcExpr::ge(var(name), ChcExpr::int(150)),
        ChcExpr::le(var(name), ChcExpr::int(100)),
    ])
}

/// `v <= -150 /\ v >= -100`: the range `-100..=-150`.
fn below(name: &str) -> ChcExpr {
    and(vec![
        ChcExpr::le(var(name), ChcExpr::int(-150)),
        ChcExpr::ge(var(name), ChcExpr::int(-100)),
    ])
}

/// Run `transition_check` on its own thread and give it `limit`.
fn check_within(
    body: ChcExpr,
    query: ChcExpr,
    limit: Duration,
) -> Option<Option<FxHashMap<String, SmtValue>>> {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(transition_check(&body, &ChcExpr::Bool(true), &query));
    });
    rx.recv_timeout(limit).ok()
}

#[test]
fn a_range_is_empty_only_when_it_holds_no_value() {
    let int = |lo, hi| ConcreteCheckRange::Int {
        name: String::from("x"),
        lo,
        hi,
    };
    let bv = |count| ConcreteCheckRange::BitVec {
        name: String::from("b"),
        width: 8,
        count,
    };
    assert!(!int(0, 0).is_empty());
    assert!(!int(-100, 100).is_empty());
    assert!(int(1, 0).is_empty());
    assert!(int(150, 100).is_empty());
    assert!(!bv(1).is_empty());
    assert!(!bv(256).is_empty());
    assert!(bv(0).is_empty());
}

/// Nine variables with the empty one at every position, on both sides of the
/// window. Before the fix the enumeration walked 101^k assignments of the `k`
/// variables before the empty one (about 10^16 for `k = 8`) and never returned.
#[test]
fn an_empty_range_answers_at_once_wherever_it_stands() {
    for empty_at in 0..9 {
        for (bound, pinned) in [
            (above(&format!("v{empty_at}")), 150),
            (below(&format!("v{empty_at}")), -150),
        ] {
            let (body, query) = instance(9, empty_at, bound, pinned);
            let answer = check_within(body, query, Duration::from_secs(60));
            assert_eq!(
                answer,
                Some(None),
                "the empty range at position {empty_at} must answer None within the limit"
            );
        }
    }
}

/// Where the old exhaustive enumeration finishes (two ranges of 101 values
/// beside the empty one), its answer and the early answer are the same `None`,
/// for every position of the empty range, although the query is satisfiable
/// just outside the empty domain (`v = 150`): the check's meaning is
/// unchanged, only the time to reach it.
#[test]
fn the_early_answer_is_the_exhaustive_enumerations_answer() {
    for empty_at in 0..3 {
        let names: Vec<String> = (0..3).map(|i| format!("v{i}")).collect();
        let ranges: Vec<ConcreteCheckRange> = names
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let (lo, hi) = if i == empty_at { (150, 100) } else { (-50, 50) };
                ConcreteCheckRange::Int {
                    name: name.clone(),
                    lo,
                    hi,
                }
            })
            .collect();
        let (body, query) = instance(3, empty_at, above(&names[empty_at]), 150);
        let mut assignment = FxHashMap::default();
        let stop = ConcreteStop::none();
        let exhaustive = enumerate_and_check_generic(
            &ranges,
            0,
            &mut assignment,
            &mut Probe::new(&query, None, stop.resolve()),
        );
        let early = transition_check(&body, &ChcExpr::Bool(true), &query);
        assert_eq!(exhaustive, None);
        assert_eq!(early, exhaustive, "position {empty_at}");

        let mut model = FxHashMap::default();
        for (i, name) in names.iter().enumerate() {
            let value = if i == empty_at { 150 } else { 0 };
            model.insert(name.clone(), SmtValue::Int(value));
        }
        assert_eq!(
            evaluate_expr(&query, &model),
            Some(SmtValue::Bool(true)),
            "control: the query holds outside the empty domain"
        );
    }
}

/// A domain with no empty range still reaches the exhaustive or sampling
/// branches and finds a counterexample inside the bounds.
#[test]
fn a_non_empty_domain_still_finds_its_counterexample() {
    let body = and(vec![
        ChcExpr::ge(var("v0"), ChcExpr::int(5)),
        ChcExpr::le(var("v0"), ChcExpr::int(7)),
    ]);
    let query = and(vec![
        ChcExpr::eq(var("v0"), ChcExpr::int(6)),
        ChcExpr::eq(var("v1"), ChcExpr::int(3)),
    ]);
    let model = transition_check(&body, &ChcExpr::Bool(true), &query);
    let model = model.expect("v0 = 6, v1 = 3 lies inside the bounded domain");
    assert_eq!(model.get("v0"), Some(&SmtValue::Int(6)));
    assert_eq!(model.get("v1"), Some(&SmtValue::Int(3)));
}
