// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn expired_or_missing_origin_never_enters_either_checker() {
    let start = Instant::now();
    for (origin, now) in [
        (Some(start), start + Duration::from_millis(100)),
        (Some(start), start + Duration::from_millis(101)),
        (None, start),
    ] {
        assert!(!check_with_clock(
            100,
            origin,
            || now,
            |_| panic!("expired first phase"),
            |_| panic!("expired fallback"),
        ));
    }
}

#[test]
fn setup_consumption_reduces_the_first_grant() {
    let start = Instant::now();
    let calls = Cell::new(0);
    assert!(check_with_clock(
        100,
        Some(start),
        || {
            calls.set(calls.get() + 1);
            start + Duration::from_millis(if calls.get() == 1 { 20 } else { 30 })
        },
        |remaining| {
            assert_eq!(remaining, Duration::from_millis(70));
            true
        },
        |_| panic!("a positive first checker must not enter fallback"),
    ));
    calls.set(0);
    assert!(!check_with_clock(
        100,
        Some(start),
        || {
            calls.set(calls.get() + 1);
            start + Duration::from_millis(if calls.get() == 1 { 20 } else { 100 })
        },
        |_| panic!("setup exhausted the first grant"),
        |_| panic!("setup exhausted the fallback grant"),
    ));
}

#[test]
fn first_phase_consumption_does_not_renew_the_fallback_deadline() {
    let start = Instant::now();
    let now = Cell::new(start + Duration::from_millis(20));
    assert!(check_with_clock(
        100,
        Some(start),
        || now.get(),
        |remaining| {
            assert_eq!(remaining, Duration::from_millis(80));
            now.set(start + Duration::from_millis(90));
            false
        },
        |deadline| {
            assert_eq!(deadline, start + Duration::from_millis(100));
            assert_eq!(
                deadline.duration_since(now.get()),
                Duration::from_millis(10)
            );
            now.set(start + Duration::from_millis(99));
            true
        },
    ));
}

#[test]
fn first_phase_overrun_is_terminal_for_both_checker_results() {
    let start = Instant::now();
    for result in [false, true] {
        for elapsed in [100, 101] {
            let now = Cell::new(start);
            assert!(!check_with_clock(
                100,
                Some(start),
                || now.get(),
                |_| {
                    now.set(start + Duration::from_millis(elapsed));
                    result
                },
                |_| panic!("an exhausted first phase cannot renew a fallback"),
            ));
        }
    }
}

#[test]
fn exhaustion_between_phases_and_opaque_fallback_overrun_refuse() {
    let start = Instant::now();
    let calls = Cell::new(0);
    assert!(!check_with_clock(
        100,
        Some(start),
        || {
            calls.set(calls.get() + 1);
            start + Duration::from_millis(if calls.get() < 4 { 0 } else { 100 })
        },
        |_| false,
        |_| panic!("expired before fallback entry"),
    ));
    for elapsed in [100, 101] {
        let now = Cell::new(start);
        assert!(!check_with_clock(
            100,
            Some(start),
            || now.get(),
            |_| false,
            |_| {
                now.set(start + Duration::from_millis(elapsed));
                true
            },
        ));
    }
}

#[test]
fn live_false_checkers_refuse_and_the_existing_ten_second_cap_is_shared() {
    let start = Instant::now();
    for (timeout_ms, origin) in [(0, None), (30_000, Some(start))] {
        let now = Cell::new(start);
        let fallback_called = Cell::new(false);
        assert!(!check_with_clock(
            timeout_ms,
            origin,
            || now.get(),
            |remaining| {
                assert_eq!(remaining, Duration::from_secs(10));
                now.set(start + Duration::from_secs(9));
                false
            },
            |deadline| {
                fallback_called.set(true);
                assert_eq!(deadline, start + Duration::from_secs(10));
                false
            },
        ));
        assert!(fallback_called.get());
    }
}

#[test]
fn real_query_checker_rejects_invalid_models_and_accepts_a_live_valid_model() {
    use ay::chc::{ChcExpr, ChcParser, ChcSort, ChcVar, PredicateInterpretation};
    let problem = ChcParser::parse(
        "(set-logic HORN)
         (declare-fun P (Int) Bool)
         (assert (forall ((x Int)) (=> (= x 0) (P x))))
         (assert (forall ((x Int)) (=> (and (P x) (< x 0)) false)))
         (check-sat)",
    )
    .unwrap();
    assert_eq!(problem.clauses().len(), 2);
    assert_eq!(problem.queries().count(), 1);
    let predicate = problem.lookup_predicate("P").unwrap();
    let var = ChcVar::new("v", ChcSort::Int);
    let now = Instant::now();
    for (formula, expected) in [
        (ChcExpr::Bool(true), false),
        (
            ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(0)),
            true,
        ),
    ] {
        let mut model = InvariantModel::default();
        model.set(
            predicate,
            PredicateInterpretation::new(vec![var.clone()], formula),
        );
        assert_eq!(
            discharges_with_clock(&problem, &model, 5000, Some(now), || now),
            expected,
        );
    }
}
