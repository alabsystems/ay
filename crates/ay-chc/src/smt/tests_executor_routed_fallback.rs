// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `check_sat_with_executor_fallback` schedule locks: an executor-routed query
//! is solved ONCE with the whole budget, never first inside the native slice
//! and then again by the fallback.

use super::check_sat::take_executor_session_budgets_for_tests;
use super::SmtContext;
use crate::{ChcExpr, ChcSort, ChcVar};
use std::time::Duration;

fn bv(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(64)))
}

fn bv_array(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(
        name,
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8))),
    ))
}

/// `a[i] = 1 ∧ a[j] = 2 ∧ i = j`: the selects are over an array VARIABLE,
/// so the #8664 read-over-write expansion keeps them, constant propagation
/// cannot settle the query, and `prepare_check_sat_query` routes it to the
/// Executor.
fn routed_unsat() -> ChcExpr {
    ChcExpr::and_all([
        ChcExpr::eq(
            ChcExpr::select(bv_array("a"), bv("i")),
            ChcExpr::BitVec(1, 8),
        ),
        ChcExpr::eq(
            ChcExpr::select(bv_array("a"), bv("j")),
            ChcExpr::BitVec(2, 8),
        ),
        ChcExpr::eq(bv("i"), bv("j")),
    ])
}

/// Counterfactual: before the executor-first schedule the first session was
/// the `prepare_check_sat_query` dispatch inside the native slice, whose
/// budget is at most min(total/4, 2s) = 2s here; an UNSAT still certifying
/// when that slice expired was discarded and solved again by the fallback.
#[test]
fn executor_routed_query_gets_the_whole_budget_in_one_session() {
    let total = Duration::from_secs(12);
    take_executor_session_budgets_for_tests();
    let result = SmtContext::new().check_sat_with_executor_fallback_timeout(&routed_unsat(), total);
    let budgets = take_executor_session_budgets_for_tests();
    assert!(result.is_unsat(), "routed query is UNSAT, got {result:?}");
    assert_eq!(
        budgets.len(),
        1,
        "a decided routed query must cost one Executor session: {budgets:?}"
    );
    assert!(
        budgets[0] > total / 2,
        "the first Executor session must receive the whole budget, not the native slice: {budgets:?}"
    );
}

/// Executor-first stays confined to executor-routed queries: a scalar query
/// the native attempt decides (#23 Stage 2.5 schedule) pays no Executor
/// session.
#[test]
fn scalar_query_decided_natively_pays_no_executor_session() {
    let x = bv("x");
    let query = ChcExpr::and_all([
        ChcExpr::Op(
            crate::ChcOp::BvUGt,
            vec![
                std::sync::Arc::new(x.clone()),
                std::sync::Arc::new(ChcExpr::BitVec(7, 64)),
            ],
        ),
        ChcExpr::Op(
            crate::ChcOp::BvULt,
            vec![
                std::sync::Arc::new(x),
                std::sync::Arc::new(ChcExpr::BitVec(3, 64)),
            ],
        ),
    ]);
    take_executor_session_budgets_for_tests();
    let result =
        SmtContext::new().check_sat_with_executor_fallback_timeout(&query, Duration::from_secs(12));
    let budgets = take_executor_session_budgets_for_tests();
    assert!(result.is_unsat(), "x > 7 ∧ x < 3 is UNSAT, got {result:?}");
    assert!(
        budgets.is_empty(),
        "no Executor session expected: {budgets:?}"
    );
}

/// A routed query that constant propagation settles never reaches the
/// Executor in `prepare_check_sat_query`, so executor-first must not pay one.
#[test]
fn constant_settled_routed_query_pays_no_executor_session() {
    let query = ChcExpr::and_all([
        ChcExpr::eq(bv("x"), ChcExpr::BitVec(1, 64)),
        ChcExpr::not(ChcExpr::eq(bv("x"), ChcExpr::BitVec(1, 64))),
        ChcExpr::eq(
            ChcExpr::select(bv_array("a"), bv("i")),
            ChcExpr::BitVec(0, 8),
        ),
    ]);
    take_executor_session_budgets_for_tests();
    let result =
        SmtContext::new().check_sat_with_executor_fallback_timeout(&query, Duration::from_secs(12));
    let budgets = take_executor_session_budgets_for_tests();
    assert!(result.is_unsat(), "x = 1 ∧ x ≠ 1 is UNSAT, got {result:?}");
    assert!(
        budgets.is_empty(),
        "no Executor session expected: {budgets:?}"
    );
}

/// A query over Real variables goes to the Executor first on the
/// Verification lane, through both entry points: the native loop runs
/// LiaSolver on Real atoms and can never return UNSAT on them (#5925 guard),
/// so it only gets a SAT-rescue slice after an undecided Executor session.
/// Counterfactual: the native attempt used to run first and decide this SAT
/// query itself, paying no Executor session.
#[test]
fn real_query_goes_to_the_executor_first() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Real));
    let query = ChcExpr::and_all([
        ChcExpr::gt(x.clone(), ChcExpr::Real(0, 1)),
        ChcExpr::lt(x, ChcExpr::Real(1, 1)),
    ]);
    let total = Duration::from_secs(12);
    for entry in ["check_sat", "check_sat_with_executor_fallback"] {
        take_executor_session_budgets_for_tests();
        let mut smt = SmtContext::new();
        let result = if entry == "check_sat" {
            smt.check_sat_with_timeout(&query, total)
        } else {
            smt.check_sat_with_executor_fallback_timeout(&query, total)
        };
        let budgets = take_executor_session_budgets_for_tests();
        assert!(
            matches!(result, super::SmtResult::Sat(_)),
            "{entry}: 0 < x < 1 is SAT over the reals, got {result:?}"
        );
        assert_eq!(
            budgets.len(),
            1,
            "{entry}: a Real query is decided by one Executor session: {budgets:?}"
        );
        assert!(
            budgets[0] > total / 2,
            "{entry}: the Executor goes first with the whole budget: {budgets:?}"
        );
    }
}

/// Under an effort (P4a slice 8) the executor route is closed: the routed
/// query that costs one Executor session above opens none, on either entry,
/// and the run counts what the closed route refused. Whatever the internal
/// path answers, it is never `sat` for this UNSAT query.
#[test]
fn under_an_effort_a_routed_query_opens_no_executor_session() {
    let total = Duration::from_secs(12);
    take_executor_session_budgets_for_tests();
    let meter = crate::run_meter::RunMeter::open(Some(1 << 40), None);
    let fallback =
        SmtContext::new().check_sat_with_executor_fallback_timeout(&routed_unsat(), total);
    let plain = SmtContext::new().check_sat_with_timeout(&routed_unsat(), total);
    let work = meter.close().expect("the run is metered");
    let budgets = take_executor_session_budgets_for_tests();
    assert!(
        budgets.is_empty(),
        "no Executor session under an effort: {budgets:?}"
    );
    assert!(
        work.closed_route_checks >= 2,
        "each entry's refusal is counted: {work:?}"
    );
    assert!(
        !fallback.is_sat() && !plain.is_sat(),
        "{fallback:?} {plain:?}"
    );
}
