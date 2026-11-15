// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The assumption-mode DPLL(T) loop honours the per-check timeout, the thread
//! deadlines and lane cancellation (see the parent module).

#![allow(clippy::unwrap_used, clippy::panic)]

use crate::cancellation::CancellationToken;
use crate::smt::{ScopedLaneCancellation, ScopedSmtDeadline, SmtContext, SmtResult};
use crate::{ChcExpr, ChcSort, ChcVar};
use std::time::{Duration, Instant};

fn int(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

/// `x = 1` in the background, `x = 2` assumed: decided at once, so any
/// `Unknown` below comes from the budget, never from the query.
fn contradiction() -> (Vec<ChcExpr>, Vec<ChcExpr>) {
    (
        vec![ChcExpr::eq(int("x"), ChcExpr::int(1))],
        vec![ChcExpr::eq(int("x"), ChcExpr::int(2))],
    )
}

/// A query this loop can only give up on: Pugh's integer-empty region
/// `27 <= 11u + 13v <= 45`, `-10 <= 7u - 9v <= 4` (the Omega-test example whose
/// real shadow is non-empty) under the unimodular map `u = x - z`, `v = y - z`,
/// with `z >= 52`. The LP relaxation is feasible along the unbounded direction
/// `(1, 1, 1)`, so every branch-and-bound split leaves a feasible relaxation,
/// and the lattice closure's real shadow is inexact on it. (The original
/// fixture, the parity core `2A = 2E - 3` of `half_true_modif_m_000`, is now
/// refuted by the LIA lattice closure.) The bounds are behind `__iuc_proxy_`
/// assumptions, the shape `IucSolver` hands the loop.
fn divergent_query() -> (Vec<ChcExpr>, Vec<ChcExpr>) {
    let (x, y, z) = (int("x"), int("y"), int("z"));
    let lin = |a: i64, b: i64, c: i64| {
        ChcExpr::add(
            ChcExpr::add(
                ChcExpr::mul(ChcExpr::int(a), x.clone()),
                ChcExpr::mul(ChcExpr::int(b), y.clone()),
            ),
            ChcExpr::mul(ChcExpr::int(c), z.clone()),
        )
    };
    let constraints = [
        ChcExpr::ge(lin(11, 13, -24), ChcExpr::int(27)),
        ChcExpr::le(lin(11, 13, -24), ChcExpr::int(45)),
        ChcExpr::ge(lin(7, -9, 2), ChcExpr::int(-10)),
        ChcExpr::le(lin(7, -9, 2), ChcExpr::int(4)),
        ChcExpr::ge(z.clone(), ChcExpr::int(52)),
    ];
    let mut background = Vec::new();
    let mut assumptions = Vec::new();
    for (idx, constraint) in constraints.into_iter().enumerate() {
        let proxy = ChcExpr::var(ChcVar::new(format!("__iuc_proxy_{idx}"), ChcSort::Bool));
        background.push(ChcExpr::or(ChcExpr::not(proxy.clone()), constraint));
        assumptions.push(proxy);
    }
    (background, assumptions)
}

fn is_unsat(result: &SmtResult) -> bool {
    matches!(
        result,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    )
}

/// Run `check` on a fresh thread (the deadlines are thread-local) and fail
/// instead of hanging when it overstays `watchdog`: before the fix the
/// divergent query ran to the 1,000,000-split cap, i.e. effectively forever.
fn solve_with_watchdog(
    watchdog: Duration,
    check: impl FnOnce() -> SmtResult + Send + 'static,
) -> (SmtResult, Duration) {
    let (tx, rx) = std::sync::mpsc::channel();
    std::thread::Builder::new()
        .name("assumption-budget".to_owned())
        .spawn(move || {
            let started = Instant::now();
            let result = check();
            let _ = tx.send((result, started.elapsed()));
        })
        .unwrap();
    rx.recv_timeout(watchdog).unwrap_or_else(|_| {
        panic!(
            "check_sat_with_assumption_conjuncts overstayed its deadline by more than {watchdog:?}"
        )
    })
}

#[test]
fn expired_deadline_refuses_before_solving() {
    let (background, assumptions) = contradiction();
    // Twin: with budget left the query is decided, so the refusal below is the
    // budget's doing.
    let decided = SmtContext::new().check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        is_unsat(&decided),
        "expected UNSAT with budget, got {decided:?}"
    );

    let _deadline = ScopedSmtDeadline::install_until(ay_core::time::Instant::now());
    let refused = SmtContext::new().check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(refused, SmtResult::Unknown),
        "an expired deadline must refuse the check, got {refused:?}"
    );
}

#[test]
fn cancelled_lane_refuses_before_solving() {
    let (background, assumptions) = contradiction();
    let token = CancellationToken::new();
    let _lane = ScopedLaneCancellation::install(token.clone(), None);
    // Twin: a live lane decides the query.
    let decided = SmtContext::new().check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        is_unsat(&decided),
        "expected UNSAT on a live lane, got {decided:?}"
    );

    token.cancel();
    let refused = SmtContext::new().check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(refused, SmtResult::Unknown),
        "a cancelled lane must refuse the check, got {refused:?}"
    );
}

/// Regression (2026-09-26, `modular_hints_1362`): the deadline is live at
/// entry and expires mid-search; the loop must stop at its next poll.
#[test]
fn divergent_branch_and_bound_stops_at_the_deadline() {
    let budget = Duration::from_millis(500);
    let (result, elapsed) = solve_with_watchdog(Duration::from_secs(60), move || {
        let (background, assumptions) = divergent_query();
        let _deadline = ScopedSmtDeadline::install(budget);
        SmtContext::new().check_sat_with_assumption_conjuncts(&background, &assumptions)
    });
    // The query is UNSAT (z3), but this loop cannot refute it: it diverges
    // until a budget signal stops it. If it ever returns Unsat here, the
    // fixture is no longer divergent and this test checks nothing; re-pin
    // it to a query the loop still cannot decide.
    assert!(
        matches!(result, SmtResult::Unknown),
        "expected the budget signal to stop a divergent search, got {result:?}"
    );
    assert!(
        elapsed < Duration::from_secs(20),
        "the check ran {elapsed:?} against a {budget:?} deadline"
    );
    assert!(
        elapsed >= budget / 2,
        "the loop gave up after {elapsed:?}, before its {budget:?} deadline: the fixture no longer diverges"
    );
}

#[test]
fn spent_check_timeout_refuses_before_solving() {
    let (background, assumptions) = contradiction();
    // Twin: under a per-check timeout with time left the query is decided, so
    // the refusal below is the timeout's doing.
    let mut live = SmtContext::new();
    let _live_timeout = live.scoped_check_timeout(Some(Duration::from_mins(1)));
    let decided = live.check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        is_unsat(&decided),
        "expected UNSAT under a live check timeout, got {decided:?}"
    );

    // `check_sat` refuses a zero per-check timeout before any work
    // (`prepare_check_sat_query`); this loop must too.
    let mut spent = SmtContext::new();
    let _spent_timeout = spent.scoped_check_timeout(Some(Duration::ZERO));
    let refused = spent.check_sat_with_assumption_conjuncts(&background, &assumptions);
    assert!(
        matches!(refused, SmtResult::Unknown),
        "a spent check timeout must refuse the check, got {refused:?}"
    );
}

/// Regression (2026-09-26 review of the budget above): the context's per-check
/// timeout (`SmtContext::scoped_check_timeout`, e.g. PDR's 5 s main-loop cap)
/// bounds this loop as it bounds `check_sat`, with no thread deadline
/// installed. The budget used to fold only the deadlines: a 1 s check timeout
/// was still splitting at 12 s.
#[test]
fn divergent_branch_and_bound_stops_at_the_check_timeout() {
    let timeout = Duration::from_millis(300);
    let (result, elapsed) = solve_with_watchdog(Duration::from_mins(1), move || {
        let (background, assumptions) = divergent_query();
        let mut ctx = SmtContext::new();
        let _timeout = ctx.scoped_check_timeout(Some(timeout));
        ctx.check_sat_with_assumption_conjuncts(&background, &assumptions)
    });
    // The query is UNSAT (z3), but this loop cannot refute it: it diverges
    // until a budget signal stops it. If it ever returns Unsat here, the
    // fixture is no longer divergent and this test checks nothing; re-pin
    // it to a query the loop still cannot decide.
    assert!(
        matches!(result, SmtResult::Unknown),
        "expected the check timeout to stop a divergent search, got {result:?}"
    );
    assert!(
        elapsed < Duration::from_secs(10),
        "the check ran {elapsed:?} against a {timeout:?} check timeout"
    );
    assert!(
        elapsed >= timeout / 2,
        "the loop gave up after {elapsed:?}, before its {timeout:?} check timeout: the fixture no longer diverges"
    );
}

/// Regression twin for lane cancellation: a portfolio cancelling the lane
/// mid-search stops the loop as well.
#[test]
fn divergent_branch_and_bound_stops_when_the_lane_is_cancelled() {
    let (result, elapsed) = solve_with_watchdog(Duration::from_secs(60), || {
        let (background, assumptions) = divergent_query();
        let token = CancellationToken::new();
        let _lane = ScopedLaneCancellation::install(token.clone(), None);
        let _cancel = token.cancel_after(Duration::from_millis(500));
        SmtContext::new().check_sat_with_assumption_conjuncts(&background, &assumptions)
    });
    // The query is UNSAT (z3), but this loop cannot refute it: it diverges
    // until a budget signal stops it. If it ever returns Unsat here, the
    // fixture is no longer divergent and this test checks nothing; re-pin
    // it to a query the loop still cannot decide.
    assert!(
        matches!(result, SmtResult::Unknown),
        "expected the budget signal to stop a divergent search, got {result:?}"
    );
    assert!(
        elapsed < Duration::from_secs(20),
        "the check ran {elapsed:?} after its lane was cancelled at 500ms"
    );
    assert!(
        elapsed >= Duration::from_millis(250),
        "the loop gave up after {elapsed:?}, before its lane was cancelled: the fixture no longer diverges"
    );
}
