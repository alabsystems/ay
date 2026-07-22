// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::thread;

#[test]
fn test_initial_state() {
    let token = CancellationToken::new();
    assert!(!token.is_cancelled());
}

#[test]
fn test_cancel() {
    let token = CancellationToken::new();
    token.cancel();
    assert!(token.is_cancelled());
}

#[test]
fn test_clone_shares_state() {
    let token1 = CancellationToken::new();
    let token2 = token1.clone();

    assert!(!token1.is_cancelled());
    assert!(!token2.is_cancelled());

    token1.cancel();

    assert!(token1.is_cancelled());
    assert!(token2.is_cancelled());
}

#[test]
fn test_reset() {
    let token = CancellationToken::new();
    token.cancel();
    assert!(token.is_cancelled());
    token.reset();
    assert!(!token.is_cancelled());
}

#[test]
fn test_child_observes_parent_cancel() {
    // Item 5: parent cancel propagates DOWN into children (and grandchildren).
    let parent = CancellationToken::new();
    let child = parent.child();
    let grandchild = child.child();
    assert!(!child.is_cancelled());
    assert!(!grandchild.is_cancelled());

    parent.cancel();

    assert!(child.is_cancelled(), "parent cancel must reach the child");
    assert!(
        grandchild.is_cancelled(),
        "parent cancel must reach the grandchild"
    );
}

#[test]
fn test_child_cancel_does_not_poison_parent() {
    // Item 5: a lane's cancel_after budget timer runs on a CHILD token, so a
    // lane budget expiry must never cancel the shared parent handle or a
    // sibling lane's token.
    let parent = CancellationToken::new();
    let lane_a = parent.child();
    let lane_b = parent.child();

    lane_a.cancel();

    assert!(lane_a.is_cancelled());
    assert!(
        !parent.is_cancelled(),
        "child cancel must not propagate up to the parent"
    );
    assert!(
        !lane_b.is_cancelled(),
        "child cancel must not leak to a sibling lane"
    );
}

#[test]
fn test_child_reset_does_not_clear_parent_cancel() {
    let parent = CancellationToken::new();
    let child = parent.child();
    parent.cancel();
    child.reset();
    assert!(
        child.is_cancelled(),
        "a child cannot reset away an upstream cancel"
    );
}

#[test]
fn test_link_upstream_attaches_parent() {
    // Item 5: a pre-existing per-stage token can be linked to the portfolio
    // handle after construction; clones made AFTER the link observe it.
    let parent = CancellationToken::new();
    let mut stage_token = CancellationToken::new();
    stage_token.link_upstream(&parent);
    let engine_clone = stage_token.clone();

    parent.cancel();

    assert!(stage_token.is_cancelled());
    assert!(engine_clone.is_cancelled());

    // Duplicate/self links are ignored (no unbounded growth, no self-cancel).
    let mut t = parent.child();
    t.link_upstream(&parent);
    assert!(t.is_cancelled(), "linked parent is already cancelled");
}

#[test]
fn test_child_cancel_after_stays_lane_local() {
    // The cancel_after timer on a child fires the CHILD only.
    let parent = CancellationToken::new();
    let lane = parent.child();
    let guard = lane.cancel_after(Duration::from_millis(20));
    thread::sleep(Duration::from_millis(200));
    drop(guard);
    assert!(lane.is_cancelled(), "lane budget timer should have fired");
    assert!(
        !parent.is_cancelled(),
        "lane budget timer must not cancel the shared parent handle"
    );
}

#[test]
fn test_cross_thread_cancellation() {
    let token = CancellationToken::new();
    let thread_token = token.clone();

    let handle = thread::spawn(move || {
        // Simulate engine polling
        while !thread_token.is_cancelled() {
            thread::yield_now();
        }
        true // Returned because of cancellation
    });

    // Small delay to let thread start polling
    thread::sleep(std::time::Duration::from_millis(10));

    // Cancel from main thread
    token.cancel();

    // Thread should exit due to cancellation
    let result = handle.join().unwrap();
    assert!(result);
}

/// Test that PDR responds to cancellation within a bounded time (#1005).
#[test]
fn test_pdr_cancellation_responsiveness() {
    use crate::expr::{ChcExpr, ChcSort, ChcVar};
    use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    use ay_core::time::Instant;
    use std::time::Duration;

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 1000 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(1000))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 1000 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(1000))),
        ),
        ClauseHead::False,
    ));

    let token = CancellationToken::new();
    let thread_token = token.clone();

    let config = PdrConfig {
        max_frames: 100,
        max_iterations: 10000,
        max_obligations: 100000,
        verbose: false,
        cancellation_token: Some(thread_token),
        ..PdrConfig::default()
    };

    let start = Instant::now();
    let handle = thread::spawn(move || {
        let mut solver = PdrSolver::new(problem, config);
        solver.solve()
    });

    thread::sleep(Duration::from_millis(100));
    token.cancel();

    let result = handle.join().unwrap();
    let elapsed = start.elapsed();

    // Use generous timeout to avoid flaky failures on loaded CI systems (#1585).
    assert!(
        elapsed < Duration::from_secs(10),
        "PDR took {elapsed:?} to respond to cancellation (expected < 10s)"
    );
    // Either Unknown (cancelled) or Safe (solved quickly) is acceptable.
    assert!(
        matches!(result, PdrResult::Unknown | PdrResult::Safe(_)),
        "PDR returned unexpected result: {result:?}"
    );
}

/// Test that BMC responds to cancellation within a bounded time (#1005).
#[test]
fn test_bmc_cancellation_responsiveness() {
    use crate::bmc::{BmcConfig, BmcSolver};
    use crate::engine_result::ChcEngineResult;
    use crate::expr::{ChcExpr, ChcSort, ChcVar};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    use ay_core::time::Instant;
    use std::time::Duration;

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let token = CancellationToken::new();
    let thread_token = token.clone();

    let config = BmcConfig::with_engine_config(1000, false, Some(thread_token));

    let start = Instant::now();
    let handle = thread::spawn(move || {
        let solver = BmcSolver::new(problem, config);
        solver.solve()
    });

    thread::sleep(Duration::from_millis(100));
    token.cancel();

    let result = handle.join().unwrap();
    let elapsed = start.elapsed();

    // Use generous timeout to avoid flaky failures on loaded CI systems (#1585).
    assert!(
        elapsed < Duration::from_secs(10),
        "BMC took {elapsed:?} to respond to cancellation (expected < 10s)"
    );
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "BMC should return Unknown on cancellation, got {result:?}"
    );
}

/// Test that `cancel_after` cancels the token after the timeout (#8554).
#[test]
fn test_cancel_after_fires_on_timeout() {
    use std::time::Duration;

    let token = CancellationToken::new();
    let _guard = token.cancel_after(Duration::from_millis(50));

    assert!(!token.is_cancelled());
    thread::sleep(Duration::from_millis(150));
    assert!(token.is_cancelled());
}

/// Test that `cancel_after` does NOT cancel the token when the guard is
/// dropped before the timeout fires (#8554).
#[test]
fn test_cancel_after_guard_drop_prevents_cancellation() {
    use std::time::Duration;

    let token = CancellationToken::new();
    {
        let _guard = token.cancel_after(Duration::from_secs(10));
        // Guard is dropped immediately here
    }
    // Timer thread should have been woken up and exited without cancelling.
    thread::sleep(Duration::from_millis(50));
    assert!(
        !token.is_cancelled(),
        "Token should NOT be cancelled when guard is dropped early"
    );
}

/// Test that the timer thread exits promptly when the guard is dropped (#8554).
#[test]
fn test_cancel_after_guard_drop_is_fast() {
    use ay_core::time::Instant;
    use std::time::Duration;

    let token = CancellationToken::new();
    let start = Instant::now();
    {
        let _guard = token.cancel_after(Duration::from_mins(1));
        // Guard dropped immediately — should NOT wait 60 seconds.
    }
    let elapsed = start.elapsed();
    assert!(
        elapsed < Duration::from_secs(1),
        "Guard drop took {elapsed:?}, expected < 1s (timer thread not cancelled promptly)"
    );
}

/// Test that PDKIND responds to cancellation within a bounded time (#1005).
#[test]
#[ntest::timeout(5_000)]
fn test_pdkind_cancellation_responsiveness() {
    use crate::engine_config::ChcEngineConfig;
    use crate::expr::{ChcExpr, ChcSort, ChcVar};
    use crate::pdkind::{PdkindConfig, PdkindResult, PdkindSolver};
    use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};
    use ay_core::time::Instant;
    use std::time::Duration;

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 1000 => Inv(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(1000))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 1000 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(1000))),
        ),
        ClauseHead::False,
    ));

    let token = CancellationToken::new();
    token.cancel();

    let config = PdkindConfig {
        base: ChcEngineConfig {
            verbose: false,
            cancellation_token: Some(token),
        },
        max_iterations: 1000,
        ..PdkindConfig::default()
    };

    let start = Instant::now();
    let solver = PdkindSolver::new(problem, config);
    let result = solver.solve();
    let elapsed = start.elapsed();

    assert!(
        elapsed < Duration::from_secs(1),
        "PDKIND took {elapsed:?} to respond to pre-cancelled token (expected < 1s)"
    );
    assert!(
        matches!(result, PdkindResult::Unknown),
        "PDKIND returned unexpected result: {result:?}"
    );
}
