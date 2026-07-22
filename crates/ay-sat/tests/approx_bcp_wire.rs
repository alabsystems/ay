// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration test for the approximate-BCP filter wire-up (issue #8789
//! Phase 2).
//!
//! This test is gated on the `approx-bcp-filter` Cargo feature. Default
//! builds do NOT depend on `ay-approx-bcp`, so the test is inert unless
//! the caller explicitly enables the feature:
//!
//! ```bash
//! cargo test -p ay-sat --features approx-bcp-filter --test approx_bcp_wire
//! ```
//!
//! The test is **observer-grade**: it exercises
//! [`Solver::run_approx_bcp_prefilter`] on a couple of small SAT instances
//! and asserts:
//!
//! 1. At least one classification counter moves (the filter is actually
//!    seeing clauses — not a no-op wire-up).
//! 2. `approx_bcp_mismatch_detected` stays at zero (the filter never
//!    reports a soundness violation against the exact trail classifier).
//!
//! A nonzero mismatch counter would indicate that
//! `ay_approx_bcp::filter::may_be_unit_or_falsified` classified some
//! clause as `NoopLikely` when the exact trail check said it was
//! unit/falsified — the only way the filter can lose soundness in the
//! Phase 3 fast path. This is the regression signal the integration test
//! is designed to catch.

#![cfg(feature = "approx-bcp-filter")]

use ay_sat::{ApproxBcpPrefilterVerdict, Literal, Solver, Variable};

/// Build a fresh solver with `n` variables pre-allocated.
fn fresh_solver(n: u32) -> Solver {
    let mut s = Solver::new(0);
    for _ in 0..n {
        s.new_var();
    }
    s
}

/// A 5-variable mixed SAT instance. Small enough to exercise every code
/// path in the filter, big enough that the arena holds several clauses of
/// different widths.
fn build_small_sat_instance() -> Solver {
    let mut s = fresh_solver(5);
    let v0 = Variable::new(0);
    let v1 = Variable::new(1);
    let v2 = Variable::new(2);
    let v3 = Variable::new(3);
    let v4 = Variable::new(4);

    // Binary clauses
    assert!(s.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]));
    assert!(s.add_clause(vec![Literal::negative(v0), Literal::positive(v2)]));
    // Ternary clauses
    assert!(s.add_clause(vec![
        Literal::positive(v1),
        Literal::negative(v2),
        Literal::positive(v3),
    ]));
    assert!(s.add_clause(vec![
        Literal::negative(v1),
        Literal::negative(v3),
        Literal::positive(v4),
    ]));
    // Quaternary clause — will keep popcount high even on partial trails.
    assert!(s.add_clause(vec![
        Literal::positive(v0),
        Literal::negative(v1),
        Literal::positive(v2),
        Literal::negative(v4),
    ]));

    s
}

#[test]
fn filter_runs_on_empty_trail_without_mismatch() {
    // Brand-new solver: no trail, no propagation performed. Counters
    // should start at zero; after one filter pass, at least one counter
    // should be nonzero (the filter has clauses to evaluate) AND the
    // mismatch counter must remain zero.
    let mut s = build_small_sat_instance();

    assert_eq!(s.approx_bcp_noop_matched(), 0);
    assert_eq!(s.approx_bcp_conflict_matched(), 0);
    assert_eq!(s.approx_bcp_mismatch_detected(), 0);

    let verdict = s.run_approx_bcp_prefilter();

    // Soundness: filter must never disagree with exact BCP in a way that
    // would cause Phase 3 to skip a unit/falsified clause.
    assert_eq!(
        s.approx_bcp_mismatch_detected(),
        0,
        "filter reported a soundness mismatch (verdict = {verdict:?})",
    );

    // The filter must have seen at least one clause — otherwise the
    // wire-up is a no-op.
    let total_classifications = s.approx_bcp_noop_matched()
        + s.approx_bcp_conflict_matched()
        + s.approx_bcp_mismatch_detected();
    assert!(
        total_classifications > 0,
        "filter classified zero clauses on non-empty arena",
    );

    // Empty trail + wide clauses → the filter should overwhelmingly
    // return `NoopLikely`. Verdict must NOT be `MismatchDetected`.
    assert!(
        matches!(
            verdict,
            ApproxBcpPrefilterVerdict::NoopLikely | ApproxBcpPrefilterVerdict::ConflictLikely
        ),
        "unexpected verdict on empty-trail small instance: {verdict:?}",
    );
}

#[test]
fn filter_runs_after_solve_without_mismatch() {
    // Solve once, then re-run the filter on the post-solve state. The
    // trail is typically nontrivial post-solve, so this exercises the
    // assignment-mask path with real data.
    let mut s = build_small_sat_instance();
    let _result = s.solve();

    // Reset the counters we care about? No — the filter may have been
    // invoked during inprocessing. We only care about deltas.
    let noop_before = s.approx_bcp_noop_matched();
    let conflict_before = s.approx_bcp_conflict_matched();
    let mismatch_before = s.approx_bcp_mismatch_detected();

    let verdict = s.run_approx_bcp_prefilter();

    let noop_after = s.approx_bcp_noop_matched();
    let conflict_after = s.approx_bcp_conflict_matched();
    let mismatch_after = s.approx_bcp_mismatch_detected();

    // Soundness: no new mismatches introduced by our explicit call.
    assert_eq!(
        mismatch_after, mismatch_before,
        "filter reported a NEW soundness mismatch post-solve (verdict = {verdict:?})",
    );

    // At least one counter should have moved between before and after
    // the explicit filter call — unless the arena was emptied by
    // preprocessing. Tolerate the zero-arena edge case by requiring
    // strict movement only when the solver has clauses in flight.
    let any_moved = noop_after > noop_before
        || conflict_after > conflict_before
        || mismatch_after > mismatch_before;
    // `any_moved` can only legitimately be false when the filter had
    // nothing to scan. The verdict in that case is always `NoopLikely`
    // (its initial value).
    if !any_moved {
        assert_eq!(
            verdict,
            ApproxBcpPrefilterVerdict::NoopLikely,
            "filter moved no counters but returned non-default verdict",
        );
    }

    // Global soundness invariant: the mismatch counter is cumulative
    // across the solver's lifetime and must remain zero.
    assert_eq!(
        mismatch_after, 0,
        "filter reported a cumulative soundness mismatch (verdict = {verdict:?})",
    );
}

#[test]
fn filter_never_mismatches_on_trivially_unsat_instance() {
    // Two unit clauses that contradict: (x0) ∧ (¬x0). The solver will
    // detect UNSAT immediately. After the solve, the trail + arena may
    // or may not still contain the clauses (preprocessing may have
    // removed them). Either way, the filter must not mismatch.
    let mut s = fresh_solver(1);
    let v0 = Variable::new(0);
    s.add_clause(vec![Literal::positive(v0)]);
    s.add_clause(vec![Literal::negative(v0)]);

    let _result = s.solve();

    let _verdict = s.run_approx_bcp_prefilter();

    assert_eq!(
        s.approx_bcp_mismatch_detected(),
        0,
        "filter reported a soundness mismatch on trivially UNSAT instance",
    );
}
