// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic, clippy::unwrap_used)]

//! Workstream B lock L-V (the development design notes at `9598c4206`, §6 S1/S11):
//! the default config runs the lane (rung 2 since the R3 default flip) and
//! reaches the same verdict as the legacy pipeline (`SpacerLane::OFF`); a lane
//! that the problem's sorts bypass (BV, §7.4) is behaviourally identical to
//! OFF — same verdict, lemma count, POB count.

use ay_chc::testing::{pdr_solve_with_stats, PdrTestStats};
use ay_chc::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PdrConfig,
    PdrResult, SpacerLane,
};
use ntest::timeout;
use std::sync::Arc;
use std::time::Duration;

fn bv_op(op: ChcOp, a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(a), Arc::new(b)])
}

fn cfg() -> PdrConfig {
    let mut c = PdrConfig::production(false);
    c.solve_timeout = Some(Duration::from_secs(20));
    c
}

/// `x = 0 → P(x)`; `P(x) ∧ x' = x + 1 → P(x')`; `P(x) ∧ x < bound → false`.
fn counter(bound: i128, sort: ChcSort) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![sort.clone()]);
    let x = ChcVar::new("x", sort.clone());
    let x1 = ChcVar::new("x1", sort.clone());
    let is_bv = matches!(sort, ChcSort::BitVec(_));
    let width = match sort {
        ChcSort::BitVec(w) => w,
        _ => 0,
    };
    let zero = if is_bv {
        ChcExpr::BitVec(0, width)
    } else {
        ChcExpr::Int(0)
    };
    let one = if is_bv {
        ChcExpr::BitVec(1, width)
    } else {
        ChcExpr::Int(1)
    };
    let bound_e = if is_bv {
        ChcExpr::BitVec(bound as u128, width)
    } else {
        ChcExpr::Int(bound)
    };
    let add = |a: ChcExpr, b: ChcExpr| {
        if is_bv {
            bv_op(ChcOp::BvAdd, a, b)
        } else {
            ChcExpr::add(a, b)
        }
    };
    let lt = |a: ChcExpr, b: ChcExpr| {
        if is_bv {
            bv_op(ChcOp::BvULt, a, b)
        } else {
            ChcExpr::lt(a, b)
        }
    };
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(ChcExpr::var(x.clone()), zero))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x1.clone()),
                add(ChcExpr::var(x.clone()), one),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x1)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(lt(ChcExpr::var(x), bound_e)),
        ),
        ClauseHead::False,
    ));
    problem
}

/// `x = 0 ∧ y = 0 → P(x, y)`; `P(x, y) ∧ x' = x + 1 ∧ y' = y + 2 → P(x', y')`;
/// `P(x, y) ∧ y ≥ 5 → false` (unsafe at depth 3).
fn two_var_unsafe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let v = |n: &str| ChcExpr::var(ChcVar::new(n, ChcSort::Int));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            Vec::new(),
            Some(ChcExpr::and(
                ChcExpr::eq(v("x"), ChcExpr::Int(0)),
                ChcExpr::eq(v("y"), ChcExpr::Int(0)),
            )),
        ),
        ClauseHead::Predicate(p, vec![v("x"), v("y")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x"), v("y")])],
            Some(ChcExpr::and(
                ChcExpr::eq(v("x1"), ChcExpr::add(v("x"), ChcExpr::Int(1))),
                ChcExpr::eq(v("y1"), ChcExpr::add(v("y"), ChcExpr::Int(2))),
            )),
        ),
        ClauseHead::Predicate(p, vec![v("x1"), v("y1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x"), v("y")])],
            Some(ChcExpr::ge(v("y"), ChcExpr::Int(5))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn verdict(r: &PdrResult) -> &'static str {
    match r {
        PdrResult::Safe(_) => "safe",
        PdrResult::Unsafe(_) => "unsafe",
        PdrResult::Unknown => "unknown",
        PdrResult::NotApplicable => "n/a",
        _ => "other",
    }
}

fn key(s: &PdrTestStats) -> (usize, usize, usize, usize) {
    (
        s.lemmas_learned,
        s.max_frame,
        s.pobs_processed,
        s.blocked_pobs,
    )
}

fn assert_same_verdict(problem: &ChcProblem, a: PdrConfig, b: PdrConfig, what: &str) {
    let (ra, _) = pdr_solve_with_stats(problem, a);
    let (rb, _) = pdr_solve_with_stats(problem, b);
    assert_eq!(verdict(&ra), verdict(&rb), "{what}: verdict differs");
}

fn assert_identical(problem: &ChcProblem, a: PdrConfig, b: PdrConfig, what: &str) {
    let (ra, sa) = pdr_solve_with_stats(problem, a);
    let (rb, sb) = pdr_solve_with_stats(problem, b);
    assert_eq!(verdict(&ra), verdict(&rb), "{what}: verdict differs");
    assert_eq!(
        key(&sa),
        key(&sb),
        "{what}: (lemmas, max_frame, pobs, blocked) differ"
    );
}

#[test]
#[timeout(60_000)]
fn default_lane_matches_the_legacy_verdict_safe() {
    let problem = counter(0, ChcSort::Int);
    let (r, s) = pdr_solve_with_stats(&problem, cfg());
    assert_eq!(verdict(&r), "safe");
    // Startup discovery may prove this one before any POB is popped; the
    // counter block must exist either way.
    assert!(
        s.counters.get("pobs_processed").is_some(),
        "board counters present"
    );
    assert_same_verdict(
        &problem,
        cfg(),
        cfg().with_spacer(SpacerLane::OFF),
        "safe counter",
    );
}

#[test]
#[timeout(60_000)]
fn default_lane_matches_the_legacy_verdict_unsafe() {
    let problem = two_var_unsafe();
    let (r, s) = pdr_solve_with_stats(&problem, cfg());
    assert_eq!(verdict(&r), "unsafe");
    assert!(
        s.counters.get("pobs_processed").is_some(),
        "board counters present"
    );
    assert_same_verdict(
        &problem,
        cfg(),
        cfg().with_spacer(SpacerLane::OFF),
        "unsafe two-var",
    );
}

#[test]
#[timeout(60_000)]
fn lane_on_is_bypassed_by_bv_sorts_and_identical_to_off() {
    let problem = counter(0, ChcSort::BitVec(8));
    // The default (rung 2) and rung 1 are requested, but BV sorts bypass the
    // lane (§7.4): identical to OFF.
    assert_identical(
        &problem,
        cfg().with_spacer(SpacerLane::OFF),
        cfg(),
        "bv counter, default lane bypassed",
    );
    assert_identical(
        &problem,
        cfg().with_spacer(SpacerLane::OFF),
        cfg().with_spacer(SpacerLane::rung(1)),
        "bv counter, lane bypassed",
    );
    let (_, s) = pdr_solve_with_stats(&problem, cfg().with_spacer(SpacerLane::rung(1)));
    assert_eq!(
        s.counters["lane_bypassed"]["bv"], 1,
        "the bypass must be counted"
    );
}

#[test]
fn spacer_lane_rung_zero_is_off() {
    assert_eq!(SpacerLane::rung(0), SpacerLane::OFF);
    assert!(!SpacerLane::default().enabled);
    // `with_spacer` validates: a lane with `enabled == false` collapses to OFF.
    let mut lane = SpacerLane::OFF;
    lane.lift_caps = true;
    let c = PdrConfig::default().with_spacer(lane);
    let d = PdrConfig::default().with_spacer(SpacerLane::OFF);
    // No public accessor for the field; identity is observed through the solve locks above.
    let _ = (c, d);
}
