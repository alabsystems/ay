// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic, clippy::unwrap_used)]

//! Workstream B lock L-C at the solve level (`DESIGN_spacer_pob_lemma_pipeline.md`
//! §4.1.5 / §6 S11, contract C6): the 3-step unsafe transition system whose
//! MBP leaves a variable free (`x' = x + 1 ∧ y' = y`, init `x = 0`, query
//! `x ≥ 3`) is refuted with a `Valid` counterexample under the lane, the
//! forward re-concretisation walk runs once per Unsafe and never fails, and
//! the delivered trace is aligned step to step (`y` constant, `x` counting
//! up). The in-crate half of the lock (`model/cex_concretize_tests.rs`)
//! drives hand-built free-variable chains through `concretize_cex_chain`
//! directly; this half proves the wiring (S's call before `build_cex`) on a
//! real solve with the lane on and off.

use ay_chc::testing::{pdr_solve_with_stats, PdrTestStats};
use ay_chc::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PdrConfig, PdrResult,
    SpacerLane,
};
use ntest::timeout;
use std::time::Duration;

fn cfg() -> PdrConfig {
    let mut c = PdrConfig::production(false);
    c.solve_timeout = Some(Duration::from_secs(20));
    c
}

fn v(n: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(n, ChcSort::Int))
}

/// `x = 0 → P(x, y)` (y free); `P(x, y) ∧ x1 = x + 1 ∧ y1 = y → P(x1, y1)`;
/// `P(x, y) ∧ x ≥ 3 → false`. Unsafe at depth 3.
fn free_y_unsafe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(v("x"), ChcExpr::Int(0)))),
        ClauseHead::Predicate(p, vec![v("x"), v("y")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x"), v("y")])],
            Some(ChcExpr::and(
                ChcExpr::eq(v("x1"), ChcExpr::add(v("x"), ChcExpr::Int(1))),
                ChcExpr::eq(v("y1"), v("y")),
            )),
        ),
        ClauseHead::Predicate(p, vec![v("x1"), v("y1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x"), v("y")])],
            Some(ChcExpr::ge(v("x"), ChcExpr::Int(3))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// `x = 0 ∧ y = 0 → P(x, y)`; `P(x, y) ∧ x' = x + 1 ∧ y' = y + 2 → P(x', y')`;
/// `P(x, y) ∧ y ≥ 5 → false` (unsafe at depth 3; every cube is a point).
fn two_var_unsafe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
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

fn concretize_counter(s: &PdrTestStats, key: &str) -> u64 {
    s.counters["cex_concretize"][key]
        .as_u64()
        .unwrap_or_else(|| panic!("cex_concretize.{key} counter present"))
}

/// The delivered trace must be one forward run of the system: `x` counts
/// 0, 1, 2, 3 and `y` is the same value on every step (the re-concretised
/// models, not four independent Q1 models).
fn assert_aligned_free_y_trace(result: &PdrResult) {
    let PdrResult::Unsafe(cex) = result else {
        panic!("expected Unsafe, got {result:?}");
    };
    assert_eq!(cex.steps.len(), 4, "depth-3 refutation has four states");
    // Every step's assignments are in its clause's own variable names: the
    // fact step binds `x`/`y`, a transition step binds `x`,`y`,`x1`,`y1`; the
    // head of a step is `x1` when present, else `x`.
    let mut head_xs: Vec<i64> = Vec::new();
    let mut ys: Vec<i64> = Vec::new();
    for (i, step) in cex.steps.iter().enumerate() {
        let head_x = step
            .assignments
            .get("x1")
            .or_else(|| step.assignments.get("x"))
            .copied()
            .unwrap_or_else(|| panic!("step {i} binds its head x"));
        head_xs.push(head_x);
        for key in ["y", "y1"] {
            if let Some(y) = step.assignments.get(key) {
                ys.push(*y);
            }
        }
    }
    let mut sorted = head_xs.clone();
    sorted.sort_unstable();
    assert_eq!(
        sorted,
        vec![0, 1, 2, 3],
        "one forward run of the counter: {head_xs:?}"
    );
    let monotone =
        head_xs.windows(2).all(|w| w[0] < w[1]) || head_xs.windows(2).all(|w| w[0] > w[1]);
    assert!(monotone, "steps are in chain order: {head_xs:?}");
    assert!(!ys.is_empty());
    assert!(
        ys.iter().all(|y| *y == ys[0]),
        "y must be carried unchanged along the trace, got {ys:?}"
    );
}

#[test]
#[timeout(60_000)]
fn lane_off_refutes_the_free_variable_system_with_the_walk() {
    // The walk runs on every level-0 hit, lane on or off (legacy child cubes
    // are not always points either; `model/cex_wiring_tests.rs`).
    let (r, s) = pdr_solve_with_stats(&free_y_unsafe(), cfg().with_spacer(SpacerLane::OFF));
    assert!(matches!(r, PdrResult::Unsafe(_)), "baseline verdict: {r:?}");
    assert_eq!(
        concretize_counter(&s, "ok"),
        1,
        "one walk per Unsafe: {}",
        s.counters
    );
    assert_eq!(concretize_counter(&s, "fail_unsat"), 0);
    assert_eq!(concretize_counter(&s, "fail_unknown"), 0);
}

#[test]
#[timeout(60_000)]
fn lane_on_reconcretises_once_and_delivers_a_valid_aligned_trace() {
    let (r, s) = pdr_solve_with_stats(&free_y_unsafe(), cfg().with_spacer(SpacerLane::rung(1)));
    assert!(matches!(r, PdrResult::Unsafe(_)), "lane verdict: {r:?}");
    assert_eq!(
        concretize_counter(&s, "ok"),
        1,
        "one walk per Unsafe: {}",
        s.counters
    );
    assert_eq!(
        concretize_counter(&s, "fail_unsat"),
        0,
        "INV-P detector silent"
    );
    assert_eq!(concretize_counter(&s, "fail_unknown"), 0);
    assert_eq!(concretize_counter(&s, "hyperedge"), 0, "linear problem");
    assert_aligned_free_y_trace(&r);
}

#[test]
#[timeout(60_000)]
fn lane_on_pinned_cubes_keep_the_walk_a_no_op() {
    // Point cubes (R1 constructor): the walk keeps every recorded model and
    // issues no solve of its own, and the verdict is unchanged.
    let (off, _) = pdr_solve_with_stats(&two_var_unsafe(), cfg().with_spacer(SpacerLane::OFF));
    let (on, s) = pdr_solve_with_stats(&two_var_unsafe(), cfg().with_spacer(SpacerLane::rung(1)));
    assert!(matches!(off, PdrResult::Unsafe(_)));
    assert!(matches!(on, PdrResult::Unsafe(_)), "lane verdict: {on:?}");
    assert_eq!(concretize_counter(&s, "ok"), 1);
    assert_eq!(
        concretize_counter(&s, "fail_unsat") + concretize_counter(&s, "fail_unknown"),
        0
    );
    let (PdrResult::Unsafe(a), PdrResult::Unsafe(b)) = (&off, &on) else {
        unreachable!()
    };
    assert_eq!(a.steps.len(), b.steps.len(), "same depth");
}

// ------------------------------------------------------------------ rung 2 (R2)

/// `x = 0 → P(x)`; `P(x) ∧ x' = x + 1 → P(x')`; `P(x) ∧ x < 0 → false` (safe).
fn safe_counter() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(v("x"), ChcExpr::Int(0)))),
        ClauseHead::Predicate(p, vec![v("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")])],
            Some(ChcExpr::eq(v("x1"), ChcExpr::add(v("x"), ChcExpr::Int(1)))),
        ),
        ClauseHead::Predicate(p, vec![v("x1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")])],
            Some(ChcExpr::lt(v("x"), ChcExpr::Int(0))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn counter(s: &PdrTestStats, key: &str) -> u64 {
    s.counters[key].as_u64().unwrap_or(0)
}

fn cube_source(s: &PdrTestStats, key: &str) -> u64 {
    s.counters["cube_source"][key].as_u64().unwrap_or(0)
}

#[test]
#[timeout(60_000)]
fn rung2_free_cubes_reconcretise_and_replay_valid() {
    // The lock L-C end to end with the R2 constructor: the child POBs leave `y`
    // free (the chain the alignment check would mark Spurious), the walk
    // re-concretises it once, and the counterexample replays Valid (the solve
    // returns Unsafe only after `verify_counterexample`).
    let (r, s) = pdr_solve_with_stats(&free_y_unsafe(), cfg().with_spacer(SpacerLane::rung(2)));
    assert!(matches!(r, PdrResult::Unsafe(_)), "rung-2 verdict: {r:?}");
    assert_eq!(concretize_counter(&s, "ok"), 1, "{}", s.counters);
    assert_eq!(
        concretize_counter(&s, "fail_unsat"),
        0,
        "INV-P detector silent"
    );
    assert_eq!(concretize_counter(&s, "fail_unknown"), 0);
    assert!(
        cube_source(&s, "MbpFree") > 0,
        "free constructor used: {}",
        s.counters
    );
    assert_eq!(
        cube_source(&s, "Legacy"),
        0,
        "no legacy child at rung 2: {}",
        s.counters
    );
    assert_eq!(
        counter(&s, "minimize_calls"),
        0,
        "no model minimisation under free_pob"
    );
    assert!(
        s.point_cube_share < 1.0,
        "free POBs are not all point cubes (share {})",
        s.point_cube_share
    );
    assert_aligned_free_y_trace(&r);
}

#[test]
#[timeout(60_000)]
fn rung2_verdicts_match_rung0_on_the_lock_fixtures() {
    for (name, problem, expect_unsafe) in [
        ("safe counter", safe_counter(), false),
        ("two-var unsafe", two_var_unsafe(), true),
        ("free-y unsafe", free_y_unsafe(), true),
    ] {
        let (off, _) = pdr_solve_with_stats(&problem, cfg().with_spacer(SpacerLane::OFF));
        let (on, s) = pdr_solve_with_stats(&problem, cfg().with_spacer(SpacerLane::rung(2)));
        let is_unsafe = |r: &PdrResult| matches!(r, PdrResult::Unsafe(_));
        let is_safe = |r: &PdrResult| matches!(r, PdrResult::Safe(_));
        assert_eq!(is_unsafe(&off), expect_unsafe, "{name}: rung 0 {off:?}");
        if expect_unsafe {
            assert!(is_unsafe(&on), "{name}: rung 2 {on:?}");
            assert_eq!(
                concretize_counter(&s, "fail_unsat"),
                0,
                "{name}: {}",
                s.counters
            );
        } else {
            assert!(
                is_safe(&off) && is_safe(&on),
                "{name}: rung 0 {off:?}, rung 2 {on:?}"
            );
        }
    }
}
