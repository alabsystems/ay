// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic, clippy::unwrap_used)]

//! Workstream B §7.5 lock (the development design notes at `9598c4206`, WP-S
//! 2026-09-23): a predicate the lane proves unreachable carries the lemma
//! `false`, and the fixed point it takes part in must reach `Safe` with that
//! predicate interpreted as `false`.
//!
//! Root cause this pins (HOLA-44: 99/99 lane lemmas `false`, 47 model
//! demotions, no verdict): the lane's `false` lemmas are proven (Phase 0 on
//! the empty seed observes UNSAT of every defining clause), but the fixed-point
//! model was rebuilt by the legacy entry-inductive path from the LOCAL
//! `frames[i]`, which Houdini-pruned the `false`, and the #3121 filter dropped
//! `false` from the frame hypothesis the model is read from. Either way the
//! unreachable predicate became `true` and the model failed its query clause.
//! Under the lane the candidate is now the full delta frame with `false` kept
//! (`false_lemma_in_model` is part of rung 1); `verify_model` still decides.

use ay_chc::testing::pdr_solve_with_stats;
use ay_chc::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PdrConfig, PdrResult,
    PredicateId, SpacerLane,
};
use ntest::timeout;
use std::time::Duration;

/// `x = 0 → P(x)`; `P(x) ∧ x' = x → P(x')`; `P(x) ∧ x = 5 → Q(x)`;
/// `Q(x) → false`. Q is unreachable (P stays at 0): its invariant is `false`
/// and the query's bad state for Q is `true` — the HOLA-44 shape.
fn unreachable_second_predicate() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let v = |n: &str| ChcExpr::var(ChcVar::new(n, ChcSort::Int));
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(v("x"), ChcExpr::Int(0)))),
        ClauseHead::Predicate(p, vec![v("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![v("x")])], Some(ChcExpr::eq(v("x1"), v("x")))),
        ClauseHead::Predicate(p, vec![v("x1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")])],
            Some(ChcExpr::eq(v("x"), ChcExpr::Int(5))),
        ),
        ClauseHead::Predicate(q, vec![v("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![v("x")])], None),
        ClauseHead::False,
    ));
    (problem, q)
}

fn with_timeout(mut config: PdrConfig) -> PdrConfig {
    config.solve_timeout = Some(Duration::from_secs(20));
    config
}

fn assert_safe_with_false_q(config: PdrConfig, what: &str) {
    let (problem, q) = unreachable_second_predicate();
    let (result, stats) = pdr_solve_with_stats(&problem, config);
    let lemma_false = stats.counters["lemma_false"].as_u64().unwrap_or(0);
    match result {
        PdrResult::Safe(model) => {
            let interp = model.get(&q).expect("Q interpreted");
            assert!(
                matches!(interp.formula, ChcExpr::Bool(false)),
                "{what}: the unreachable predicate must be interpreted as false, got {}",
                interp.formula
            );
        }
        other => panic!(
            "{what}: expected Safe, got {other:?} (lemma_false={lemma_false}, model failures={})",
            stats.model_verification_failures
        ),
    }
    assert!(
        lemma_false >= 1,
        "{what}: the lane must learn `false` for Q"
    );
    assert_eq!(
        stats.model_verification_failures, 0,
        "{what}: no fixed-point model may be demoted for dropping the `false` lemma"
    );
}

#[test]
#[timeout(60_000)]
fn unreachable_predicate_false_lemma_reaches_safe_with_startup() {
    assert_safe_with_false_q(
        with_timeout(PdrConfig::production(false)).with_spacer(SpacerLane::rung(1)),
        "rung 1, production (startup discovery on)",
    );
}

#[test]
#[timeout(60_000)]
fn unreachable_predicate_false_lemma_reaches_safe_without_startup() {
    // `portfolio_spacer_variant` skips startup discovery: the lane has to learn
    // P's `x ≠ 5` itself before Q's `false` becomes a fixed point.
    assert_safe_with_false_q(
        with_timeout(PdrConfig::portfolio_spacer_variant()).with_spacer(SpacerLane::rung(1)),
        "rung 1, startup discovery skipped",
    );
}
