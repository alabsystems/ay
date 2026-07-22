// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #7626: gj2007_m_3 times out because PDR startup
//! discovers the query-blocking invariant but then runs expensive
//! post-fixpoint bound passes before checking safety.
//!
//! The fix adds a safety gate after fixpoint convergence and before
//! `discover_bound_invariants_post_fixpoint()`.

#[cfg(not(debug_assertions))]
const GJ2007_M_3: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/gj2007_m_3_000.smt2");

/// gj2007_m_3 should return SAT within the default budget. Before #7626,
/// it timed out because the fixpoint loop found the invariant but then
/// spent the remaining budget in post-fixpoint bound discovery passes.
#[test]
#[cfg(not(debug_assertions))]
fn test_gj2007_m_3_solves_within_budget() {
    let problem = ay_chc::ChcParser::parse(GJ2007_M_3).expect("parse");
    problem.validate().expect("validate");

    let config = ay_chc::AdaptiveConfig::test_default();
    let solver = ay_chc::AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    assert!(
        result.is_safe(),
        "gj2007_m_3 should be SAT (safe), got: {result:?}",
    );
}
