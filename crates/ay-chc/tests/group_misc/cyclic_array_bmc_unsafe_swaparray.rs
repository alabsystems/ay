// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression test for the cyclic-array Unsafe BMC lane (Fix C)
//! plus the transform-tolerant counterexample replay (FM2b).
//!
//! heap__swaparray_000 (llreve-bench/muz, official CHC-COMP 2026 verdict:
//! false = UNSAFE) is a 2-predicate cyclic array CHC with `div` in the query
//! constraint. Historically every engine (PDR/IMC/TPA/BMC) found Unsafe and
//! validation rejected every counterexample, yielding `unknown`:
//!
//! 1. The multi-pred lineup had no counterexample-finder for cyclic array
//!    problems (BMC was acyclic-gated).
//! 2. ClauseInliner witnesses carried engine-space predicate ids, canonical
//!    names, and clause indices that the original-clause replay could not
//!    align (`could not apply entry state to clause head` → Spurious).
//! 3. The executor backend produces false UNSATs on ground
//!    const-array/store disequalities, killing the query-violation replay.
//!
//! With Fix C (BMC lane + witness back-translation + content-based clause
//! re-resolution + ground witness evaluation override) the instance solved
//! as UNSAFE in ~1s through the portfolio's BMC lane. Since 75e0906e1 the
//! array ghost-pair route, which runs before the portfolio is built, finds an
//! init-violation counterexample here; it carries no witness, so it is
//! accepted only once `BmcSolver::replay_confirm_unsafe_on_problem` confirms
//! it on the original clauses, and the verdict then lands before the
//! portfolio exists. So `test_heap_swaparray_cyclic_array_bmc_unsafe` pins
//! the end-to-end verdict (and with it that replay), while
//! `test_heap_swaparray_fix_c_bmc_engine_lands_validated_unsafe` pins the
//! Fix C BMC lane itself.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser};
use ntest::timeout;
use std::time::Duration;

const HEAP_SWAPARRAY: &str = include_str!("../fixtures/chc_comp/llreve/heap__swaparray_000.smt2");

/// heap__swaparray_000 must solve as UNSAFE (official verdict: false).
/// Never sat; unknown means a counterexample pipeline regressed: the
/// original-clause replay of a witness-free Unsafe (the depth-1 `END_QUERY`
/// witness must confirm well inside its 10s budget) or the Fix C lane.
#[test]
#[timeout(120000)]
fn test_heap_swaparray_cyclic_array_bmc_unsafe() {
    let problem = ChcParser::parse(HEAP_SWAPARRAY).expect("parse heap__swaparray_000");
    problem.validate().expect("validate heap__swaparray_000");

    // Full engine lineup: `test_default` caps max_engines at 3, which cuts
    // the Unsafe-only BMC lane this test exercises.
    let mut config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(30));
    config.max_engines = None;
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    assert!(
        !result.is_safe(),
        "heap__swaparray_000 is UNSAFE (official verdict false); sat is a soundness bug. Got: {result:?}",
    );
    assert!(
        result.is_unsafe(),
        "heap__swaparray_000 should solve as UNSAFE (a pre-portfolio route's \
         counterexample confirmed by the original-clause BMC replay, or the \
         cyclic-array BMC lane). Got: {result:?}",
    );
}

/// Fix C lane pin (8cd8c6474), independent of the adaptive pre-routes that
/// now land this instance before the portfolio is built: the exact
/// Unsafe-only BMC lane Fix C adds to the multi-pred lineup (max_depth 30,
/// `acyclic_safe` false, k-induction and adaptive stepping off; the lineup
/// entry itself is pinned by
/// `adaptive::tests::engine_selection::multi_pred_lineup_keeps_fix_c_unsafe_only_bmc_for_cyclic_arrays`),
/// run through the portfolio with preprocessing ON: its counterexample is
/// back-translated through the ClauseInliner and must pass the portfolio's
/// counterexample verification against the original clauses, the stage
/// whose Unknown was this instance's historical failure.
#[test]
#[timeout(120000)]
fn test_heap_swaparray_fix_c_bmc_engine_lands_validated_unsafe() {
    use ay_chc::{testing, BmcConfig, EngineConfig, PortfolioConfig, PortfolioResult};
    let problem = ChcParser::parse(HEAP_SWAPARRAY).expect("parse heap__swaparray_000");
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Bmc(
        BmcConfig::with_engine_config(30, false, None),
    )])
    .parallel(false)
    .timeout(Some(Duration::from_secs(30)));
    let result = testing::new_portfolio_solver(problem, config).solve();
    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "the Fix C cyclic-array BMC lane must land a validated UNSAFE. Got: {result:?}"
    );
}
