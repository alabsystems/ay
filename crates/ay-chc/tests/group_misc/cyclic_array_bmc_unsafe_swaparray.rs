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
//! re-resolution + ground witness evaluation override) the instance solves
//! as UNSAFE in ~1s.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser};
use ntest::timeout;
use std::time::Duration;

const HEAP_SWAPARRAY: &str = include_str!("../fixtures/chc_comp/llreve/heap__swaparray_000.smt2");

/// heap__swaparray_000 must solve as UNSAFE (official verdict: false).
/// Never sat; unknown means the Fix C counterexample pipeline regressed.
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
        "heap__swaparray_000 should solve as UNSAFE via the cyclic-array BMC lane \
         (depth-0 witness, transform-tolerant replay). Got: {result:?}",
    );
}
