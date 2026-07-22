// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression test for #7930: DT+BV simple loop problems must not enter the
//! BV dual-lane in the adaptive solver.
//!
//! The BV dual-lane (BvToBool/BvToInt) does not handle DT constructor/selector
//! operations, causing combinatorial blowup and timeout on problems like
//! Option<BV8> equality. This test ensures the adaptive solver routes DT+BV
//! problems through the DT-safe portfolio with escalation caps and no Kind.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const DT_BV_OPTION_EQ: &str = include_str!("../../../../benchmarks/smt/chc_dt_bv_option_eq.smt2");

/// DT+BV simple loop: Option<BV8> equality must solve within budget.
///
/// Before the #7930 fix, this entered the BV dual-lane and timed out.
/// With the DT-safe portfolio guard, it solves via PDR in seconds.
#[test]
#[timeout(60_000)]
fn adaptive_dt_bv_option_eq_safe_7930() {
    let problem =
        ChcParser::parse(DT_BV_OPTION_EQ).expect("chc_dt_bv_option_eq benchmark should parse");
    problem
        .validate()
        .expect("chc_dt_bv_option_eq benchmark should validate");

    // Verify the problem has both DT and BV sorts (the condition that triggers
    // the DT+BV guard).
    assert!(
        problem.has_datatype_sorts(),
        "Test problem must have datatype sorts"
    );
    assert!(problem.has_bv_sorts(), "Test problem must have BV sorts");

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(45)
    } else {
        Duration::from_secs(15)
    };

    let solver = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    let result = solver.solve();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "#7930: chc_dt_bv_option_eq.smt2 is safe. DT+BV simple loops must \
         bypass the BV dual-lane and use the DT-safe portfolio. \
         AdaptivePortfolio returned {result:?}."
    );
}
