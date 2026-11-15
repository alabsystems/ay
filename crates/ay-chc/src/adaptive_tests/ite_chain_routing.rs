// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! MODEL_CHECKER_CONSUMER ask 2026-10-14-acyclic-8bit-ite-chain: the route, not only the
//! verdict.
//!
//! The parser inlines the chain's defining equality into `bb4`'s argument, so
//! the constraint-only `has_ite` misses it, and with 27 predicates and DAG
//! depth 25 the size half of the acyclic BV proof-lane gates stays closed.
//! The algebraic lane and the later exact-BvToInt probe also answer this
//! query, seconds later, so a verdict-and-budget test cannot tell the routes
//! apart: these tests pin that the pre-algebraic gate opens and that the
//! collapsed BV-native prepass decides.

use super::*;

const ITE_CHAIN: &str =
    include_str!("../../tests/fixtures/model_checker_consumer_acyclic_8bit_ite_chain.smt2");

fn ite_chain_portfolio(source: &str) -> AdaptivePortfolio {
    let problem = ChcParser::parse(source).expect("fixture parses");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(15)),
    );
    let features = adaptive.features();
    assert!(
        !features.has_ite && features.num_predicates < 32 && features.dag_depth < 32,
        "only the inlined ite can open the gate on this fixture"
    );
    assert!(
        should_prioritize_acyclic_bv_proof_prepass(&features, &adaptive.problem),
        "an ite the parser inlined into a head argument must open the pre-algebraic gate"
    );
    adaptive
}

fn assert_prepass_decided(
    trace: &crate::AdaptiveSolveTrace,
    outcome: crate::AdaptiveStrategyOutcome,
) {
    let observed = trace
        .observations()
        .iter()
        .find(|observation| observation.stage == "collapsed_bv_native_query_prepass")
        .expect("the collapsed BV-native prepass must run");
    assert!(observed.gate_result);
    assert_eq!(observed.outcome, outcome);
}

#[test]
#[timeout(90_000)]
fn inlined_ite_chain_takes_the_pre_algebraic_collapsed_prepass() {
    let adaptive = ite_chain_portfolio(ITE_CHAIN);
    let trace_session = adaptive.decision_log.begin_trace();
    let result = adaptive.solve();
    assert_prepass_decided(
        &trace_session.finish(),
        crate::AdaptiveStrategyOutcome::Safe,
    );
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "got {result:?}"
    );
}

/// Negative twin: `x = 12` mapped to 11 reaches `error_p17`, and the same
/// prepass answers with a validated counterexample.
#[test]
#[timeout(90_000)]
fn inlined_ite_chain_with_a_wrong_link_takes_the_same_prepass() {
    assert_eq!(ITE_CHAIN.matches("#x0d #x0c)").count(), 1);
    let adaptive = ite_chain_portfolio(&ITE_CHAIN.replace("#x0d #x0c)", "#x0d #x0b)"));
    let trace_session = adaptive.decision_log.begin_trace();
    let result = adaptive.solve();
    assert_prepass_decided(
        &trace_session.finish(),
        crate::AdaptiveStrategyOutcome::Unsafe,
    );
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "got {result:?}"
    );
}
