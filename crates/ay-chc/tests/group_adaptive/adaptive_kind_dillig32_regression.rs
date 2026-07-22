// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::panic)]

use ay_chc::{testing, AdaptiveConfig, AdaptivePortfolio, ChcParser, PdrConfig, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

const DILLIG32_BENCHMARK: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig32_000.smt2");

/// Regression guard for #7598 / #5970, soundness-hardened.
///
/// `dillig32` is a safe pure-LIA loop (alternating-counter family: one of two
/// counters increments per step, selected by a 0/1 toggle; the query needs
/// counter equality when the step counter reaches `2 * bound`).
///
/// History: this test originally asserted `Safe`. That assertion was
/// satisfied by the algebraic-synthesis route, whose candidate invariant does
/// NOT discharge the query clause (the SMT validator finds a concrete
/// counterexample assignment, e.g. `{E:1, B:200, C:100, D:0}`). The candidate
/// was accepted only because `validation_interval_compare_result` treated two
/// unbounded intervals (`lower == upper == None`) as a matching singleton, so
/// `d != e` conjuncts were "evaluated" as definitely-false and whole clauses
/// were discharged unsoundly. With that soundness bug fixed, the invalid
/// model is rejected and no current engine proves the required
/// toggle-parity invariant (`counter_diff = flag - initial_flag` plus
/// `flag + steps` parity) within budget.
///
/// Until an engine covers that invariant family soundly, `Unknown` is the
/// correct, sound outcome. What this guard must catch:
/// - `Unsafe` on a safe system: soundness bug, always a failure.
/// - `Safe` whose model fails independent PDR re-verification: the original
///   unsound acceptance resurfacing, always a failure.
/// - Verified `Safe`: capability regained — the assertion below can be
///   tightened back to `matches!(result, VerifiedChcResult::Safe(_))`.
#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_adaptive_kind_accepts_dillig32_k_inductive_safe() {
    let problem = ChcParser::parse(DILLIG32_BENCHMARK)
        .unwrap_or_else(|err| panic!("dillig32 benchmark should parse: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("dillig32 benchmark should validate: {err}"));

    let budget = if cfg!(debug_assertions) {
        Duration::from_secs(90)
    } else {
        Duration::from_secs(40)
    };

    let solver = AdaptivePortfolio::new(
        problem.clone(),
        AdaptiveConfig::test_default().with_time_budget(budget),
    );
    let result = solver.solve();

    match result {
        VerifiedChcResult::Safe(inv) => {
            // Capability path: Safe is the true answer, but the certificate
            // must survive independent re-verification (#7598 history above).
            let mut verifier = testing::new_pdr_solver(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(inv.model()),
                "dillig32: Safe certificate failed independent model \
                 re-verification — unsound acceptance resurfaced"
            );
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!(
                "SOUNDNESS BUG: dillig32_000.smt2 is safe, but AdaptivePortfolio returned Unsafe"
            )
        }
        other => {
            // Sound capability gap: no engine currently proves the
            // toggle-parity invariant family within budget.
            eprintln!(
                "dillig32: sound capability gap, AdaptivePortfolio returned {other:?} \
                 (Safe requires the toggle-parity invariant family)"
            );
        }
    }
}
