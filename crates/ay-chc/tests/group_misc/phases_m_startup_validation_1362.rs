// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Soundness guard for #1362: phases_m must never return Unsafe.
//
// PDR can discover a parity invariant for phases_m through conjunct
// decomposition, and the startup path accepts it via the free_vars_sanitized
// fallback. However, whether PDR discovers the invariant within budget is
// non-deterministic. Safe and Unknown are both acceptable; Unsafe would be
// a soundness bug (this benchmark is known-safe).

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;

/// Soundness guard: phases_m must not return Unsafe.
///
/// This benchmark has an explicit mod constraint in its transitions:
///   (= (mod __p0_a0 2) 0)
/// The system is known-safe. Returning Unsafe would indicate a soundness bug.
/// Returning Unknown is acceptable (non-deterministic invariant discovery).
/// Returning Safe confirms the startup model acceptance fallback (#1362) works.
#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(40_000))]
fn test_phases_m_never_unsafe_1362() {
    let input =
        include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/phases_m_000.smt2");
    let problem = ChcParser::parse(input).expect("parse phases_m benchmark");

    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let result = adaptive.solve();

    match &result {
        VerifiedChcResult::Safe(invariant) => {
            // Startup model acceptance worked — the parity invariant was found
            // and accepted via the free_vars_sanitized fallback path (#1362).
            assert!(
                !invariant.model().is_empty(),
                "BUG (#1362): phases_m returned Safe with an empty model"
            );
        }
        VerifiedChcResult::Unsafe(cex) => {
            panic!(
                "SOUNDNESS BUG (#1362): phases_m is SAT (safe), but solver returned Unsafe \
                 at steps={}. This benchmark has explicit mod constraints and is known-safe.",
                cex.counterexample().steps.len()
            );
        }
        VerifiedChcResult::Unknown(_) => {
            // Non-deterministic: PDR didn't find the invariant within budget.
            // This is acceptable — the parity discovery is timing-sensitive.
        }
        _ => {}
    }
}
