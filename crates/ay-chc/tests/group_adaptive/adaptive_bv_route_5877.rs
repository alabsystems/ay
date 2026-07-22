// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! End-to-end adaptive routing tests for BV CHC problems (#5877).
//!
//! This test pins the current user-visible adaptive behavior on the
//! canonical `nested4` regression benchmark.
//!
//! The internal lane choice has changed multiple times during #5877.
//! What matters for consumers is the adaptive entrypoint result, not which
//! internal lane won.
//!
//! Current behavior (W1:3285, 2026-03-17):
//! - nested4 returns Unknown within the 25s budget through the triple-lane path
//! - The direct BV-native route was tested (W1:3285) and also returns Unknown
//! - Z3 returns sat (the problem IS safe)
//! - BV-native PDR cannot find the right invariant in the BV domain
//! - BvToBool/BvToInt lanes are the best current approach but still time out on nested4
//!
//! When this test starts passing as Safe, that's the resolution of #5877.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

/// The nested4 benchmark from CHC-COMP (BV simple-loop, 5 BV32 + 3 Bool params).
/// Canonical #5877 regression case. z3 returns sat within 30s.
///
/// Embedded here (matching bv_clause_splitting_5877.rs) so the test is
/// self-contained and does not depend on benchmark file paths.
const NESTED4_BENCHMARK: &str = "(set-logic HORN)\n\n\n(declare-fun |state| ( Bool Bool Bool (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) (_ BitVec 32) ) Bool)\n\n(assert\n  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F Bool) (G Bool) (H Bool) ) \n    (=>\n      (and\n        (and (not G) (not F) (not H))\n      )\n      (state H G F B A D C E)\n    )\n  )\n)\n(assert\n  (forall ( (A Bool) (B Bool) (C Bool) (D (_ BitVec 32)) (E (_ BitVec 32)) (F (_ BitVec 32)) (G (_ BitVec 32)) (H (_ BitVec 32)) (I (_ BitVec 32)) (J (_ BitVec 32)) (K (_ BitVec 32)) (L (_ BitVec 32)) (M (_ BitVec 32)) (N (_ BitVec 32)) (O (_ BitVec 32)) (P Bool) (Q Bool) (R Bool) ) \n    (=>\n      (and\n        (state R Q P G E J H L)\n        (or (and (not C)\n         (not B)\n         A\n         (not P)\n         (not Q)\n         (not R)\n         (= M N)\n         (= K O)\n         (= E D)\n         (= I #x00000001)\n         (= G F)\n         (not (bvsle M #x00000000)))\n    (and (not C)\n         B\n         A\n         (not P)\n         (not Q)\n         R\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D L)\n         (not (bvsle J H)))\n    (and C\n         (not B)\n         (not A)\n         (not P)\n         Q\n         R\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D L)\n         (bvsle J E))\n    (and (not C)\n         B\n         A\n         (not P)\n         Q\n         R\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D (bvadd #x00000001 E))\n         (not (bvsle J E)))\n    (and (not C)\n         (not B)\n         A\n         P\n         (not Q)\n         (not R)\n         (= M L)\n         (= K J)\n         (= E D)\n         (= I (bvadd #x00000001 H))\n         (= G F)\n         (bvsle J E))\n    (and C\n         (not B)\n         A\n         P\n         (not Q)\n         (not R)\n         (= M L)\n         (= K J)\n         (= E D)\n         (= I H)\n         (= G F)\n         (not (bvsle J E))\n         (not (bvsle #x00000001 E)))\n    (and C\n         (not B)\n         (not A)\n         P\n         (not Q)\n         (not R)\n         (= M L)\n         (= K J)\n         (= I H)\n         (= G F)\n         (= D (bvadd #x00000001 E))\n         (not (bvsle J E))\n         (bvsle #x00000001 E))\n    (and C B (not A) P (not Q) R (= M L) (= K J) (= E D) (= I H) (= G F))\n    (and C B (not A) P Q (not R)))\n      )\n      (state A B C F D K I M)\n    )\n  )\n)\n(assert\n  (forall ( (A (_ BitVec 32)) (B (_ BitVec 32)) (C (_ BitVec 32)) (D (_ BitVec 32)) (E (_ BitVec 32)) (F Bool) (G Bool) (H Bool) ) \n    (=>\n      (and\n        (state H G F B A D C E)\n        (and (= G true) (= F true) (not H))\n      )\n      false\n    )\n  )\n)\n\n(check-sat)\n(exit)\n";

/// End-to-end test: nested4 through the adaptive entrypoint.
///
/// This is the truthful regression gate for #5877. nested4 currently returns
/// Unknown because BV-native PDR cannot find the invariant in the BV domain,
/// and the BvToBool/BvToInt transformed lanes also time out on this benchmark.
///
/// Z3 solves this as sat (safe). When AY's BV-native PDR internals are improved
/// (lemma generalization, interpolation quality), this test should start
/// returning Safe. At that point, update the assertion to assert Safe.
///
/// W1:3285 tested the direct BV-native route (bypassing KIND + transformed
/// lanes) — nested4 still returned Unknown after 25s. The bottleneck is
/// BV-native PDR lemma quality, not dispatch routing.
#[test]
#[timeout(35_000)]
fn test_nested4_adaptive_current_behavior() {
    let problem = ChcParser::parse(NESTED4_BENCHMARK).expect("nested4 should parse");

    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(25));
    let solver = AdaptivePortfolio::new(problem, config);
    let result = solver.solve();

    match &result {
        VerifiedChcResult::Safe(_) => {
            // If we reach here, #5877 may be resolved. Celebrate, then update
            // this test to assert Safe permanently.
        }
        VerifiedChcResult::Unknown(_) => {
            // Current expected behavior: nested4 times out within the 25s budget.
            // This is the documented gap tracked by #5877.
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!("nested4 is safe (Z3 returns sat). Unsafe is a soundness bug.");
        }
        _ => {
            panic!("Unexpected VerifiedChcResult variant");
        }
    }
}
