// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A fact whose head argument is a term over a fact-local variable must not
//! give PDR a must summary that drops that argument.
//!
//! `y = 0 => B(true, (mod y 3))` has no summary in B's canonical frame
//! (`y` binds no head position). `rewrite_fact_summary` used to drop the
//! position, summarizing the fact as "every `B(true, _)` is reachable"; PDR
//! then found a one-step counterexample to `B(k, m) /\ m > 6 => false`, its
//! root-state satisfiability check accepted it, and AY answered `unsat` on this
//! safe system (z3 5.1: `sat`) at default and `--competition`. The unused
//! predicate `U` only steers the portfolio to multi-predicate PDR. Found by the
//! 2026-09-29 CHC differential generator (`gen/chc`, job `loops_1`, file 1).

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

/// B = {(false, 4), (true, 4), (true, 0), (false, 6)}: no `m > 6`.
const SAFE: &str = "(set-logic HORN)
(declare-fun U (Int) Bool)
(declare-fun B (Bool Int) Bool)
(assert (forall ((i Bool)) (B i 4)))
(assert (forall ((y Int)) (=> (and (>= y 0) (<= y 0)) (B true (mod y 3)))))
(assert (forall ((y Bool) (z Int)) (=> (and (B y z) (not y)) (B y 6))))
(assert (forall ((k Bool) (m Int)) (=> (and (B k m) (> m 6)) false)))
(check-sat)
";

#[test]
#[timeout(180_000)]
fn a_local_compound_fact_argument_does_not_make_a_safe_system_unsafe() {
    for strict_proofs in [false, true] {
        let problem = ChcParser::parse(SAFE).expect("parse");
        let mut config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
        config.strict_proofs = strict_proofs;
        let result = AdaptivePortfolio::new(problem, config).solve();
        assert!(
            !matches!(result, VerifiedChcResult::Unsafe(_)),
            "safe (z3: sat); strict_proofs = {strict_proofs}: {result:?}"
        );
    }
}

/// The same system with the fact's argument `m >= 7` reachable is unsafe and
/// stays decided Unsafe: skipping the summary costs no refutation here.
#[test]
#[timeout(180_000)]
fn the_unsafe_control_stays_unsafe() {
    let unsafe_input = SAFE.replace("(B true (mod y 3))", "(B true (+ (mod y 3) 7))");
    assert_ne!(unsafe_input, SAFE, "the control rewrite must apply");
    let problem = ChcParser::parse(&unsafe_input).expect("parse");
    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
    let result = AdaptivePortfolio::new(problem, config).solve();
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "unsafe (B(true, 7) reaches the query): {result:?}"
    );
}
