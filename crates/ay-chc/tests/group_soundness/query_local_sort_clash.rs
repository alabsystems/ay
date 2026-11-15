// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Two queries binding one variable name at two sorts must not make an unsafe
//! acyclic system Safe.
//!
//! BMC's acyclic probe compiles every query into one formula and keeps each
//! query's constraint-local variables under their source names, so `t: Bool`
//! in the first query and `t: Int` in the second became one mis-sorted
//! variable; the probe refuted the unsafe system and AY published `sat` with a
//! SAFE certificate at default and `--competition` (z3 5.1: `unsat`). Found by
//! the 2026-09-29 CHC differential generator (`gen/chc`, job `headonly_1`,
//! file 246, which plants the derivation `Q(5)`, `t = 5`).

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

/// `U(x)` for `x >= 2`, `Q = U`; the second query fires on `Q(5)` with `t = 5`.
const UNSAFE: &str = "(set-logic HORN)
(declare-fun U (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (>= x 2) (U x))))
(assert (forall ((y Int)) (=> (U y) (Q y))))
(assert (forall ((c Int) (t Bool)) (=> (and (= t (= c 1)) (Q c) t) false)))
(assert (forall ((y Int) (t Int)) (=> (and (= t y) (>= t 5) (Q y)) false)))
(check-sat)
";

fn solve(input: &str, strict_proofs: bool) -> VerifiedChcResult {
    let problem = ChcParser::parse(input).expect("parse");
    let mut config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
    config.strict_proofs = strict_proofs;
    AdaptivePortfolio::new(problem, config).solve()
}

#[test]
#[timeout(180_000)]
fn a_query_local_name_at_two_sorts_does_not_make_the_system_safe() {
    for strict_proofs in [false, true] {
        let result = solve(UNSAFE, strict_proofs);
        assert!(
            !matches!(result, VerifiedChcResult::Safe(_)),
            "unsafe (z3: unsat); strict_proofs = {strict_proofs}: {result:?}"
        );
    }
}

/// The renamed control (`s` for the Bool `t`) was always decided Unsafe.
#[test]
#[timeout(180_000)]
fn the_renamed_control_stays_unsafe() {
    let control = UNSAFE.replace(
        "(t Bool)) (=> (and (= t (= c 1)) (Q c) t)",
        "(s Bool)) (=> (and (= s (= c 1)) (Q c) s)",
    );
    assert_ne!(control, UNSAFE, "the control rename must apply");
    let result = solve(&control, true);
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "unsafe: {result:?}"
    );
}
