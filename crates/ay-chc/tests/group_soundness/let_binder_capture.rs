// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A `let` and a stripped quantifier binder of the same name must not capture.
//!
//! The CHC parser expands a `let` by substituting its value after parsing the
//! body, while `exists`/`forall` binders are stripped into the flat clause
//! scope. In `LET_OVER_EXISTS` the substitution rewrote the exists binder's own
//! `y` (`exists y. y = x + 10` became `5 = x + 10`); in `LET_INSIDE_EXISTS` the
//! binder, renamed apart from the clause binder `y`, captured the let body's
//! `y` and the let was dropped. Both systems are unsafe (z3 5.1: `unsat`); AY
//! answered `sat` at default and `--competition`. Found by the 2026-09-29 CHC
//! differential generator (`scripts/differential/gen/chc`, shape `binders`).

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

/// `P(7)`; `P(x) /\ let y = 5 in (x > y /\ exists y. y = x + 10) => false`.
const LET_OVER_EXISTS: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (P 7))
(assert (forall ((x Int)) (=> (P x) (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (let ((y 5)) (and (> x y) (exists ((y Int)) (= y (+ x 10)))))) false)))
(check-sat)
";

/// `P(0)`, `Q(1)`; `P(y) /\ exists y'. (Q(y') /\ let y = 5 in y > 3) => false`.
const LET_INSIDE_EXISTS: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (P 0))
(assert (Q 1))
(assert (forall ((y Int)) (=> (and (P y) (exists ((y Int)) (and (Q y) (let ((y 5)) (> y 3))))) false)))
(check-sat)
";

fn solve(input: &str, strict_proofs: bool) -> VerifiedChcResult {
    let problem = ChcParser::parse(input).expect("parse");
    let mut config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
    config.strict_proofs = strict_proofs;
    AdaptivePortfolio::new(problem, config).solve()
}

fn assert_unsafe(label: &str, input: &str) {
    for strict_proofs in [false, true] {
        let result = solve(input, strict_proofs);
        assert!(
            matches!(result, VerifiedChcResult::Unsafe(_)),
            "{label} is unsafe (z3: unsat); strict_proofs = {strict_proofs}: {result:?}"
        );
    }
}

#[test]
#[timeout(180_000)]
fn a_binder_inside_a_let_of_the_same_name_is_not_captured() {
    assert_unsafe("let-over-exists", LET_OVER_EXISTS);
}

#[test]
#[timeout(180_000)]
fn a_let_inside_a_renamed_binder_of_the_same_name_is_not_dropped() {
    assert_unsafe("let-inside-exists", LET_INSIDE_EXISTS);
}

/// The controls: the same systems with the let renamed apart were always
/// decided Unsafe.
#[test]
#[timeout(180_000)]
fn the_renamed_controls_stay_unsafe() {
    let over = LET_OVER_EXISTS.replace("(let ((y 5)) (and (> x y)", "(let ((k 5)) (and (> x k)");
    let inside = LET_INSIDE_EXISTS.replace("(let ((y 5)) (> y 3))", "(let ((k 5)) (> k 3))");
    assert_ne!(
        over, LET_OVER_EXISTS,
        "the let-over-exists rename must apply"
    );
    assert_ne!(
        inside, LET_INSIDE_EXISTS,
        "the let-inside-exists rename must apply"
    );
    assert_unsafe("let-over-exists (renamed)", &over);
    assert_unsafe("let-inside-exists (renamed)", &inside);
}
