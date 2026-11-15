// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A head-only variable must not make an unsafe acyclic system Safe.
//!
//! In each system below, `P(a) => Q(a, t(x))` binds `x` only in the head. The
//! acyclic BMC probe mapped only BODY variables to level-specific names
//! (`BmcSolver::mk_rule_vars`, since the initial publish), so `x` kept its
//! source name, was shared with the fact `true => P(x + 1)`, and the unrolling
//! wrongly tied the two clause instances together. With z3 answering `unsat`
//! (unsafe) on both, AY published `sat` with a SAFE certificate at default and
//! `--rigor certified`, and the in-process route MODEL_CHECKER_CONSUMER calls returned
//! `Safe` with `strict_proofs = true`. The renamed controls (`y`, `m`) were
//! always `Unsafe`. Found by the 2026-09-29 MODEL_CHECKER_CONSUMER state assessment.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::Duration;

/// `P(x+1)`, `P(a) => Q(a, x+2)`, `Q(a,c) and c = a+5 => false`: unsafe
/// (`x = a + 3` reaches the query).
const H3: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> true (P (+ x 1)))))
(assert (forall ((a Int) (x Int)) (=> (P a) (Q a (+ x 2)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (= c (+ a 5))) false)))
(check-sat)
";

/// `P(2n)`, `P(a) => Q(a, 2n)`, `Q(a,c) and a != c => false`: unsafe.
const H8: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((n Int)) (=> true (P (* 2 n)))))
(assert (forall ((a Int) (n Int)) (=> (P a) (Q a (* 2 n)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (not (= a c))) false)))
(check-sat)
";

fn solve(input: &str, strict_proofs: bool) -> VerifiedChcResult {
    let problem = ChcParser::parse(input).expect("parse");
    let mut config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20));
    config.strict_proofs = strict_proofs;
    AdaptivePortfolio::new(problem, config).solve()
}

fn assert_never_safe(label: &str, input: &str) {
    for strict_proofs in [false, true] {
        let result = solve(input, strict_proofs);
        assert!(
            !matches!(result, VerifiedChcResult::Safe(_)),
            "{label} is unsafe (z3: unsat) but AY answered Safe with \
             strict_proofs = {strict_proofs}: {result:?}"
        );
    }
}

#[test]
#[timeout(180_000)]
fn a_head_only_offset_variable_does_not_make_the_system_safe() {
    assert_never_safe("h3", H3);
}

#[test]
#[timeout(180_000)]
fn a_head_only_even_variable_does_not_make_the_system_safe() {
    assert_never_safe("h8", H8);
}

/// The controls: the same systems with the head-only binder renamed apart
/// from the fact's binder were always decided Unsafe.
#[test]
#[timeout(180_000)]
fn the_renamed_controls_stay_unsafe() {
    let h3y = H3.replace(
        "(x Int)) (=> (P a) (Q a (+ x 2))",
        "(y Int)) (=> (P a) (Q a (+ y 2))",
    );
    let h8m = H8.replace(
        "(n Int)) (=> (P a) (Q a (* 2 n))",
        "(m Int)) (=> (P a) (Q a (* 2 m))",
    );
    assert_ne!(h3y, H3, "the h3 control rename must apply");
    assert_ne!(h8m, H8, "the h8 control rename must apply");
    for (label, input) in [("h3y", h3y), ("h8m", h8m)] {
        let result = solve(&input, true);
        assert!(
            matches!(result, VerifiedChcResult::Unsafe(_)),
            "{label} is unsafe and was always decided Unsafe: {result:?}"
        );
    }
}
