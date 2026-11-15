// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! MODEL_CHECKER_CONSUMER ask 2026-10-14-acyclic-8bit-ite-chain: the CHC of
//! `walker_loop_fuel_exit_dual.rs::safe_returns_count`, 27 relations and
//! acyclic, whose method value is a 13-deep `ite` chain over one 8-bit input.
//! z3 says unsat at once; ay took five and a half minutes, and a cancelled
//! per-property batch returned minutes past its budget.
//!
//! Two defects. The parser inlines the chain's defining equality into
//! `bb4`'s argument, and the acyclic BV proof-lane gates read `ite` from
//! constraints only, so the collapsed BV-native probe, which decides the
//! query in milliseconds, ran only after the algebraic pre-strategy. That
//! pre-strategy's syntactic validator evaluated both branches of every
//! undecided `ite` twice, `2^13` evaluations, in a scan that polls no budget.
//!
//! The unsafe twin makes the chain's value for `x = 12` wrong (11), so
//! `error_p17` is reachable.
//!
//! Opening the gate to inlined `ite`s exposed a third defect, already live
//! for constraint `ite`s: on a problem with a stutter rule `P(x) => P(x)`,
//! which the classifier calls acyclic, the probe's exhaustive empty-model
//! Safe can never pass the finalize re-check (it refuses the stutter rule as a
//! cycle), and returning it ended the round as unknown before the algebraic
//! lane that answers ran. And with the stutter rule on the predicate the
//! query reads, the exact acyclic BMC encoding kept the rule as a circular
//! definition, answered Unknown on the safe system, and the probe spent its
//! stage budget on an unsafe-only pass. The stutter tests pin both.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser, VerifiedChcResult};
use ntest::timeout;
use std::time::{Duration, Instant};

const ITE_CHAIN: &str =
    include_str!("../fixtures/model_checker_consumer_acyclic_8bit_ite_chain.smt2");

/// The chain's innermost link, `(ite (not (bvuge #x0c x)) #x0d #x0c)`: `x = 12`
/// takes its else value.
const INNERMOST_LINK: &str = "#x0d #x0c)";
const INNERMOST_LINK_WRONG: &str = "#x0d #x0b)";

/// Solves `source` and returns the answer with the wall time it took, and the
/// budget the solve was given.
fn solve(source: &str, release_budget: Duration) -> (VerifiedChcResult, Duration, Duration) {
    let problem = ChcParser::parse(source).unwrap_or_else(|err| panic!("fixture parses: {err}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("fixture validates: {err}"));
    let budget = if cfg!(debug_assertions) {
        release_budget * 4
    } else {
        release_budget
    };
    let started = Instant::now();
    let result = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(budget),
    )
    .solve();
    (result, started.elapsed(), budget)
}

/// Safe, and inside the budget: before the fix the solve held its thread for
/// minutes whatever budget it was given.
#[test]
#[timeout(120_000)]
fn acyclic_8bit_ite_chain_is_safe_within_budget() {
    let (result, elapsed, budget) = solve(ITE_CHAIN, Duration::from_secs(10));
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "error_p17 is unreachable: the chain is min(x, 13) and x <= 12 (z3: unsat); got {result:?}"
    );
    assert!(
        elapsed <= budget,
        "the answer arrived {elapsed:?} into a {budget:?} budget"
    );
}

/// Negative twin: the same chain with `x = 12` mapped to 11 reaches
/// `error_p17`, and the answer is a validated counterexample.
#[test]
#[timeout(120_000)]
fn acyclic_8bit_ite_chain_with_a_wrong_link_is_unsafe() {
    assert_eq!(ITE_CHAIN.matches(INNERMOST_LINK).count(), 1);
    let unsafe_twin = ITE_CHAIN.replace(INNERMOST_LINK, INNERMOST_LINK_WRONG);
    let (result, elapsed, budget) = solve(&unsafe_twin, Duration::from_secs(10));
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "x = 12 yields 11 != 12, so error_p17 is reachable (z3: sat); got {result:?}"
    );
    assert!(
        elapsed <= budget,
        "the answer arrived {elapsed:?} into a {budget:?} budget"
    );
}

/// `p0 -> p1 -> err` with a stutter rule on `stutter_on`; the transition
/// defines `o` by a 6-deep chain (`min(x, 6)` under `x <= 5`), inlined into
/// `p1`'s argument, and `extra_guard` is conjoined to its constraint.
fn stutter_chain(stutter_on: &str, extra_guard: &str, innermost_else: &str) -> String {
    let chain = "(ite (not (bvuge #x00 x)) (ite (not (bvuge #x01 x)) \
                 (ite (not (bvuge #x02 x)) (ite (not (bvuge #x03 x)) \
                 (ite (not (bvuge #x04 x)) (ite (not (bvuge #x05 x)) #x06 INNER) \
                 #x04) #x03) #x02) #x01) #x00)"
        .replace("INNER", innermost_else);
    format!(
        "(set-logic HORN)\n\
         (declare-var x (_ BitVec 8))\n(declare-var y (_ BitVec 8))\n(declare-var o (_ BitVec 8))\n\
         (declare-rel p0 ((_ BitVec 8) (_ BitVec 8)))\n\
         (declare-rel p1 ((_ BitVec 8) (_ BitVec 8)))\n(declare-rel err ())\n\
         (rule (=> true (p0 x y)))\n\
         (rule (=> ({stutter_on} x y) ({stutter_on} x y)))\n\
         (rule (=> (and (p0 x y) (bvule x #x05) {extra_guard} (= o {chain})) (p1 x o)))\n\
         (rule (=> (and (p1 x y) (not (= y x))) err))\n(query err)\n"
    )
}

/// The chain alone (the gate opens on the inlined `ite`), and with an `ite`
/// guard that stays in the constraint (the gate was already open), with the
/// stutter rule on the facts and on the predicate the query reads: Safe
/// every time.
#[test]
#[timeout(240_000)]
fn stutter_rule_does_not_strand_the_acyclic_probe() {
    for (stutter_on, guard) in [
        ("p0", ""),
        ("p0", "(bvule (ite (bvule x #x03) x y) #xfe)"),
        ("p1", ""),
        ("p1", "(bvule (ite (bvule x #x03) x y) #xfe)"),
    ] {
        let (result, elapsed, budget) = solve(
            &stutter_chain(stutter_on, guard, "#x05"),
            Duration::from_secs(10),
        );
        assert!(
            matches!(result, VerifiedChcResult::Safe(_)),
            "the chain is x for x <= 5, so err is unreachable (z3: unsat); stutter on \
             {stutter_on}, guard {guard:?}, got {result:?}"
        );
        assert!(
            elapsed <= budget,
            "the answer arrived {elapsed:?} into a {budget:?} budget"
        );
    }
}

/// Negative twin: `x = 5` mapped to 4 reaches `err`.
#[test]
#[timeout(120_000)]
fn stutter_rule_with_a_wrong_link_is_unsafe() {
    for stutter_on in ["p0", "p1"] {
        let (result, _, _) = solve(
            &stutter_chain(stutter_on, "", "#x04"),
            Duration::from_secs(10),
        );
        assert!(
            matches!(result, VerifiedChcResult::Unsafe(_)),
            "x = 5 yields 4 != 5, so err is reachable (z3: sat); stutter on {stutter_on}, \
             got {result:?}"
        );
    }
}
