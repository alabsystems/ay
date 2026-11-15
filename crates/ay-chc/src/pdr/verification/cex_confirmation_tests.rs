// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `confirm_counterexample` names the counterexample a `Valid` verdict rests
//! on, and never changes the verdict `verify_counterexample` reports.
//!
//! The bounded-BMC replay (inc-9) decides `Valid` from its own verified
//! derivation and never reads the content of the counterexample it was handed.
//! Before this API existed, every publishing caller shipped that unchecked
//! input beside the replay's verdict.

use super::*;
use crate::pdr::{CounterexampleStep, PdrConfig};
use crate::{ChcParser, ChcProblem};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ntest::timeout;

/// Cyclic two-predicate refutation `P(0) -> ... -> P(3) -> Q(3) -> false`.
/// It has no transition-system encoding, so a witness-free counterexample
/// can only be decided by the bounded replay.
const UNSAFE_MULTIPRED: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (< x 3) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 3)) (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (= x 3)) false)))
(check-sat)
";

/// The safe twin: `Q` only ever holds 3, so `Q(4)` is unreachable.
const SAFE_MULTIPRED: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (< x 3) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 3)) (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (= x 4)) false)))
(check-sat)
";

/// `three_var_soundness_685`: the abort state needs 7 transitions.
const THREE_VAR_685: &str = "(set-logic HORN)
(declare-fun S (Int Int Int) Bool)
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (= pc 0) (= x 0) (= c 0)) (S pc x c))))
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc 0) (<= c 5)) (S 0 (+ x 1) (+ c 1)))))
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc 0) (> c 5) (<= x 100)) (S (- 2) x c))))
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc (- 2))) false)))
(check-sat)
";

fn parse(script: &str) -> ChcProblem {
    ChcParser::parse(script).expect("fixture parses")
}

fn verifier(problem: &ChcProblem, replay: bool) -> PdrSolver {
    let config = PdrConfig {
        disable_cex_replay: !replay,
        ..PdrConfig::default()
    };
    PdrSolver::new(problem.clone(), config)
}

/// A witness-free counterexample with `len` value-free steps per predicate
/// order: only its shape (and so the replay's depth hint) is present.
fn skeleton(problem: &ChcProblem, len: usize) -> Counterexample {
    let predicates = problem.predicates();
    Counterexample::new(
        (0..len)
            .map(|i| {
                let predicate = predicates[i.min(predicates.len() - 1)].id;
                CounterexampleStep::new(predicate, FxHashMap::default())
            })
            .collect(),
    )
}

#[test]
#[timeout(120_000)]
fn a_replay_decided_valid_publishes_the_replays_counterexample() {
    let problem = parse(UNSAFE_MULTIPRED);
    let input = skeleton(&problem, 2);
    assert_eq!(
        verifier(&problem, true).verify_counterexample(&input),
        CexVerificationResult::Valid,
        "setup: the replay decides this refutation"
    );
    assert_eq!(
        input.ground_checks_unsafe(&problem).ok(),
        None,
        "setup: the value-free input cannot be confirmed by itself"
    );

    let published = verifier(&problem, true)
        .confirm_counterexample(input)
        .expect("same verdict as verify_counterexample");
    assert!(
        published
            .witness
            .as_ref()
            .is_some_and(|witness| !witness.entries.is_empty()),
        "the published counterexample is the replay's witness-bearing one"
    );
    assert_eq!(
        published.ground_checks_unsafe(&problem).ok(),
        Some(true),
        "--strict-proofs STEP D confirms what is published"
    );
}

#[test]
#[timeout(120_000)]
fn a_directly_verified_counterexample_is_published_unchanged() {
    let problem = parse(UNSAFE_MULTIPRED);
    let replayed = verifier(&problem, true)
        .confirm_counterexample(skeleton(&problem, 2))
        .expect("setup: the replay confirms");
    // The replay disabled: `Valid` can only come from checking the input.
    let published = verifier(&problem, false)
        .confirm_counterexample(replayed.clone())
        .expect("the replay's counterexample verifies directly");
    assert_eq!(format!("{published:?}"), format!("{replayed:?}"));
}

#[test]
#[timeout(120_000)]
fn without_the_replay_nothing_is_substituted_and_the_verdict_stays_unknown() {
    let problem = parse(UNSAFE_MULTIPRED);
    let input = skeleton(&problem, 2);
    assert_eq!(
        verifier(&problem, false).verify_counterexample(&input),
        CexVerificationResult::Unknown
    );
    assert_eq!(
        verifier(&problem, false)
            .confirm_counterexample(input)
            .err(),
        Some(CexVerificationResult::Unknown)
    );
}

/// Negative twin: the replay never confirms a safe problem (it exhausts its
/// bounded budget), and the verdict the two APIs report is the same.
#[test]
#[timeout(120_000)]
fn a_safe_problem_is_never_confirmed() {
    let problem = parse(SAFE_MULTIPRED);
    let input = skeleton(&problem, 2);
    let mut verifier = verifier(&problem, true);
    let verdict = verifier
        .confirm_counterexample(input.clone())
        .expect_err("a safe problem has no counterexample to publish");
    assert_eq!(verdict, CexVerificationResult::Unknown);
    // Same solver: its failed-depth memo answers without a second replay.
    assert_eq!(verifier.verify_counterexample(&input), verdict);
}

/// A witness-free trace that stops one transition short of the query is
/// decided (refuted) on its own depth when the problem encodes as a
/// transition system: it is `Spurious`, and nothing is published.
#[test]
#[timeout(120_000)]
fn a_checkable_short_trace_is_refuted_not_replaced() {
    let problem = parse(THREE_VAR_685);
    let one_short = skeleton(&problem, 7);
    assert_eq!(
        verifier(&problem, true)
            .confirm_counterexample(one_short)
            .err(),
        Some(CexVerificationResult::Spurious)
    );
}
