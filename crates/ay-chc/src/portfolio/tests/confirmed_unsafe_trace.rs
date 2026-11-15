// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Unsafe that is published is the counterexample that passed validation
//! on the original clauses, also when only the bounded-BMC replay passed, and
//! its steps are the trace its validated ground derivation derives.
//!
//! `three_var_soundness_685`: preprocessing (pc-split, then inlining the abort
//! location into the query) makes the engine-space trace end at `S(0, 6, 6)`.
//! The back-translation does not re-insert the final `S(-2, 6, 6)` step, so its
//! trace is one transition short of the query and its witness is inconclusive
//! on the original clauses. The bounded replay then decides `Valid` from its
//! own trace. Before the fix the portfolio and the adaptive final gate still
//! published the short translation: `ay --stats` exported a depth-6
//! `expected-result: sat` trace-validity obligation that z3 refutes, and
//! `--strict-proofs` STEP D could not confirm the counterexample.

use super::*;
use crate::bmc::BmcSolver;
use crate::engine_result::ValidationEvidence;
use crate::pdr::PdrSolver;
use crate::{AdaptiveConfig, AdaptivePortfolio, VerifiedChcResult};

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

/// Nondeterministic increments: BMC's counterexample carries a ground
/// derivation, and the abort location is inlined into the query.
const NONDET_INC: &str = "(set-logic HORN)
(declare-fun S (Int Int Int) Bool)
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (= pc 0) (= x 0) (= c 0)) (S pc x c))))
(assert (forall ((pc Int) (x Int) (c Int) (d Int))
    (=> (and (S pc x c) (= pc 0) (<= c 5) (>= d 1) (<= d 2)) (S 0 (+ x d) (+ c 1)))))
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc 0) (> c 5) (>= x 9)) (S (- 2) x c))))
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (S pc x c) (= pc (- 2))) false)))
(check-sat)
";

/// The middle location `pc = 1` is inlined: six of its states are missing.
const MID_LOCATION: &str = "(set-logic HORN)
(declare-fun S (Int Int Int) Bool)
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (= pc 0) (= x 0) (= c 0)) (S pc x c))))
(assert (forall ((pc Int) (x Int) (c Int) (d Int))
    (=> (and (S pc x c) (= pc 0) (<= c 5) (>= d 1) (<= d 2)) (S 1 (+ x d) c))))
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (S pc x c) (= pc 1)) (S 0 x (+ c 1)))))
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (S pc x c) (= pc 0) (> c 5) (>= x 9)) false)))
(check-sat)
";

/// Two locations (`pc = 5`, `pc = 6`) are inlined into the query.
const TWO_INLINED: &str = "(set-logic HORN)
(declare-fun S (Int Int Int) Bool)
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (= pc 1) (= x 0) (= c 0)) (S pc x c))))
(assert (forall ((pc Int) (x Int) (c Int) (d Int))
    (=> (and (S pc x c) (= pc 1) (<= c 3) (>= d 0) (<= d 3)) (S 1 (+ x d) (+ c 1)))))
(assert (forall ((pc Int) (x Int) (c Int))
    (=> (and (S pc x c) (= pc 1) (> c 3) (= x 7)) (S 5 x c))))
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (S pc x c) (= pc 5)) (S 6 (* x 2) c))))
(assert (forall ((pc Int) (x Int) (c Int)) (=> (and (S pc x c) (= pc 6) (= x 14)) false)))
(check-sat)
";

/// Cyclic two-predicate refutation: no transition-system encoding, so a
/// witness-free Unsafe is decided only by the bounded replay.
const UNSAFE_MULTIPRED: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (< x 3) (= y (+ x 1))) (P y))))
(assert (forall ((x Int)) (=> (and (P x) (>= x 3)) (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (= x 3)) false)))
(check-sat)
";

fn preprocessing_config() -> PortfolioConfig {
    PortfolioConfig {
        external_cancellation: None,
        engines: vec![],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,
        enable_preprocessing: true,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    }
}

/// The first line AY's own fresh executor prints for an exported obligation.
fn ay_decides(smtlib: &str) -> String {
    let commands = ay_frontend::parse(smtlib).expect("the obligation parses");
    let mut executor = crate::smt::executor_adapter::new_search_executor();
    let outputs = executor
        .execute_all(&commands)
        .expect("the obligation executes");
    outputs.first().cloned().unwrap_or_default()
}

fn trace_obligation(problem: &ChcProblem, cex: &Counterexample) -> (String, String) {
    let obligations = cex
        .trace_validity_replay_obligations(problem)
        .expect("a single-predicate trace exports its obligation");
    let [obligation] = obligations.as_slice() else {
        panic!("one trace-validity obligation, got {}", obligations.len());
    };
    (obligation.name.clone(), ay_decides(&obligation.smtlib))
}

#[test]
#[timeout(120_000)]
fn the_portfolio_publishes_the_replays_trace_not_the_short_translation() {
    let original = ChcParser::parse(THREE_VAR_685).expect("fixture parses");
    let solver = PortfolioSolver::new(original.clone(), preprocessing_config());
    assert!(
        solver.engine_problem().clauses().len() < original.clauses().len(),
        "setup: preprocessing folds the abort clause into the query"
    );
    let bmc = BmcSolver::new(
        solver.engine_problem().clone(),
        BmcConfig::default().with_max_depth(12),
    );
    let ChcEngineResult::Unsafe(mut engine_cex) = bmc.solve() else {
        panic!("setup: BMC refutes the preprocessed problem");
    };
    // BMC's counterexample carries its ground derivation, whose translation
    // derives the full trace; drop it to exercise a witness-only engine.
    engine_cex.ground_derivation = None;

    // The bug's precondition: the translation stops one transition short, its
    // obligation is refuted, and it does not pass without the replay.
    let translated = backtranslate_counterexample_with_ground_evidence(
        solver.back_translator.as_ref(),
        &original,
        &engine_cex,
        &CancellationToken::new(),
    );
    assert_eq!(
        trace_obligation(&original, &translated),
        ("trace-validity-depth-6".to_string(), "unsat".to_string()),
        "setup: the short translation's obligation is refuted"
    );
    let no_replay = PdrConfig {
        disable_cex_replay: true,
        preserve_original_clauses: true,
        disable_array_scalarization: true,
        ..PdrConfig::default()
    };
    assert_ne!(
        PdrSolver::new(original.clone(), no_replay).verify_counterexample(&translated),
        crate::pdr::CexVerificationResult::Valid,
        "setup: without the replay the translation does not pass"
    );

    let published = solver
        .validate_unsafe_translating(&engine_cex)
        .expect("the replay confirms the verdict on the original problem");
    assert_eq!(
        trace_obligation(&original, &published),
        ("trace-validity-depth-7".to_string(), "sat".to_string()),
        "the published trace runs init -> bad on the problem's own clauses"
    );
    assert_eq!(
        published.ground_checks_unsafe(&original).ok(),
        Some(true),
        "--strict-proofs STEP D confirms the published counterexample"
    );
}

/// The adaptive final gate builds the public `VerifiedChcResult`: it wraps
/// the counterexample that passed, not the witness-free candidate.
#[test]
#[timeout(120_000)]
fn the_final_gate_wraps_the_counterexample_that_passed() {
    let problem = ChcParser::parse(UNSAFE_MULTIPRED).expect("fixture parses");
    let candidate = Counterexample::new(
        problem
            .predicates()
            .iter()
            .map(|p| CounterexampleStep::new(p.id, FxHashMap::default()))
            .collect(),
    );
    assert_eq!(
        candidate.ground_checks_unsafe(&problem).ok(),
        None,
        "setup: the value-free candidate cannot be confirmed by itself"
    );
    let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default());
    let verified = adaptive.finalize_verified_result(
        PortfolioResult::Unsafe(candidate),
        ValidationEvidence::CounterexampleVerification,
    );
    let VerifiedChcResult::Unsafe(cex) = verified else {
        panic!("the replay confirms this genuine refutation: {verified:?}");
    };
    assert_eq!(
        cex.counterexample().ground_checks_unsafe(&problem).ok(),
        Some(true),
        "the public Unsafe carries the replay's confirmable counterexample"
    );
}

/// The ground-derivation fast path decides on the back-translated derivation,
/// which expands the inlined clauses, not on the back-translated steps, which
/// omit the inlined states. What is published (by the portfolio and by the
/// adaptive final gate) is the derivation's trace: before the fix, the short
/// steps with `trace-validity-depth-6` / `-6` / `-4` obligations AY's executor
/// and z3 refute, and a strict `unsat` STEP D confirmed from the derivation.
#[test]
#[timeout(120_000)]
fn the_portfolio_publishes_the_derivations_trace_not_the_short_steps() {
    for (fixture, depth) in [(NONDET_INC, 7), (MID_LOCATION, 12), (TWO_INLINED, 6)] {
        let original = ChcParser::parse(fixture).expect("fixture parses");
        let solver = PortfolioSolver::new(original.clone(), preprocessing_config());
        let bmc = BmcSolver::new(
            solver.engine_problem().clone(),
            BmcConfig::default().with_max_depth(20),
        );
        let ChcEngineResult::Unsafe(engine_cex) = bmc.solve() else {
            panic!("setup: BMC refutes the preprocessed problem (depth {depth})");
        };

        // The bug's precondition: the derivation validates on the original
        // clauses, the steps stop short of it, and the exporter refuses them.
        let translated = backtranslate_counterexample_with_ground_evidence(
            solver.back_translator.as_ref(),
            &original,
            &engine_cex,
            &CancellationToken::new(),
        );
        assert!(
            translated.has_ground_derivation(),
            "setup: the derivation back-translates and validates (depth {depth})"
        );
        assert!(
            translated.steps.len() < depth + 1,
            "setup: the back-translated steps omit the inlined states (depth {depth})"
        );
        let refused = translated
            .trace_validity_replay_obligations(&original)
            .expect_err("the exporter refuses steps short of the validated derivation");
        assert!(
            refused.to_string().contains("derivation derives"),
            "{refused}"
        );

        let published = solver
            .validate_unsafe_translating(&engine_cex)
            .expect("the derivation confirms the verdict on the original problem");
        let expected = (format!("trace-validity-depth-{depth}"), "sat".to_string());
        assert_eq!(trace_obligation(&original, &published), expected);
        assert_eq!(published.ground_checks_unsafe(&original).ok(), Some(true));

        let adaptive = AdaptivePortfolio::new(original.clone(), AdaptiveConfig::test_default());
        let verified = adaptive.finalize_verified_result(
            PortfolioResult::Unsafe(translated),
            ValidationEvidence::CounterexampleVerification,
        );
        let VerifiedChcResult::Unsafe(cex) = verified else {
            panic!("the final gate confirms the derivation (depth {depth}): {verified:?}");
        };
        assert_eq!(trace_obligation(&original, cex.counterexample()), expected);
    }
}
