// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A witness-free Unsafe in a ladder race where the caller requires a ground
//! UNSAFE trace: re-derived before it decides, held when it cannot be, and
//! untouched where no ground trace is required.
//!
//! Measured at e2e3bd3a8 (`ay --strict-proofs` on `UNSAFE` below): the
//! SimpleLoop race was decided by the portfolio foreground's CEGAR trace at
//! 0.07 s, which carries no concrete values; the final boundary accepted it
//! through the transition-system reachability check and the CLI's trace
//! check demoted the correct `unsat` to `unknown` ("missing concrete trace
//! assignment for step 0, state arg 0").

use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use ntest::timeout;

use super::super::LadderMember;
use super::*;
use crate::adaptive::{AdaptiveConfig, AdaptiveExecutionMode};
use crate::engine_result::ValidationEvidence;
use crate::pdr::CounterexampleStep;
use crate::{ChcParser, VerifiedChcResult};

const UNSAFE: &str = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
"#;

/// `UNSAFE` with the increment guarded by `x < 5`: `x` never exceeds 5.
const SAFE_TWIN: &str = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 5)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
"#;

/// Upper bound on any waiting loop below.
const SAFETY: Duration = Duration::from_secs(30);

/// `x = 0 .. 6` reaches `x > 5`: seven steps.
const UNSAFE_STEPS: usize = 7;

/// A solve deadline this close leaves the replay less than its floor.
const NO_REPLAY_BUDGET: Duration = Duration::from_millis(300);

/// How long a still-searching participant keeps going after the witness-free
/// verdict landed, unless that verdict decided the race. A decided race
/// cancels every participant at once, so this window only has to outlast that
/// cancellation; it must also end well inside [`NO_REPLAY_BUDGET`], because
/// the race admits a participant's verdict only before the caller's original
/// deadline (`adaptive_ladder_race::admission`): one offered after it is
/// refused as Unknown however good its witness.
const STILL_SEARCHING: Duration = Duration::from_millis(100);

fn parse(text: &str) -> ChcProblem {
    ChcParser::parse(text).expect("fixture parses")
}

fn requiring_ground_trace() -> AdaptiveConfig {
    AdaptiveConfig {
        require_ground_unsafe_trace: true,
        ..AdaptiveConfig::test_default()
    }
}

/// What a witness-free engine hands the race: one step per level, no values,
/// no derivation witness, no ground derivation.
fn value_free(problem: &ChcProblem, steps: usize) -> Counterexample {
    let predicate = problem.predicates()[0].id;
    Counterexample::new(
        (0..steps)
            .map(|_| CounterexampleStep::new(predicate, FxHashMap::default()))
            .collect(),
    )
}

fn unsafe_outcome(cex: Counterexample) -> LadderOutcome {
    (
        PortfolioResult::Unsafe(cex),
        ValidationEvidence::CounterexampleVerification,
    )
}

fn unknown() -> LadderOutcome {
    (
        PortfolioResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

/// Spin until this thread's lane is cancelled; false after `limit`.
fn lane_cancelled_within(limit: Duration) -> bool {
    let started = Instant::now();
    while started.elapsed() < limit {
        if crate::smt::deadline::lane_cancelled() {
            return true;
        }
        std::thread::sleep(Duration::from_millis(2));
    }
    false
}

fn ground_checks(problem: &ChcProblem, cex: &Counterexample) -> Option<bool> {
    cex.ground_checks_unsafe(problem).ok()
}

fn is_value_free(cex: &Counterexample) -> bool {
    cex.witness.is_none()
        && cex.ground_derivation.is_none()
        && cex.steps.iter().all(|step| step.assignments.is_empty())
}

/// The race handed back the witness-free candidate exactly as offered.
fn assert_unchanged_candidate((result, _): &LadderOutcome, why: &str) {
    let PortfolioResult::Unsafe(cex) = result else {
        panic!("{why}: expected the offered Unsafe, got {result:?}");
    };
    assert!(
        is_value_free(cex) && cex.steps.len() == UNSAFE_STEPS,
        "{why}"
    );
}

/// The strict gate's view of what the race publishes.
fn assert_published_trace_ground_checks(
    portfolio: &AdaptivePortfolio,
    problem: &ChcProblem,
    (result, evidence): LadderOutcome,
) {
    let PortfolioResult::Unsafe(cex) = &result else {
        panic!("the race must keep the Unsafe verdict: {result:?}");
    };
    assert_eq!(
        ground_checks(problem, cex),
        Some(true),
        "the race's Unsafe must carry a ground-checkable trace"
    );
    let VerifiedChcResult::Unsafe(published) = portfolio.finalize_verified_result(result, evidence)
    else {
        panic!("the final boundary must admit the counterexample");
    };
    assert_eq!(
        ground_checks(problem, published.counterexample()),
        Some(true),
        "--strict-proofs STEP D must confirm the published counterexample"
    );
}

#[test]
#[timeout(120_000)]
fn a_witness_free_member_verdict_is_published_with_a_ground_checked_trace() {
    let problem = parse(UNSAFE);
    assert_eq!(
        ground_checks(&problem, &value_free(&problem, UNSAFE_STEPS)),
        None,
        "setup: the value-free trace cannot be ground-checked by itself"
    );
    let portfolio = AdaptivePortfolio::new(problem.clone(), requiring_ground_trace());
    let foreground_cancelled = AtomicBool::new(false);
    let members = vec![LadderMember::new("witness_free", || {
        Some(unsafe_outcome(value_free(&problem, UNSAFE_STEPS)))
    })];
    let outcome = portfolio.race_ladder("test", members, || {
        foreground_cancelled.store(lane_cancelled_within(SAFETY), Ordering::Relaxed);
        unknown()
    });
    assert!(
        foreground_cancelled.load(Ordering::Relaxed),
        "the re-derived verdict still decides the race"
    );
    assert_published_trace_ground_checks(&portfolio, &problem, outcome);
}

#[test]
#[timeout(120_000)]
fn a_witness_free_foreground_verdict_is_published_with_a_ground_checked_trace() {
    let problem = parse(UNSAFE);
    let portfolio = AdaptivePortfolio::new(problem.clone(), requiring_ground_trace());
    let members = vec![LadderMember::new("gives_up", || None)];
    let outcome = portfolio.race_ladder("test", members, || {
        unsafe_outcome(value_free(&problem, UNSAFE_STEPS))
    });
    assert_published_trace_ground_checks(&portfolio, &problem, outcome);
}

/// A witness-free verdict the replay cannot re-derive (here: no budget left
/// for it) does not decide: the race stays open and a witness-bearing verdict
/// that arrives later decides with a checkable trace. Offered as it was, the
/// witness-free verdict would have decided and cancelled the searcher.
#[test]
#[timeout(120_000)]
fn an_unconfirmed_witness_free_verdict_is_held_until_a_witness_bearing_one_decides() {
    assert!(
        3 * STILL_SEARCHING <= NO_REPLAY_BUDGET,
        "the witness-bearing verdict must be offered before the caller's deadline"
    );
    let problem = parse(UNSAFE);
    let witnessed = crate::bmc::BmcSolver::replay_confirm_unsafe_on_problem(
        &problem,
        UNSAFE_STEPS + 2,
        SAFETY,
        None,
        false,
    )
    .expect("setup: BMC finds the counterexample");
    assert_eq!(ground_checks(&problem, &witnessed), Some(true), "setup");
    let portfolio = AdaptivePortfolio::new(problem.clone(), requiring_ground_trace());
    let witness_free_returned = AtomicBool::new(false);
    let members = vec![
        LadderMember::new("witness_free", || {
            witness_free_returned.store(true, Ordering::SeqCst);
            Some(unsafe_outcome(value_free(&problem, UNSAFE_STEPS)))
        }),
        LadderMember::new("still_searching", || {
            let started = Instant::now();
            while !witness_free_returned.load(Ordering::SeqCst) && started.elapsed() < SAFETY {
                std::thread::sleep(Duration::from_millis(2));
            }
            // A decided race stops a searcher, as it stops every real stage.
            if lane_cancelled_within(STILL_SEARCHING) {
                return None;
            }
            Some(unsafe_outcome(witnessed.clone()))
        }),
    ];
    let outcome = {
        let _no_replay_budget =
            crate::smt::ScopedSolveDeadline::new(Some(Instant::now() + NO_REPLAY_BUDGET));
        portfolio.race_ladder("test", members, unknown)
    };
    assert_published_trace_ground_checks(&portfolio, &problem, outcome);
}

/// A held verdict is never dropped: when nothing else decides, the race
/// publishes it unchanged and the final boundary and strict gate judge it.
#[test]
#[timeout(120_000)]
fn an_undecided_race_publishes_the_held_verdict_unchanged() {
    let problem = parse(UNSAFE);
    let portfolio = AdaptivePortfolio::new(problem.clone(), requiring_ground_trace());
    let members = vec![
        LadderMember::new("witness_free", || {
            Some(unsafe_outcome(value_free(&problem, UNSAFE_STEPS)))
        }),
        LadderMember::new("gives_up", || None),
    ];
    let outcome = {
        let _no_replay_budget =
            crate::smt::ScopedSolveDeadline::new(Some(Instant::now() + NO_REPLAY_BUDGET));
        portfolio.race_ladder("test", members, unknown)
    };
    assert_unchanged_candidate(&outcome, "the held verdict must be published as offered");
}

/// Without the requirement (the default) a witness-free verdict decides at
/// once, unchanged: no replay holds it back. (On this unsafe loop a replay
/// would have confirmed and replaced it, as the first test shows.)
#[test]
#[timeout(120_000)]
fn without_the_requirement_a_witness_free_verdict_decides_at_once_unchanged() {
    let problem = parse(UNSAFE);
    let portfolio = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default());
    let foreground_cancelled = AtomicBool::new(false);
    let members = vec![LadderMember::new("witness_free", || {
        Some(unsafe_outcome(value_free(&problem, UNSAFE_STEPS)))
    })];
    let outcome = portfolio.race_ladder("test", members, || {
        foreground_cancelled.store(lane_cancelled_within(SAFETY), Ordering::Relaxed);
        unknown()
    });
    assert!(foreground_cancelled.load(Ordering::Relaxed));
    assert_unchanged_candidate(&outcome, "default mode must not replay");
}

/// Negative twin: on the safe twin a forged witness-free Unsafe gains
/// nothing. The replay confirms no counterexample, the undecided race
/// publishes the forged trace unchanged (no trust added), and the final
/// boundary refuses it; the safe twin itself still solves Safe.
#[test]
#[timeout(120_000)]
fn the_safe_twin_stays_safe_and_a_forged_witness_free_unsafe_is_not_admitted() {
    let problem = parse(SAFE_TWIN);
    let portfolio = AdaptivePortfolio::new(problem.clone(), requiring_ground_trace());
    let members = vec![LadderMember::new("forged", || {
        Some(unsafe_outcome(value_free(&problem, UNSAFE_STEPS)))
    })];
    let outcome = portfolio.race_ladder("test", members, unknown);
    assert_unchanged_candidate(&outcome, "a replay that confirms nothing adds nothing");
    let (result, evidence) = outcome;
    assert!(
        !matches!(
            portfolio.finalize_verified_result(result, evidence),
            VerifiedChcResult::Unsafe(_)
        ),
        "the final boundary must refuse an Unsafe on a safe problem"
    );

    let solved = AdaptivePortfolio::new(problem, requiring_ground_trace()).solve();
    assert!(
        matches!(solved, VerifiedChcResult::Safe(_)),
        "the safe twin must stay safe: {solved:?}"
    );
}

/// Deterministic-sequential mode keeps the serial ladder exactly: the
/// member's outcome is returned as it was produced.
#[test]
#[timeout(120_000)]
fn deterministic_mode_returns_the_members_outcome_unchanged() {
    let problem = parse(UNSAFE);
    let portfolio = AdaptivePortfolio::new(
        problem.clone(),
        requiring_ground_trace()
            .with_execution_mode(AdaptiveExecutionMode::DeterministicSequential),
    );
    let members = vec![LadderMember::new("witness_free", || {
        Some(unsafe_outcome(value_free(&problem, UNSAFE_STEPS)))
    })];
    let outcome = portfolio.race_ladder("test", members, unknown);
    assert_unchanged_candidate(&outcome, "the serial ladder returns the member's verdict");
}

#[test]
fn replay_budget_leaves_the_final_boundary_half_the_solve_and_is_capped() {
    assert_eq!(witness_replay_budget(None), WITNESS_REPLAY_CAP);
    assert_eq!(
        witness_replay_budget(Some(Duration::from_secs(4))),
        Duration::from_secs(2)
    );
    assert_eq!(
        witness_replay_budget(Some(Duration::from_secs(600))),
        WITNESS_REPLAY_CAP
    );
    assert!(witness_replay_budget(Some(NO_REPLAY_BUDGET)) < WITNESS_REPLAY_FLOOR);
}
