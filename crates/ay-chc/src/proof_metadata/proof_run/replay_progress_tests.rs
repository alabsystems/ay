// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::engine_result::ValidationEvidence;
use crate::ground_derivation::{
    validate_ground_derivation, GroundDerivation, GroundDerivationStep,
};
use crate::{ClauseBody, Counterexample, HornClause, VerifiedCounterexample};
use std::time::Duration;

mod cancellation_tests;

const REPLAY_BUDGET: Duration = Duration::from_secs(60);
const SOLVE_ELAPSED: Duration = Duration::from_secs(3);

fn run() -> ChcPdrProofRun {
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        true,
    ))));
    let derivation = GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: Default::default(),
            premises: Vec::new(),
        }],
        query_step: 0,
    };
    validate_ground_derivation(&problem, &derivation).unwrap();
    let counterexample = Counterexample::new(Vec::new()).with_ground_derivation(derivation);
    ChcPdrProofRun::new(
        problem,
        VerifiedChcResult::Unsafe(VerifiedCounterexample::from_validated(counterexample)),
        "report-progress-test",
    )
}

fn report(run: ChcPdrProofRun, solve_cancelled: bool) -> ChcProofRunWithBudgetReport {
    ChcProofRunWithBudgetReport::from_direct_pdr(
        run,
        Some(REPLAY_BUDGET),
        SOLVE_ELAPSED,
        solve_cancelled,
    )
}

fn successful_poll_count() -> usize {
    let mut calls = 0;
    let checked =
        report(run(), false).with_checked_replay_with_progress(REPLAY_BUDGET, &mut || {
            calls += 1;
            true
        });
    assert!(checked.checked_replay().is_some());
    assert!(calls > 2);
    calls
}

#[test]
fn always_continue_matches_legacy_checked_evidence() {
    let original = run();
    let legacy = report(original.clone(), false).with_checked_replay(REPLAY_BUDGET);
    let current =
        report(original, false).with_checked_replay_with_progress(REPLAY_BUDGET, &mut || true);
    assert_eq!(
        legacy.checked_replay().unwrap().summary().identity_sha256(),
        current
            .checked_replay()
            .unwrap()
            .summary()
            .identity_sha256()
    );
    assert_eq!(
        legacy.proof_run().metadata().to_json_value(),
        current.proof_run().metadata().to_json_value()
    );
    assert_eq!(legacy.stop_reason(), current.stop_reason());
    assert_eq!(legacy.adaptive_trace(), current.adaptive_trace());
    assert!(current.budget_report().total_elapsed >= SOLVE_ELAPSED);
}

#[test]
fn precancellation_preserves_exact_solve_evidence_and_telemetry() {
    for solve_cancelled in [false, true] {
        let original = run();
        let retained = original.clone();
        let metadata = original.metadata().to_json_value();
        let pending = report(original, solve_cancelled);
        let trace = pending.adaptive_trace().clone();
        let mut calls = 0;
        let stopped = pending.with_checked_replay_with_progress(REPLAY_BUDGET, &mut || {
            calls += 1;
            false
        });
        assert_eq!(calls, 1);
        assert!(stopped.checked_replay().is_none());
        assert!(stopped.proof_run().result().is_unsafe());
        assert!(std::ptr::eq(
            retained.problem(),
            stopped.proof_run().problem()
        ));
        assert_eq!(stopped.proof_run().metadata().to_json_value(), metadata);
        assert_eq!(stopped.adaptive_trace(), &trace);
        assert_eq!(stopped.stop_reason(), ChcProofRunStopReason::Definitive);
        assert_eq!(stopped.cancellation_requested_at_return(), solve_cancelled);
        assert!(stopped.budget_report().entries.is_empty());
        assert!(stopped.budget_report().total_elapsed >= SOLVE_ELAPSED);
    }
}

#[test]
fn every_callback_refusal_is_terminal_and_retry_can_admit() {
    let total = successful_poll_count();
    let original = run();
    let metadata = original.metadata().to_json_value();
    for stop_at in 1..=total {
        let mut calls = 0;
        let stopped = report(original.clone(), false).with_checked_replay_with_progress(
            REPLAY_BUDGET,
            &mut || {
                calls += 1;
                calls != stop_at
            },
        );
        assert_eq!(calls, stop_at, "refusal cannot be polled again");
        assert!(stopped.checked_replay().is_none(), "poll {stop_at}");
        assert_eq!(stopped.proof_run().metadata().to_json_value(), metadata);
        assert_eq!(stopped.stop_reason(), ChcProofRunStopReason::Definitive);
        assert!(!stopped.cancellation_requested_at_return());
    }
    assert!(report(original, false)
        .with_checked_replay_with_progress(REPLAY_BUDGET, &mut || true)
        .checked_replay()
        .is_some());
}

#[test]
fn existing_checked_report_is_an_exact_noop_even_when_cancelled() {
    let checked = report(run(), false).with_checked_replay(REPLAY_BUDGET);
    let identity = checked
        .checked_replay()
        .unwrap()
        .summary()
        .identity_sha256();
    let elapsed = checked.budget_report().total_elapsed;
    let trace = checked.adaptive_trace().clone();
    let unchanged = checked.with_checked_replay_with_progress(Duration::ZERO, &mut || {
        panic!("an already checked report does not start another attempt")
    });
    assert_eq!(unchanged.budget_report().total_elapsed, elapsed);
    assert_eq!(unchanged.adaptive_trace(), &trace);
    assert_eq!(
        unchanged
            .checked_replay()
            .unwrap()
            .summary()
            .identity_sha256(),
        identity
    );
    assert!(!unchanged.cancellation_requested_at_return());
}

#[test]
fn ineligible_report_never_calls_progress_or_changes_elapsed() {
    let unknown = ChcPdrProofRun::new(
        ChcProblem::new(),
        VerifiedChcResult::from_validated(
            crate::ChcEngineResult::Unknown,
            ValidationEvidence::FullVerification,
        ),
        "report-progress-unknown",
    );
    let pending = report(unknown, true);
    let metadata = pending.proof_run().metadata().to_json_value();
    let stopped = pending.with_checked_replay_with_progress(REPLAY_BUDGET, &mut || {
        panic!("ineligible reports do not start replay")
    });
    assert_eq!(stopped.budget_report().total_elapsed, SOLVE_ELAPSED);
    assert_eq!(stopped.proof_run().metadata().to_json_value(), metadata);
    assert!(stopped.checked_replay().is_none());
    assert_eq!(
        stopped.stop_reason(),
        ChcProofRunStopReason::ExternallyCancelled
    );
    assert!(stopped.cancellation_requested_at_return());
}

#[test]
fn zero_budget_never_upgrades_and_elapsed_saturates() {
    let mut pending = report(run(), false);
    let metadata = pending.proof_run().metadata().to_json_value();
    pending.budget_report.total_elapsed = Duration::MAX;
    let stopped = pending.with_checked_replay_with_progress(Duration::ZERO, &mut || true);
    assert!(stopped.checked_replay().is_none());
    assert_eq!(stopped.proof_run().metadata().to_json_value(), metadata);
    assert_eq!(stopped.budget_report().total_elapsed, Duration::MAX);
}

#[test]
fn classified_callback_panics_at_entry_and_final_poll_retain_original_report() {
    for stop_at in [1, successful_poll_count()] {
        let original = run();
        let metadata = original.metadata().to_json_value();
        let mut calls = 0;
        let stopped =
            report(original, false).with_checked_replay_with_progress(REPLAY_BUDGET, &mut || {
                calls += 1;
                assert_ne!(calls, stop_at, "BUG: synthetic replay callback panic");
                true
            });
        assert_eq!(calls, stop_at);
        assert!(stopped.checked_replay().is_none());
        assert_eq!(stopped.proof_run().metadata().to_json_value(), metadata);
        assert!(stopped.budget_report().total_elapsed >= SOLVE_ELAPSED);
    }
}

#[test]
fn ordinary_callback_panic_preserves_existing_unwind_policy() {
    let total = successful_poll_count();
    let mut calls = 0;
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        report(run(), false).with_checked_replay_with_progress(REPLAY_BUDGET, &mut || {
            calls += 1;
            assert_ne!(calls, total, "ordinary caller failure");
            true
        })
    }));
    assert!(outcome.is_err(), "ordinary caller panics are not swallowed");
    assert_eq!(calls, total);
}

/// Under an effort the stop reason is the run node's (P4a slice 8): the
/// count's stop is `EffortExhausted` whatever the wall clock read, and a
/// backstop is never the count's. Here the wall says the budget elapsed and
/// no token was set, so without an effort the reason would be
/// `BudgetExhausted` every time.
#[test]
fn under_an_effort_the_stop_reason_is_the_run_nodes_stop() {
    use ay_core::resource::Exhausted;
    let undecided = || {
        let mut problem = ChcProblem::new();
        problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
            false,
        ))));
        ChcPdrProofRun::new(
            problem,
            VerifiedChcResult::unknown_candidate_not_admitted(),
            "effort-stop-test",
        )
    };
    for (stop, expected) in [
        (
            Some(Exhausted::Rlimit),
            ChcProofRunStopReason::EffortExhausted,
        ),
        (
            Some(Exhausted::Deadline),
            ChcProofRunStopReason::BudgetExhausted,
        ),
        (
            Some(Exhausted::Cancelled),
            ChcProofRunStopReason::ExternallyCancelled,
        ),
        (Some(Exhausted::Memory), ChcProofRunStopReason::Inconclusive),
        (None, ChcProofRunStopReason::Inconclusive),
    ] {
        let work = crate::ChcRunWork {
            effort: Some(1_000),
            stop,
            ..crate::ChcRunWork::default()
        };
        let report = ChcProofRunWithBudgetReport::from_direct_pdr(
            undecided().with_work(Some(work)),
            Some(Duration::from_millis(1)),
            SOLVE_ELAPSED,
            false,
        );
        assert_eq!(report.stop_reason(), expected, "{stop:?}");
    }
    let without_effort = ChcProofRunWithBudgetReport::from_direct_pdr(
        undecided().with_work(Some(crate::ChcRunWork::default())),
        Some(Duration::from_millis(1)),
        SOLVE_ELAPSED,
        false,
    );
    assert_eq!(
        without_effort.stop_reason(),
        ChcProofRunStopReason::BudgetExhausted
    );
    let decided = ChcProofRunWithBudgetReport::from_direct_pdr(
        run().with_work(Some(crate::ChcRunWork {
            effort: Some(1_000),
            stop: Some(Exhausted::Rlimit),
            ..crate::ChcRunWork::default()
        })),
        Some(REPLAY_BUDGET),
        SOLVE_ELAPSED,
        false,
    );
    assert_eq!(decided.stop_reason(), ChcProofRunStopReason::Definitive);
}
