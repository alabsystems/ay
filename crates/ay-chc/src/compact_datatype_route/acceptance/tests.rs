// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ChcParser;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

fn source() -> ChcProblem {
    ChcParser::parse(
        "(set-logic HORN)
         (declare-datatype Pair ((pair (read (_ BitVec 8)) (unread Bool))))
         (declare-var a Pair) (declare-var b Pair)
         (declare-rel P (Pair))
         (rule (P a))
         (rule (=> (and (P b) (= (read b) #x05)) false))",
    )
    .expect("original product source")
}

fn candidate(problem: &ChcProblem) -> Counterexample {
    match run(problem, None, None, None) {
        Some(ChcEngineResult::Unsafe(candidate)) => candidate,
        other => panic!("requires actual original Unsafe, got {other:?}"),
    }
}

#[test]
fn accepted_candidate_replays_original_and_has_no_placeholder_trace() {
    let problem = source();
    let candidate = candidate(&problem);
    let confirmed = confirm(&problem, &candidate, None, None, None).expect("fresh replay");
    assert!(confirmed.has_compact_ground_derivation());
    assert!(confirmed
        .ground_checks_unsafe(&problem)
        .expect("original replay"));
    let summary = confirmed.to_certificate(&problem);
    assert!(summary.contains("not a standalone certificate"));
    assert!(summary.contains("No expanded legacy state trace"));
    let mut changed = source();
    changed.clauses_mut()[1].body.constraint = Some(crate::ChcExpr::Bool(false));
    assert!(confirm(&changed, &candidate, None, None, None).is_none());
}

#[test]
fn new_caller_ambient_deadline_is_terminal_for_retained_evidence() {
    let problem = source();
    let candidate = candidate(&problem);
    {
        let _deadline = crate::smt::deadline::ScopedSmtDeadline::install(Duration::ZERO);
        assert!(!candidate
            .ground_checks_unsafe(&problem)
            .expect("stopped replay"));
    }
    assert!(confirm(&problem, &candidate, None, None, None).is_none());
}

#[test]
fn new_one_shot_callback_refusal_cannot_revive_after_scope() {
    let problem = source();
    let candidate = candidate(&problem);
    let armed = Arc::new(AtomicBool::new(true));
    {
        let signal = Arc::clone(&armed);
        let _scope = enter_check_stop(Arc::new(move || signal.swap(false, Ordering::AcqRel)));
        assert!(confirm(&problem, &candidate, None, None, None).is_none());
    }
    assert!(!armed.load(Ordering::Acquire));
    assert!(confirm(&problem, &candidate, None, None, None).is_none());
}

#[test]
fn zero_original_guard_is_unknown_not_inapplicability() {
    let problem = source();
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(0)));
    let _scope = guard.enter();
    assert!(matches!(
        run(&problem, None, None, None),
        Some(ChcEngineResult::Unknown)
    ));
}

/// A source without datatypes is outside this route even when the caller is
/// already stopped: the route must not end the caller's solve as its own
/// terminal Unknown (the adaptive report then lost every dispatch and round
/// observation of a precancelled solve).
#[test]
fn precancelled_source_without_datatypes_is_inapplicable_not_unknown() {
    let problem = ChcParser::parse(
        "(set-logic HORN)
         (declare-rel P ((_ BitVec 8)))
         (declare-var x (_ BitVec 8))
         (rule (=> (= x #x00) (P x)))
         (rule (=> (and (P x) (= x #x05)) false))",
    )
    .expect("scalar source");
    assert!(problem.datatype_defs().is_empty());
    let cancellation = crate::CancellationToken::new();
    cancellation.cancel();
    assert!(run(&problem, None, Some(&cancellation), None).is_none());
}

/// Negative twin: a datatype source under the same stopped caller is still
/// this route's terminal Unknown, never inapplicability and never Unsafe.
#[test]
fn precancelled_datatype_source_remains_terminal_unknown() {
    let problem = source();
    let cancellation = crate::CancellationToken::new();
    cancellation.cancel();
    assert!(matches!(
        run(&problem, None, Some(&cancellation), None),
        Some(ChcEngineResult::Unknown)
    ));
}

#[test]
fn new_caller_interrupt_and_memory_cannot_bypass_retained_owner() {
    let problem = source();
    let first = candidate(&problem);
    {
        let _memory = crate::SmtContext::scoped_thread_term_memory_budget(Some(1));
        assert!(confirm(&problem, &first, None, None, None).is_none());
    }
    assert!(confirm(&problem, &first, None, None, None).is_none());
    let candidate = candidate(&problem);
    let flag = Arc::new(AtomicBool::new(true));
    let _lane = crate::smt::deadline::ScopedLaneCancellation::install(
        crate::CancellationToken::new(),
        Some(flag),
    );
    assert!(confirm(&problem, &candidate, None, None, None).is_none());
}

#[test]
fn positive_later_guard_refuses_actual_confirmation_and_export_stickily() {
    let problem = source();
    for export in [false, true] {
        let candidate = candidate(&problem);
        let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(1)));
        {
            let _scope = guard.enter();
            if export {
                assert!(candidate
                    .compact_ground_derivation_artifact(&problem)
                    .is_err());
            } else {
                assert!(confirm(&problem, &candidate, None, None, None).is_none());
            }
        }
        assert!(guard.ticks() > 0, "positive caller credit must be spent");
        assert!(confirm(&problem, &candidate, None, None, None).is_none());
    }
}

#[test]
fn export_keeps_later_memory_cap_after_callback_removes_scope() {
    let problem = source();
    let candidate = candidate(&problem);
    let used = candidate
        .compact_evidence()
        .expect("evidence")
        .owner()
        .admitted_storage_for_test();
    // Restore the thread even though the callback deliberately removes an
    // outer scope while the exporter has installed its own inner one.
    let _restore = crate::SmtContext::scoped_thread_term_memory_budget(None);
    let mut scope = Some(crate::SmtContext::scoped_thread_term_memory_budget(Some(
        used + 64,
    )));
    let mut called = false;
    let result = candidate.compact_ground_derivation_artifact_with_progress(&problem, &mut || {
        called = true;
        drop(scope.take());
        true
    });
    assert!(called, "must exercise removal, not refuse before callback");
    assert!(scope.is_none());
    assert!(result.is_err());
    assert!(confirm(&problem, &candidate, None, None, None).is_none());
}

#[test]
fn adequate_later_memory_export_preserves_exact_artifact_bytes() {
    let problem = source();
    let expected = candidate(&problem)
        .compact_ground_derivation_artifact(&problem)
        .expect("normal export")
        .into_bytes();
    let candidate = candidate(&problem);
    let _restore = crate::SmtContext::scoped_thread_term_memory_budget(None);
    let mut scope = Some(crate::SmtContext::scoped_thread_term_memory_budget(Some(
        4 * 1024 * 1024,
    )));
    let actual = candidate
        .compact_ground_derivation_artifact_with_progress(&problem, &mut || {
            drop(scope.take());
            true
        })
        .expect("adequately bounded export")
        .into_bytes();
    assert!(scope.is_none());
    assert_eq!(actual, expected);
}

fn adaptive_report(
    problem: ChcProblem,
    cancellation: Option<&crate::CancellationToken>,
) -> (
    crate::VerifiedChcResult,
    Vec<(&'static str, crate::AdaptiveStrategyOutcome)>,
) {
    let mut portfolio = crate::adaptive::AdaptivePortfolio::new(
        problem,
        crate::adaptive::AdaptiveConfig::test_default()
            .with_execution_mode(crate::adaptive::AdaptiveExecutionMode::DeterministicSequential),
    );
    if let Some(cancellation) = cancellation {
        portfolio = portfolio.with_cancellation_parent(cancellation);
    }
    let (result, report) = portfolio.solve_with_adaptive_report();
    let stages = report
        .strategy_trace()
        .observations()
        .iter()
        .map(|observation| (observation.stage, observation.outcome.clone()))
        .collect();
    (result, stages)
}

/// A precancelled datatype source is reported like any other stopped
/// invocation: the ordinary pre-dispatch check observes the stop.
#[test]
fn adaptive_report_observes_a_precancelled_datatype_source() {
    let cancellation = crate::CancellationToken::new();
    cancellation.cancel();
    let (result, stages) = adaptive_report(source(), Some(&cancellation));
    assert!(matches!(result, crate::VerifiedChcResult::Unknown(_)));
    assert!(stages
        .iter()
        .any(|(stage, _)| *stage == "budget_or_cancellation_before_dispatch"));
    assert!(!stages
        .iter()
        .any(|(stage, _)| *stage == "compact_datatype_route"));
}

/// A live datatype source decided by the route names the route.
#[test]
fn adaptive_report_names_the_compact_route_that_decided() {
    let (result, stages) = adaptive_report(source(), None);
    assert!(matches!(result, crate::VerifiedChcResult::Unsafe(_)));
    assert!(stages
        .iter()
        .any(|(stage, outcome)| *stage == "compact_datatype_route"
            && *outcome == crate::AdaptiveStrategyOutcome::Unsafe));
}

mod selector_overloads;
