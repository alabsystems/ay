// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::QuantifiedChcCompleteValue;
use super::*;
use ay_model_check::ModelValue;
use ntest::timeout;

const WALL: Duration = Duration::from_secs(20);
const TERMS: usize = 128 * 1024 * 1024;
const KEEPS: &str = include_str!("tests/range_write_keeps_lane_0.smt2");
const WRITES: &str = include_str!("tests/range_write_writes_lane_1.smt2");
const STALE: &str = include_str!("tests/range_write_refutes_stale_lane_1.smt2");

// ModelValue intentionally has no global PartialEq; these fixtures require
// exact scalar variant, bit width, and arbitrary-precision integer identity.
fn assert_scalar_eq(actual: &ModelValue, expected: &ModelValue) {
    match (actual, expected) {
        (ModelValue::Bool(actual), ModelValue::Bool(expected)) => assert_eq!(actual, expected),
        (
            ModelValue::BitVec {
                width: actual_width,
                value: actual_value,
            },
            ModelValue::BitVec {
                width: expected_width,
                value: expected_value,
            },
        ) => {
            assert_eq!(actual_width, expected_width, "bit-vector width");
            assert_eq!(actual_value, expected_value, "bit-vector integer payload");
        }
        _ => panic!("expected matching Bool or BitVec model values"),
    }
}

fn source(text: &str) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(text).expect("unchanged original source")
}

fn remaining(end: Instant) -> Duration {
    end.saturating_duration_since(Instant::now())
}

fn original_safe(text: &str) {
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let problem = source(text);
    let QuantifiedChcCompleteResult::Safe(evidence) =
        problem.solve_with_complete_trace(remaining(end), Some(TERMS), &token)
    else {
        panic!("original 20-second source must be Safe");
    };
    assert_eq!(evidence.source_smtlib(), problem.source_smtlib());
    assert!(evidence
        .replay_obligations()
        .iter()
        .any(|row| row.smtlib.contains("(forall ")));
    assert!(evidence.recheck(&problem, remaining(end), &token));
    assert!(Instant::now() < end);
}

#[test]
#[timeout(30000)]
fn original_keeps_lane_zero_safe_with_one_twenty_second_end() {
    original_safe(KEEPS);
}

#[test]
#[timeout(30000)]
fn original_writes_lane_one_safe_with_one_twenty_second_end() {
    original_safe(WRITES);
}

#[test]
#[timeout(30000)]
fn original_stale_lane_one_unsafe_requires_complete_original_pinned_replay() {
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let problem = source(STALE);
    let QuantifiedChcCompleteResult::Unsafe(trace) =
        problem.solve_with_complete_trace(remaining(end), Some(TERMS), &token)
    else {
        panic!("original 20-second source must produce a genuine complete Unsafe");
    };
    assert_eq!(trace.source_smtlib(), problem.source_smtlib());
    assert_eq!(trace.clause_indices(), &[0, 1]);
    assert_eq!(trace.premise_steps(), &[vec![], vec![0]]);
    assert!(trace.replay_obligation().contains("(forall "));
    assert_eq!(trace.replay_obligation().matches("(assert ").count(), 1);
    let query = trace
        .bindings()
        .iter()
        .find(|binding| binding.occurrence() == 1)
        .expect("complete query occurrence-local array");
    let QuantifiedChcCompleteValue::FunctionalArray(array) = query.value() else {
        panic!("a finite sampled substitute is not the complete range witness");
    };
    let mut work = 100_000;
    let value = array
        .read_with_stop(&ModelValue::bitvec(1.into(), 64), &mut work, &mut || {
            token.is_cancelled() || Instant::now() >= end
        })
        .expect("live whole-model read");
    assert_scalar_eq(&value, &ModelValue::bitvec(9.into(), 8));
    assert!(trace.recheck(&problem, remaining(end), &token));
    assert!(Instant::now() < end);
}

#[test]
fn zero_time_zero_cap_and_cancelled_entry_never_publish_complete_results() {
    let token = CancellationToken::new();
    let problem = source(STALE);
    assert!(matches!(
        problem.solve_with_complete_trace(Duration::ZERO, None, &token),
        QuantifiedChcCompleteResult::Unknown
    ));
    assert!(matches!(
        problem.solve_with_complete_trace(WALL, Some(0), &token),
        QuantifiedChcCompleteResult::Unknown
    ));
    token.cancel();
    assert!(matches!(
        problem.solve_with_complete_trace(WALL, Some(TERMS), &token),
        QuantifiedChcCompleteResult::Unknown
    ));
}

#[test]
fn expired_ambient_owner_cannot_be_renewed_by_complete_workflow() {
    let problem = source(STALE);
    let token = CancellationToken::new();
    let _wall = ScopedSmtDeadline::install_until(Instant::now());
    assert!(matches!(
        problem.solve_with_complete_trace(WALL, Some(TERMS), &token),
        QuantifiedChcCompleteResult::Unknown
    ));
}

#[test]
fn original_cancel_observation_survives_reset_and_forbids_safe_fallback() {
    let problem = source(KEEPS);
    let token = CancellationToken::new();
    let end = Instant::now() + WALL;
    let control = SourceControl::new(end, &token);
    token.cancel();
    assert!(control.poll().is_none());
    token.reset();
    assert!(!token.is_cancelled());
    assert!(complete_inner(&problem, end, Some(TERMS), &token, &control).is_none());
}

#[test]
fn exhausted_original_source_ledger_cannot_grant_safe_fallback() {
    let problem = source(KEEPS);
    let token = CancellationToken::new();
    let end = Instant::now() + WALL;
    let control = SourceControl::new(end, &token);
    assert!(control.bytes(usize::MAX).is_none());
    assert!(complete_inner(&problem, end, Some(TERMS), &token, &control).is_none());
}

#[test]
fn complete_workflow_restores_deadline_and_term_cap_on_refusal() {
    let problem = source(STALE);
    let token = CancellationToken::new();
    let end = Instant::now() + WALL;
    let _wall = ScopedSmtDeadline::install_until(end);
    let _cap = SmtContext::scoped_thread_term_memory_budget(Some(17));
    assert!(matches!(
        problem.solve_with_complete_trace(WALL, Some(0), &token),
        QuantifiedChcCompleteResult::Unknown
    ));
    assert_eq!(crate::smt::deadline::current_smt_deadline(), Some(end));
    assert_eq!(SmtContext::new().term_memory_budget, Some(17));
}

mod fill;
