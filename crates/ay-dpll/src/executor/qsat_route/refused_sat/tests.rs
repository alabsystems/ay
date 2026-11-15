// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private routing fixtures are DATA, not quantified SAT credentials.

use super::super::QsatMemo;
use super::*;
use ay_core::resource::{current_check_stop, enter_check_stop, CheckStop};
use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

/// Arm the exact private gate-refused handoff over a simple authored formula.
fn handed_off() -> Executor {
    let mut executor = Executor::new();
    let commands =
        ay_frontend::parse("(set-logic QF_UF) (declare-const p Bool) (assert p)").unwrap();
    executor.execute_all(&commands).unwrap();
    executor.begin_external_decision_query(false);
    executor.qsat_route.applied = true;
    executor.qsat_route.sat_handed_off = true;
    executor.qsat_route.memo = Some(QsatMemo {
        roots: executor.ctx.assertions.clone(),
        published: true,
        stats: Vec::new(),
    });
    executor.last_result = Some(SolveResult::Unknown);
    executor.last_unknown_reason = Some(UnknownReason::SelfCheckRejected);
    executor
}

fn assert_withdrawn_without_retry(executor: &Executor) {
    assert!(!executor.qsat_route.sat_handed_off);
    assert!(!executor.qsat_route.applied);
    assert!(executor.qsat_route.strategy.is_none());
    assert!(!executor.qsat_route.memo.as_ref().unwrap().published);
    assert_eq!(
        executor.last_statistics.get_string("qsat.publish"),
        Some("sat-gate-refused"),
    );
    assert_eq!(
        executor
            .last_statistics
            .get_int("qsat.refused_sat_resolves"),
        None
    );
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert!(executor.last_model.is_none());
    assert!(executor.last_sat_certificate.is_none());
}

#[test]
fn callback_only_original_refusal_skips_retry_without_guessing_a_typed_cause() {
    let mut executor = handed_off();
    let raw = Arc::new(AtomicBool::new(false));
    let end = Instant::now() + Duration::from_secs(20);
    executor.set_solve_controls(Some(Arc::clone(&raw)), Some(end));
    let attempt = executor.evaluation_attempt();
    attempt.add_conflicts(13);
    let _stop = enter_check_stop(Arc::new(|| true));
    assert_eq!(executor.external_stop_reason(), None);
    assert_eq!(
        executor
            .qsat_refused_sat_resolve(SolveResult::Unknown)
            .unwrap(),
        SolveResult::Unknown,
    );
    assert_withdrawn_without_retry(&executor);
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::SelfCheckRejected)
    );
    assert!(!raw.load(Ordering::Relaxed));
    assert_eq!(executor.solve_deadline.get(), Some(end));
    assert!(executor.evaluation_attempt().is_same_attempt(&attempt));
    assert_eq!(attempt.consumed_conflicts(), 13);
}

#[test]
fn consumed_callback_handoff_cannot_retry_after_the_original_flag_resets() {
    let mut executor = handed_off();
    let raw = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&raw));
    let original = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&original);
    let scope = enter_check_stop(Arc::new(move || observed.load(Ordering::Relaxed)));
    assert_eq!(executor.external_stop_reason(), None);
    assert_eq!(
        executor
            .qsat_refused_sat_resolve(SolveResult::Unknown)
            .unwrap(),
        SolveResult::Unknown,
    );
    assert_withdrawn_without_retry(&executor);
    original.store(false, Ordering::Relaxed);
    drop(scope);
    assert_eq!(
        executor
            .qsat_refused_sat_resolve(SolveResult::Unknown)
            .unwrap(),
        SolveResult::Unknown,
    );
    assert_withdrawn_without_retry(&executor);
    assert!(!raw.load(Ordering::Relaxed));
}

#[test]
fn consumed_executor_raw_handoff_cannot_retry_after_the_original_flag_resets() {
    let mut executor = handed_off();
    let raw = Arc::new(AtomicBool::new(true));
    executor.set_interrupt(Arc::clone(&raw));
    let _scope = enter_check_stop(Arc::new(|| false));
    assert_eq!(
        executor.external_stop_reason(),
        Some(UnknownReason::Interrupted)
    );
    assert_eq!(
        executor
            .qsat_refused_sat_resolve(SolveResult::Unknown)
            .unwrap(),
        SolveResult::Unknown,
    );
    assert_withdrawn_without_retry(&executor);
    assert!(raw.load(Ordering::Relaxed));
    raw.store(false, Ordering::Relaxed);
    assert_eq!(executor.external_stop_reason(), None);
    assert_eq!(
        executor
            .qsat_refused_sat_resolve(SolveResult::Unknown)
            .unwrap(),
        SolveResult::Unknown,
    );
    assert_withdrawn_without_retry(&executor);
    assert!(!raw.load(Ordering::Relaxed));
}

#[test]
fn healthy_handoff_uses_primary_emission_without_renewing_the_original_owner() {
    let mut executor = handed_off();
    let end = Instant::now() + Duration::from_secs(20);
    let raw = Arc::new(AtomicBool::new(false));
    executor.set_solve_controls(Some(Arc::clone(&raw)), Some(end));
    let original: CheckStop = Arc::new(|| false);
    let _scope = enter_check_stop(Arc::clone(&original));
    let attempt = executor.evaluation_attempt();
    attempt.add_conflicts(17);
    let work = attempt.functional_work_counter();
    work.store(29, Ordering::Relaxed);
    assert_eq!(
        executor
            .qsat_refused_sat_resolve(SolveResult::Unknown)
            .unwrap(),
        SolveResult::Sat,
    );
    // This real ground verdict crossed the unchanged emission funnel.
    assert!(executor.last_model.is_some());
    assert!(executor.last_sat_certificate.is_some());
    assert_eq!(
        executor
            .last_statistics
            .get_int("qsat.refused_sat_resolves"),
        Some(1)
    );
    assert!(!executor.qsat_route.sat_handed_off);
    assert!(!executor.qsat_route.applied);
    assert!(!executor.qsat_route.memo.as_ref().unwrap().published);
    assert_eq!(executor.solve_deadline.get(), Some(end));
    assert_eq!(executor.certification_deadline.get(), Some(end));
    assert!(Arc::ptr_eq(
        executor.solve_interrupt.as_ref().unwrap(),
        &raw
    ));
    assert!(!raw.load(Ordering::Relaxed));
    assert!(Arc::ptr_eq(
        &current_check_stop().unwrap().unwrap(),
        &original
    ));
    assert!(executor.evaluation_attempt().is_same_attempt(&attempt));
    assert!(attempt.consumed_conflicts() >= 17);
    assert!(Arc::ptr_eq(
        &executor.evaluation_attempt().functional_work_counter(),
        &work
    ));
    assert!(work.load(Ordering::Relaxed) >= 29);
}

#[test]
fn a_retained_evaluation_refusal_is_not_rearmed_by_the_legacy_retry() {
    let mut executor = handed_off();
    let end = Instant::now() + Duration::from_secs(20);
    executor.set_deadline(Some(end));
    let attempt = executor.evaluation_attempt();
    attempt.add_conflicts(31);
    executor.record_evaluation_stop(crate::executor_types::UnknownOrigin::MemoryBudget);
    let _scope = enter_check_stop(Arc::new(|| false));
    assert_eq!(
        executor
            .qsat_refused_sat_resolve(SolveResult::Unknown)
            .unwrap(),
        SolveResult::Unknown,
    );
    assert!(executor.evaluation_attempt().is_same_attempt(&attempt));
    assert_eq!(attempt.consumed_conflicts(), 31);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(crate::executor_types::UnknownOrigin::MemoryBudget),
    );
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownReason::MemoryLimit)
    );
    assert!(executor.last_model.is_none());
    assert!(executor.last_sat_certificate.is_none());
    assert_eq!(executor.solve_deadline.get(), Some(end));
    assert_eq!(executor.certification_deadline.get(), Some(end));
    assert!(!executor.qsat_route.sat_handed_off);
}

#[test]
fn typed_stop_handoffs_keep_their_original_reason_and_never_retry() {
    for reason in [
        UnknownReason::Timeout,
        UnknownReason::ResourceLimit,
        UnknownReason::MemoryLimit,
        UnknownReason::Interrupted,
    ] {
        let mut executor = handed_off();
        executor.last_unknown_reason = Some(reason);
        let _scope = enter_check_stop(Arc::new(|| false));
        assert_eq!(
            executor
                .qsat_refused_sat_resolve(SolveResult::Unknown)
                .unwrap(),
            SolveResult::Unknown,
        );
        assert_withdrawn_without_retry(&executor);
        assert_eq!(executor.last_unknown_reason, Some(reason));
    }
}
