// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::executor::model::{eval_memo, EvalMemoSession, EvalValue};
use crate::executor_types::SolveResult;
use ay_core::Sort;
use std::sync::atomic::{AtomicBool, Ordering};

mod stop_flag;

#[test]
fn decision_retries_keep_the_first_stop_and_conflict_debit() {
    let mut executor = Executor::new();
    let attempt = executor.evaluation_attempt();
    attempt.add_conflicts(13);
    attempt.record_stop(UnknownOrigin::InterruptFlag);
    executor.begin_public_solve(false);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    assert_eq!(executor.evaluation_attempt().consumed_conflicts(), 13);
    executor.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
    executor.begin_external_decision_query(false);
    assert_eq!(executor.evaluation_stop_origin(), None);
    assert_eq!(executor.evaluation_attempt().consumed_conflicts(), 0);
    assert_eq!(attempt.stop_origin(), Some(UnknownOrigin::InterruptFlag));
}

#[test]
fn upper_theory_checkpoint_consumes_the_retained_first_origin() {
    let mut executor = Executor::new();
    executor.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
    let flag = Arc::new(AtomicBool::new(true));
    executor.set_interrupt(flag.clone());
    assert!(executor.should_abort_theory_loop());
    assert_eq!(executor.last_result, Some(SolveResult::Unknown));
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownOrigin::DeterministicResourceBudget.reason())
    );
    executor.finalize_unknown_diagnostics();
    assert_eq!(
        executor.last_unknown_reason,
        Some(UnknownOrigin::DeterministicResourceBudget.reason())
    );
    flag.store(false, Ordering::Relaxed);
    executor.begin_public_solve(false);
    assert!(executor.should_abort_theory_loop());
    executor.begin_external_decision_query(false);
    assert!(!executor.should_abort_theory_loop());
}

#[test]
fn nested_reads_share_their_attempt_and_restore_the_decision_owner() {
    let executor = Executor::new();
    executor.evaluation_attempt().add_conflicts(17);
    executor.record_evaluation_stop(UnknownOrigin::SolveDeadline);
    let outer = executor.begin_external_evaluation_read();
    assert_eq!(executor.evaluation_stop_origin(), None);
    executor.evaluation_attempt().add_conflicts(3);
    let inner = executor.begin_external_evaluation_read();
    executor.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    drop(outer); // Ownership does not depend on lexical drop order.
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::MemoryBudget)
    );
    assert_eq!(executor.evaluation_attempt().consumed_conflicts(), 3);
    drop(inner);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::SolveDeadline)
    );
    assert_eq!(executor.evaluation_attempt().consumed_conflicts(), 17);
    let _fresh = executor.begin_external_evaluation_read();
    assert_eq!(executor.evaluation_stop_origin(), None);
}

#[test]
fn read_unwind_restores_decision_but_does_not_rearm_a_retained_attempt() {
    let executor = Executor::new();
    let decision = executor.evaluation_attempt();
    decision.add_conflicts(7);
    let mut retained = None;
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _read = executor.begin_external_evaluation_read();
        retained = Some(executor.evaluation_attempt());
        executor.record_evaluation_stop(UnknownOrigin::InterruptFlag);
        panic!("test read unwind");
    }));
    assert!(result.is_err());
    assert_eq!(executor.evaluation_stop_origin(), None);
    assert_eq!(executor.evaluation_attempt().consumed_conflicts(), 7);
    assert_eq!(
        retained.unwrap().stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
}

#[test]
fn internal_decision_during_a_read_cannot_replenish_either_owner() {
    let mut executor = Executor::new();
    executor.record_evaluation_stop(UnknownOrigin::SolveDeadline);
    executor.evaluation_attempt().add_conflicts(19);
    let outer = executor.begin_external_evaluation_read();
    let inner = executor.begin_external_evaluation_read();
    executor.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    executor.evaluation_attempt().add_conflicts(5);
    executor.begin_external_decision_query(false);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::MemoryBudget)
    );
    assert_eq!(executor.evaluation_attempt().consumed_conflicts(), 5);
    drop(inner);
    drop(outer);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::SolveDeadline)
    );
    assert_eq!(executor.evaluation_attempt().consumed_conflicts(), 19);
}

#[test]
fn attempt_isolation_and_conflict_accounting_are_not_thread_global() {
    let first = Executor::new();
    let second = Executor::new();
    first.record_evaluation_stop(UnknownOrigin::DeterministicResourceBudget);
    first.evaluation_attempt().add_conflicts(u64::MAX);
    first.evaluation_attempt().add_conflicts(1);
    assert_eq!(first.evaluation_attempt().consumed_conflicts(), u64::MAX);
    assert_eq!(second.evaluation_stop_origin(), None);
    assert_eq!(second.evaluation_attempt().consumed_conflicts(), 0);
}

#[test]
fn nested_temporary_arenas_share_the_remaining_source_allowance() {
    let attempt = EvaluationAttempt::default();
    let outer = attempt.temporary_arena().unwrap();
    assert_eq!(outer.check_usage(100, 40, Some(200)), Ok(()));
    let inner = attempt.temporary_arena().unwrap();
    assert_eq!(inner.check_usage(100, 60, Some(200)), Ok(()));
    assert_eq!(
        inner.check_usage(100, 61, Some(200)),
        Err(UnknownOrigin::MemoryBudget)
    );
    drop(inner);
    assert_eq!(
        outer.check_usage(100, 0, None),
        Err(UnknownOrigin::MemoryBudget)
    );
}

#[test]
fn arena_drop_releases_capacity_and_arithmetic_overflow_refuses() {
    let attempt = EvaluationAttempt::default();
    let outer = attempt.temporary_arena().unwrap();
    let inner = attempt.temporary_arena().unwrap();
    inner.check_usage(100, 90, Some(200)).unwrap();
    drop(inner);
    assert_eq!(outer.check_usage(100, 100, Some(200)), Ok(()));
    assert_eq!(
        outer.check_usage(usize::MAX, 1, Some(usize::MAX)),
        Err(UnknownOrigin::MemoryBudget)
    );
}

#[test]
fn releasing_an_old_read_arena_does_not_release_a_new_read_slot() {
    let executor = Executor::new();
    let read = executor.begin_external_evaluation_read();
    let old = executor.evaluation_attempt().temporary_arena().unwrap();
    old.check_usage(10, 90, Some(100)).unwrap();
    drop(read);
    let _fresh = executor.begin_external_evaluation_read();
    let current = executor.evaluation_attempt().temporary_arena().unwrap();
    current.check_usage(10, 90, Some(100)).unwrap();
    drop(old);
    let sibling = executor.evaluation_attempt().temporary_arena().unwrap();
    assert_eq!(
        sibling.check_usage(10, 1, Some(100)),
        Err(UnknownOrigin::MemoryBudget)
    );
}

#[test]
fn a_stop_blocks_preexisting_memo_values_until_an_explicit_fresh_attempt() {
    let mut executor = Executor::new();
    let term = executor.ctx.terms.mk_bool(true);
    let model = executor.completed_default_model();
    let _memo = EvalMemoSession::new();
    eval_memo::seed_for_test(term, EvalValue::Bool(true));
    executor.record_evaluation_stop(UnknownOrigin::InterruptFlag);
    assert!(matches!(
        executor.evaluate_term(&model, term),
        EvalValue::Unknown
    ));
    assert_eq!(eval_memo::get(term), Some(EvalValue::Bool(true)));
    let _read = executor.begin_external_evaluation_read();
    assert_eq!(executor.evaluate_term(&model, term), EvalValue::Bool(true));
}

#[test]
fn output_fallback_cannot_revive_a_read_after_a_live_interrupt_clears() {
    let mut executor = Executor::new();
    let flag = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(flag.clone());
    let term = executor.ctx.terms.mk_bool(true);
    let model = executor.completed_default_model();
    let read = executor.begin_external_evaluation_read();
    flag.store(true, Ordering::Relaxed);
    assert!(matches!(
        executor.evaluate_term(&model, term),
        EvalValue::Unknown
    ));
    flag.store(false, Ordering::Relaxed);
    assert!(executor.term_value_string(&model, term).is_err());
    assert!(executor
        .checked_evaluation_output(|| "true".into())
        .starts_with("(error "));
    drop(read);
    let _fresh = executor.begin_external_evaluation_read();
    assert_eq!(executor.term_value_string(&model, term), Ok("true".into()));
}

#[test]
fn real_public_sat_survives_a_cancelled_text_read_and_fresh_retry_succeeds() {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(
        "(set-option :produce-models true) (declare-const p Bool) (assert p) (check-sat)",
    )
    .unwrap();
    let outputs = executor.execute_all(&commands).unwrap();
    assert_eq!(outputs.last().map(String::as_str), Some("sat"));
    let flag = Arc::new(AtomicBool::new(true));
    executor.set_interrupt(flag.clone());
    for text in ["(get-value (p))", "(get-model)", "(eval p)"] {
        let commands = ay_frontend::parse(text).unwrap();
        let output = executor.execute_all(&commands).unwrap();
        assert!(output[0].starts_with("(error "), "{text}: {output:?}");
        assert_eq!(executor.last_result, Some(SolveResult::Sat));
        assert_eq!(executor.evaluation_stop_origin(), None);
    }
    flag.store(false, Ordering::Relaxed);
    let commands = ay_frontend::parse("(get-value (p))").unwrap();
    assert_eq!(executor.execute_all(&commands).unwrap(), vec!["((p true))"]);
}

#[test]
fn parked_decision_is_not_charged_with_a_subset_attempts_stop() {
    let mut executor = Executor::new();
    executor.begin_public_solve(false);
    executor.begin_external_decision_query(false);
    let outer = executor.evaluation_attempt();
    let parked = executor.park_evaluation_decision();
    assert!(
        parked.is_some(),
        "no read is live, so the decision must park"
    );
    // The subset attempt is a different object from the outer decision.
    assert!(!executor.evaluation_attempt().is_same_attempt(&outer));
    executor.record_evaluation_stop(UnknownOrigin::SolveDeadline);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::SolveDeadline)
    );
    // A second subset attempt starts clean: the first one's expiry is not
    // read back as its refusal.
    executor.begin_subset_evaluation_attempt();
    assert_eq!(executor.evaluation_stop_origin(), None);
    executor.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    executor.restore_evaluation_decision(parked);
    assert_eq!(executor.evaluation_stop_origin(), None);
    assert!(executor.evaluation_attempt().is_same_attempt(&outer));
    assert_eq!(outer.stop_origin(), None);
}

#[test]
fn parked_decision_keeps_the_stop_it_already_earned() {
    let mut executor = Executor::new();
    executor.begin_external_decision_query(false);
    executor.record_evaluation_stop(UnknownOrigin::InterruptFlag);
    let parked = executor.park_evaluation_decision();
    assert_eq!(executor.evaluation_stop_origin(), None);
    executor.record_evaluation_stop(UnknownOrigin::SolveDeadline);
    executor.restore_evaluation_decision(parked);
    // The decision's OWN refusal still publishes; the nested one does not
    // overwrite it either way (first origin is permanent).
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
}

/// #check-sat-assuming-empty-core: the stop a strict walk noted is re-imported
/// onto the live attempt by the proof-repair controls, so it is parked and
/// refreshed with the attempt. A subset attempt's noted stop is neither the
/// next attempt's nor the restored decision's.
#[test]
fn parked_decision_carries_its_noted_certification_stop() {
    use crate::api::proofs::EnvelopeStop;
    let executor = Executor::new();
    executor.note_certification_stop(EnvelopeStop::Interrupt);
    let parked = executor.park_evaluation_decision();
    assert!(parked.is_some());
    assert_eq!(executor.certification_stop(), None);
    executor.note_certification_stop(EnvelopeStop::Backstop);
    executor.begin_subset_evaluation_attempt();
    assert_eq!(executor.certification_stop(), None);
    executor.note_certification_stop(EnvelopeStop::Backstop);
    executor.restore_evaluation_decision(parked);
    assert_eq!(executor.certification_stop(), Some(EnvelopeStop::Interrupt));
}

/// Negative twin: inside a model read parking is a no-op, for the noted stop
/// as for the attempt; the decision inside the read shares both.
#[test]
fn parking_inside_a_read_keeps_the_noted_certification_stop() {
    use crate::api::proofs::EnvelopeStop;
    let executor = Executor::new();
    let read = executor.begin_external_evaluation_read();
    executor.note_certification_stop(EnvelopeStop::Backstop);
    assert!(executor.park_evaluation_decision().is_none());
    executor.begin_subset_evaluation_attempt();
    assert_eq!(executor.certification_stop(), Some(EnvelopeStop::Backstop));
    drop(read);
}

/// #check-sat-assuming-empty-core: a caller-visible decision starts with no
/// certification stop an earlier decision noted. Negative twin: a decision
/// inside a model read is part of that read and keeps the stop the read noted.
#[test]
fn a_decision_resets_the_noted_certification_stop_except_inside_a_read() {
    use crate::api::proofs::EnvelopeStop;
    let executor = Executor::new();
    executor.note_certification_stop(EnvelopeStop::Backstop);
    executor.begin_evaluation_decision();
    assert_eq!(executor.certification_stop(), None);
    let read = executor.begin_external_evaluation_read();
    executor.note_certification_stop(EnvelopeStop::Backstop);
    executor.begin_evaluation_decision();
    assert_eq!(executor.certification_stop(), Some(EnvelopeStop::Backstop));
    drop(read);
}

#[test]
fn parked_subset_attempt_inherits_the_read_controls() {
    let executor = Executor::new();
    let flag = Arc::new(AtomicBool::new(false));
    let read = executor.begin_native_evaluation_read(flag.clone(), None, Some(7), Some(11));
    // Inside a read, parking is a no-op: the decision is part of the read.
    assert!(executor.park_evaluation_decision().is_none());
    executor.record_evaluation_stop(UnknownOrigin::MemoryBudget);
    executor.restore_evaluation_decision(None);
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::MemoryBudget)
    );
    drop(read);
    // Outside a read the parked decision's controls (here: none) are cloned
    // onto the fresh attempt, so the caller's envelope keeps governing.
    let read = executor.begin_native_evaluation_read(flag, None, Some(7), Some(11));
    assert_eq!(
        executor
            .evaluation_read_controls()
            .and_then(|controls| controls.term_memory_limit),
        Some(11)
    );
    drop(read);
    assert!(executor.evaluation_read_controls().is_none());
}

#[test]
fn restore_during_a_live_read_lands_in_the_reads_saved_slot() {
    let executor = Executor::new();
    executor.record_evaluation_stop(UnknownOrigin::InterruptFlag);
    let parked = executor.park_evaluation_decision();
    assert!(parked.is_some());
    let read = executor.begin_external_evaluation_read();
    executor.restore_evaluation_decision(parked);
    // The read still owns the live attempt...
    assert_eq!(executor.evaluation_stop_origin(), None);
    drop(read);
    // ...and its last guard reinstates the PARKED decision, not the subset
    // attempt the read had displaced.
    assert_eq!(
        executor.evaluation_stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
}

/// The unsat-core minimizer's subset solves decide REDUCED problems on the
/// same executor. A stop one of them records is evidence about that subset
/// only and must never be published against the certified entry verdict.
/// Before the entry attempt was parked, the subset's expiry landed on the
/// entry decision's ledger and `emit_sat_verdict` downgraded a certified
/// UNSAT to `Unknown(Timeout)` (measured on deductive-checks's `*_push_*`
/// obligations: verdict decided in ~1 s, published as a timeout).
///
/// The stop is injected through the one channel ONLY the evaluator polls —
/// the attempt's read-control deadline, which `should_abort_theory_loop`
/// never consults — so the subset solve runs to a SAT candidate whose model
/// gate then records the expiry, exactly the production order.
#[test]
fn minimizer_subset_attempt_stop_is_not_published_as_the_entry_verdicts() {
    let mut executor = Executor::new();
    let x = executor
        .ctx
        .terms
        .mk_fresh_var("core_minimize_attempt_x", Sort::Int);
    let zero = executor.ctx.terms.mk_int(0.into());
    let positive = executor.ctx.terms.mk_gt(x, zero);
    let negative = executor.ctx.terms.mk_lt(x, zero);
    let named = vec![positive, negative];
    executor.ctx.assertions = Vec::new();
    executor.begin_public_solve(false);
    executor.begin_external_decision_query(false);
    let entry = executor
        .check_sat_assuming(&named)
        .expect("contradictory bounds must solve");
    assert!(entry.is_unsat());
    assert_eq!(executor.evaluation_stop_origin(), None);

    // An evaluator-only stop source, inherited by every subset attempt.
    let outer = executor.evaluation_attempt();
    lock(&outer.data).read_controls = Some(EvaluationReadControls {
        interrupt: Arc::new(AtomicBool::new(false)),
        deadline: Some(Instant::now()),
        memory_limit: None,
        term_memory_limit: None,
    });

    let result = executor
        .minimize_assumption_core(&named, Ok(entry), None, std::time::Duration::ZERO)
        .expect("minimizer never alters the verdict");
    assert!(result.is_unsat());
    assert!(
        executor
            .last_statistics
            .get_string("solver.uc_minimize")
            .is_some_and(|line| line.contains("attempts=") && !line.contains("attempts=0")),
        "the pass must have run subset attempts: {:?}",
        executor.last_statistics.get_string("solver.uc_minimize")
    );
    assert!(executor.evaluation_attempt().is_same_attempt(&outer));
    assert_eq!(
        executor.evaluation_stop_origin(),
        None,
        "a subset attempt's expiry must not be charged to the entry decision"
    );
    assert!(!executor.publish_evaluation_stop());
    assert!(matches!(executor.last_result, Some(SolveResult::Unsat(_))));
}

/// The stop poll at every top-level `evaluate_term` shares its attempt's
/// memory gate: only the first poll of an evaluation attempt observes process
/// memory (one syscall), the rest of the interval is rate limited, and a new
/// decision starts a new gate.
#[test]
fn evaluation_polls_share_one_memory_gate_per_attempt() {
    let mut executor = Executor::new();
    let attempt = executor.evaluation_attempt();
    assert!(
        attempt.memory_observation_due(),
        "an attempt's first poll observes"
    );
    for poll in 1..10 {
        assert!(
            !attempt.memory_observation_due(),
            "poll {poll} of the same attempt is inside the gate's interval"
        );
    }
    assert!(
        !executor.evaluation_attempt().memory_observation_due(),
        "clones of the live attempt share its gate"
    );
    for _ in 0..1_000 {
        assert_eq!(executor.poll_evaluation_stop(), Ok(()));
    }
    executor.begin_external_decision_query(false);
    assert!(
        executor.evaluation_attempt().memory_observation_due(),
        "a new decision gets a fresh gate"
    );
}
