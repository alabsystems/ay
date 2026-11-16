// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod caller_poll;

#[test]
fn unavailable_capture_keeps_authored_reconstruction_without_new_credit() {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let commands = ay_frontend::parse(
        "(set-logic QF_BV) (declare-const x (_ BitVec 4))
         (assert (= x #x1)) (assert (= x #x2))",
    )
    .unwrap();
    executor.execute_all(&commands).unwrap();
    let roots = executor.ctx.assertions.clone();
    // This direct internal finalizer does not open a public query itself.
    // Establish the actual authored epoch once, before capturing the owner;
    // do not reset the enclosing evaluation or replenish its resource grants.
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let caller = TraceCaller::capture(&executor);
    let budget = executor.search_proof_bookkeeping_budget();
    let trace = caller
        .handoff(Err(ConsumingTraceError::Unavailable))
        .unwrap();
    assert!(trace.is_none());
    assert_eq!(caller.state.attempt.stop_origin(), None);
    assert_eq!(executor.search_proof_bookkeeping_budget(), budget);
    assert!(executor
        .finalize_bv_unsat(trace, &Default::default(), true)
        .unwrap()
        .is_unsat());
    assert_eq!(executor.ctx.assertions, roots);
    let proof = executor
        .last_proof()
        .expect("independent authored-source proof")
        .clone();
    let quality = executor
        .check_proof_strict_with_datatypes(&proof)
        .expect("strict authored-source reconstruction");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
    ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots)
        .expect("fallback assumptions stay within the unchanged authored roots");
    assert_eq!(executor.search_proof_bookkeeping_budget(), budget);
    assert!(caller
        .state
        .attempt
        .is_same_attempt(&executor.evaluation_attempt()));
    assert_eq!(caller.state.attempt.stop_origin(), None);
}

#[test]
fn nested_sat_one_shot_stop_reaches_attempt_before_capture_is_dropped() {
    let executor = Executor::new();
    let armed = Arc::new(AtomicBool::new(false));
    let observed = armed.clone();
    let original = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.swap(false, Ordering::AcqRel)
    }));
    let caller = TraceCaller::capture(&executor);
    let attempt = executor.evaluation_attempt();
    let nested = caller.enter();
    let mut solver = ay_sat::Solver::new(1);
    solver.enable_consuming_clause_trace().unwrap();
    drop(nested);
    drop(original);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    armed.store(true, Ordering::Release);
    solver.add_clause(vec![ay_sat::Literal::positive(ay_sat::Variable::new(0))]);
    assert_eq!(
        attempt.stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
    assert!(!armed.load(Ordering::Acquire));
    let outcome = solver.into_consuming_clause_trace(&mut || false);
    assert!(caller.handoff(outcome).is_err());
    drop(caller);
    assert_eq!(
        attempt.stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
}

#[test]
fn semantic_refusal_can_retry_but_typed_original_stop_never_can() {
    let executor = Executor::new();
    let caller = TraceCaller::capture(&executor);
    for _ in 0..2 {
        assert!(caller
            .handoff(Err(ConsumingTraceError::Unavailable))
            .unwrap()
            .is_none());
        assert!(!caller.stopped());
    }
    assert!(caller
        .handoff(Err(ConsumingTraceError::Stopped(ConsumingTraceStop::Work)))
        .is_err());
    assert_eq!(
        caller.state.attempt.stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    assert!(caller
        .handoff(Err(ConsumingTraceError::Unavailable))
        .is_err());
}

#[test]
fn caught_callback_panic_cannot_restore_a_healthy_alternative() {
    let executor = Executor::new();
    let armed = Arc::new(AtomicBool::new(true));
    let observed = armed.clone();
    let original = ay_core::resource::enter_check_stop(Arc::new(move || {
        assert!(
            !observed.swap(false, Ordering::AcqRel),
            "injected callback panic"
        );
        false
    }));
    let caller = TraceCaller::capture(&executor);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| caller.stopped())).is_err());
    drop(original);
    assert!(caller.stopped());
    assert!(caller
        .handoff(Err(ConsumingTraceError::Unavailable))
        .is_err());
}

#[test]
fn callback_reentry_that_returns_false_is_still_a_terminal_stop() {
    let executor = Executor::new();
    let original = ay_core::resource::enter_check_stop(Arc::new(|| {
        let _ = ay_core::resource::check_stop_requested();
        false
    }));
    let caller = TraceCaller::capture(&executor);
    let nested = caller.enter();
    assert!(caller.stopped());
    assert_eq!(
        caller.state.attempt.stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
    drop(nested);
    drop(original);
    assert!(caller
        .handoff(Err(ConsumingTraceError::Unavailable))
        .is_err());
}

#[test]
fn bridge_does_not_import_a_search_slice_into_certification() {
    use ay_core::resource::{ChildSpec, DeadlineSource, Guard, NodeLabel};
    let executor = Executor::new();
    let search = Guard::root_child(
        ChildSpec::new(NodeLabel::Search)
            .with_deadline(DeadlineSource::Fixed(ay_core::time::Instant::now())),
    );
    let entered = search.enter();
    let caller = TraceCaller::capture(&executor);
    let nested = caller.enter();
    let certify = search.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let certify_scope = certify.enter();
    assert!(search.poll().is_some());
    assert_eq!(certify.poll(), None);
    assert!(
        !caller.stopped(),
        "the bridge retains explicit callbacks, not search deadlines"
    );
    drop(certify_scope);
    drop(nested);
    drop(entered);
    assert_eq!(caller.state.attempt.stop_origin(), None);
}

#[test]
fn recorded_guard_stop_survives_solver_cleanup_without_an_unsat_handoff() {
    let executor = Executor::new();
    let mut guard = ay_core::resource::Guard::new();
    guard.set_rlimit(Some(3));
    let entered = guard.enter();
    let mut caller = TraceCaller::capture(&executor);
    let nested = caller.enter();
    let mut solver = ay_sat::Solver::new(1);
    caller.retain_capture(solver.enable_consuming_clause_trace().unwrap());
    drop(nested);
    drop(entered);
    let replacement = ay_core::resource::Guard::new();
    let _replacement = replacement.enter();
    solver.add_clause(vec![ay_sat::Literal::positive(ay_sat::Variable::new(0))]);
    assert!(guard.poll().is_some());
    drop(solver);
    assert!(caller.stopped());
    assert_eq!(
        caller.state.attempt.stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    assert_eq!(replacement.ticks(), 0);
}

#[test]
fn consuming_handoff_keeps_cancel_only_certification_after_search_expiry() {
    use ay_core::resource::{ChildSpec, DeadlineSource, Guard, LiveDeadline, NodeLabel};
    let deadline = LiveDeadline::new(None);
    let search = Guard::root_child(
        ChildSpec::new(NodeLabel::Search).with_deadline(DeadlineSource::Live(deadline.clone())),
    );
    let _search_scope = search.enter();
    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    executor.solve_interrupt = Some(interrupt.clone());
    let mut caller = TraceCaller::capture(&executor);
    let _nested = caller.enter();
    let mut solver = ay_sat::Solver::new(2);
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    caller.retain_capture(solver.enable_consuming_clause_trace().unwrap());
    let a = ay_sat::Literal::positive(ay_sat::Variable::new(0));
    let b = ay_sat::Literal::positive(ay_sat::Variable::new(1));
    for clause in [
        [a, b],
        [a.negated(), b],
        [a, b.negated()],
        [a.negated(), b.negated()],
    ] {
        solver.add_clause(clause.to_vec());
    }
    assert!(solver.solve().into_inner().is_unsat());
    let (handoff, transfers) = observation::observe(&executor.evaluation_attempt(), || {
        caller.handoff(solver.into_consuming_clause_trace(&mut || false))
    });
    assert_eq!(transfers, 1);
    let trace = handoff
        .unwrap()
        .expect("real consuming transfer before the search slice expires");
    assert!(trace.original_clauses().count() > 0);
    assert_eq!(caller.capture.as_ref().unwrap().observed_stop(), None);

    deadline.set(Some(ay_core::time::Instant::now()));
    let certify = search.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let _certify_scope = certify.enter();
    assert!(search.poll().is_some());
    assert_eq!(certify.poll(), None);
    assert!(!caller.stopped());
    ay_sat::validate_clause_trace_resolution(
        &trace,
        2,
        &ay_sat::ResolutionValidationLimits::default(),
    )
    .expect("native replay under Certify/CancelOnly must not revive the search deadline");
    assert!(!caller.stopped());
    assert_eq!(caller.capture.as_ref().unwrap().observed_stop(), None);
    assert_eq!(caller.state.attempt.stop_origin(), None);

    interrupt.store(true, Ordering::Release);
    assert!(
        caller.stopped(),
        "CancelOnly still observes real cancellation"
    );
    assert_eq!(
        caller.state.attempt.stop_origin(),
        Some(UnknownOrigin::InterruptFlag)
    );
}

#[test]
fn successful_handoff_observation_excludes_unavailable_and_typed_stops() {
    let executor = Executor::new();
    let foreign = Executor::new();
    let caller = TraceCaller::capture(&executor);
    let ((), transfers) = observation::observe_trace(
        &executor.evaluation_attempt(),
        |_| panic!("unavailable, foreign or stopped captures have no inspectable transfer"),
        || {
            assert!(caller
                .handoff(Err(ConsumingTraceError::Unavailable))
                .unwrap()
                .is_none());
            observation::note_successful_handoff(&foreign.evaluation_attempt());
            assert!(caller
                .handoff(Err(ConsumingTraceError::Stopped(ConsumingTraceStop::Work)))
                .is_err());
            assert!(caller
                .handoff(Err(ConsumingTraceError::Unavailable))
                .is_err());
        },
    );
    assert_eq!(transfers, 0);
    assert_eq!(
        executor.evaluation_attempt().stop_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
}

#[test]
fn successful_handoff_observation_requires_the_final_original_owner_fence() {
    let mut solver = ay_sat::Solver::new(2);
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    solver.enable_consuming_clause_trace().unwrap();
    let a = ay_sat::Literal::positive(ay_sat::Variable::new(0));
    let b = ay_sat::Literal::positive(ay_sat::Variable::new(1));
    for clause in [
        [a, b],
        [a.negated(), b],
        [a, b.negated()],
        [a.negated(), b.negated()],
    ] {
        solver.add_clause(clause.to_vec());
    }
    assert!(solver.solve().into_inner().is_unsat());
    let trace = solver.into_consuming_clause_trace(&mut || false).unwrap();
    ay_sat::validate_clause_trace_resolution(
        &trace,
        2,
        &ay_sat::ResolutionValidationLimits::default(),
    )
    .expect("the refused handoff carries a real native refutation");

    let executor = Executor::new();
    let original = ay_core::resource::enter_check_stop(Arc::new(|| true));
    let caller = TraceCaller::capture(&executor);
    drop(original);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    let (result, transfers) = observation::observe_trace(
        &executor.evaluation_attempt(),
        |_| panic!("a failed original-owner fence must not inspect the trace"),
        || caller.handoff(Ok(trace)),
    );
    assert!(result.is_err());
    assert_eq!(transfers, 0);
    assert_eq!(
        executor.evaluation_attempt().stop_origin(),
        Some(UnknownOrigin::IncompleteSolverLane)
    );
}
