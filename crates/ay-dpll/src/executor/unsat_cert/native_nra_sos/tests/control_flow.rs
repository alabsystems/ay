// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One borrowed control through real construction and final admission phases.

#![cfg(test)]

use super::*;
use ay_core::{time::Instant, Symbol, TermStore};
use std::cell::{Cell, RefCell};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Entry,
    Build,
    Evidence,
    Final,
}

fn square_terms() -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("control_x", CoreSort::Real);
    let square = terms.mk_app(Symbol::named("*"), [x, x], CoreSort::Real);
    let zero = terms.mk_rational(BigRational::from_integer(0.into()));
    let root = terms.mk_app(Symbol::named("<"), [square, zero], CoreSort::Bool);
    (terms, root)
}

fn through_phases(
    terms: &mut TermStore,
    root: TermId,
    control: &mut Control<'_>,
    phase: &Cell<Phase>,
) -> Result<build::BuiltSosProof, build::BuildError> {
    phase.set(Phase::Entry);
    if !control.poll_terms(terms, 0, 0) {
        return Err(build::BuildError::ResourceLimit);
    }
    phase.set(Phase::Build);
    let built = build::build(terms, &[root], &[], &mut |work, bytes| {
        control.poll(work, bytes)
    })?
    .ok_or(build::BuildError::InvalidProof)?;
    phase.set(Phase::Evidence);
    if !built
        .evidence
        .is_current_for_with_progress(terms, &[root], &[], &mut |work, bytes| {
            control.poll(work, bytes)
        })?
    {
        return Err(build::BuildError::InvalidProof);
    }
    phase.set(Phase::Final);
    if !control.poll_terms(terms, 0, 0) {
        return Err(build::BuildError::ResourceLimit);
    }
    Ok(built)
}

fn live_trace(executor: &Executor) -> Vec<Phase> {
    let (mut terms, root) = square_terms();
    let phase = Cell::new(Phase::Entry);
    let trace = RefCell::new(Vec::new());
    let mut callback = |_, _| {
        trace.borrow_mut().push(phase.get());
        true
    };
    let mut control = Control::with_progress(executor, &mut callback);
    let built = through_phases(&mut terms, root, &mut control, &phase).unwrap();
    assert!(built.quality.is_complete());
    assert!(!control.stopped());
    drop(control);
    trace.into_inner()
}

#[test]
fn every_cross_phase_refusal_is_terminal_and_a_fresh_control_can_succeed() {
    let executor = Box::new(Executor::new());
    let trace = live_trace(&executor);
    assert!(trace.contains(&Phase::Build));
    assert!(trace.contains(&Phase::Evidence));
    assert_eq!(trace.first(), Some(&Phase::Entry));
    assert_eq!(trace.last(), Some(&Phase::Final));
    for stop in 1..=trace.len() {
        let (mut terms, root) = square_terms();
        let phase = Cell::new(Phase::Entry);
        let calls = Cell::new(0);
        let mut callback = |_, _| {
            calls.set(calls.get() + 1);
            assert_eq!(phase.get(), trace[calls.get() - 1]);
            calls.get() != stop // It would return true if wrongly called again.
        };
        let mut control = Control::with_progress(&executor, &mut callback);
        assert!(
            matches!(
                through_phases(&mut terms, root, &mut control, &phase),
                Err(build::BuildError::ResourceLimit)
            ),
            "refusal {stop}"
        );
        assert!(control.stopped());
        assert_eq!(calls.get(), stop);
        assert!(matches!(
            through_phases(&mut terms, root, &mut control, &phase),
            Err(build::BuildError::ResourceLimit)
        ));
        assert_eq!(
            calls.get(),
            stop,
            "no callback or alternate phase after refusal"
        );
    }
    assert_eq!(live_trace(&executor), trace, "independent fresh control");
}

struct ResetMemorySignal;

impl Drop for ResetMemorySignal {
    fn drop(&mut self) {
        ay_sys::force_process_memory_exceeded_for_testing(false);
    }
}

fn past() -> Instant {
    Instant::now().checked_sub(Duration::from_secs(1)).unwrap()
}

#[test]
fn a_true_final_callback_cannot_publish_past_memory_or_deadline_refusal() {
    let _reset = ResetMemorySignal;
    let executor = Box::new(Executor::new());
    for memory in [false, true] {
        executor.certification_deadline.set(None);
        ay_sys::force_process_memory_exceeded_for_testing(false);
        let (mut terms, root) = square_terms();
        let phase = Cell::new(Phase::Entry);
        let final_callbacks = Cell::new(0);
        let mut callback = |_, _| {
            if phase.get() == Phase::Final {
                final_callbacks.set(final_callbacks.get() + 1);
                if memory {
                    ay_sys::force_process_memory_exceeded_for_testing(true);
                } else {
                    executor.certification_deadline.set(Some(past()));
                }
            }
            true
        };
        let mut control = Control::with_progress(&executor, &mut callback);
        assert!(matches!(
            through_phases(&mut terms, root, &mut control, &phase),
            Err(build::BuildError::ResourceLimit)
        ));
        assert_eq!(final_callbacks.get(), 1);
        assert!(control.stopped());
        executor.certification_deadline.set(None);
        ay_sys::force_process_memory_exceeded_for_testing(false);
        assert!(!control.poll_terms(&terms, 0, 0));
        assert_eq!(final_callbacks.get(), 1);
    }
}

/// Six integer linear constraints with no integer solution and a rational
/// solution: `benchmarks/smt/QF_LIA/system_03.smt2`, inlined so the pin is
/// corpus-free. A degree-bounded SOS search over the rational relaxation has
/// no witness to find here, so the lane's whole allowance is spent looking.
const INTEGER_ONLY_INFEASIBLE: &str = "\
    (declare-const v0 Int) (declare-const v1 Int) \
    (declare-const v2 Int) (declare-const v3 Int) \
    (assert (<= (+ (* -4 v0) (* -2 v1) (* -4 v2) (* 3 v3)) 47)) \
    (assert (= (+ (* 4 v0) (* 4 v1) (* 4 v2) (* -2 v3)) 49)) \
    (assert (<= (+ (* 1 v0) (* 2 v1) (* 2 v2) (* -1 v3)) 25)) \
    (assert (= (+ (* -1 v0) (* 4 v1) (* 4 v2) (* -5 v3)) 28)) \
    (assert (= (+ (* -4 v0) (* -2 v1) (* 5 v2) (* -2 v3)) -17)) \
    (assert (>= (+ (* -4 v0) (* -3 v1) (* -2 v2) (* -3 v3)) 20))";

#[test]
fn a_spent_search_allowance_yields_to_the_existing_presentation_but_a_terminal_stop_retires_it() {
    // The construction itself: the search runs out of this lane's allowance,
    // and the control records that as an allowance stop, not a terminal one.
    let mut executor = load(INTEGER_ONLY_INFEASIBLE);
    let roots = executor.ctx.assertions.clone();
    let mut callback = |_, _| true;
    let mut control = Control::with_progress(&executor, &mut callback);
    assert!(control.poll_terms(&executor.ctx.terms, 0, 0));
    assert!(matches!(
        build::supports_source(&executor.ctx.terms, &roots, &[], &mut |work, bytes| {
            control.poll(work, bytes)
        }),
        Ok(true)
    ));
    assert!(matches!(
        build::build(&mut executor.ctx.terms, &roots, &[], &mut |work, bytes| {
            control.poll(work, bytes)
        }),
        Err(build::BuildError::ResourceLimit)
    ));
    assert_eq!(control.stop(), Some(Stop::Allowance));
    assert!(!control.poll_terms(&executor.ctx.terms, 0, 0), "sticky");
    drop(control);

    // The common mint sees "no evidence" and keeps its checked presentation.
    // Before this pin, the same preparation returned the terminal rejection
    // and a computed UNSAT was published as `unknown`.
    open(&mut executor, &[]);
    assert!(matches!(
        executor.prepare_strict_native_nra_sos_bundle(&[]),
        Ok(None)
    ));

    // A terminal stop is still terminal, whichever handle raised it.
    for interrupted in [false, true] {
        let mut executor = load(INTEGER_ONLY_INFEASIBLE);
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&flag));
        open(&mut executor, &[]);
        if interrupted {
            flag.store(true, Ordering::Relaxed);
        } else {
            executor.certification_deadline.set(Some(past()));
        }
        assert!(matches!(
            executor.prepare_strict_native_nra_sos_bundle(&[]),
            Err(UnsatCertificationError::StrictProofRejected { .. })
        ));
    }
}

#[test]
fn a_prepared_proof_cannot_bind_after_a_new_deadline_or_interrupt() {
    for interrupted in [false, true] {
        let mut executor = load(SQUARE);
        let flag = Arc::new(AtomicBool::new(false));
        executor.set_interrupt(Arc::clone(&flag));
        open(&mut executor, &[]);
        let prepared = prepare(&mut executor, &[]);
        let scope = executor.authenticate_unsat_query_scope(&[], true).unwrap();
        assert!(executor.last_proof.is_none());
        if interrupted {
            flag.store(true, Ordering::Relaxed);
        } else {
            executor.certification_deadline.set(Some(past()));
        }
        assert!(prepared.bind(scope, &mut executor).is_none());
        assert!(executor.last_proof.is_none());
        assert!(executor.last_unsat_certificate.is_none());
        assert!(!executor.has_strict_native_nra_sos_bundle_state());
    }
}

#[test]
fn a_fake_unsat_decision_on_a_satisfiable_source_cannot_cross_the_common_mint() {
    let mut executor = load("(declare-const x Real) (assert (<= (* x x) 0.0))");
    open(&mut executor, &[]);
    executor.last_result = Some(SolveResult::unsat());
    assert!(executor.last_proof.is_none());
    // Explicit strict proof demand disables independent re-solving fallback;
    // x=0 satisfies the source, and there is no presented proof to discharge.
    assert!(matches!(
        executor.mint_unsat_certificate(&[]),
        Err(UnsatCertificationError::MissingProof)
    ));
    assert!(executor.last_unsat_certificate.is_none());
    assert!(!executor.has_strict_native_nra_sos_bundle_state());
}
