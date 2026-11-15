// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn local_trace_quota_and_invalid_authority_are_unavailable_not_caller_stops() {
    for corrupt_authority in [false, true] {
        let mut solver = configured();
        solver.enable_consuming_clause_trace().unwrap();
        if !corrupt_authority {
            solver.set_proof_bookkeeping_budget(Some(0));
        }
        formula(&mut solver);
        assert!(solver.solve().into_inner().is_unsat());
        if corrupt_authority {
            solver.cold.original_clause_id_bits.fill(false);
        }
        let control = solver
            .cold
            .clause_trace
            .as_ref()
            .unwrap()
            .original_control()
            .unwrap();
        assert!(matches!(
            solver.into_consuming_clause_trace(&mut || false),
            Err(ConsumingTraceError::Unavailable)
        ));
        assert_eq!(control.stop_reason(), None);
        assert!(
            control.caller_open(),
            "independent caller credit was not exhausted"
        );
    }
}

#[test]
fn real_one_shot_stop_wins_even_after_local_capture_declined() {
    let armed = Arc::new(AtomicBool::new(false));
    let observed = armed.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.swap(false, Ordering::AcqRel)
    }));
    let mut solver = configured();
    solver.enable_consuming_clause_trace().unwrap();
    solver.set_proof_bookkeeping_budget(Some(0));
    formula(&mut solver);
    drop(scope);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    armed.store(true, Ordering::Release);
    assert!(matches!(
        solver.into_consuming_clause_trace(&mut || false),
        Err(ConsumingTraceError::Stopped(ConsumingTraceStop::Observer))
    ));
    assert!(
        !armed.load(Ordering::Acquire),
        "the retained callback actually ran"
    );
}

#[test]
fn captured_guard_refusal_retains_its_honest_work_classification() {
    let mut guard = ay_core::resource::Guard::new();
    guard.set_rlimit(Some(1));
    let entered = guard.enter();
    let mut solver = configured();
    solver.enable_consuming_clause_trace().unwrap();
    drop(entered);
    formula(&mut solver);
    assert!(matches!(
        solver.into_consuming_clause_trace(&mut || false),
        Err(ConsumingTraceError::Stopped(ConsumingTraceStop::Work))
    ));
}

#[test]
fn unsupported_fresh_capture_does_not_poison_an_ordinary_capture() {
    let mut solver = configured();
    solver.enable_clause_trace();
    assert!(matches!(
        solver.enable_consuming_clause_trace(),
        Err(ConsumingTraceError::Unavailable)
    ));
    formula(&mut solver);
    assert!(solver.solve().into_inner().is_unsat());
    checked(&solver.take_clause_trace().unwrap());
}
