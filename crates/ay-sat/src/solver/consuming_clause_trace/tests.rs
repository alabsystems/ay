// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[path = "tests/outcomes.rs"]
mod outcomes;

fn formula(solver: &mut Solver) {
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    for clause in [
        [a, b],
        [a.negated(), b],
        [a, b.negated()],
        [a.negated(), b.negated()],
    ] {
        solver.add_clause(clause.to_vec());
    }
}

fn configured() -> Solver {
    let mut solver = Solver::new(2);
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    solver.set_startup_walk_enabled(false);
    solver
}

fn rows(trace: &ClauseTrace) -> Vec<(u64, Vec<Literal>, bool, Vec<u64>)> {
    trace
        .entries()
        .iter()
        .map(|row| {
            (
                row.id,
                row.clause.to_vec(),
                row.is_original,
                row.resolution_hints.to_vec(),
            )
        })
        .collect()
}

fn checked(trace: &ClauseTrace) {
    assert_eq!(trace.solver_num_vars(), Some(2));
    assert_eq!(trace.scope_assumptions(), Some(&[][..]));
    crate::validate_clause_trace_resolution(
        trace,
        2,
        &crate::ResolutionValidationLimits::unbounded(),
    )
    .unwrap();
}

#[test]
fn consuming_solver_preserves_exact_legacy_native_refutation() {
    let mut legacy = configured();
    legacy.enable_clause_trace();
    legacy.set_proof_bookkeeping_budget(Some(100_000));
    formula(&mut legacy);
    assert!(legacy.solve().into_inner().is_unsat());
    let old = legacy.take_clause_trace().unwrap();
    checked(&old);

    let mut solver = configured();
    assert!(solver.enable_consuming_clause_trace().is_ok());
    solver.set_proof_bookkeeping_budget(Some(100_000));
    formula(&mut solver);
    assert!(solver.clause_trace().is_none());
    assert!(solver.snapshot_clause_trace().is_none());
    assert!(solver.take_clause_trace().is_none());
    assert!(solver.solve().into_inner().is_unsat());
    let source_literals = solver.cold.original_ledger.clause(0).as_ptr();
    let new = solver.into_consuming_clause_trace(&mut || false).unwrap();
    assert_eq!(
        source_literals,
        new.original_clauses().next().unwrap().clause.as_ptr()
    );
    checked(&new);
    assert_eq!(rows(&new), rows(&old));
    assert!(
        new.used_bytes() < old.used_bytes(),
        "actual original metadata/copy removed"
    );
}

#[test]
fn recorded_refusal_cannot_be_reset_to_a_fresh_trace_budget() {
    let mut solver = configured();
    assert!(solver.enable_consuming_clause_trace().is_ok());
    solver.set_proof_bookkeeping_budget(Some(0));
    formula(&mut solver);
    assert!(solver
        .cold
        .clause_trace
        .as_ref()
        .unwrap()
        .proof_work_exhausted());
    solver.set_proof_bookkeeping_budget(None);
    assert!(solver.into_consuming_clause_trace(&mut || false).is_err());
}

#[test]
fn fresh_only_mode_rejects_scope_history_existing_proof_and_prior_solve() {
    let mut scoped = configured();
    scoped.push();
    assert!(scoped.pop());
    assert!(scoped.enable_consuming_clause_trace().is_err());
    let mut proof = Solver::with_proof(2, Vec::<u8>::new());
    assert!(proof.enable_consuming_clause_trace().is_err());
    let mut solved = configured();
    assert!(matches!(solved.solve().into_inner(), SatResult::Sat(_)));
    assert!(solved.enable_consuming_clause_trace().is_err());
}

#[test]
fn scope_history_late_original_and_pending_global_fail_closed_after_capture() {
    for kind in 0..3 {
        let mut solver = configured();
        assert!(solver.enable_consuming_clause_trace().is_ok());
        formula(&mut solver);
        match kind {
            0 => {
                solver.push();
                assert!(solver.pop());
            }
            1 => {
                solver.cold.has_solved_once = true;
                solver.register_ledger_original(
                    &[Literal::positive(Variable(0))],
                    original_clause_ids::OriginalLifetime::Scoped,
                );
            }
            _ => {
                solver.cold.original_ledger.push_scope();
                solver
                    .cold
                    .original_ledger
                    .push_clause_global(&[Literal::positive(Variable(0))]);
            }
        }
        assert!(
            solver.into_consuming_clause_trace(&mut || false).is_err(),
            "kind {kind}"
        );
    }
}

#[test]
fn original_callback_replacement_cannot_revive_registration_or_handoff() {
    let armed = Arc::new(AtomicBool::new(false));
    let observer = armed.clone();
    let original = ay_core::resource::enter_check_stop(Arc::new(move || {
        observer.swap(false, Ordering::AcqRel)
    }));
    let mut solver = configured();
    assert!(solver.enable_consuming_clause_trace().is_ok());
    drop(original);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    armed.store(true, Ordering::Release);
    formula(&mut solver);
    assert!(solver
        .cold
        .clause_trace
        .as_ref()
        .unwrap()
        .proof_work_exhausted());
    assert!(solver.into_consuming_clause_trace(&mut || false).is_err());
}

#[test]
fn handoff_callback_refusal_and_restricted_subsetup_fence_withhold_native_trace() {
    let mut baseline = configured();
    assert!(baseline.enable_consuming_clause_trace().is_ok());
    formula(&mut baseline);
    assert!(baseline.solve().into_inner().is_unsat());
    let mut calls = 0;
    let trace = baseline
        .into_consuming_clause_trace(&mut || {
            calls += 1;
            false
        })
        .unwrap();
    checked(&trace);
    assert!(calls > 2);
    for refusal in [1, calls / 2, calls] {
        let mut solver = configured();
        assert!(solver.enable_consuming_clause_trace().is_ok());
        formula(&mut solver);
        assert!(solver.solve().into_inner().is_unsat());
        let mut seen = 0;
        assert!(
            solver
                .into_consuming_clause_trace(&mut || {
                    seen += 1;
                    seen == refusal
                })
                .is_err(),
            "refusal {refusal}"
        );
    }
}

#[test]
fn unbound_or_falsely_original_ids_do_not_acquire_solver_authority() {
    let mut solver = configured();
    assert!(solver.enable_consuming_clause_trace().is_ok());
    formula(&mut solver);
    assert!(solver.solve().into_inner().is_unsat());
    solver.cold.original_clause_id_bits.fill(false);
    assert!(solver.into_consuming_clause_trace(&mut || false).is_err());
}

#[test]
fn caught_capture_callback_panic_cannot_rearm_the_same_solver() {
    let armed = Arc::new(AtomicBool::new(true));
    let observer = armed.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        assert!(
            !observer.swap(false, Ordering::AcqRel),
            "injected capture panic"
        );
        false
    }));
    let mut solver = configured();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        solver.enable_consuming_clause_trace()
    }))
    .is_err());
    drop(scope);
    assert!(solver.enable_consuming_clause_trace().is_err());
    assert!(solver.into_consuming_clause_trace(&mut || false).is_err());
}

#[test]
fn original_membership_is_exact_logarithmic_and_charged_to_captured_owner() {
    let owner = ay_core::resource::Guard::new();
    let entered = owner.enter();
    let mut solver = configured();
    solver.enable_consuming_clause_trace().unwrap();
    solver.set_proof_bookkeeping_budget(Some(20_000));
    let literal = Literal::positive(Variable(0));
    let mut last = 0;
    for _ in 0..1024 {
        last = solver
            .register_ledger_original(&[literal], original_clause_ids::OriginalLifetime::Scoped);
    }
    let gap = solver.cold.next_clause_id;
    solver.cold.next_clause_id += 1;
    solver.register_ledger_original(&[literal], original_clause_ids::OriginalLifetime::Scoped);
    drop(entered);
    let replacement = ay_core::resource::Guard::new();
    let _replacement = replacement.enter();
    for (id, present) in [(last, true), (gap, false), (u64::MAX, false)] {
        let ticks = owner.ticks();
        let remaining = solver.cold.proof_bookkeeping_budget.unwrap();
        assert_eq!(solver.consuming_original_contains(id), Some(present));
        let used = remaining - solver.cold.proof_bookkeeping_budget.unwrap();
        assert!((1..=11).contains(&used), "one debit per binary probe");
        assert_eq!(owner.ticks() - ticks, used);
        assert_eq!(replacement.ticks(), 0);
    }
}

#[test]
fn original_membership_quota_and_caller_refusals_remain_distinct() {
    let armed = Arc::new(AtomicBool::new(false));
    let observed = armed.clone();
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.swap(false, Ordering::AcqRel)
    }));
    for caller_stop in [false, true] {
        let mut solver = configured();
        let capture = solver.enable_consuming_clause_trace().unwrap();
        let id = solver.register_ledger_original(
            &[Literal::positive(Variable(0))],
            original_clause_ids::OriginalLifetime::Scoped,
        );
        if caller_stop {
            armed.store(true, Ordering::Release);
        } else {
            solver.set_proof_bookkeeping_budget(Some(1));
        }
        assert_eq!(solver.consuming_original_contains(id), None);
        assert_eq!(
            capture.observed_stop(),
            caller_stop.then_some(ConsumingTraceStop::Observer)
        );
        let expected = if caller_stop {
            ConsumingTraceError::Stopped(ConsumingTraceStop::Observer)
        } else {
            ConsumingTraceError::Unavailable
        };
        assert_eq!(
            solver
                .into_consuming_clause_trace(&mut || false)
                .unwrap_err(),
            expected
        );
    }
}

#[test]
fn complete_handoff_debits_provenance_rows_to_the_same_captured_owner() {
    let owner = ay_core::resource::Guard::new();
    let _entered = owner.enter();
    let mut solver = configured();
    let capture = solver.enable_consuming_clause_trace().unwrap();
    solver.set_proof_bookkeeping_budget(Some(100_000));
    formula(&mut solver);
    assert!(solver.solve().into_inner().is_unsat());
    let ticks = owner.ticks();
    let remaining = solver.cold.proof_bookkeeping_budget.unwrap();
    let trace = solver
        .finish_consuming_trace(&capture.0, &mut || false)
        .expect("complete storage and issued-ID validation");
    let used = remaining - solver.cold.proof_bookkeeping_budget.unwrap();
    assert!(used > trace.entries().len() as u64);
    assert_eq!(
        owner.ticks() - ticks,
        used,
        "the issued-ID pass must not merely poll after the metered structure pass"
    );
    checked(&trace);
}
