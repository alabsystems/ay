// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for `keep_proof_inprocessing_after_exhaustion`: which inprocessing
//! controls a solver continues with once its proof bookkeeping budget runs
//! out.

use super::*;
use crate::keep_proof_inprocessing_after_exhaustion;

/// The six transforms proof mode disables (no LRAT support), as
/// `(bve, decompose, factor, sbva, congruence, sweep)`.
fn lrat_incompatible_controls(solver: &Solver) -> [bool; 6] {
    let ctrl = &solver.inproc_ctrl;
    [
        ctrl.bve.enabled,
        ctrl.decompose.enabled,
        ctrl.factor.enabled,
        ctrl.sbva.enabled,
        ctrl.congruence.enabled,
        ctrl.sweep.enabled,
    ]
}

/// A solver with every LRAT-incompatible transform switched on, then a clause
/// trace, which clamps them off.
fn traced_solver_with_every_transform_on() -> Solver {
    let mut solver = Solver::new(4);
    solver.inproc_ctrl.bve.enabled = true;
    solver.inproc_ctrl.decompose.enabled = true;
    solver.inproc_ctrl.factor.enabled = true;
    solver.inproc_ctrl.sbva.enabled = true;
    solver.inproc_ctrl.congruence.enabled = true;
    solver.inproc_ctrl.sweep.enabled = true;
    solver.enable_clause_trace();
    assert_eq!(lrat_incompatible_controls(&solver), [false; 6]);
    solver
}

fn exhaust(solver: &mut Solver) {
    if let Some(trace) = solver.cold.clause_trace.as_mut() {
        trace.mark_proof_work_exhausted();
    }
    solver.degrade_proof_bookkeeping_after_exhaustion();
    assert!(!solver.cold.lrat_enabled, "the degrade drops the trace");
}

/// Outside a scope, exhaustion restores the pristine controls: the transforms
/// proof mode disabled run again, as `--no-proof` would run them.
#[test]
fn exhaustion_outside_a_scope_restores_the_pristine_controls() {
    let mut solver = traced_solver_with_every_transform_on();
    solver.set_proof_bookkeeping_budget(Some(0));
    assert!(!solver.keeps_proof_inprocessing_after_exhaustion());
    exhaust(&mut solver);
    assert_eq!(lrat_incompatible_controls(&solver), [true; 6]);
}

/// A budget set inside a scope latches the choice, and exhaustion keeps the
/// proof-mode controls, even after the scope has closed.
#[test]
fn a_budget_set_inside_a_scope_keeps_the_proof_mode_controls() {
    let mut solver = traced_solver_with_every_transform_on();
    {
        let _scope = keep_proof_inprocessing_after_exhaustion();
        solver.set_proof_bookkeeping_budget(Some(0));
    }
    assert!(solver.keeps_proof_inprocessing_after_exhaustion());
    exhaust(&mut solver);
    assert_eq!(lrat_incompatible_controls(&solver), [false; 6]);
    assert!(solver.inproc_ctrl_pre_proof.is_none());
}

/// NEGATIVE TWIN: only a budget latches. A scope opened after the budget was
/// set, a `None` budget inside a scope, and a closed scope latch nothing.
#[test]
fn only_a_budget_set_inside_an_open_scope_latches() {
    let mut late = traced_solver_with_every_transform_on();
    late.set_proof_bookkeeping_budget(Some(0));
    let scope = keep_proof_inprocessing_after_exhaustion();
    assert!(!late.keeps_proof_inprocessing_after_exhaustion());

    let mut cleared = traced_solver_with_every_transform_on();
    cleared.set_proof_bookkeeping_budget(Some(0));
    cleared.set_proof_bookkeeping_budget(None);
    assert!(!cleared.keeps_proof_inprocessing_after_exhaustion());
    drop(scope);

    let mut after = traced_solver_with_every_transform_on();
    after.set_proof_bookkeeping_budget(Some(0));
    assert!(!after.keeps_proof_inprocessing_after_exhaustion());
    exhaust(&mut after);
    assert_eq!(lrat_incompatible_controls(&after), [true; 6]);
}

/// Scopes nest: closing the inner one leaves the outer one open.
#[test]
fn nested_scopes_stay_open_until_the_outermost_closes() {
    let outer = keep_proof_inprocessing_after_exhaustion();
    drop(keep_proof_inprocessing_after_exhaustion());
    let mut solver = traced_solver_with_every_transform_on();
    solver.set_proof_bookkeeping_budget(Some(0));
    assert!(solver.keeps_proof_inprocessing_after_exhaustion());
    drop(outer);
}

#[test]
fn an_open_scope_does_not_latch_another_threads_budget() {
    let scope = keep_proof_inprocessing_after_exhaustion();
    std::thread::spawn(|| {
        let mut solver = traced_solver_with_every_transform_on();
        solver.set_proof_bookkeeping_budget(Some(0));
        assert!(!solver.keeps_proof_inprocessing_after_exhaustion());
        exhaust(&mut solver);
        assert_eq!(lrat_incompatible_controls(&solver), [true; 6]);
    })
    .join()
    .expect("independent thread completes");
    let mut local = traced_solver_with_every_transform_on();
    local.set_proof_bookkeeping_budget(Some(0));
    assert!(local.keeps_proof_inprocessing_after_exhaustion());
    drop(scope);
    local.set_proof_bookkeeping_budget(Some(0));
    assert!(!local.keeps_proof_inprocessing_after_exhaustion());
}

#[test]
fn unwinding_an_inner_scope_preserves_and_then_retires_the_outer_scope() {
    let outer = keep_proof_inprocessing_after_exhaustion();
    assert!(std::panic::catch_unwind(|| {
        let _inner = keep_proof_inprocessing_after_exhaustion();
        panic!("unwind the inner scope");
    })
    .is_err());
    let mut solver = traced_solver_with_every_transform_on();
    solver.set_proof_bookkeeping_budget(Some(0));
    assert!(solver.keeps_proof_inprocessing_after_exhaustion());
    drop(outer);
    solver.set_proof_bookkeeping_budget(Some(0));
    assert!(!solver.keeps_proof_inprocessing_after_exhaustion());
}

#[test]
fn the_scope_guard_is_neither_send_nor_sync() {
    // A second applicable implementation makes the inferred marker ambiguous.
    // This is a compile-time negative check, with no helper dependency.
    {
        trait AmbiguousIfSend<Marker> {
            fn check() {}
        }
        impl<T: ?Sized> AmbiguousIfSend<()> for T {}
        struct IsSend;
        impl<T: ?Sized + Send> AmbiguousIfSend<IsSend> for T {}
        let _ = <ProofInprocessingKeptAfterExhaustion as AmbiguousIfSend<_>>::check;
    }
    {
        trait AmbiguousIfSync<Marker> {
            fn check() {}
        }
        impl<T: ?Sized> AmbiguousIfSync<()> for T {}
        struct IsSync;
        impl<T: ?Sized + Sync> AmbiguousIfSync<IsSync> for T {}
        let _ = <ProofInprocessingKeptAfterExhaustion as AmbiguousIfSync<_>>::check;
    }
}
