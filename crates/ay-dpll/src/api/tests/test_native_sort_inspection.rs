// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::api::*;

fn owner() -> NativeDeclarationBudget {
    NativeDeclarationBudget::new(NativeDeclarationLimits::new(64 << 20, 64 << 20, 128))
}

#[test]
fn native_sort_inspection_requires_current_owned_nominals_recursively() {
    let mut solver = Solver::new(Logic::All);
    let unknown = Sort::Uninterpreted("SortInspectionOwned".into());
    let nested = Sort::array(Sort::Int, Sort::seq(unknown.clone()));
    assert!(solver
        .try_live_sort_with_progress(&nested, &mut owner(), &mut |_, _| true)
        .is_err());
    solver
        .try_declare_opaque_sort("SortInspectionOwned")
        .unwrap();
    let current = solver
        .try_live_sort_with_progress(&nested, &mut owner(), &mut |_, _| true)
        .unwrap();
    let term = solver.declare_const("sort_inspection_owned_value", nested.clone());
    assert_eq!(
        solver
            .try_engine_term_sort_with_progress(term, &mut owner(), &mut |_, _| true)
            .unwrap(),
        current
    );
    solver.try_reset().unwrap();
    assert!(solver
        .try_live_sort_with_progress(&nested, &mut owner(), &mut |_, _| true)
        .is_err());
    // A newly forged native raw-U term after reset does not supply ownership
    // for the stale cached public sort, even when its visible name agrees.
    let raw = solver
        .terms_mut()
        .mk_var("unregistered_after_reset", unknown.clone());
    let forged = solver.wrap_term(raw);
    assert_eq!(
        solver
            .try_engine_term_sort_with_progress(forged, &mut owner(), &mut |_, _| true)
            .unwrap(),
        unknown
    );
    assert!(solver
        .try_live_sort_with_progress(&nested, &mut owner(), &mut |_, _| true)
        .is_err());
    assert!(solver
        .try_engine_term_sort_with_progress(term, &mut owner(), &mut |_, _| true)
        .is_err());
}

#[test]
fn native_sort_inspection_keeps_actual_old_carrier_distinct_from_current_same_name() {
    let mut solver = Solver::new(Logic::All);
    let dt = DatatypeSort::new(
        "InspectedEpoch",
        vec![DatatypeConstructor::unit("inspected_epoch")],
    );
    solver.try_push().unwrap();
    // Parsed declarations are assertion-scoped; native declaration handles
    // deliberately outlive assertion pop and are not used to simulate this.
    solver
        .executor
        .execute_all(
            &ay_frontend::parse("(declare-datatype InspectedEpoch ((inspected_epoch)))").unwrap(),
        )
        .unwrap();
    let old = solver
        .try_datatype_constructor(&dt, "inspected_epoch", &[])
        .unwrap();
    let actual_old = solver
        .try_engine_term_sort_with_progress(old, &mut owner(), &mut |_, _| true)
        .unwrap();
    solver.try_pop().unwrap();
    assert!(solver
        .try_live_sort_with_progress(&Sort::Datatype(dt.clone()), &mut owner(), &mut |_, _| true)
        .is_err());
    assert!(solver
        .try_live_sort_with_progress(&actual_old, &mut owner(), &mut |_, _| true)
        .is_err());
    solver
        .executor
        .execute_all(
            &ay_frontend::parse("(declare-datatype InspectedEpoch ((inspected_epoch)))").unwrap(),
        )
        .unwrap();
    let current = solver
        .try_live_sort_with_progress(&Sort::Datatype(dt), &mut owner(), &mut |_, _| true)
        .unwrap();
    assert_ne!(actual_old, current);
    assert_eq!(
        solver
            .try_engine_term_sort_with_progress(old, &mut owner(), &mut |_, _| true)
            .unwrap(),
        actual_old
    );
    // A first incarnation can share its spelling with the public source
    // name. Re-resolving such source data selects the NEW binding, never the
    // retained old engine identity; truly private popped names refuse.
    if let Ok(resolved) =
        solver.try_live_sort_with_progress(&actual_old, &mut owner(), &mut |_, _| true)
    {
        assert_eq!(resolved, current);
        assert_ne!(resolved, actual_old);
    }
}

#[test]
fn native_sort_inspection_authenticates_foreign_and_stale_handles_before_sort_copy() {
    let mut first = Solver::new(Logic::All);
    let mut second = Solver::new(Logic::All);
    let foreign = first.int_const(1);
    let before = second.terms().len();
    assert!(matches!(
        second.try_engine_term_sort_with_progress(foreign, &mut owner(), &mut |_, _| true),
        Err(NativeDeclarationError::Declaration(
            SolverError::InvalidTermHandle { .. }
        ))
    ));
    assert_eq!(second.terms().len(), before);
    let old = second.int_const(2);
    second.try_reset().unwrap();
    assert!(second
        .try_engine_term_sort_with_progress(old, &mut owner(), &mut |_, _| true)
        .is_err());
}

#[test]
fn native_sort_inspection_bounds_actual_payload_and_retains_sticky_stop() {
    let mut solver = Solver::new(Logic::All);
    let sort = Sort::Uninterpreted("wide_actual_sort".repeat(4096));
    let id = solver.terms_mut().mk_var("wide_sort_value", sort.clone());
    let term = solver.wrap_term(id);
    let before = solver.terms().len();
    let mut small = NativeDeclarationBudget::new(NativeDeclarationLimits::new(1 << 20, 1024, 128));
    assert!(matches!(
        solver.try_engine_term_sort_with_progress(term, &mut small, &mut |_, _| true),
        Err(NativeDeclarationError::Refused(
            NativeDeclarationRefusal::Storage { .. }
        ))
    ));
    assert!(solver
        .try_engine_term_sort_with_progress(term, &mut small, &mut |_, _| true)
        .is_err());
    assert_eq!(solver.terms().len(), before);
    let mut cancelled = owner();
    let calls = std::cell::Cell::new(0usize);
    assert!(solver
        .try_engine_term_sort_with_progress(term, &mut cancelled, &mut |_, _| {
            calls.set(calls.get() + 1);
            calls.get() < 3
        })
        .is_err());
    assert!(solver
        .try_engine_term_sort_with_progress(term, &mut cancelled, &mut |_, _| true)
        .is_err());
    assert_eq!(
        solver
            .try_engine_term_sort_with_progress(term, &mut owner(), &mut |_, _| true)
            .unwrap(),
        sort
    );
    assert_eq!(solver.terms().len(), before);
}
