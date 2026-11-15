// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;
use crate::{AletheAuthoredSurfaces, AletheStreamError};

fn contradiction() -> (TermStore, Proof, [TermId; 2]) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let mut proof = Proof::new();
    let positive = proof.add_assume(p, None);
    let negative = proof.add_assume(not_p, None);
    proof.add_resolution(vec![], p, positive, negative);
    (terms, proof, [p, not_p])
}

#[test]
fn initial_caller_refusal_returns_a_typed_error_before_any_output() {
    let (terms, proof, scope) = contradiction();
    let mut output = Vec::new();
    let result = crate::try_export_alethe_with_authored_surfaces_to_with_progress(
        &mut output,
        &proof,
        &terms,
        &scope,
        None,
        AletheAuthoredSurfaces::default(),
        None,
        &mut || false,
    );
    assert!(matches!(
        result,
        Err(AletheStreamError::Print(
            AlethePrintError::EmissionStopped { steps_rendered: 0 }
        ))
    ));
    assert!(output.is_empty());
}

#[test]
fn an_accepting_control_preserves_the_exact_export_bytes() {
    let (terms, proof, scope) = contradiction();
    let ordinary = crate::try_export_alethe_with_authored_surfaces(
        &proof,
        &terms,
        &scope,
        None,
        AletheAuthoredSurfaces::default(),
        None,
    )
    .expect("ordinary refutation");
    let controlled = crate::try_export_alethe_with_authored_surfaces_with_progress(
        &proof,
        &terms,
        &scope,
        None,
        AletheAuthoredSurfaces::default(),
        None,
        &mut || true,
    )
    .expect("same refutation under accepting owner");
    assert_eq!(ordinary, controlled);
}

#[test]
fn planner_cancellation_is_not_recovered_by_another_equivalence_schema() {
    let (terms, proof, scope) = contradiction();
    let mut overrides = HashMap::default();
    overrides.insert(scope[0], "(or p false)".to_string());
    let calls = std::cell::Cell::new(0usize);
    let result = crate::effective_wire_term_overrides_for_authored_proof_with_progress(
        &proof,
        &terms,
        Some(&overrides),
        AletheAuthoredSurfaces::default(),
        None,
        &mut || {
            calls.set(calls.get() + 1);
            calls.get() != 10
        },
    );
    assert!(matches!(
        result,
        Err(AlethePrintError::EmissionStopped { .. })
    ));
    assert_eq!(calls.get(), 10);
}

#[test]
fn a_nested_printer_reports_the_original_owners_typed_refusal() {
    let (terms, _, _) = contradiction();
    let allowed = std::cell::Cell::new(true);
    let mut callback = || allowed.get();
    let owner = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let nested = AlethePrinter::new(&terms).with_parent_emission_progress(&owner);
    assert!(!nested.work_budget_exhausted());
    allowed.set(false);
    assert!(nested.work_budget_exhausted());
    allowed.set(true);
    assert!(owner.work_budget_exhausted());
    assert!(matches!(
        owner.work_budget_error(0),
        AlethePrintError::EmissionStopped { .. }
    ));
}

#[test]
fn every_wire_planner_poll_including_final_refuses_publication() {
    let (terms, proof, _) = contradiction();
    let mut calls = 0;
    let accepting = crate::effective_wire_term_overrides_for_authored_proof_with_progress(
        &proof,
        &terms,
        None,
        AletheAuthoredSurfaces::default(),
        None,
        &mut || {
            calls += 1;
            true
        },
    );
    assert!(matches!(accepting, Ok(None)));
    assert!(calls > 1, "initial and terminal observations are required");
    for stop_at in 1..=calls {
        let mut observed = 0;
        let result = crate::effective_wire_term_overrides_for_authored_proof_with_progress(
            &proof,
            &terms,
            None,
            AletheAuthoredSurfaces::default(),
            None,
            &mut || {
                observed += 1;
                observed != stop_at
            },
        );
        assert!(matches!(
            result,
            Err(AlethePrintError::EmissionStopped { .. })
        ));
        assert_eq!(observed, stop_at, "refusal at poll {stop_at}/{calls}");
    }
}
