// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The fresh-definition bound driven through the REAL step validator.
//!
//! The sibling file tests `FreshDefRegistry` directly. These tests go through
//! `validate_step_with_datatypes`, which is what every whole-proof entry point
//! actually calls, and pin the two dispatch decisions that live there: strict
//! mode consults the registry (and refuses without one), non-strict mode admits
//! the clause exactly as it admits the `trust` step this rule replaces.

use super::eq::push_eq;
use super::{fixture, push_bound, reason, FreshDefRegistry};
use ay_core::{AletheRule, Proof, ProofStep};

use crate::checker::{validate_step, validate_step_with_datatypes, ProofCheckError};

/// Which fresh-definition rule the shared harness should build.
#[derive(Clone, Copy)]
enum Form {
    Bound,
    Eq,
}

/// `(assume 0 <= x)`, the definition of `d := x` in one of the two forms, then
/// a contradiction nobody derives — the point is only which steps the CHECKER
/// accepts.
fn strict_outcome_for(form: Form, with_registry: bool) -> Result<(), ProofCheckError> {
    let mut f = fixture();
    let d = f.fresh(1);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, f.x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    match form {
        Form::Bound => push_bound(&mut proof, &mut f.terms, d, f.x, false),
        Form::Eq => push_eq(&mut proof, &mut f.terms, d, f.x),
    }
    let mut derived = Vec::new();
    if with_registry {
        let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))?;
        for (idx, step) in proof.steps.iter().enumerate() {
            validate_step_with_datatypes(
                &f.terms,
                &mut derived,
                ay_core::ProofId(idx as u32),
                step,
                true,
                None,
                None,
                None,
                None,
                None,
                Some(&registry),
                None,
            )?;
        }
    } else {
        for (idx, step) in proof.steps.iter().enumerate() {
            validate_step_with_datatypes(
                &f.terms,
                &mut derived,
                ay_core::ProofId(idx as u32),
                step,
                true,
                None,
                None,
                None,
                None,
                None,
                None,
                None,
            )?;
        }
    }
    Ok(())
}

fn strict_outcome(with_registry: bool) -> Result<(), ProofCheckError> {
    strict_outcome_for(Form::Bound, with_registry)
}

#[test]
fn strict_mode_accepts_a_vetted_fresh_def_bound() {
    strict_outcome(true).expect("a vetted bound validates in strict mode");
}

#[test]
fn strict_mode_accepts_a_vetted_fresh_def_eq() {
    strict_outcome_for(Form::Eq, true).expect("a vetted equality validates in strict mode");
}

#[test]
fn strict_mode_rejects_a_fresh_def_bound_without_a_registry() {
    // The registry, not the step, is where freshness is decided. An entry
    // point that does not build one must not accept the step on shape alone.
    let error = strict_outcome(false).expect_err("no registry means nothing was checked");
    assert!(
        reason(&error).contains("whole-proof provenance registry"),
        "{error:?}"
    );
}

#[test]
fn strict_mode_rejects_a_fresh_def_eq_without_a_registry() {
    // The equality form must fail closed for the same reason and through the
    // same gate. Without this, an entry point that builds no registry would
    // accept an arbitrary `(= x y)` labelled `fresh_def_eq`.
    let error =
        strict_outcome_for(Form::Eq, false).expect_err("no registry means nothing was checked");
    assert!(
        reason(&error).contains("whole-proof provenance registry"),
        "{error:?}"
    );
}

#[test]
fn non_strict_mode_admits_the_equality_clause_exactly_as_it_admits_trust() {
    // The step REPLACES a premiseless `trust`, which non-strict checking
    // already admits. Rejecting it here would regress every partial check.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let atom = f.terms.mk_eq(d, lin);
    let step = ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    };
    let mut derived = Vec::new();
    validate_step(
        &f.terms,
        &mut derived,
        ay_core::ProofId(0),
        &step,
        false,
        None,
    )
    .expect("non-strict checking admits the clause");
    assert_eq!(derived, vec![Some(vec![atom])]);
}

#[test]
fn non_strict_mode_admits_the_clause_exactly_as_it_admits_trust() {
    // The step REPLACES a premiseless `trust`, which non-strict checking
    // already admits. Rejecting it here would regress every partial check.
    let mut f = fixture();
    let d = f.fresh(1);
    let lin = f.diff();
    let atom = f.terms.mk_le(d, lin);
    let step = ProofStep::Step {
        rule: AletheRule::FreshDefBound,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![d],
    };
    let mut derived = Vec::new();
    validate_step(
        &f.terms,
        &mut derived,
        ay_core::ProofId(0),
        &step,
        false,
        None,
    )
    .expect("non-strict checking admits the clause");
    assert_eq!(derived, vec![Some(vec![atom])]);
}
