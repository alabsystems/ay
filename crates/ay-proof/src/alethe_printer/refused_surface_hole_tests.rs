// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::try_export_alethe_with_problem_scope_and_overrides;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermStore};

/// A congruence whose authored left side no bridge relates to the internal
/// one (a changed multiplier is not a commutation): the printer refuses it.
fn refused_congruence() -> (TermStore, Proof, TermId, [TermId; 2]) {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let sixteen = terms.mk_int(16.into());
    let seven = terms.mk_int(7.into());
    let mul = terms.mk_app(Symbol::named("*"), [c, sixteen], Sort::Int);
    let left = terms.mk_app(Symbol::named("+"), [mul, s], Sort::Int);
    let right = terms.mk_app(Symbol::named("+"), [mul, seven], Sort::Int);
    let premise_equality = terms.mk_app(Symbol::named("="), [s, seven], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let mut proof = Proof::new();
    let premise = proof.add_assume(premise_equality, None);
    proof.add_rule_step(
        AletheRule::Cong,
        vec![conclusion],
        vec![premise],
        Vec::new(),
    );
    (terms, proof, left, [premise_equality, conclusion])
}

fn export(
    terms: &TermStore,
    proof: &Proof,
    left: TermId,
    scope: [TermId; 2],
) -> Result<String, AlethePrintError> {
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(left, "(+ (* 15 c) s)".to_string());
    try_export_alethe_with_problem_scope_and_overrides(proof, terms, &scope, Some(&overrides))
}

#[test]
fn a_refused_surface_step_refuses_the_document_outside_the_scope() {
    let (terms, proof, left, scope) = refused_congruence();
    let error = export(&terms, &proof, left, scope).expect_err("no bridge spells the step");
    assert!(
        matches!(error, AlethePrintError::InvalidCongruenceStep { .. }),
        "{error}"
    );
}

#[test]
fn inside_the_scope_a_refused_surface_step_is_the_honest_hole_over_its_clause() {
    let (terms, proof, left, scope) = refused_congruence();
    let output =
        with_refused_surface_steps_declined_to_hole(|| export(&terms, &proof, left, scope))
            .expect("the refused step declines to a hole");
    assert!(
        output.contains("(step t1 (cl (= (+ (* 15 c) s) (+ (* c 16) 7))) :rule hole)"),
        "{output}"
    );
    assert!(!output.contains(":rule cong"), "{output}");
    // The scope does not outlive the call.
    assert!(export(&terms, &proof, left, scope).is_err());
}

/// An `assume` has no hole: a refusal there still refuses the document.
#[test]
fn only_surface_refusals_of_steps_with_a_clause_are_declined() {
    let (terms, proof, _, _) = refused_congruence();
    let printer = AlethePrinter::new_with_overrides(&terms, None);
    let error = AlethePrintError::InvalidCongruenceStep {
        id: ProofId(0),
        reason: "fixture".to_string(),
    };
    with_refused_surface_steps_declined_to_hole(|| {
        assert!(printer
            .refused_surface_step_hole(&proof.steps[0], ProofId(0), &error)
            .is_none());
        assert!(printer
            .refused_surface_step_hole(&proof.steps[1], ProofId(1), &error)
            .is_some());
        let unrelated = AlethePrintError::UnavailableAuthenticatedSurface { reason: "fixture" };
        assert!(printer
            .refused_surface_step_hole(&proof.steps[1], ProofId(1), &unrelated)
            .is_none());
    });
}
