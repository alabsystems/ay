// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for string lemma application, proof tracking, and lowering.

use super::*;

#[test]
fn test_apply_string_lemma_with_proof_tracking_records_premise_and_mapping() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(0, theory);
    let mut tracker = proof_tracker::ProofTracker::new();
    tracker.enable();
    tracker.set_theory("Strings");

    let atom_a = TermId::new(1000);
    let atom_b = TermId::new(1001);
    dpll.apply_string_lemma_with_proof_tracking(&[atom_a, atom_b], &mut tracker);

    assert_eq!(
        tracker.num_steps(),
        1,
        "string lemma should be a proof premise"
    );

    let mapped_terms: ay_core::kani_compat::DetHashSet<TermId> =
        dpll.var_to_term().values().copied().collect();
    assert!(
        mapped_terms.contains(&atom_a) && mapped_terms.contains(&atom_b),
        "all string-lemma atoms should be mapped to SAT vars"
    );
}

#[test]
fn test_apply_string_lemma_with_proof_tracking_deduplicates_same_clause() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(0, theory);
    let mut tracker = proof_tracker::ProofTracker::new();
    tracker.enable();
    tracker.set_theory("Strings");

    let atom_a = TermId::new(2000);
    let atom_b = TermId::new(2001);
    dpll.apply_string_lemma_with_proof_tracking(&[atom_a, atom_b], &mut tracker);
    dpll.apply_string_lemma_with_proof_tracking(&[atom_a, atom_b], &mut tracker);

    assert_eq!(
        tracker.num_steps(),
        1,
        "reapplying the same string lemma should not duplicate proof premises"
    );
}

/// Bug #3375: apply_string_lemma must use negative literal for NOT(atom)
/// instead of creating a separate SAT variable.
///
/// Before the fix, [eq, NOT(eq)] created two independent variables,
/// causing sync_theory to feed contradictory assertions to the theory solver.
#[test]
fn test_apply_string_lemma_negation_shares_variable() {
    let mut terms = TermStore::new();
    let sort_s = Sort::Uninterpreted("S".to_string());
    let a = terms.mk_var("a", sort_s.clone());
    let b = terms.mk_var("b", sort_s);
    let eq = terms.mk_eq(a, b);
    let neq = terms.mk_not(eq);

    let theory = EufSolver::new(&terms);
    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(terms.true_term());
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    dpll.apply_string_lemma(&[eq, neq]);

    // eq and NOT(eq) must share the same SAT variable
    let var_eq = dpll.var_for_term(eq).expect("eq should be registered");
    // NOT(eq) should NOT have its own variable
    assert!(
        dpll.var_for_term(neq).is_none(),
        "NOT(eq) must not have its own SAT variable"
    );
    // The theory_atoms list should contain eq, not NOT(eq)
    assert!(
        dpll.theory_atoms.contains(&eq),
        "eq should be a theory atom"
    );
    assert!(
        !dpll.theory_atoms.contains(&neq),
        "NOT(eq) should not be a separate theory atom"
    );
    // Verify the variable is frozen
    assert!(dpll.sat_solver().is_frozen(var_eq));
}

#[test]
fn lower_dynamic_axiom_implication_becomes_binary_clause() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let empty = terms.mk_string(String::new());
    let x_eq_empty = terms.mk_eq(x, empty);
    let y_eq_empty = terms.mk_eq(y, empty);
    let implication = terms.mk_implies(x_eq_empty, y_eq_empty);

    let theory = EufSolver::new(&terms);
    let tseitin = Tseitin::new(&terms);
    let result = tseitin.transform(terms.true_term());
    let mut dpll = DpllT::from_tseitin(&terms, &result, theory);

    dpll.apply_string_lemma(&[implication]);

    assert!(
        dpll.var_for_term(implication).is_none(),
        "implication wrapper must be lowered to clause literals"
    );
    assert!(
        dpll.var_for_term(x_eq_empty).is_some(),
        "antecedent atom should be registered"
    );
    assert!(
        dpll.var_for_term(y_eq_empty).is_some(),
        "consequent atom should be registered"
    );
    assert!(
        dpll.theory_atoms.contains(&x_eq_empty),
        "antecedent atom should be a theory atom"
    );
    assert!(
        dpll.theory_atoms.contains(&y_eq_empty),
        "consequent atom should be a theory atom"
    );
}
