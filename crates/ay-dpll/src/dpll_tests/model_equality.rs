// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the `apply_model_equality` mechanism (#4906).
//!
//! Verifies that the DpllT layer correctly allocates SAT variables for
//! speculative model equalities and sets the phase hint to `true`,
//! following the Z3 `assume_eq` + `try_true_first` pattern.

use super::*;

/// Verify `apply_model_equality` allocates a new SAT variable for a fresh atom
/// and registers it as a theory atom (#4906).
#[test]
fn test_apply_model_equality_fresh_atom() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    let eq_atom = TermId::new(100);

    // Pre-condition: atom has no SAT variable yet.
    assert!(dpll.var_for_term(eq_atom).is_none());

    dpll.apply_model_equality(eq_atom);

    // Post-condition: atom is now registered with a SAT variable.
    let var = dpll
        .var_for_term(eq_atom)
        .expect("apply_model_equality should register the atom");
    // The reverse mapping must also hold.
    assert_eq!(dpll.term_for_var(var), Some(eq_atom));
    // The variable should be frozen (theory atoms are frozen).
    assert!(dpll.sat_solver().is_frozen(var));
    // The atom should appear in the theory-atom list.
    assert!(dpll.theory_atoms.contains(&eq_atom));
}

/// Verify `apply_model_equality` reuses an existing SAT variable when the atom
/// was already registered (#4906).
#[test]
fn test_apply_model_equality_existing_atom() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    let eq_atom = TermId::new(200);

    // Manually register the atom first.
    dpll.register_theory_atom(eq_atom, 0);
    let original_var = dpll
        .var_for_term(eq_atom)
        .expect("register_theory_atom should have registered the atom");
    assert_eq!(original_var, Variable::new(0));

    // apply_model_equality should reuse variable 0, not allocate a new one.
    dpll.apply_model_equality(eq_atom);

    let var_after = dpll
        .var_for_term(eq_atom)
        .expect("atom should still be registered after apply_model_equality");
    assert_eq!(
        var_after, original_var,
        "should reuse existing SAT variable"
    );
}

/// Verify that multiple distinct model equality atoms each get separate
/// SAT variables (#4906).
#[test]
fn test_apply_model_equality_multiple_atoms() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(0, theory);

    let atoms: Vec<TermId> = (300..305).map(TermId::new).collect();

    for &atom in &atoms {
        dpll.apply_model_equality(atom);
    }

    // Each atom should have a distinct variable.
    let vars: Vec<Variable> = atoms
        .iter()
        .map(|a| dpll.var_for_term(*a).expect("atom should be registered"))
        .collect();

    // All variables should be distinct.
    let var_set: ay_core::kani_compat::DetHashSet<u32> = vars.iter().map(|v| v.id()).collect();
    assert_eq!(
        var_set.len(),
        atoms.len(),
        "each atom should get a unique variable"
    );
}

/// Verify `apply_model_equality` sets the phase hint to `true` (Z3 `try_true_first`).
///
/// This is the core mechanism: the SAT solver should decide the equality atom
/// as `true` first, so the theory sees the speculative equality and can propagate
/// consequences. If the hint were missing or inverted, Nelson-Oppen model-based
/// combination would not work (#4906, #6160 Gap 2).
#[test]
fn test_apply_model_equality_sets_phase_hint_true() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(0, theory);

    let eq_atom = TermId::new(400);

    // Pre-condition: no phase hint set.
    dpll.apply_model_equality(eq_atom);

    let var = dpll
        .var_for_term(eq_atom)
        .expect("apply_model_equality should register the atom");

    // The phase hint must be `true` so the solver decides the equality positively.
    assert_eq!(
        dpll.sat_solver().var_phase(var),
        Some(true),
        "apply_model_equality must set phase hint to true (Z3 try_true_first)"
    );
}

/// Verify that calling `apply_model_equality` on an already-registered atom
/// still refreshes the phase hint to `true` (#4906, #6160 Gap 2).
#[test]
fn test_apply_model_equality_refreshes_phase_hint_on_existing_atom() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    let eq_atom = TermId::new(500);

    // Register the atom manually (no phase hint set by register_theory_atom).
    dpll.register_theory_atom(eq_atom, 0);
    let var = dpll
        .var_for_term(eq_atom)
        .expect("atom should be registered");

    // Phase should not be set yet (register_theory_atom doesn't set phase).
    // Note: the SAT solver may have a default phase, but no explicit hint.
    // We don't assert the pre-condition since default phase behavior varies.

    // apply_model_equality should set the phase hint to true.
    dpll.apply_model_equality(eq_atom);

    assert_eq!(
        dpll.sat_solver().var_phase(var),
        Some(true),
        "apply_model_equality must set phase hint to true even for pre-existing atoms"
    );
}

/// Verify model equality atoms survive a SAT-state round trip and new atoms can
/// be added incrementally without rebuilding from Tseitin (#6282).
#[test]
fn test_apply_model_equality_after_sat_state_round_trip_6282() {
    let terms = TermStore::new();
    let mut dpll = DpllT::new(0, PropositionalTheory);

    let eq_atom1 = TermId::new(600);
    let eq_atom2 = TermId::new(601);

    dpll.apply_model_equality(eq_atom1);
    let eq_var1 = dpll
        .var_for_term(eq_atom1)
        .expect("first model equality should register a SAT variable");

    let sat_state = dpll.into_sat_state();
    let mut dpll = DpllT::from_sat_state(&terms, PropositionalTheory, sat_state);

    assert_eq!(
        dpll.var_for_term(eq_atom1),
        Some(eq_var1),
        "SAT-state reconstruction should preserve existing model equality atoms"
    );

    dpll.apply_model_equality(eq_atom2);

    let eq_var2 = dpll
        .var_for_term(eq_atom2)
        .expect("second model equality should register after reconstruction");

    assert_ne!(
        eq_var1, eq_var2,
        "incremental model equality should allocate a fresh SAT variable"
    );
    assert_eq!(
        dpll.term_for_var(eq_var1),
        Some(eq_atom1),
        "round-trip reconstruction must preserve the original reverse mapping"
    );
    assert_eq!(
        dpll.term_for_var(eq_var2),
        Some(eq_atom2),
        "newly added model equality must be visible through the reverse mapping"
    );
    assert_eq!(
        dpll.sat_solver().var_phase(eq_var1),
        Some(true),
        "original model equality should keep its positive phase hint"
    );
    assert_eq!(
        dpll.sat_solver().var_phase(eq_var2),
        Some(true),
        "incrementally added model equality should also get a positive phase hint"
    );
}
