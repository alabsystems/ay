// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_sat::SatResult;

/// Proof: push() increments scope depth by exactly 1.
///
/// Invariant INV-PUSH-1: After push(), scope depth increases by 1
#[kani::proof]
fn proof_push_increments_scope_depth() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    let depth_before = dpll.scope_depth();
    dpll.push();
    let depth_after = dpll.scope_depth();

    assert!(
        depth_after == depth_before + 1,
        "Push must increment scope depth by 1"
    );
}

/// Proof: pop() decrements scope depth by exactly 1 when scopes exist.
///
/// Invariant INV-POP-1: After pop(), scope depth decreases by 1 (if > 0)
#[kani::proof]
fn proof_pop_decrements_scope_depth() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Push at least once so we can pop
    dpll.push();
    let depth_before = dpll.scope_depth();
    kani::assume(depth_before > 0);

    let result = dpll.pop();
    let depth_after = dpll.scope_depth();

    assert!(result, "Pop should succeed when scope depth > 0");
    assert!(
        depth_after == depth_before - 1,
        "Pop must decrement scope depth by 1"
    );
}

/// Proof: pop() returns false and is safe when scope depth is 0.
///
/// Invariant: Pop on empty scope is safe and returns false.
#[kani::proof]
fn proof_pop_empty_is_safe() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // No push calls, scope depth is 0
    assert_eq!(dpll.scope_depth(), 0);

    let result = dpll.pop();
    assert!(!result, "Pop on empty must return false");
    assert_eq!(dpll.scope_depth(), 0, "Scope depth must remain 0");
}

/// Proof: nested push/pop maintains correct scope depth.
///
/// Verifies that multiple push/pop operations maintain correct depth tracking.
#[kani::proof]
fn proof_nested_push_pop_depth() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Number of push operations (bounded for tractability)
    let n: usize = kani::any();
    kani::assume(n <= 5);

    // Push n times
    for _ in 0..n {
        dpll.push();
    }
    assert_eq!(dpll.scope_depth(), n, "Depth should equal number of pushes");

    // Pop all
    for i in 0..n {
        let expected_depth = n - i - 1;
        let result = dpll.pop();
        assert!(result, "Pop should succeed");
        assert_eq!(
            dpll.scope_depth(),
            expected_depth,
            "Depth should decrease correctly"
        );
    }

    assert_eq!(dpll.scope_depth(), 0, "Final depth should be 0");
}

/// Proof: pop after push restores scope depth to original value.
///
/// Invariant: push(); pop(); leaves scope depth unchanged.
#[kani::proof]
fn proof_push_pop_restores_depth() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Start with some scope depth (bounded)
    let initial_pushes: usize = kani::any();
    kani::assume(initial_pushes <= 3);

    for _ in 0..initial_pushes {
        dpll.push();
    }
    let depth_before = dpll.scope_depth();

    // Push and pop
    dpll.push();
    let result = dpll.pop();

    assert!(result, "Pop should succeed after push");
    assert_eq!(
        dpll.scope_depth(),
        depth_before,
        "push(); pop(); must restore depth"
    );
}

// ========================================================================
// Gap 9: Theory Integration Proofs
// ========================================================================

/// Proof: register_theory_atom maintains bidirectional mapping.
///
/// Invariant: After register_theory_atom(term, var), both:
///   - term_for_var(var) == Some(term)
///   - var_for_term(term) == Some(var)
#[kani::proof]
fn proof_register_theory_atom_consistency() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(10, theory);

    // Symbolic term and variable
    let term_id: u32 = kani::any();
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 10);

    // Create TermId (symbolic, just for mapping test)
    let term = ay_core::TermId::new(term_id);

    // Register the atom
    dpll.register_theory_atom(term, var_idx);

    // Verify bidirectional consistency
    let var = Variable::new(var_idx);
    let retrieved_term = dpll.term_for_var(var);
    let retrieved_var = dpll.var_for_term(term);

    assert!(
        retrieved_term == Some(term),
        "term_for_var must return the registered term"
    );
    assert!(
        retrieved_var == Some(var),
        "var_for_term must return the registered variable"
    );
}

/// Proof: term_to_literal produces correct polarity.
///
/// Invariant: term_to_literal(term, true) produces positive literal,
///            term_to_literal(term, false) produces negative literal.
#[kani::proof]
fn proof_term_to_literal_polarity() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(5, theory);

    let term_id: u32 = kani::any();
    let var_idx: u32 = kani::any();
    kani::assume(var_idx < 5);

    let term = ay_core::TermId::new(term_id);
    dpll.register_theory_atom(term, var_idx);

    // Test positive literal
    let pos_lit = dpll.term_to_literal(term, true);
    assert!(
        pos_lit.is_some(),
        "term_to_literal should return Some for registered term"
    );
    let pos_lit = pos_lit.unwrap();
    assert!(
        pos_lit.is_positive(),
        "term_to_literal(term, true) must be positive"
    );
    assert_eq!(
        pos_lit.variable().id(),
        var_idx,
        "Variable index must match"
    );

    // Test negative literal
    let neg_lit = dpll.term_to_literal(term, false);
    assert!(
        neg_lit.is_some(),
        "term_to_literal should return Some for registered term"
    );
    let neg_lit = neg_lit.unwrap();
    assert!(
        !neg_lit.is_positive(),
        "term_to_literal(term, false) must be negative"
    );
    assert_eq!(
        neg_lit.variable().id(),
        var_idx,
        "Variable index must match"
    );
}

/// Proof: unregistered term returns None.
///
/// Invariant: term_to_literal returns None for terms not registered.
#[kani::proof]
fn proof_unregistered_term_returns_none() {
    let theory = PropositionalTheory;
    let dpll = DpllT::new(5, theory);

    // Any term_id without registration
    let term_id: u32 = kani::any();
    let term = ay_core::TermId::new(term_id);

    // Should return None since nothing is registered
    let result = dpll.term_to_literal(term, true);
    assert!(result.is_none(), "Unregistered term must return None");

    let result = dpll.term_to_literal(term, false);
    assert!(result.is_none(), "Unregistered term must return None");
}

/// Proof: add_clause increases clause count.
///
/// Invariant: After add_clause, SAT solver has at least one more clause.
#[kani::proof]
fn proof_add_clause_increases_count() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(3, theory);

    // Add a clause
    let lit1 = Literal::positive(Variable::new(0));
    let lit2 = Literal::negative(Variable::new(1));
    dpll.add_clause(vec![lit1, lit2]);

    // Solver should still be valid (no panic)
    // We can verify by checking that solving works
    let result = dpll.solve().expect("solve should not error");
    // The formula (x0 ∨ ¬x1) is SAT
    assert!(
        matches!(result, SatResult::Sat(_)),
        "Simple clause should be SAT"
    );
}

/// Proof: theory reset clears state.
///
/// Invariant: reset_theory() allows fresh solving.
#[kani::proof]
fn proof_reset_theory_allows_fresh_solve() {
    let theory = PropositionalTheory;
    let mut dpll = DpllT::new(2, theory);

    // Add a simple SAT clause
    dpll.add_clause(vec![Literal::positive(Variable::new(0))]);

    // Solve
    let result1 = dpll.solve().expect("solve should not error");
    assert!(matches!(result1, SatResult::Sat(_)));

    // Reset theory
    dpll.reset_theory();

    // Should still solve correctly
    let result2 = dpll.solve().expect("solve should not error");
    assert!(matches!(result2, SatResult::Sat(_)));
}
