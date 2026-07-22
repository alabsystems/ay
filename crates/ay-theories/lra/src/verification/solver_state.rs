// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Solver State Invariants
// ========================================================================

/// Push increases scope depth, pop decreases it
#[kani::proof]
fn proof_push_pop_scope_depth() {
    let terms = ay_core::term::TermStore::new();
    let mut solver = LraSolver::new(&terms);

    let initial_scopes = solver.scopes.len();
    assert!(initial_scopes == 0, "Initially no scopes");

    solver.push();
    assert!(solver.scopes.len() == 1, "Push adds scope");

    solver.push();
    assert!(solver.scopes.len() == 2, "Second push adds scope");

    solver.pop();
    assert!(solver.scopes.len() == 1, "Pop removes scope");

    solver.pop();
    assert!(solver.scopes.len() == 0, "Final pop returns to empty");
}

/// Pop on empty scopes is safe (no-op)
#[kani::proof]
fn proof_pop_empty_is_safe() {
    let terms = ay_core::term::TermStore::new();
    let mut solver = LraSolver::new(&terms);

    // Pop with no pushes should be a no-op
    solver.pop();
    assert!(solver.scopes.is_empty(), "Pop on empty is no-op");
}

/// Reset clears all state
#[kani::proof]
fn proof_reset_clears_state() {
    let terms = ay_core::term::TermStore::new();
    let mut solver = LraSolver::new(&terms);

    // Add some state
    solver.push();
    solver.next_var = 10;

    solver.reset();

    assert!(solver.rows.is_empty(), "Reset clears rows");
    assert!(solver.vars.is_empty(), "Reset clears vars");
    assert!(solver.term_to_var.is_empty(), "Reset clears term_to_var");
    assert!(solver.var_to_term.is_empty(), "Reset clears var_to_term");
    assert!(solver.next_var == 0, "Reset resets next_var");
    assert!(solver.trail.is_empty(), "Reset clears trail");
    assert!(solver.scopes.is_empty(), "Reset clears scopes");
    assert!(solver.asserted.is_empty(), "Reset clears asserted");
}

/// Asserting a constant Bool contradiction is UNSAT.
///
/// This covers cases like `X != X` where the term layer folds `(= X X)` to `true`.
#[kani::proof]
fn proof_bool_constant_contradiction_is_unsat() {
    let mut terms = ay_core::term::TermStore::new();

    // X != X should be UNSAT (reflexivity of equality)
    let x = terms.mk_var("X", ay_core::Sort::Real);
    let eq_xx = terms.mk_eq(x, x);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq_xx, false); // X != X

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "X != X must be UNSAT (reflexivity), got {:?}",
        result
    );
}
