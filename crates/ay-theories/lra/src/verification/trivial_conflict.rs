// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========================================================================
// Trivial Conflict Proofs (#2012, #2016, #2017)
// ========================================================================

/// Trivial conflicts recorded in a scope are cleared on pop().
///
/// Part of #2016: When a scope containing a trivial conflict is popped,
/// the conflict must be cleared so that subsequent checks don't incorrectly
/// return UNSAT.
#[kani::proof]
fn proof_trivial_conflict_cleared_on_pop() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let atom = terms.mk_lt(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.push();

    // Create a violated constant constraint: 1 <= 0 (false).
    solver.assert_bound(
        LinearExpr::constant(BigRational::one()),
        BigRational::zero(),
        BoundType::Upper,
        false,
        atom,
        true,
    );
    assert!(
        solver.trivial_conflict.is_some(),
        "Expected a recorded trivial conflict"
    );

    solver.pop();
    assert!(
        solver.trivial_conflict.is_none(),
        "pop() must clear trivial_conflict"
    );
}

/// Trivial conflicts are returned before any simplex iterations run.
///
/// Part of #2017: When a trivial conflict is detected (e.g., a constant
/// constraint like `1 <= 0`), dual_simplex must return UNSAT immediately
/// without performing any pivot iterations.
#[kani::proof]
fn proof_trivial_conflict_returned_before_simplex() {
    let mut terms = ay_core::term::TermStore::new();
    let x = terms.mk_var("x", ay_core::Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let atom = terms.mk_lt(x, zero);

    let mut solver = LraSolver::new(&terms);

    // Create a violated constant constraint: 1 <= 0 (false).
    solver.assert_bound(
        LinearExpr::constant(BigRational::one()),
        BigRational::zero(),
        BoundType::Upper,
        false,
        atom,
        true,
    );

    // Even with zero iteration budget, the solver must return UNSAT from trivial_conflict.
    let expected = TheoryLit::new(atom, true);
    let result = solver.dual_simplex_with_max_iters(0);
    match result {
        TheoryResult::Unsat(lits) => assert!(lits.contains(&expected), "{lits:?}"),
        other => panic!("Expected UNSAT, got {other:?}"),
    }
    assert!(
        solver.trivial_conflict.is_none(),
        "dual_simplex must consume trivial_conflict"
    );
}
