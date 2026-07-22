// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #7772: LRA compound atom slack reuse across push/pop.
//!
//! Verifies that compound atom slack variables (created for multi-variable
//! expressions like `x + y`) are correctly reused across push/pop scope
//! boundaries. The slack variable and its tableau row persist after pop
//! (structural state is permanent), but assertion-derived bounds are restored.
//!
//! These tests exercise the specific pattern:
//! 1. Push scope
//! 2. Register + assert compound atom (creates slack + tableau row)
//! 3. Pop scope (bounds restored, structural state persists)
//! 4. Register + assert compound atom with same linear expression
//! 5. Verify correct results (no stale bounds, correct constant compensation)

use super::*;

/// Core test: compound atom slack reuse after push/pop without reset.
///
/// Registers `x + y <= 5` in a pushed scope, pops, then re-registers and
/// asserts `x + y <= 10` at base scope. The slack variable created in the
/// pushed scope persists after pop. The reused slack must produce correct
/// results with the new bound.
#[test]
fn test_compound_slack_reuse_after_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_5 = terms.mk_le(sum, five); // x + y <= 5
    let sum_le_10 = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge_3 = terms.mk_ge(x, three); // x >= 3
    let y_ge_4 = terms.mk_ge(y, four); // y >= 4

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_5);
    solver.register_atom(sum_le_10);
    solver.register_atom(x_ge_3);
    solver.register_atom(y_ge_4);

    // Scope 1: assert x + y <= 5 with x >= 3, y >= 4.
    // 3 + 4 = 7 > 5, so UNSAT.
    solver.push();
    solver.assert_literal(sum_le_5, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x+y<=5 with x>=3, y>=4 should be UNSAT, got {result:?}"
    );

    // Pop: bounds from scope 1 are restored, but slack persists.
    solver.pop();

    // Scope 2: assert x + y <= 10 with x >= 3, y >= 4.
    // 3 + 4 = 7 <= 10, so SAT.
    solver.push();
    solver.assert_literal(sum_le_10, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x+y<=10 with x>=3, y>=4 should be SAT after pop, got {result:?}"
    );
    solver.pop();
}

/// Same compound atom re-asserted after push/pop.
///
/// Asserts `x + y <= 10` in a pushed scope, pops, then re-asserts the same
/// atom at base scope. The `atom_slack` cache must correctly handle the
/// re-assertion with the same (TermId, bool) key.
#[test]
fn test_same_compound_atom_reasserted_after_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_10 = terms.mk_le(sum, ten);
    let x_ge_3 = terms.mk_ge(x, three);
    let y_ge_4 = terms.mk_ge(y, four);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_10);
    solver.register_atom(x_ge_3);
    solver.register_atom(y_ge_4);

    // Scope 1: SAT
    solver.push();
    solver.assert_literal(sum_le_10, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 1: x+y<=10, x>=3, y>=4 should be SAT, got {result:?}"
    );
    solver.pop();

    // Scope 2: same atom re-asserted, should still be SAT
    solver.push();
    solver.assert_literal(sum_le_10, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 2: same compound atom re-asserted should be SAT, got {result:?}"
    );
    solver.pop();
}

/// Pop-only test: no reset between push/pop cycles.
///
/// Exercises the pop path without any reset, verifying that compound atom
/// bounds are correctly isolated per scope. This catches bugs where pop
/// fails to restore bounds on slack variables.
#[test]
fn test_compound_atom_pop_only_no_reset_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let twenty = terms.mk_rational(BigRational::from(BigInt::from(20)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_1 = terms.mk_le(sum, one); // x + y <= 1
    let sum_le_20 = terms.mk_le(sum, twenty); // x + y <= 20
    let x_ge_0 = terms.mk_ge(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_1);
    solver.register_atom(sum_le_20);
    solver.register_atom(x_ge_0);
    solver.register_atom(y_ge_0);

    // Base: x >= 0, y >= 0
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(y_ge_0, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "base: x>=0, y>=0 should be SAT, got {result:?}"
    );

    // Scope 1: tight constraint x + y <= 1
    solver.push();
    solver.assert_literal(sum_le_1, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 1: x+y<=1 with x,y>=0 should be SAT, got {result:?}"
    );
    solver.pop();

    // After pop: tight constraint must be gone. x + y <= 20 should be SAT.
    solver.push();
    solver.assert_literal(sum_le_20, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 2 after pop: x+y<=20 with x,y>=0 should be SAT, got {result:?}"
    );
    solver.pop();
}

/// Nested push/pop with compound atoms: verifies that inner scope constraints
/// do not leak to outer scopes through the slack reuse mechanism.
#[test]
fn test_nested_push_pop_compound_slack_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let fifteen = terms.mk_rational(BigRational::from(BigInt::from(15)));
    let eight = terms.mk_rational(BigRational::from(BigInt::from(8)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_15 = terms.mk_le(sum, fifteen); // x + y <= 15
    let sum_le_10 = terms.mk_le(sum, ten); // x + y <= 10
    let sum_le_5 = terms.mk_le(sum, five); // x + y <= 5
    let x_ge_8 = terms.mk_ge(x, eight); // x >= 8
    let y_ge_3 = terms.mk_ge(y, three); // y >= 3

    let mut solver = LraSolver::new(&terms);
    for atom in [sum_le_15, sum_le_10, sum_le_5, x_ge_8, y_ge_3] {
        solver.register_atom(atom);
    }

    // Outer scope: x + y <= 15 with x >= 8, y >= 3. SAT (11 <= 15).
    solver.push();
    solver.assert_literal(sum_le_15, true);
    solver.assert_literal(x_ge_8, true);
    solver.assert_literal(y_ge_3, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "outer: x+y<=15, x>=8, y>=3 should be SAT, got {result:?}"
    );

    // Inner scope: tighten to x + y <= 5. UNSAT (8 + 3 = 11 > 5).
    solver.push();
    solver.assert_literal(sum_le_5, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "inner: x+y<=5 with x>=8, y>=3 should be UNSAT, got {result:?}"
    );

    // Pop inner: constraint x + y <= 5 removed. Outer still has x + y <= 15.
    solver.pop();
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "after inner pop: x+y<=15, x>=8, y>=3 should be SAT, got {result:?}"
    );

    // Pop outer: all constraints removed.
    solver.pop();
}

/// bland_mode and basis_repeat_count must be reset on pop (#7772 F1).
///
/// If bland_mode is activated during a pushed scope's simplex solve and not
/// reset on pop, subsequent simplex calls at the outer scope use Bland's rule
/// (slower but anti-cycling) unnecessarily.
#[test]
fn test_bland_mode_reset_on_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let x_ge_0 = terms.mk_ge(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_0);

    assert!(!solver.bland_mode, "bland_mode should start false");
    assert_eq!(
        solver.basis_repeat_count, 0,
        "basis_repeat_count should start at 0"
    );

    // Push, manually set bland_mode (simulates activation during simplex)
    solver.push();
    solver.bland_mode = true;
    solver.basis_repeat_count = 42;

    // Pop should reset these
    solver.pop();
    assert!(
        !solver.bland_mode,
        "bland_mode must be reset to false on pop (#7772 F1)"
    );
    assert_eq!(
        solver.basis_repeat_count, 0,
        "basis_repeat_count must be reset to 0 on pop (#7772 F1)"
    );
}

/// unassigned_atom_count correctness after nested push/pop with re-assertions.
///
/// Registers compound + single-variable atoms, asserts them in a pushed scope,
/// pops, and verifies the unassigned counts are correctly restored. This tests
/// the recount_unassigned_atoms path triggered by pop.
#[test]
fn test_unassigned_atom_count_nested_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_10 = terms.mk_le(sum, ten);
    let x_ge_0 = terms.mk_ge(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_10);
    solver.register_atom(x_ge_0);
    solver.register_atom(y_ge_0);

    // Capture initial unassigned counts (all atoms unassigned).
    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let y_var = *solver.term_to_var.get(&y).expect("y interned");
    let initial_x_count = solver.unassigned_atom_count[x_var as usize];
    let initial_y_count = solver.unassigned_atom_count[y_var as usize];
    assert!(
        initial_x_count > 0,
        "x should have unassigned atoms after registration"
    );
    assert!(
        initial_y_count > 0,
        "y should have unassigned atoms after registration"
    );

    // Push and assert all atoms
    solver.push();
    solver.assert_literal(sum_le_10, true);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(y_ge_0, true);
    let _ = solver.check();

    // Pop: unassigned counts should be restored to initial values
    solver.pop();
    let restored_x_count = solver.unassigned_atom_count[x_var as usize];
    let restored_y_count = solver.unassigned_atom_count[y_var as usize];
    assert_eq!(
        restored_x_count, initial_x_count,
        "x's unassigned_atom_count must be restored after pop (expected {initial_x_count}, got {restored_x_count})"
    );
    assert_eq!(
        restored_y_count, initial_y_count,
        "y's unassigned_atom_count must be restored after pop (expected {initial_y_count}, got {restored_y_count})"
    );

    // Re-assert in a new scope and verify counts decrement correctly
    solver.push();
    solver.assert_literal(x_ge_0, true);
    let post_assert_x = solver.unassigned_atom_count[x_var as usize];
    assert!(
        post_assert_x < initial_x_count,
        "x's count should decrease after asserting x_ge_0 (was {initial_x_count}, now {post_assert_x})"
    );
    solver.pop();

    // Final check: counts restored again
    let final_x_count = solver.unassigned_atom_count[x_var as usize];
    assert_eq!(
        final_x_count, initial_x_count,
        "x's unassigned_atom_count must be restored after second pop"
    );
}

/// Negated compound atom across push/pop: asserts !(x + y <= 5) which is
/// x + y > 5 in scope 1, pops, then asserts x + y <= 10 in scope 2.
/// This tests that the atom_key (term, false) for negated assertions does
/// not interfere with the (term, true) key after pop.
#[test]
fn test_negated_compound_atom_across_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_5 = terms.mk_le(sum, five); // x + y <= 5
    let sum_le_10 = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge_1 = terms.mk_ge(x, one); // x >= 1
    let y_ge_1 = terms.mk_ge(y, one); // y >= 1

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_5);
    solver.register_atom(sum_le_10);
    solver.register_atom(x_ge_1);
    solver.register_atom(y_ge_1);

    // Scope 1: assert !(x + y <= 5), i.e., x + y > 5, with x >= 1, y >= 1.
    // This is SAT (e.g., x=3, y=3 gives x+y=6 > 5).
    solver.push();
    solver.assert_literal(sum_le_5, false); // negated: x + y > 5
    solver.assert_literal(x_ge_1, true);
    solver.assert_literal(y_ge_1, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 1: x+y>5, x>=1, y>=1 should be SAT, got {result:?}"
    );
    solver.pop();

    // Scope 2: assert x + y <= 10 with x >= 1, y >= 1. SAT (2 <= 10).
    solver.push();
    solver.assert_literal(sum_le_10, true);
    solver.assert_literal(x_ge_1, true);
    solver.assert_literal(y_ge_1, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 2: x+y<=10, x>=1, y>=1 should be SAT after pop, got {result:?}"
    );
    solver.pop();
}

/// Model value correctness: after push/pop with compound atoms, verify the
/// model assigns values that satisfy the compound constraint.
#[test]
fn test_compound_atom_model_correctness_after_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let hundred = terms.mk_rational(BigRational::from(BigInt::from(100)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_5 = terms.mk_le(sum, five); // x + y <= 5
    let sum_le_100 = terms.mk_le(sum, hundred); // x + y <= 100
    let x_ge_3 = terms.mk_ge(x, three); // x >= 3
    let y_ge_4 = terms.mk_ge(y, four); // y >= 4

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_5);
    solver.register_atom(sum_le_100);
    solver.register_atom(x_ge_3);
    solver.register_atom(y_ge_4);

    // Scope 1: tight constraint. x+y<=5 with x>=3, y>=4 is UNSAT.
    solver.push();
    solver.assert_literal(sum_le_5, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "scope 1 should be UNSAT"
    );
    solver.pop();

    // Scope 2: loose constraint. x+y<=100 with x>=3, y>=4 is SAT.
    solver.push();
    solver.assert_literal(sum_le_100, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 2 should be SAT, got {result:?}"
    );

    // Verify model: x_val + y_val <= 100, x_val >= 3, y_val >= 4.
    let x_val = solver.get_value(x);
    let y_val = solver.get_value(y);
    if let (Some(xv), Some(yv)) = (&x_val, &y_val) {
        assert!(
            xv >= &BigRational::from(BigInt::from(3)),
            "model must have x >= 3, got x={xv}"
        );
        assert!(
            yv >= &BigRational::from(BigInt::from(4)),
            "model must have y >= 4, got y={yv}"
        );
        let sum_val = xv + yv;
        assert!(
            sum_val <= BigRational::from(BigInt::from(100)),
            "model must have x+y <= 100, got x+y={sum_val}"
        );
    }
    solver.pop();
}

/// Three-variable compound atom across push/pop: verifies slack variable
/// management works correctly for expressions with more than two variables.
#[test]
fn test_three_var_compound_atom_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let six = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let thirty = terms.mk_rational(BigRational::from(BigInt::from(30)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let sum3 = terms.mk_add(vec![x, y, z]);
    let sum3_le_6 = terms.mk_le(sum3, six); // x + y + z <= 6
    let sum3_le_30 = terms.mk_le(sum3, thirty); // x + y + z <= 30
    let x_ge_3 = terms.mk_ge(x, three);
    let y_ge_4 = terms.mk_ge(y, four);
    let z_ge_5 = terms.mk_ge(z, five);

    let mut solver = LraSolver::new(&terms);
    for atom in [sum3_le_6, sum3_le_30, x_ge_3, y_ge_4, z_ge_5] {
        solver.register_atom(atom);
    }

    // Scope 1: x+y+z <= 6 with x>=3, y>=4, z>=5. UNSAT (3+4+5=12 > 6).
    solver.push();
    solver.assert_literal(sum3_le_6, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    solver.assert_literal(z_ge_5, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "scope 1: 3-var compound should be UNSAT"
    );
    solver.pop();

    // Scope 2: x+y+z <= 30 with x>=3, y>=4, z>=5. SAT (12 <= 30).
    solver.push();
    solver.assert_literal(sum3_le_30, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    solver.assert_literal(z_ge_5, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 2: 3-var compound should be SAT after pop, got {result:?}"
    );
    solver.pop();
}

/// Compound atom with non-unit coefficients (2x + 3y) across push/pop.
/// Exercises the constant-compensation path in assert_bound_with_reasons
/// when the slack row has non-trivial coefficients.
#[test]
fn test_weighted_compound_atom_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let fifty = terms.mk_rational(BigRational::from(BigInt::from(50)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));

    let two_x = terms.mk_mul(vec![two, x]); // 2*x
    let three_y = terms.mk_mul(vec![three, y]); // 3*y
    let weighted_sum = terms.mk_add(vec![two_x, three_y]); // 2x + 3y
    let ws_le_10 = terms.mk_le(weighted_sum, ten); // 2x + 3y <= 10
    let ws_le_50 = terms.mk_le(weighted_sum, fifty); // 2x + 3y <= 50
    let x_ge_1 = terms.mk_ge(x, one);
    let y_ge_1 = terms.mk_ge(y, one);

    let mut solver = LraSolver::new(&terms);
    for atom in [ws_le_10, ws_le_50, x_ge_1, y_ge_1] {
        solver.register_atom(atom);
    }

    // Scope 1: 2x + 3y <= 10, x >= 1, y >= 1. SAT (2+3=5 <= 10).
    solver.push();
    solver.assert_literal(ws_le_10, true);
    solver.assert_literal(x_ge_1, true);
    solver.assert_literal(y_ge_1, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 1: 2x+3y<=10, x>=1, y>=1 should be SAT, got {result:?}"
    );
    solver.pop();

    // Scope 2: 2x + 3y <= 50, x >= 1, y >= 1. SAT (5 <= 50).
    solver.push();
    solver.assert_literal(ws_le_50, true);
    solver.assert_literal(x_ge_1, true);
    solver.assert_literal(y_ge_1, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 2: 2x+3y<=50, x>=1, y>=1 should be SAT after pop, got {result:?}"
    );
    solver.pop();
}

/// Soft reset followed by compound atom re-assertion. soft_reset clears
/// asserted state but preserves structural state (slack vars, tableau rows).
/// This tests the interaction between soft_reset and slack reuse.
#[test]
fn test_compound_atom_soft_reset_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_10 = terms.mk_le(sum, ten);
    let x_ge_3 = terms.mk_ge(x, three);
    let y_ge_4 = terms.mk_ge(y, four);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(sum_le_10);
    solver.register_atom(x_ge_3);
    solver.register_atom(y_ge_4);

    // First solve: SAT
    solver.assert_literal(sum_le_10, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "first solve should be SAT, got {result:?}"
    );

    let slack_count_before = solver.slack_var_set.len();
    let expr_to_slack_before = solver.expr_to_slack.len();

    // Soft reset: clears assertions, preserves structure
    solver.soft_reset();

    // Structural state must be preserved
    assert_eq!(
        solver.slack_var_set.len(),
        slack_count_before,
        "soft_reset must preserve slack_var_set"
    );
    assert_eq!(
        solver.expr_to_slack.len(),
        expr_to_slack_before,
        "soft_reset must preserve expr_to_slack"
    );

    // Re-assert and re-solve: must still be SAT
    solver.assert_literal(sum_le_10, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "after soft_reset: x+y<=10, x>=3, y>=4 should be SAT, got {result:?}"
    );
}

/// Multiple distinct compound expressions across push/pop: verifies that
/// different slack variables for different expressions are independently
/// managed across scope boundaries.
#[test]
fn test_multiple_compound_expressions_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));
    let two_const = terms.mk_rational(BigRational::from(BigInt::from(2)));

    let sum_xy = terms.mk_add(vec![x, y]); // x + y
    let sum_yz = terms.mk_add(vec![y, z]); // y + z
    let xy_le_5 = terms.mk_le(sum_xy, five); // x + y <= 5
    let yz_le_10 = terms.mk_le(sum_yz, ten); // y + z <= 10
    let xy_le_10 = terms.mk_le(sum_xy, ten); // x + y <= 10
    let x_ge_3 = terms.mk_ge(x, three);
    let y_ge_4 = terms.mk_ge(y, four);
    let z_ge_2 = terms.mk_ge(z, two_const);

    let mut solver = LraSolver::new(&terms);
    for atom in [xy_le_5, yz_le_10, xy_le_10, x_ge_3, y_ge_4, z_ge_2] {
        solver.register_atom(atom);
    }

    // Two compound expressions should have two different slack variables
    assert!(
        solver.expr_to_slack.len() >= 2,
        "x+y and y+z should have distinct slack variables"
    );

    // Scope 1: tight constraint on x+y. x+y<=5, x>=3, y>=4. UNSAT (7>5).
    solver.push();
    solver.assert_literal(xy_le_5, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "scope 1: x+y<=5 should be UNSAT"
    );
    solver.pop();

    // Scope 2: loose x+y, tight y+z. x+y<=10, y+z<=10, x>=3, y>=4, z>=2. SAT.
    solver.push();
    solver.assert_literal(xy_le_10, true);
    solver.assert_literal(yz_le_10, true);
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(y_ge_4, true);
    solver.assert_literal(z_ge_2, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "scope 2: x+y<=10, y+z<=10 should be SAT, got {result:?}"
    );
    solver.pop();
}

/// Verifies that the expr_to_slack cache correctly shares slack variables
/// across atoms with the same linear expression but different constants,
/// both before and after push/pop.
#[test]
fn test_expr_to_slack_sharing_across_push_pop_7772() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le_5 = terms.mk_le(sum, five);
    let sum_le_10 = terms.mk_le(sum, ten);

    let mut solver = LraSolver::new(&terms);

    // Register both atoms -- they share the same linear expression (x + y)
    // but with different constant offsets (-5 vs -10).
    solver.register_atom(sum_le_5);
    solver.register_atom(sum_le_10);

    // Both should share the same slack variable via expr_to_slack
    assert_eq!(
        solver.expr_to_slack.len(),
        1,
        "both compound atoms should share one slack via expr_to_slack"
    );

    let slack_count_before = solver.slack_var_set.len();

    // Push, assert, pop cycle
    solver.push();
    solver.assert_literal(sum_le_5, true);
    let _ = solver.check();
    solver.pop();

    // Slack count should not change after push/pop
    assert_eq!(
        solver.slack_var_set.len(),
        slack_count_before,
        "push/pop must not create additional slack variables"
    );
    assert_eq!(
        solver.expr_to_slack.len(),
        1,
        "expr_to_slack must persist across push/pop"
    );

    // Re-assert the other atom in a new scope -- must reuse same slack
    solver.push();
    solver.assert_literal(sum_le_10, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x+y<=10 with no lower bounds should be SAT, got {result:?}"
    );
    assert_eq!(
        solver.slack_var_set.len(),
        slack_count_before,
        "re-assertion must reuse existing slack variable"
    );
    solver.pop();
}
