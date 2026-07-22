// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_fractional_part() {
    // frac(6/5) = frac(1.2) = 0.2 = 1/5
    let v = BigRational::new(BigInt::from(6), BigInt::from(5));
    assert_eq!(
        fractional_part(&v),
        BigRational::new(BigInt::from(1), BigInt::from(5))
    );

    // frac(-6/5) = frac(-1.2) = -1.2 - floor(-1.2) = -1.2 - (-2) = 0.8 = 4/5
    let v = BigRational::new(BigInt::from(-6), BigInt::from(5));
    assert_eq!(
        fractional_part(&v),
        BigRational::new(BigInt::from(4), BigInt::from(5))
    );

    // frac(31/5) = frac(6.2) = 0.2 = 1/5
    let v = BigRational::new(BigInt::from(31), BigInt::from(5));
    assert_eq!(
        fractional_part(&v),
        BigRational::new(BigInt::from(1), BigInt::from(5))
    );

    // frac(5) = 0
    let v = BigRational::from(BigInt::from(5));
    assert_eq!(fractional_part(&v), BigRational::zero());

    // frac(-5) = 0
    let v = BigRational::from(BigInt::from(-5));
    assert_eq!(fractional_part(&v), BigRational::zero());

    // frac(1/5) = 1/5
    let v = BigRational::new(BigInt::from(1), BigInt::from(5));
    assert_eq!(
        fractional_part(&v),
        BigRational::new(BigInt::from(1), BigInt::from(5))
    );

    // frac(-1/5) = frac(-0.2) = -0.2 - (-1) = 0.8 = 4/5
    let v = BigRational::new(BigInt::from(-1), BigInt::from(5));
    assert_eq!(
        fractional_part(&v),
        BigRational::new(BigInt::from(4), BigInt::from(5))
    );
}

#[test]
fn test_linear_expr_basic() {
    let mut expr = LinearExpr::zero();
    assert!(expr.is_constant());
    assert!(expr.constant.is_zero());

    expr.add_term(0, BigRational::from(BigInt::from(3)));
    assert!(!expr.is_constant());
    assert_eq!(expr.coeffs.len(), 1);
    assert_eq!(expr.coeffs[0], (0, Rational::from(3_i64)));
}

#[test]
fn test_linear_expr_combine() {
    let mut expr = LinearExpr::zero();
    expr.add_term(0, BigRational::from(BigInt::from(3)));
    expr.add_term(0, BigRational::from(BigInt::from(2)));

    // Should combine: 3x + 2x = 5x
    assert_eq!(expr.coeffs.len(), 1);
    assert_eq!(expr.coeffs[0], (0, Rational::from(5_i64)));
}

#[test]
fn test_linear_expr_cancel() {
    let mut expr = LinearExpr::zero();
    expr.add_term(0, BigRational::from(BigInt::from(3)));
    expr.add_term(0, BigRational::from(BigInt::from(-3)));

    // Should cancel: 3x - 3x = 0
    assert!(expr.coeffs.is_empty());
}

#[test]
fn test_lra_solver_trivial_sat() {
    let terms = TermStore::new();
    let mut solver = LraSolver::new(&terms);

    // Empty problem is SAT
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_lra_needs_final_check_after_sat_for_bcp() {
    let terms = TermStore::new();
    assert!(LraSolver::new(&terms).needs_final_check_after_sat());
}

#[test]
fn test_lra_solver_simple_bound() {
    let mut terms = TermStore::new();

    // x <= 5
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let atom = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(atom, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_lra_solver_conflicting_bounds() {
    let mut terms = TermStore::new();

    // x >= 10 and x <= 5 should be UNSAT
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let le_atom = terms.mk_le(x, five); // x <= 5
    let ge_atom = terms.mk_ge(x, ten); // x >= 10

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_atom, true);
    solver.assert_literal(ge_atom, true);

    let result = solver.check();
    assert!(matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_lra_check_during_propagate_keeps_local_bound_conflict() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let le_atom = terms.mk_le(x, five);
    let ge_atom = terms.mk_ge(x, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_atom, true);
    solver.assert_literal(ge_atom, true);

    let result = solver.check_during_propagate();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "BCP-time LRA check must still report local arithmetic conflicts, got {result:?}"
    );
}

#[test]
fn test_lra_check_during_propagate_defers_disequality_conflict() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let eq = terms.mk_eq(x, five);
    let ge = terms.mk_ge(x, five);
    let le = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq, false);
    solver.assert_literal(ge, true);
    solver.assert_literal(le, true);

    assert!(
        matches!(solver.check_during_propagate(), TheoryResult::Sat),
        "BCP-time LRA check should defer disequality/model-only work to final check"
    );

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "final LRA check must still report the deferred disequality conflict, got {result:?}"
    );
}

#[test]
fn test_lra_solver_linear_constraint() {
    let mut terms = TermStore::new();

    // x + y <= 10, x >= 5, y >= 6 should be UNSAT (5 + 6 = 11 > 10)
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let six = terms.mk_rational(BigRational::from(BigInt::from(6)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge = terms.mk_ge(x, five); // x >= 5
    let y_ge = terms.mk_ge(y, six); // y >= 6

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    let result = solver.check();
    assert!(matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_lra_solver_linear_constraint_sat() {
    let mut terms = TermStore::new();

    // x + y <= 10, x >= 3, y >= 4 should be SAT (3 + 4 = 7 <= 10)
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
    let x_ge = terms.mk_ge(x, three); // x >= 3
    let y_ge = terms.mk_ge(y, four); // y >= 4

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat));
}

#[test]
fn test_lra_solver_push_pop() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let le_atom = terms.mk_le(x, ten); // x <= 10
    let ge_atom = terms.mk_ge(x, five); // x >= 5
    let lt_atom = terms.mk_lt(x, three); // x < 3

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_atom, true);
    solver.assert_literal(ge_atom, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Push and add conflicting constraint
    solver.push();
    solver.assert_literal(lt_atom, true);

    // x >= 5 and x < 3 conflicts
    let result = solver.check();
    assert!(matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));

    // Pop should restore SAT state
    solver.pop();
    solver.reset(); // Need reset to clear asserted atoms
    solver.assert_literal(le_atom, true);
    solver.assert_literal(ge_atom, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_pop_requeues_atom_index_vars_for_bound_reprop_6582() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_5 = terms.mk_le(x, five);
    let x_lt_0 = terms.mk_lt(x, zero);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_5);
    solver.register_atom(x_lt_0);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_5, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    assert!(
        solver.atom_index.contains_key(&x_var),
        "registered x atoms must remain indexed before pop()"
    );

    // #inc-prop-trail: pop no longer wholesale-clears propagated_atoms — it
    // removes exactly the entries inserted in the popped scopes (whose DPLL
    // literals the backtrack unassigned), while pre-push propagations (still
    // assigned, still justified by root-scope bounds) persist and are
    // correctly not re-sent. Capture the pre-push count to assert the
    // scope-exact rewind below.
    let root_propagated = solver.propagated_atoms.len();

    solver.push();
    solver.assert_literal(x_lt_0, true);
    let result = solver.check();
    assert!(matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));

    solver.pop();

    assert_eq!(
        solver.propagated_atoms.len(),
        root_propagated,
        "pop() must remove exactly the propagation markers inserted in the \
         popped scope (scope-exact trail rewind), preserving root-scope ones"
    );
    assert!(
        solver.propagation_dirty_vars.contains(&x_var),
        "pop() must re-mark atom_index vars dirty so bound propagation replays"
    );
}

#[test]
fn test_soft_reset_requeues_atom_index_vars_for_bound_reprop_6582() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.register_atom(x_ge_0);
    solver.register_atom(x_le_5);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_5, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");
    assert!(
        solver.atom_index.contains_key(&x_var),
        "soft_reset() regression requires preserved atom_index entries"
    );

    solver.soft_reset();

    assert!(
        solver.propagated_atoms.is_empty(),
        "soft_reset() should clear stale propagated atoms"
    );
    assert!(
        solver.atom_index.contains_key(&x_var),
        "soft_reset() must preserve atom_index for incremental replay"
    );
    assert!(
        solver.propagation_dirty_vars.contains(&x_var),
        "soft_reset() must re-mark atom_index vars dirty for replayed bound propagation"
    );
}

#[test]
fn test_pop_reseeds_compound_source_dirty_vars_6588() {
    assert_compound_source_keys_reseeded(CompoundDirtyResetKind::Pop);
}

#[test]
fn test_soft_reset_reseeds_compound_source_dirty_vars_6588() {
    assert_compound_source_keys_reseeded(CompoundDirtyResetKind::SoftReset);
}

#[test]
fn test_lra_solver_strict_inequality() {
    let mut terms = TermStore::new();

    // x < 5 and x > 5 should be UNSAT
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let lt_atom = terms.mk_lt(x, five); // x < 5
    let gt_atom = terms.mk_gt(x, five); // x > 5

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(lt_atom, true);
    solver.assert_literal(gt_atom, true);

    let result = solver.check();
    assert!(matches!(
        result,
        TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_lra_solver_equality() {
    let mut terms = TermStore::new();

    // x = 5 and x > 5 should be UNSAT
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let eq_atom = terms.mk_eq(x, five); // x = 5
    let gt_atom = terms.mk_gt(x, five); // x > 5

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq_atom, true);
    solver.assert_literal(gt_atom, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "{result:?}"
    );
}

#[test]
fn test_lra_solver_scaled_variable() {
    let mut terms = TermStore::new();

    // 2*x >= 10 should be SAT when x >= 5
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    let scaled = terms.mk_mul(vec![two, x]);
    let ge_scaled = terms.mk_ge(scaled, ten); // 2*x >= 10
    let ge_five = terms.mk_ge(x, five); // x >= 5

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_scaled, true);
    solver.assert_literal(ge_five, true);

    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn test_lra_solver_nonlinear_returns_unknown() {
    let mut terms = TermStore::new();

    // x * y = 1 is non-linear; the LRA solver must not claim SAT.
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));

    let xy = terms.mk_mul(vec![x, y]);
    let eq = terms.mk_eq(xy, one);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq, true);

    assert!(matches!(
        solver.check(),
        TheoryResult::Unknown | TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
    ));
}

#[test]
fn test_lra_solver_disequality_violated() {
    let mut terms = TermStore::new();

    // x != 5 combined with x = 5 should return UNSAT (model violates disequality).
    // The solver detects that the only solution (x=5) violates x != 5.
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x = 5 (equality atom, asserted as NOT TRUE means x != 5)
    let eq = terms.mk_eq(x, five);
    // x >= 5
    let ge = terms.mk_ge(x, five);
    // x <= 5
    let le = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    // Assert x != 5 by asserting the equality atom with value=false
    solver.assert_literal(eq, false);
    // Assert x >= 5
    solver.assert_literal(ge, true);
    // Assert x <= 5
    solver.assert_literal(le, true);

    // This is unsatisfiable (x=5 but x!=5). The solver should detect this
    // by checking that the model (x=5) violates the disequality.
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected Unsat but got {result:?}"
    );
}

/// Regression test for #805: X != X should return UNSAT (reflexivity)
///
/// **FIXED:** Issue #805 was fixed by adding Bool constant handling in check().
/// The term layer simplifies `X = X` to `true`, so asserting its negation
/// (`X != X`) asserts `false`, which is detected as UNSAT.
#[test]
fn test_lra_solver_reflexivity_x_neq_x() {
    let mut terms = TermStore::new();

    // X != X should be UNSAT (reflexivity of equality)
    let x = terms.mk_var("X", Sort::Real);
    let eq_xx = terms.mk_eq(x, x);

    let mut solver = LraSolver::new(&terms);
    // Assert X != X (equality asserted as false means disequality)
    solver.assert_literal(eq_xx, false);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "X != X must be UNSAT (reflexivity), but got {result:?}"
    );
}

#[test]
fn test_lra_solver_two_var_equality_with_bounds_sat() {
    let mut terms = TermStore::new();

    // 4*x + 3*y = 70, x >= 0, y >= 0, x <= 17 is satisfiable over reals.
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let four = terms.mk_rational(BigRational::from(BigInt::from(4)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let seventy = terms.mk_rational(BigRational::from(BigInt::from(70)));
    let zero = terms.mk_rational(BigRational::zero());
    let seventeen = terms.mk_rational(BigRational::from(BigInt::from(17)));

    let four_x = terms.mk_mul(vec![four, x]);
    let three_y = terms.mk_mul(vec![three, y]);
    let lhs = terms.mk_add(vec![four_x, three_y]);

    let eq = terms.mk_eq(lhs, seventy);
    let x_ge = terms.mk_ge(x, zero);
    let y_ge = terms.mk_ge(y, zero);
    let x_le = terms.mk_le(x, seventeen);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(x_le, true);

    let result = solver.check();
    assert!(matches!(result, TheoryResult::Sat), "{result:?}");
}

#[test]
fn test_lra_solver_distinct_atom_forced_unsat() {
    let mut terms = TermStore::new();

    // (distinct x 5) with x = 5 forced should return UNSAT.
    // This tests the distinct atom parsing (not negated equality).
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // Create distinct atom directly
    let distinct = terms.mk_distinct(vec![x, five]);
    // x >= 5
    let ge = terms.mk_ge(x, five);
    // x <= 5
    let le = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    // Assert (distinct x 5) = true means x != 5
    solver.assert_literal(distinct, true);
    // Assert x >= 5 and x <= 5, forcing x = 5
    solver.assert_literal(ge, true);
    solver.assert_literal(le, true);

    // x is forced to 5 but (distinct x 5) requires x != 5: UNSAT
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Expected Unsat but got {result:?}"
    );
}

#[test]
fn test_lra_solver_distinct_atom_with_slack_unknown() {
    let mut terms = TermStore::new();

    // (distinct x 5) with x >= 3 should return Unknown (or Sat with x != 5)
    // because simplex might find x=5 but other solutions exist.
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // Create distinct atom
    let distinct = terms.mk_distinct(vec![x, five]);
    // x >= 3
    let ge = terms.mk_ge(x, three);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(distinct, true);
    solver.assert_literal(ge, true);

    // Result should be Sat (x=3 or x=4 works) or Unknown (if simplex found x=5)
    // It should NOT be Unsat because solutions exist.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::Unknown),
        "Expected Sat or Unknown but got {result:?}"
    );
}
