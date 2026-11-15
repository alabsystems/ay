// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A ZERO coefficient in a linear expression means the expression does not
//! depend on that variable.
//!
//! `(* 0 x)` parsed through `LinearExpr::scale_rat(0)` used to keep the entry
//! `(x, 0)`; `is_expression_forced_to_value` then took the single-variable
//! branch and computed `(target - constant) / 0`, a divide-by-zero panic in
//! num-bigint. Reached end-to-end by the quantified model check of an affine
//! universal whose coefficients the model sets to 0
//! (`forall v. (f 1)*v = (f 0)*v or v = 3`): the nested refutation rebuilt a
//! proof through LRA's disequality check, panicked, and the session answered
//! `unknown` to that and every later check-sat.

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;

fn int(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(BigRational::from(BigInt::from(n)))
}

/// `x` registered and pinned to `[1, 1]`, so the single-variable branch finds
/// a `VarInfo` for it (an unregistered var returned `None` before the divide).
fn pinned_x(terms: &mut TermStore) -> (TermId, TermId, TermId) {
    let x = terms.mk_var("x", Sort::Real);
    let one = int(terms, 1);
    let ge = terms.mk_ge(x, one);
    let le = terms.mk_le(x, one);
    (x, ge, le)
}

#[test]
fn zero_coefficient_is_a_constant_expression_not_a_division() {
    let mut terms = TermStore::new();
    let (x, ge, le) = pinned_x(&mut terms);
    let mut solver = LraSolver::new(&terms);
    solver.register_atom(ge);
    solver.register_atom(le);
    solver.assert_literal(ge, true);
    solver.assert_literal(le, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
    let x_var = *solver.term_to_var.get(&x).expect("x must be interned");

    let zero_target = BigRational::zero();
    // 0*x + 0 is identically 0: forced to 0 with no reasons needed.
    let expr = LinearExpr {
        coeffs: vec![(x_var, Rational::zero())],
        constant: Rational::zero(),
    };
    let forced = solver.is_expression_forced_to_value(&expr, &zero_target);
    assert!(
        matches!(&forced, Some((reasons, true)) if reasons.is_empty()),
        "0*x + 0 must be forced to 0 with no reasons, got {forced:?}"
    );

    // 0*x + 3 is identically 3: decided, and NOT forced to 0.
    let expr = LinearExpr {
        coeffs: vec![(x_var, Rational::zero())],
        constant: Rational::from_big(BigRational::from(BigInt::from(3))),
    };
    let forced = solver.is_expression_forced_to_value(&expr, &zero_target);
    assert!(
        matches!(forced, Some((_, false))),
        "0*x + 3 is the constant 3, not forced to 0, got {forced:?}"
    );

    // x + 0*x' (a zero entry beside a live one) is the single-variable `x`,
    // pinned to 1: forced to 1, by x's own bound reasons.
    let expr = LinearExpr {
        coeffs: vec![(x_var, Rational::one()), (x_var + 1000, Rational::zero())],
        constant: Rational::zero(),
    };
    let forced = solver.is_expression_forced_to_value(&expr, &BigRational::from(BigInt::from(1)));
    assert!(
        matches!(&forced, Some((reasons, true)) if !reasons.is_empty()),
        "x (pinned to 1) with a zero-coefficient passenger must be forced to 1, got {forced:?}"
    );
}

#[test]
fn scale_by_zero_drops_every_coefficient() {
    let mut expr = LinearExpr::var(4);
    expr.add_term_rat(9, Rational::from_big(BigRational::from(BigInt::from(-2))));
    expr.constant = Rational::from_big(BigRational::from(BigInt::from(5)));
    expr.scale_rat(&Rational::zero());
    assert!(expr.coeffs.is_empty(), "0 * e has no variables: {expr:?}");
    assert!(expr.constant.is_zero(), "0 * e is 0: {expr:?}");
}

/// `(not (= (* 0 x) 0))` with `x` pinned: the disequality is violated by
/// every model (0*x is 0), so the check is a conflict blaming the atom — and
/// must not panic. `(not (= (* 0 x) 5))` holds in every model.
#[test]
fn disequality_over_zero_times_var_decides_without_panicking() {
    for (rhs, expect_conflict) in [(0, true), (5, false)] {
        let mut terms = TermStore::new();
        let (x, ge, le) = pinned_x(&mut terms);
        let zero = int(&mut terms, 0);
        // Raw application: the term-store builder would fold `0*x` away.
        let zero_x = terms.mk_app(Symbol::named("*"), vec![zero, x], Sort::Real);
        let rhs_t = int(&mut terms, rhs);
        let eq = terms.mk_app(Symbol::named("="), vec![zero_x, rhs_t], Sort::Bool);

        let mut solver = LraSolver::new(&terms);
        for atom in [ge, le, eq] {
            solver.register_atom(atom);
        }
        let parsed = solver.parse_linear_expr(zero_x);
        assert!(
            parsed.coeffs.is_empty(),
            "(* 0 x) parses to a constant: {parsed:?}"
        );

        solver.assert_literal(ge, true);
        solver.assert_literal(le, true);
        solver.assert_literal(eq, false);
        let result = solver.check();
        let conflict = matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        );
        assert_eq!(
            conflict, expect_conflict,
            "(not (= (* 0 x) {rhs})) with x = 1: got {result:?}"
        );
    }
}
