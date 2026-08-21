// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coefficient, alias, and compound-factor regression tests.

use super::*;
use ay_core::term::TermStore;
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn monomial_signs(solver: &NraSolver<'_>, factors: &[TermId]) -> Vec<SignConstraint> {
    let mut key = factors.to_vec();
    key.sort_by_key(|term| term.0);
    solver
        .sign_constraints
        .get(&key)
        .map(|constraints| {
            constraints
                .iter()
                .map(|(constraint, _)| *constraint)
                .collect()
        })
        .unwrap_or_default()
}

fn sign_machinery_reports_conflict(solver: &NraSolver<'_>) -> bool {
    sign::check_sign_consistency(
        &solver.monomials,
        &solver.sign_constraints,
        &solver.var_sign_constraints,
        &solver.asserted,
        false,
    )
    .is_some()
}

#[test]
fn zero_scaled_product_remains_opaque() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let product = terms.mk_mul(vec![x, y, zero]);
    let atom = terms.mk_le(product, zero);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(solver.monomials.is_empty());
    assert!(solver.scaled_aliases.is_empty());
    assert!(solver.aux_to_monomial.is_empty());
}

#[test]
fn scaled_sign_constraints_follow_the_coefficient() {
    for (coefficient, expected) in [
        (2, SignConstraint::NonPositive),
        (-2, SignConstraint::NonNegative),
    ] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let zero = terms.mk_rational(BigRational::zero());
        let factor = terms.mk_rational(integer(coefficient));
        let product = terms.mk_mul(vec![x, x, factor]);
        let atom = terms.mk_le(product, zero);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(atom, true);
        assert_eq!(monomial_signs(&solver, &[x, x]), vec![expected]);
    }
}

#[test]
fn scaled_aliases_are_tracked_and_receive_coefficient_aware_signs() {
    for (factor, scaled_sign) in [
        (2, SignConstraint::Positive),
        (-2, SignConstraint::Negative),
    ] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let zero = terms.mk_rational(BigRational::zero());
        let coefficient = terms.mk_rational(integer(factor));
        let bare = terms.mk_mul(vec![x, y]);
        let scaled = terms.mk_mul(vec![x, y, coefficient]);
        let bare_atom = terms.mk_le(bare, zero);
        let scaled_atom = terms.mk_le(scaled, zero);
        let x_nonpositive = terms.mk_le(x, zero);
        let y_nonpositive = terms.mk_le(y, zero);

        let mut solver = NraSolver::new(&terms);
        solver.internalize_atom(bare_atom);
        solver.internalize_atom(scaled_atom);
        solver.assert_literal(x_nonpositive, false);
        solver.assert_literal(y_nonpositive, false);
        assert_eq!(solver.monomials.len(), 1);
        assert_eq!(solver.scaled_aliases.len(), 1);
        assert_eq!(solver.products().count(), 2);

        let products: Vec<_> = solver.products().cloned().collect();
        sign::propagate_product_signs(products.iter(), &mut solver.var_sign_constraints);
        for (auxiliary, expected) in [(bare, SignConstraint::Positive), (scaled, scaled_sign)] {
            assert_eq!(
                solver
                    .var_sign_constraints
                    .get(&auxiliary)
                    .and_then(|constraints| constraints.first())
                    .map(|(constraint, _)| *constraint),
                Some(expected),
                "derived sign for coefficient {factor} auxiliary {auxiliary:?}",
            );
        }
    }
}

#[test]
fn scaled_binary_sign_conflict_respects_the_coefficient() {
    for (factor, expect_conflict) in [(2, true), (-2, false)] {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let zero = terms.mk_rational(BigRational::zero());
        let coefficient = terms.mk_rational(integer(factor));
        let scaled = terms.mk_mul(vec![x, y, coefficient]);
        let scaled_negative = terms.mk_lt(scaled, zero);
        let x_nonpositive = terms.mk_le(x, zero);
        let y_nonpositive = terms.mk_le(y, zero);

        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(scaled_negative, true);
        solver.assert_literal(x_nonpositive, false);
        solver.assert_literal(y_nonpositive, false);
        assert_eq!(
            sign_machinery_reports_conflict(&solver),
            expect_conflict,
            "{factor}*x*y < 0 with positive factors",
        );
    }
}

fn fixed_scaled_pair(rhs: i64) -> TheoryResult {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(integer(3));
    let five = terms.mk_rational(integer(5));
    let four = terms.mk_rational(integer(4));
    let expected = terms.mk_rational(integer(rhs));
    let scaled = terms.mk_mul(vec![x, y, four]);
    let scaled_eq = terms.mk_eq(scaled, expected);
    let x_eq = terms.mk_eq(x, three);
    let y_eq = terms.mk_eq(y, five);
    let mut solver = NraSolver::new(&terms);
    for atom in [scaled_eq, x_eq, y_eq] {
        solver.assert_literal(atom, true);
    }
    solver.check()
}

#[test]
fn scaled_product_consistency_uses_coefficient() {
    assert!(matches!(fixed_scaled_pair(60), TheoryResult::Sat));
    assert!(!matches!(fixed_scaled_pair(61), TheoryResult::Sat));
}

#[test]
fn representative_and_alias_constraints_agree_exactly() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let three = terms.mk_rational(integer(3));
    let five = terms.mk_rational(integer(5));
    let fifteen = terms.mk_rational(integer(15));
    let thirty = terms.mk_rational(integer(30));
    let two = terms.mk_rational(integer(2));
    let bare = terms.mk_mul(vec![x, y]);
    let scaled = terms.mk_mul(vec![two, x, y]);
    let assertions = [
        terms.mk_eq(x, three),
        terms.mk_eq(y, five),
        terms.mk_eq(bare, fifteen),
        terms.mk_eq(scaled, thirty),
    ];
    let mut solver = NraSolver::new(&terms);
    for atom in assertions {
        solver.assert_literal(atom, true);
    }
    assert!(matches!(solver.check(), TheoryResult::Sat));
    assert!(!solver.has_inconsistent_monomials());
}

#[test]
fn compound_factor_is_recorded_and_blocks_unavailable_models() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let sum = terms.mk_add(vec![a, b]);
    let product = terms.mk_mul(vec![c, sum]);
    let zero = terms.mk_rational(BigRational::zero());
    let atom = terms.mk_le(product, zero);
    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(solver.compound_factors.contains(&sum));
    assert!(solver.has_undefined_compound_factors());
    assert!(solver.has_inconsistent_monomials());
}

#[test]
fn compound_factor_definition_prevents_premature_sat() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let sum = terms.mk_add(vec![a, b]);
    let product = terms.mk_mul(vec![c, sum]);
    let two = terms.mk_rational(integer(2));
    let three = terms.mk_rational(integer(3));
    let one = terms.mk_rational(integer(1));
    let hundred = terms.mk_rational(integer(100));
    let assertions = [
        terms.mk_eq(a, two),
        terms.mk_eq(b, three),
        terms.mk_eq(c, one),
        terms.mk_eq(product, hundred),
    ];
    let mut solver = NraSolver::new(&terms);
    for atom in assertions {
        solver.assert_literal(atom, true);
    }
    assert!(!matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn linear_factor_expansion_is_exact_and_bounded() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let two = terms.mk_rational(integer(2));
    let seven = terms.mk_rational(integer(7));
    let two_a = terms.mk_mul(vec![two, a]);
    let neg_b = terms.mk_sub(vec![b, b, b]);
    let sum = terms.mk_add(vec![two_a, neg_b, seven]);
    let solver = NraSolver::new(&terms);
    let mut atoms = Vec::new();
    let mut constant = BigRational::zero();
    assert!(solver.linear_definition_of(sum, &BigRational::one(), 0, &mut atoms, &mut constant,));
    let coefficient = |term| {
        atoms
            .iter()
            .filter(|(atom, _)| *atom == term)
            .fold(BigRational::zero(), |sum, (_, value)| sum + value)
    };
    assert_eq!(constant, integer(7));
    assert_eq!(coefficient(a), integer(2));
    assert_eq!(coefficient(b), integer(-1));

    assert!(!solver.linear_definition_of(
        sum,
        &BigRational::one(),
        LINEAR_DEFINITION_MAX_DEPTH + 1,
        &mut Vec::new(),
        &mut BigRational::zero(),
    ));
}

#[test]
fn linear_factor_expansion_keeps_genuine_products_opaque() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Real);
    let b = terms.mk_var("b", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let product = terms.mk_mul(vec![a, b]);
    let sum = terms.mk_add(vec![product, c]);
    let solver = NraSolver::new(&terms);
    let mut atoms = Vec::new();
    let mut constant = BigRational::zero();
    assert!(solver.linear_definition_of(sum, &BigRational::one(), 0, &mut atoms, &mut constant,));
    assert!(atoms.iter().any(|(atom, _)| *atom == product));
    assert!(constant.is_zero());
}

/// UNIFIED-RESOLVER CONTRACT, both halves at once.
///
/// [`NraSolver::check_monomial_consistency`] resolves factors through
/// [`NraSolver::monomial_factor_value`] rather than `var_value`, and that
/// function asks the tableau FIRST and only then evaluates structurally. This
/// test pins both properties on the HORNER shape they exist for — a product
/// whose last factor is a compound `+`, as MetiTarski's Taylor polynomials emit.
///
/// 1. RESOLVES WHAT THE TABLEAU CANNOT. `var_value` answers `None` for the
///    compound `+` (it is a linear combination, not a column). Under the
///    fail-CLOSED residual that would reject the monomial for lack of evidence
///    instead of checking it on its merits — historically the shape that let
///    `sqrt-1mcosq-7-chunk-0170` pass all 30 of its monomials vacuously.
///
/// 2. OPAQUE FIRST, AND THAT ORDER IS LOAD-BEARING. The nested product `x*x`
///    contributes the value the LINEAR abstraction gave it, NOT a structural
///    recomputation from `x`. Here the abstraction is still unfaithful — `x = 2`
///    while its opaque `x*x` column is `0` — so the Horner factor must come back
///    as `0 + 1 = 1`. If it ever returns `4 + 1 = 5`, the structural path is
///    recomputing nested products, every monomial then agrees with itself, and
///    `check_monomial_consistency` can never fail again.
#[test]
fn horner_factor_resolves_through_the_tableau_first() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(integer(1));
    let two = terms.mk_rational(integer(2));
    // `(* x (+ (* x x) 1))` — the Horner shape: a compound `+` as last factor.
    let inner = terms.mk_mul(vec![x, x]);
    let horner = terms.mk_add(vec![inner, one]);
    let product = terms.mk_mul(vec![x, horner]);
    let hundred = terms.mk_rational(integer(100));
    let assertions = [terms.mk_eq(x, two), terms.mk_le(product, hundred)];
    let mut solver = NraSolver::new(&terms);
    for atom in assertions {
        solver.assert_literal(atom, true);
    }
    let _ = solver.check();

    assert!(
        solver.compound_factors.contains(&horner),
        "the `+` node must be recorded as a compound factor"
    );
    assert_eq!(
        solver.var_value(horner),
        None,
        "precondition: the tableau does not carry the compound `+` node, which \
         is exactly why `var_value` alone is not enough"
    );

    let opaque_inner = solver
        .var_value(inner)
        .expect("the nested product has an opaque LRA column");
    let resolved = solver
        .monomial_factor_value(horner)
        .expect("the Horner factor must resolve through the structural path");
    assert_eq!(
        resolved,
        opaque_inner + integer(1),
        "the Horner factor must be the OPAQUE nested-product value plus one, \
         never a structural recomputation of x*x"
    );
}
