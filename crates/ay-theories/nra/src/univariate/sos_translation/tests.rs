// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-boundary tests; no NRA search or external solver is invoked.

use super::*;
use crate::sos::budget::{MAX_SOS_TERM_DEPTH, MAX_SOS_TERM_VISITS};
use ay_core::term::TermStore;
use num_bigint::BigInt;

fn real(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(BigInt::from(value)))
}

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

#[test]
fn sos_translation_quartic_matches_original_polynomial_and_polarity() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = real(&mut terms, 1);
    let xy = app(&mut terms, "*", &[x, y], Sort::Real);
    let shifted = app(&mut terms, "-", &[xy, one], Sort::Real);
    let square = app(&mut terms, "*", &[shifted, shifted], Sort::Real);
    let zero = real(&mut terms, 0);
    let mut atoms = Vec::new();
    for name in ["<", "<=", "=", ">=", ">", "distinct"] {
        atoms.push(app(&mut terms, name, &[square, zero], Sort::Bool));
    }
    let solver = NraSolver::new(&terms);
    for atom in atoms {
        for value in [false, true] {
            let expected = solver.atom_to_multi(atom, value);
            let actual = solver.sos_source_atom(atom, value, &mut SosPolynomialBudget::default());
            let (Some(MultiAtom::Constraint(expected)), Some(MultiAtom::Constraint(actual))) =
                (expected, actual)
            else {
                panic!("a quartic comparison must retain its source polynomial");
            };
            assert_eq!(actual.poly.terms, expected.poly.terms);
            assert_eq!(actual.rel, expected.rel);
        }
    }
}

#[test]
fn sos_translation_preserves_constant_and_unsupported_policy() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    let vacuous = app(&mut terms, "<", &[zero, one], Sort::Bool);
    let supported = app(&mut terms, ">", &[x, zero], Sort::Bool);
    let division = app(&mut terms, "/", &[x, one], Sort::Real);
    let unsupported = app(&mut terms, ">", &[division, zero], Sort::Bool);
    let mut solver = NraSolver::new(&terms);
    solver.asserted = vec![(vacuous, true), (supported, true)];
    assert_eq!(
        solver
            .sos_source_constraints()
            .expect("complete view")
            .len(),
        1
    );
    solver.asserted.push((unsupported, true));
    assert!(solver.sos_source_constraints().is_none());
    solver.asserted = vec![(vacuous, false)];
    assert!(solver.sos_source_constraints().is_none());
}

#[test]
fn sos_translation_rejects_mistyped_source_atoms_and_children() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let integer = terms.mk_int(BigInt::from(1u8));
    let zero = real(&mut terms, 0);
    let boolean = terms.mk_var("b", Sort::Bool);
    let mixed = app(&mut terms, "+", &[x, integer], Sort::Real);
    let non_numeric = app(&mut terms, "+", &[x, boolean], Sort::Real);
    let atoms = [
        app(&mut terms, "<", &[x, zero], Sort::Real),
        app(&mut terms, "<", &[x, integer], Sort::Bool),
        app(&mut terms, "<", &[mixed, zero], Sort::Bool),
        app(&mut terms, "<", &[non_numeric, zero], Sort::Bool),
    ];
    let solver = NraSolver::new(&terms);
    for atom in atoms {
        assert!(solver
            .sos_source_atom(atom, true, &mut SosPolynomialBudget::default())
            .is_none());
    }
}

#[test]
fn sos_translation_checks_coefficients_before_cloning_and_after_products() {
    let mut terms = TermStore::new();
    let edge = BigInt::from(1u8) << (MAX_SOS_COEFFICIENT_BITS - 1) as usize;
    let inside = terms.mk_rational(BigRational::from_integer(edge.clone()));
    let outside = terms.mk_rational(BigRational::from_integer(edge << 1usize));
    let factor = terms.mk_rational(BigRational::from_integer(BigInt::from(1u8) << 600usize));
    let product = app(&mut terms, "*", &[factor, factor], Sort::Real);
    let solver = NraSolver::new(&terms);
    assert!(solver
        .sos_source_polynomial(inside, 0, &mut SosPolynomialBudget::default())
        .is_some());
    for term in [outside, product] {
        assert!(solver
            .sos_source_polynomial(term, 0, &mut SosPolynomialBudget::default())
            .is_none());
    }
}

#[test]
fn sos_translation_declines_degree_five() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let degree_four = app(&mut terms, "*", &[x; 4], Sort::Real);
    let degree_five = app(&mut terms, "*", &[x; 5], Sort::Real);
    let solver = NraSolver::new(&terms);
    assert!(solver
        .sos_source_polynomial(degree_four, 0, &mut SosPolynomialBudget::default())
        .is_some());
    assert!(solver
        .sos_source_polynomial(degree_five, 0, &mut SosPolynomialBudget::default())
        .is_none());
}

#[test]
fn sos_translation_depth_includes_the_source_comparison() {
    let mut terms = TermStore::new();
    let mut nested = terms.mk_var("x", Sort::Real);
    for _ in 1..MAX_SOS_TERM_DEPTH {
        nested = app(&mut terms, "-", &[nested], Sort::Real);
    }
    let zero = real(&mut terms, 0);
    let inside = app(&mut terms, ">", &[nested, zero], Sort::Bool);
    nested = app(&mut terms, "-", &[nested], Sort::Real);
    let outside = app(&mut terms, ">", &[nested, zero], Sort::Bool);
    let solver = NraSolver::new(&terms);
    assert!(solver
        .sos_source_atom(inside, true, &mut SosPolynomialBudget::default())
        .is_some());
    assert!(solver
        .sos_source_atom(outside, true, &mut SosPolynomialBudget::default())
        .is_none());
}

#[test]
fn sos_translation_shares_source_visit_budget_across_atoms() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let atom = app(&mut terms, ">", &[x, zero], Sort::Bool);
    let solver = NraSolver::new(&terms);
    let mut budget = SosPolynomialBudget::default();
    for _ in 0..MAX_SOS_TERM_VISITS - 3 {
        assert!(budget.visit_term(0));
    }
    assert!(solver.sos_source_atom(atom, true, &mut budget).is_some());
    assert!(solver.sos_source_atom(atom, true, &mut budget).is_none());
}

#[test]
fn sos_translation_caps_assertions_before_walking() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let atom = app(&mut terms, ">", &[x, zero], Sort::Bool);
    let mut solver = NraSolver::new(&terms);
    solver.asserted = vec![(atom, true); MAX_SOS_ASSERTED_LITERALS];
    assert_eq!(
        solver
            .sos_source_constraints()
            .expect("inclusive boundary")
            .len(),
        MAX_SOS_ASSERTED_LITERALS
    );
    solver.asserted.push((atom, true));
    assert!(solver.sos_source_constraints().is_none());
}

#[test]
fn sos_translation_caps_total_retained_polynomial_terms() {
    let mut terms = TermStore::new();
    let vars: Vec<_> = (0..8)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Real))
        .collect();
    let sum = app(&mut terms, "+", &vars, Sort::Real);
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    let shifted = app(&mut terms, "+", &[sum, one], Sort::Real);
    let inside = app(&mut terms, ">", &[sum, zero], Sort::Bool);
    let outside = app(&mut terms, ">", &[shifted, zero], Sort::Bool);
    let mut solver = NraSolver::new(&terms);
    solver.asserted = vec![(inside, true); MAX_SOS_TOTAL_POLY_TERMS / 8];
    assert!(solver.sos_source_constraints().is_some());
    // The same number of assertions now carries nine terms per polynomial.
    solver.asserted.fill((outside, true));
    assert!(solver.sos_source_constraints().is_none());
}
