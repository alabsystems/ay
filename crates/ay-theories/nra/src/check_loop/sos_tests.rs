// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-to-certificate evidence helper tests, without the NRA decision loop.

use ay_core::term::{Symbol, TermStore};
use ay_core::Sort;
use num_rational::BigRational;
use num_traits::Zero;

use super::NraSolver;

#[test]
fn nra_sos_helper_builds_and_rechecks_a_source_quartic_certificate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xx = terms.mk_app(Symbol::named("*"), [x, x], Sort::Real);
    let yy = terms.mk_app(Symbol::named("*"), [y, y], Sort::Real);
    let sum = terms.mk_app(Symbol::named("+"), [xx, yy], Sort::Real);
    let quartic = terms.mk_app(Symbol::named("*"), [sum, sum], Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let impossible = terms.mk_app(Symbol::named("<"), [quartic, zero], Sort::Bool);
    let neighbor = terms.mk_app(Symbol::named("<="), [quartic, zero], Sort::Bool);
    let mut solver = NraSolver::new(&terms);
    solver.asserted = vec![(impossible, true)];

    let certificate = solver
        .try_build_unsat_sos_certificate()
        .expect("quartic square");
    let source = solver.sos_source_constraints().expect("bounded source");
    assert!(certificate.basis.iter().any(|monomial| monomial.len() == 2));
    assert!(certificate.verify(&source).is_ok());
    assert!(
        solver.last_unsat_certificate.is_none(),
        "helper is not publication"
    );

    // x=y=0 satisfies this neighboring source. Reuse must fail its fresh check.
    solver.asserted = vec![(neighbor, true)];
    let changed = solver.sos_source_constraints().expect("bounded neighbor");
    assert!(certificate.verify(&changed).is_err());
    assert!(solver.try_build_unsat_sos_certificate().is_none());
}

#[test]
fn nra_sos_helper_declines_excess_source_variables_before_search() {
    let mut terms = TermStore::new();
    let zero = terms.mk_rational(BigRational::zero());
    let mut asserted = Vec::new();
    for index in 0..=crate::sos::MAX_VARS {
        let var = terms.mk_var(format!("x{index}"), Sort::Real);
        let atom = terms.mk_app(Symbol::named(">"), [var, zero], Sort::Bool);
        asserted.push((atom, true));
    }
    let mut solver = NraSolver::new(&terms);
    solver.asserted = asserted;
    assert!(
        solver.sos_source_constraints().is_some(),
        "source fits its envelope"
    );
    assert!(solver.try_build_unsat_sos_certificate().is_none());
    assert!(solver.last_unsat_certificate.is_none());
}

#[test]
fn nra_sos_pop_cannot_reuse_a_retracted_source_certificate() {
    use ay_core::TheorySolver;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let square = terms.mk_app(Symbol::named("*"), [x, x], Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let impossible = terms.mk_app(Symbol::named("<"), [square, zero], Sort::Bool);
    let neighbor = terms.mk_app(Symbol::named("<="), [square, zero], Sort::Bool);
    let mut solver = NraSolver::new(&terms);
    solver.push();
    solver.assert_literal(impossible, true);
    let certificate = solver
        .try_build_unsat_sos_certificate()
        .expect("strict square is refuted");
    assert!(certificate
        .verify(&solver.sos_source_constraints().expect("original source"))
        .is_ok());
    solver.last_unsat_certificate = Some(certificate);
    assert!(solver.took_sos_unsat_certificate());

    solver.pop();

    assert!(solver.asserted.is_empty());
    assert!(!solver.took_sos_unsat_certificate());
    assert!(solver.render_sos_unsat_certificate("stale").is_none());
    solver.assert_literal(neighbor, true);
    assert!(solver.try_build_unsat_sos_certificate().is_none());
}
