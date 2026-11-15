// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recognizer boundary tests (Risk R8): everything admitted parses linearly.

use ay_core::{Sort, Symbol, TermStore};
use num_rational::BigRational;

use super::recognize::qlra_problem_shape;

fn real(terms: &mut TermStore, n: i64) -> ay_core::TermId {
    terms.mk_rational(BigRational::from_integer(n.into()))
}

#[test]
fn recognizer_admits_linear_real_universal() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let two = real(&mut terms, 2);
    let lhs = terms.mk_mul(vec![two, x]);
    let body = terms.mk_lt(lhs, c);
    let q = terms.mk_forall(vec![("x".to_string(), Sort::Real)], body);
    assert!(qlra_problem_shape(&terms, &[q]));
}

#[test]
fn recognizer_refuses_ground_problems() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Real);
    let zero = real(&mut terms, 0);
    let atom = terms.mk_lt(c, zero);
    assert!(
        !qlra_problem_shape(&terms, &[atom]),
        "no quantifier, no lane"
    );
}

#[test]
fn recognizer_refuses_nonlinear_uf_int_and_arith_ite() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c = terms.mk_var("c", Sort::Real);
    let binder = vec![("x".to_string(), Sort::Real)];

    let xc = terms.mk_mul(vec![x, c]);
    let zero = real(&mut terms, 0);
    let nonlinear = terms.mk_lt(xc, zero);
    let q1 = terms.mk_forall(binder.clone(), nonlinear);
    assert!(!qlra_problem_shape(&terms, &[q1]), "nonlinear");

    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Real);
    let uf = terms.mk_lt(fx, c);
    let q2 = terms.mk_forall(binder.clone(), uf);
    assert!(!qlra_problem_shape(&terms, &[q2]), "uninterpreted function");

    let n = terms.mk_var("n", Sort::Int);
    let zero_i = terms.mk_int(0.into());
    let int_atom = terms.mk_lt(n, zero_i);
    let q3 = terms.mk_forall(binder.clone(), int_atom);
    assert!(!qlra_problem_shape(&terms, &[q3]), "Int");

    let p = terms.mk_var("p", Sort::Bool);
    let ite = terms.mk_ite(p, x, c);
    let ite_atom = terms.mk_lt(ite, zero);
    let q4 = terms.mk_forall(binder, ite_atom);
    assert!(!qlra_problem_shape(&terms, &[q4]), "arithmetic ite");
}
