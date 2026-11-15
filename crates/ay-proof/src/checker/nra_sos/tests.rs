// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{NraSosTerm, Sort, Symbol};

mod gram_oracle;
mod mutations;
mod source;

fn rat(n: i64) -> NraSosRational {
    NraSosRational {
        numerator: n.into(),
        denominator: 1.into(),
    }
}
fn term(position: u32, multiplier: i64) -> NraSosTerm {
    NraSosTerm {
        origin: NraSosOrigin::ClauseLiteral { position },
        multiplier: rat(multiplier),
    }
}
fn real(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(BigRational::from_integer(n.into()))
}
fn certificate(
    basis: Vec<Vec<TermId>>,
    gram: &[&[i64]],
    terms: Vec<NraSosTerm>,
    rhs: i64,
) -> NraSosCertificate {
    NraSosCertificate {
        basis,
        gram: gram
            .iter()
            .map(|row| row.iter().map(|&n| rat(n)).collect())
            .collect(),
        terms,
        rhs: rat(rhs),
    }
}
fn validate(
    terms: &TermStore,
    clause: &[TermId],
    cert: &NraSosCertificate,
) -> Result<(), ProofCheckError> {
    validate_nra_sos_with_progress(terms, ProofId(0), clause, cert, &mut |_, _| true)
}

fn linear() -> (TermStore, Vec<TermId>, NraSosCertificate) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = real(&mut terms, 0);
    let one = real(&mut terms, 1);
    let lower = terms.mk_ge(x, one);
    let upper = terms.mk_le(x, zero);
    let clause = vec![terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
    let cert = certificate(vec![vec![]], &[&[0]], vec![term(0, 1), term(1, 1)], -1);
    (terms, clause, cert)
}

fn quartic() -> (TermStore, Vec<TermId>, NraSosCertificate) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = real(&mut terms, 0);
    let two = real(&mut terms, 2);
    let xx = terms.mk_mul(vec![x, x]);
    let yy = terms.mk_mul(vec![y, y]);
    let xxxx = terms.mk_mul(vec![xx, xx]);
    let yyyy = terms.mk_mul(vec![yy, yy]);
    let cross = terms.mk_mul(vec![two, xx, yy]);
    let pure = terms.mk_add(vec![xxxx, yyyy]);
    let expanded = terms.mk_sub(vec![pure, cross]);
    let assertion = terms.mk_lt(expanded, zero);
    let clause = vec![terms.mk_not_raw(assertion)];
    let cert = certificate(
        vec![vec![], vec![x, x], vec![y, y]],
        &[&[0, 0, 0], &[0, 1, -1], &[0, -1, 1]],
        vec![term(0, 1)],
        0,
    );
    (terms, clause, cert)
}

#[test]
fn accepts_hand_authored_linear_and_expanded_quartic_witnesses() {
    for (terms, clause, cert) in [linear(), quartic()] {
        validate(&terms, &clause, &cert).unwrap();
    }
}

#[test]
fn accepts_shifted_square_and_singular_psd() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = real(&mut terms, 1);
    let zero = real(&mut terms, 0);
    let shifted = terms.mk_sub(vec![x, one]);
    let square = terms.mk_mul(vec![shifted, shifted]);
    let assertion = terms.mk_lt(square, zero);
    let clause = [terms.mk_not_raw(assertion)];
    let cert = certificate(
        vec![vec![], vec![x]],
        &[&[1, -1], &[-1, 1]],
        vec![term(0, 1)],
        0,
    );
    validate(&terms, &clause, &cert).unwrap();
}

#[test]
fn equality_multiplier_is_free() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = real(&mut terms, 1);
    let zero = real(&mut terms, 0);
    let square = terms.mk_mul(vec![x, x]);
    let positive = terms.mk_add(vec![square, one]);
    let assertion = terms.mk_app(Symbol::named("="), [positive, zero], Sort::Bool);
    let clause = [terms.mk_not_raw(assertion)];
    let cert = certificate(
        vec![vec![], vec![x]],
        &[&[0, 0], &[0, 1]],
        vec![term(0, -1)],
        -1,
    );
    validate(&terms, &clause, &cert).unwrap();
    let reversed = terms.mk_app(Symbol::named("="), [zero, positive], Sort::Bool);
    let reversed_clause = [terms.mk_not_raw(reversed)];
    assert!(validate(&terms, &reversed_clause, &cert).is_err());
    let mut reversed_cert = cert.clone();
    reversed_cert.terms = vec![term(0, 1)];
    validate(&terms, &reversed_clause, &reversed_cert).unwrap();
    assert!(validate(&terms, &clause, &reversed_cert).is_err());
}

#[test]
fn constant_comparison_keeps_its_exact_slot() {
    let (mut terms, mut clause, mut cert) = linear();
    let one = real(&mut terms, 1);
    let constant_true = terms.mk_app(Symbol::Named("=".into()), [one, one], Sort::Bool);
    clause.insert(0, terms.mk_not_raw(constant_true));
    cert.terms = vec![term(1, 1), term(2, 1)];
    validate(&terms, &clause, &cert).unwrap();
    cert.terms = vec![term(0, 1), term(1, 1)];
    assert!(validate(&terms, &clause, &cert).is_err());
}

#[test]
fn product_is_strict_only_when_both_factors_are_strict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = real(&mut terms, 0);
    let x_positive = terms.mk_gt(x, zero);
    let y_positive = terms.mk_gt(y, zero);
    let product = terms.mk_mul(vec![x, y]);
    let nonpositive = terms.mk_le(product, zero);
    let mut clause = vec![
        terms.mk_not_raw(x_positive),
        terms.mk_not_raw(y_positive),
        terms.mk_not_raw(nonpositive),
    ];
    let product_term = NraSosTerm {
        origin: NraSosOrigin::Product { left: 0, right: 1 },
        multiplier: rat(1),
    };
    let cert = certificate(vec![vec![]], &[&[0]], vec![product_term, term(2, 1)], 0);
    validate(&terms, &clause, &cert).unwrap();
    let nonnegative = terms.mk_ge(x, zero);
    clause[0] = terms.mk_not_raw(nonnegative);
    // x=0, y=1 satisfies this mutated conjunction.
    assert!(validate(&terms, &clause, &cert).is_err());
    let equality = terms.mk_eq(x, zero);
    clause[0] = terms.mk_not_raw(equality);
    assert!(validate(&terms, &clause, &cert).is_err());
}

#[test]
fn strict_dispatch_publishes_only_fully_checked_clause() {
    let (terms, clause, mut cert) = quartic();
    let mut derived = Vec::new();
    let step = ay_core::ProofStep::NraSos {
        clause: clause.clone(),
        certificate: cert.clone(),
    };
    super::super::validate_step(&terms, &mut derived, ProofId(0), &step, true, None).unwrap();
    assert_eq!(derived, vec![Some(clause.clone())]);
    cert.rhs = rat(1);
    let step = ay_core::ProofStep::NraSos {
        clause,
        certificate: cert,
    };
    let mut derived = Vec::new();
    assert!(
        super::super::validate_step(&terms, &mut derived, ProofId(0), &step, false, None).is_err()
    );
    assert!(derived.is_empty());
}
