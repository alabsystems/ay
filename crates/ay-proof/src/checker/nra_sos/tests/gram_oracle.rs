// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Analytic controls independent of the producer's search or PSD routine.

use super::*;

fn fraction(numerator: i64, denominator: i64) -> NraSosRational {
    let value = BigRational::new(numerator.into(), denominator.into());
    NraSosRational {
        numerator: value.numer().clone(),
        denominator: value.denom().clone(),
    }
}

#[test]
fn exact_two_by_two_psd_matches_all_principal_minors() {
    let mut accepted = 0;
    let mut rejected = 0;
    for denominator in [1, 3] {
        for a in -2i64..=3 {
            for b in -3i64..=3 {
                for c in -2i64..=3 {
                    let matrix = vec![
                        vec![fraction(a, denominator), fraction(b, denominator)],
                        vec![fraction(b, denominator), fraction(c, denominator)],
                    ];
                    // All principal minors are nonnegative iff a real
                    // symmetric 2x2 matrix is PSD. The common positive
                    // denominator does not change their signs.
                    let expected = a >= 0 && c >= 0 && a * c >= b * b;
                    let actual = gram::decode_and_check(&matrix, &mut WorkMeter::new()).is_ok();
                    assert_eq!(
                        actual, expected,
                        "matrix [{a}, {b}; {b}, {c}] / {denominator}"
                    );
                    if actual {
                        accepted += 1;
                    } else {
                        rejected += 1;
                    }
                }
            }
        }
    }
    assert!(accepted > 0 && rejected > 0);
    assert_eq!(accepted + rejected, 504);
}

#[test]
fn an_exact_identity_with_positive_diagonal_is_not_a_psd_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = real(&mut terms, 0);
    let four = real(&mut terms, 4);
    let xx = terms.mk_mul(vec![x, x]);
    let yy = terms.mk_mul(vec![y, y]);
    let cross = terms.mk_mul(vec![four, x, y]);
    let polynomial = terms.mk_add(vec![xx, cross, yy]);
    let negative = terms.mk_lt(polynomial, zero);
    let clause = [terms.mk_not_raw(negative)];
    let cert = certificate(
        vec![vec![], vec![x], vec![y]],
        &[&[0, 0, 0], &[0, 1, 2], &[0, 2, 1]],
        vec![term(0, 1)],
        0,
    );
    // The proposed identity cancels exactly, and both variable diagonals are
    // positive. Nevertheless x=1, y=-1 makes the original polynomial -2:
    // its Gram matrix is indefinite and the source conjunction is SAT.
    let (x_value, y_value) = (1i64, -1i64);
    assert!(x_value * x_value + 4 * x_value * y_value + y_value * y_value < 0);
    assert!(matches!(
        validate(&terms, &clause, &cert),
        Err(ProofCheckError::InvalidTheoryLemma { reason, .. }) if reason.contains("not PSD")
    ));
}

fn weighted_linear() -> (TermStore, Vec<TermId>, NraSosCertificate) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = real(&mut terms, 2);
    let zero = real(&mut terms, 0);
    let twice_x = terms.mk_mul(vec![two, x]);
    let lower = terms.mk_ge(twice_x, two);
    let upper = terms.mk_le(x, zero);
    let clause = vec![terms.mk_not_raw(lower), terms.mk_not_raw(upper)];
    let cert = certificate(vec![vec![]], &[&[0]], vec![term(0, 1), term(1, 2)], -2);
    (terms, clause, cert)
}

#[test]
fn unequal_source_weights_require_the_matching_positional_remap() {
    let (terms, mut clause, mut cert) = weighted_linear();
    validate(&terms, &clause, &cert).expect("weighted source identity");
    clause.swap(0, 1);
    assert!(validate(&terms, &clause, &cert).is_err());
    cert.terms[0].origin = NraSosOrigin::ClauseLiteral { position: 1 };
    cert.terms[1].origin = NraSosOrigin::ClauseLiteral { position: 0 };
    validate(&terms, &clause, &cert).expect("exactly remapped weighted identity");
}

#[test]
fn duplicate_source_slots_are_preserved_not_implicitly_deduplicated() {
    let (terms, mut clause, mut cert) = weighted_linear();
    clause.insert(0, clause[0]);
    cert.terms[1].origin = NraSosOrigin::ClauseLiteral { position: 2 };
    validate(&terms, &clause, &cert).expect("first duplicate is a legitimate source slot");
    cert.terms[0].origin = NraSosOrigin::ClauseLiteral { position: 1 };
    validate(&terms, &clause, &cert).expect("second duplicate denotes the same constraint");
    cert.terms[1].origin = NraSosOrigin::ClauseLiteral { position: 1 };
    assert!(validate(&terms, &clause, &cert).is_err());
}
