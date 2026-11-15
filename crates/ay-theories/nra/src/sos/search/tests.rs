// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::budget::{MAX_SOS_COEFFICIENT_BITS, MAX_SOS_POLY_TERMS};
use super::*;

mod progress;

fn unmetered_degree_search(
    constraints: &[MultiConstraint],
    vars: &[TermId],
    degree: Degree,
) -> Option<SosCertificate> {
    search_degree(
        constraints,
        vars,
        degree,
        &mut SosProgress::new(&mut |_, _| true),
    )
}

fn rational(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn poly(terms: &[(&[TermId], i64)]) -> MultiPoly {
    let mut result = MultiPoly::zero();
    for &(monomial, coefficient) in terms {
        let mut monomial = monomial.to_vec();
        monomial.sort_unstable();
        result.add_term(monomial, rational(coefficient));
    }
    result
}

fn constraint(poly: MultiPoly, rel: Rel) -> MultiConstraint {
    MultiConstraint { poly, rel }
}

fn shifted_quartic(rel: Rel) -> Vec<MultiConstraint> {
    let x = TermId(1);
    vec![constraint(
        poly(&[(&[x, x, x, x], 1), (&[x, x], -2), (&[], 1)]),
        rel,
    )]
}

#[test]
fn quartic_sum_of_monomial_squares_refutes() {
    let x = TermId(1);
    let y = TermId(2);
    let source = vec![constraint(
        poly(&[(&[x, x, x, x], 1), (&[y, y, y, y], 1)]),
        Rel::Lt,
    )];
    assert!(unmetered_degree_search(&source, &[x, y], Degree::Quadratic).is_none());
    let cert = search(&source, &[x, y]).expect("degree-4 DSOS certificate");
    assert_eq!(cert.verify(&source), Ok(()));
    assert!(cert.basis.iter().any(|monomial| monomial.len() == 2));
    assert!(cert.rhs.is_zero());
}

#[test]
fn quartic_difference_square_uses_cross_gram_entries() {
    let x = TermId(1);
    let y = TermId(2);
    let source = vec![constraint(
        poly(&[(&[x, x, x, x], 1), (&[x, x, y, y], -2), (&[y, y, y, y], 1)]),
        Rel::Lt,
    )];
    let cert = search(&source, &[x, y]).expect("(x²-y²)²<0 refutation");
    assert_eq!(cert.verify(&source), Ok(()));
    let x2 = cert
        .basis
        .iter()
        .position(|monomial| monomial == &[x, x])
        .unwrap();
    let y2 = cert
        .basis
        .iter()
        .position(|monomial| monomial == &[y, y])
        .unwrap();
    assert!(cert.gram[x2][y2].is_negative());
}

#[test]
fn quartic_shifted_square_requires_constant_dictionary_entry() {
    let source = shifted_quartic(Rel::Lt);
    let cert = search(&source, &[TermId(1)]).expect("(x²-1)²<0 refutation");
    assert_eq!(cert.verify(&source), Ok(()));
    assert!(cert.gram[0][0].is_positive());
    assert!(cert.gram[0].iter().any(Signed::is_negative));
}

#[test]
fn affine_shifted_square_is_available_in_quartic_fallback() {
    let x = TermId(1);
    let source = vec![constraint(
        poly(&[(&[x, x], 1), (&[x], -2), (&[], 1)]),
        Rel::Lt,
    )];
    assert!(unmetered_degree_search(&source, &[x], Degree::Quadratic).is_none());
    let cert = search(&source, &[x]).expect("(x-1)²<0 shifted refutation");
    assert_eq!(cert.verify(&source), Ok(()));
}

#[test]
fn quartic_nonstrict_neighbors_are_not_refuted() {
    // (x²-1)² <= 0 and =0 are both satisfied by x=1.
    for relation in [Rel::Le, Rel::Eq] {
        assert!(search(&shifted_quartic(relation), &[TermId(1)]).is_none());
    }
    let x = TermId(1);
    let y = TermId(2);
    // x^4+y^4<=0 is satisfied by (0,0).
    let source = vec![constraint(
        poly(&[(&[x, x, x, x], 1), (&[y, y, y, y], 1)]),
        Rel::Le,
    )];
    assert!(search(&source, &[x, y]).is_none());
}

#[test]
fn quartic_nonlinear_source_products_are_found() {
    let x = TermId(1);
    let y = TermId(2);
    let left = poly(&[(&[x, x], 1), (&[], -1)]);
    let right = poly(&[(&[y, y], 1), (&[], -1)]);
    // g0>=0, g1>=0, -(g0*g1)-1>=0 contradict g0*g1>=0.
    let negative_product = left.mul(&right).neg().sub(&MultiPoly::constant(one()));
    let source = vec![
        constraint(left, Rel::Ge),
        constraint(right, Rel::Ge),
        constraint(negative_product, Rel::Ge),
    ];
    let cert = search(&source, &[x, y]).expect("nonlinear source-product certificate");
    assert_eq!(cert.verify(&source), Ok(()));
    assert!(cert
        .terms
        .iter()
        .any(|term| term.origin == CertOrigin::Product(0, 1) && term.multiplier.is_positive()));
    assert!(cert.rhs.is_negative());
}

#[test]
fn original_degree_two_dictionary_remains_first() {
    let x = TermId(1);
    let y = TermId(2);
    let source = vec![constraint(poly(&[(&[x, x], 1), (&[y, y], 1)]), Rel::Lt)];
    let cert = search(&source, &[x, y]).expect("original degree-2 certificate");
    assert_eq!(cert.verify(&source), Ok(()));
    assert_eq!(cert.basis, vec![vec![], vec![x], vec![y]]);
}

#[test]
fn degree_two_certificate_survives_an_unused_quartic_source_conjunct() {
    let x = TermId(1);
    let y = TermId(2);
    let source = vec![
        constraint(poly(&[(&[x, x], 1)]), Rel::Lt),
        constraint(poly(&[(&[y; 4], 1)]), Rel::Ge),
    ];
    let cert = search(&source, &[x, y]).expect("degree-2 contradiction remains first");
    assert_eq!(cert.verify(&source), Ok(()));
    assert!(cert.basis.iter().all(|monomial| monomial.len() <= 1));
}

#[test]
fn independently_authored_quartic_gram_verifies_without_search() {
    let x = TermId(1);
    let y = TermId(2);
    let source = vec![constraint(
        poly(&[(&[x; 4], 1), (&[x, x, y, y], -2), (&[y; 4], 1)]),
        Rel::Lt,
    )];
    let cert = SosCertificate {
        basis: vec![vec![], vec![x, x], vec![y, y]],
        gram: vec![
            vec![zero(), zero(), zero()],
            vec![zero(), one(), -one()],
            vec![zero(), -one(), one()],
        ],
        terms: vec![CertTerm {
            origin: CertOrigin::Constraint(0),
            multiplier: one(),
        }],
        rhs: zero(),
    };
    assert_eq!(cert.verify(&source), Ok(()));
}

#[test]
fn independently_authored_nonlinear_product_checks_exact_source_indices() {
    let x = TermId(1);
    let y = TermId(2);
    let left = poly(&[(&[x, x], 1), (&[], -1)]);
    let right = poly(&[(&[y, y], 1), (&[], -1)]);
    let contrary = left.mul(&right).neg().sub(&MultiPoly::constant(one()));
    let source = vec![
        constraint(left, Rel::Ge),
        constraint(right, Rel::Ge),
        constraint(contrary, Rel::Ge),
    ];
    let mut cert = SosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![zero()]],
        terms: vec![
            CertTerm {
                origin: CertOrigin::Product(0, 1),
                multiplier: one(),
            },
            CertTerm {
                origin: CertOrigin::Constraint(2),
                multiplier: one(),
            },
        ],
        rhs: -one(),
    };
    assert_eq!(cert.verify(&source), Ok(()));
    cert.terms[0].origin = CertOrigin::Product(0, 0);
    assert_eq!(cert.verify(&source), Err(SosError::IdentityMismatch));
}

#[test]
fn complete_quartic_dictionary_preflights_unavoidable_tableau_size() {
    assert_eq!(quartic_support_size(4), Some(70));
    assert_eq!(quartic_support_size(5), Some(126));
    assert!(lp_dimensions_fit(70, 15 * 15));
    assert!(!lp_dimensions_fit(126, 21 * 21));
    let variables = (1..=5).map(TermId).collect::<Vec<_>>();
    let source = vec![constraint(poly(&[(&[variables[0]; 4], 1)]), Rel::Lt)];
    assert!(unmetered_degree_search(&source, &variables, Degree::Quartic).is_none());
}

#[test]
fn source_mismatches_and_noncanonical_polynomials_decline() {
    let x = TermId(1);
    let y = TermId(2);
    let source = shifted_quartic(Rel::Lt);
    assert!(search(&source, &[y]).is_none());
    assert!(search(&source, &[x, x]).is_none());
    let duplicate = MultiPoly {
        terms: vec![(vec![x], one()), (vec![x], -one())],
    };
    assert!(search(&[constraint(duplicate, Rel::Gt)], &[x]).is_none());
    let unsorted = MultiPoly {
        terms: vec![(vec![y, x], one())],
    };
    assert!(search(&[constraint(unsorted, Rel::Lt)], &[x, y]).is_none());
}

#[test]
fn polynomial_dimensions_and_coefficients_decline_before_search_expansion() {
    let x = TermId(1);
    let oversized = MultiPoly {
        terms: vec![(vec![x], one()); MAX_SOS_POLY_TERMS + 1],
    };
    assert!(search(&[constraint(oversized, Rel::Lt)], &[x]).is_none());
    let coefficient = BigRational::from_integer(BigInt::one() << MAX_SOS_COEFFICIENT_BITS as usize);
    let source = vec![constraint(
        MultiPoly {
            terms: vec![(vec![x; 4], coefficient)],
        },
        Rel::Lt,
    )];
    assert!(search(&source, &[x]).is_none());
    let degree_five = vec![constraint(poly(&[(&[x; 5], 1)]), Rel::Lt)];
    assert!(search(&degree_five, &[x]).is_none());
}

#[test]
fn quartic_checker_rejects_tampering_and_changed_source() {
    let source = shifted_quartic(Rel::Lt);
    let cert = search(&source, &[TermId(1)]).expect("quartic certificate");
    let mut changed = cert.clone();
    changed.gram[0][0] = -one();
    assert_eq!(changed.verify(&source), Err(SosError::GramNotPsd));
    let mut changed = cert.clone();
    changed.basis[1] = vec![TermId(99)];
    assert_eq!(changed.verify(&source), Err(SosError::InvalidBasis));
    let mut changed = cert.clone();
    changed.terms[0].multiplier = -one();
    assert_eq!(changed.verify(&source), Err(SosError::NegativeMultiplier));
    assert_eq!(
        cert.verify(&shifted_quartic(Rel::Le)),
        Err(SosError::NonStrictZeroRhs)
    );
    let changed_source = vec![constraint(poly(&[(&[TermId(1); 4], 1)]), Rel::Lt)];
    assert_eq!(
        cert.verify(&changed_source),
        Err(SosError::IdentityMismatch)
    );
}

fn product_zero_certificate() -> SosCertificate {
    SosCertificate {
        basis: vec![vec![]],
        gram: vec![vec![zero()]],
        terms: vec![CertTerm {
            origin: CertOrigin::Product(0, 1),
            multiplier: one(),
        }],
        rhs: zero(),
    }
}

#[test]
fn product_strictness_requires_both_original_factors_strict() {
    let x = TermId(1);
    // x²>0 and 0>=0 are satisfiable at x=1. Their zero product is NOT strict.
    let mut source = vec![
        constraint(poly(&[(&[x, x], 1)]), Rel::Gt),
        constraint(MultiPoly::zero(), Rel::Ge),
    ];
    let cert = product_zero_certificate();
    assert_eq!(cert.verify(&source), Err(SosError::NonStrictZeroRhs));
    source[1].rel = Rel::Gt; // Now 0>0 is genuinely contradictory.
    assert_eq!(cert.verify(&source), Ok(()));
    source[1].rel = Rel::Eq;
    assert_eq!(cert.verify(&source), Err(SosError::NotOrientable));
}

#[test]
fn checker_rejects_over_degree_product_before_multiplication() {
    let x = TermId(1);
    let source = vec![
        constraint(poly(&[(&[x; 3], 1)]), Rel::Gt),
        constraint(poly(&[(&[x; 2], 1)]), Rel::Gt),
    ];
    assert_eq!(
        product_zero_certificate().verify(&source),
        Err(SosError::NotOrientable)
    );
}

#[test]
fn checker_declines_oversized_gram_and_rationals() {
    let source = shifted_quartic(Rel::Lt);
    let mut cert = product_zero_certificate();
    cert.basis = vec![vec![]; MAX_BASIS + 1];
    assert_eq!(cert.verify(&source), Err(SosError::ResourceLimit));
    let mut cert = search(&source, &[TermId(1)]).expect("quartic certificate");
    cert.terms[0].multiplier =
        BigRational::from_integer(BigInt::one() << MAX_SOS_COEFFICIENT_BITS as usize);
    assert_eq!(cert.verify(&source), Err(SosError::ResourceLimit));
}
