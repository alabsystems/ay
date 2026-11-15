// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use num_traits::One;

fn single_term(variable: u32, degree: usize) -> MultiPoly {
    MultiPoly {
        terms: vec![(vec![TermId(variable); degree], BigRational::one())],
    }
}

fn power_of_two(bits: usize) -> BigRational {
    BigRational::from_integer(BigInt::one() << bits)
}

#[test]
fn source_visit_and_depth_limits_decline_at_the_boundary() {
    let mut visits = SosPolynomialBudget {
        term_visits: MAX_SOS_TERM_VISITS - 1,
        ..SosPolynomialBudget::default()
    };
    assert!(visits.visit_term(0));
    assert!(!visits.visit_term(0));

    let mut depth = SosPolynomialBudget::default();
    assert!(depth.visit_term(MAX_SOS_TERM_DEPTH));
    assert!(!depth.visit_term(MAX_SOS_TERM_DEPTH + 1));
    assert_eq!(depth.term_visits, 1);
}

#[test]
fn monomial_and_product_work_limits_decline_at_the_boundary() {
    let mut monomials = SosPolynomialBudget {
        monomial_work: MAX_SOS_MONOMIAL_WORK - 1,
        ..SosPolynomialBudget::default()
    };
    assert!(monomials.charge_monomial());
    assert!(!monomials.charge_monomial());

    let mut products = SosPolynomialBudget {
        term_products: MAX_SOS_TERM_PRODUCTS - 1,
        ..SosPolynomialBudget::default()
    };
    assert!(checked_poly_mul(&single_term(1, 2), &single_term(2, 2), &mut products).is_some());
    assert!(checked_poly_mul(&single_term(1, 2), &single_term(2, 2), &mut products).is_none());
}

#[test]
fn quartic_degree_is_admitted_but_degree_five_declines() {
    let quartic = checked_poly_mul(
        &single_term(1, 2),
        &single_term(2, 2),
        &mut SosPolynomialBudget::default(),
    )
    .expect("degree-four product fits");
    assert_eq!(
        quartic.terms[0].0,
        vec![TermId(1), TermId(1), TermId(2), TermId(2)]
    );
    assert!(polynomial_fits(&quartic, None));
    assert!(!polynomial_fits(&single_term(1, 5), None));
    assert!(checked_poly_mul(
        &quartic,
        &single_term(1, 1),
        &mut SosPolynomialBudget::default(),
    )
    .is_none());
}

#[test]
fn malformed_polynomials_decline_before_operations() {
    let mut duplicated = single_term(1, 1);
    duplicated.terms.push(duplicated.terms[0].clone());
    let malformed = [
        duplicated,
        MultiPoly {
            terms: vec![(vec![TermId(2), TermId(1)], BigRational::one())],
        },
        MultiPoly {
            terms: vec![(vec![TermId(1)], BigRational::zero())],
        },
        single_term(1, 5),
    ];
    for poly in malformed {
        assert!(!polynomial_fits(&poly, None));
        assert!(checked_poly_add(
            &poly,
            &MultiPoly::zero(),
            &mut SosPolynomialBudget::default()
        )
        .is_none());
        assert!(checked_poly_sub(
            &MultiPoly::zero(),
            &poly,
            &mut SosPolynomialBudget::default()
        )
        .is_none());
        assert!(checked_poly_neg(&poly, &mut SosPolynomialBudget::default()).is_none());
        assert!(checked_poly_mul(
            &poly,
            &MultiPoly::zero(),
            &mut SosPolynomialBudget::default()
        )
        .is_none());
    }
}

#[test]
fn variable_membership_and_unordered_distinct_terms_are_checked() {
    let mut poly = single_term(2, 1);
    poly.terms.extend(single_term(1, 1).terms);
    assert!(polynomial_fits(&poly, Some(&[TermId(1), TermId(2)])));
    assert!(!polynomial_fits(&poly, Some(&[TermId(1)])));
    assert!(!polynomial_fits(
        &poly,
        Some(&vec![TermId(1); MAX_SOS_POLY_TERMS + 1])
    ));
}

#[test]
fn retained_term_limit_and_cancellation_are_checked() {
    let mut poly = MultiPoly {
        terms: (0..MAX_SOS_POLY_TERMS)
            .map(|index| (vec![TermId(index as u32)], BigRational::one()))
            .collect(),
    };
    assert!(polynomial_fits(&poly, None));
    let extra = single_term(MAX_SOS_POLY_TERMS as u32, 1);
    assert!(checked_poly_add(&poly, &extra, &mut SosPolynomialBudget::default()).is_none());
    let mut replacement = single_term(0, 1);
    replacement.terms[0].1 = -BigRational::one();
    replacement.terms.extend(extra.terms.clone());
    let replaced = checked_poly_add(&poly, &replacement, &mut SosPolynomialBudget::default())
        .expect("cancellation frees one retained term");
    assert_eq!(replaced.terms.len(), MAX_SOS_POLY_TERMS);
    assert!(polynomial_fits(&replaced, None));
    poly.terms.extend(extra.terms);
    assert!(!polynomial_fits(&poly, None));
}

#[test]
fn coefficient_numerator_and_denominator_limits_are_exact() {
    let at_limit = power_of_two(MAX_SOS_COEFFICIENT_BITS as usize - 1);
    let over_limit = power_of_two(MAX_SOS_COEFFICIENT_BITS as usize);
    assert!(rational_fits(&at_limit));
    assert!(rational_fits(&-at_limit.clone()));
    assert!(!rational_fits(&over_limit));
    assert!(rational_fits(&at_limit.recip()));
    assert!(!rational_fits(&over_limit.recip()));
}

#[test]
fn malformed_raw_rational_denominators_decline() {
    for denominator in [BigInt::zero(), -BigInt::one()] {
        let value = BigRational::new_raw(BigInt::one(), denominator);
        assert!(!rational_fits(&value));
        let poly = MultiPoly::constant(value);
        assert!(!polynomial_fits(&poly, None));
        assert!(checked_poly_neg(&poly, &mut SosPolynomialBudget::default()).is_none());
    }
}

#[test]
fn oversized_input_and_oversized_result_both_decline() {
    let at_limit = MultiPoly::constant(power_of_two(MAX_SOS_COEFFICIENT_BITS as usize - 1));
    let over_limit = MultiPoly::constant(power_of_two(MAX_SOS_COEFFICIENT_BITS as usize));
    assert!(checked_poly_add(&at_limit, &at_limit, &mut SosPolynomialBudget::default()).is_none());
    assert!(checked_poly_mul(&at_limit, &at_limit, &mut SosPolynomialBudget::default()).is_none());
    // Cancellation or multiplication by zero must not evade input preflight.
    assert!(checked_poly_sub(
        &over_limit,
        &over_limit,
        &mut SosPolynomialBudget::default()
    )
    .is_none());
    assert!(checked_poly_mul(
        &over_limit,
        &MultiPoly::zero(),
        &mut SosPolynomialBudget::default()
    )
    .is_none());
}

#[test]
fn addition_charges_copied_terms_and_subtraction_cancels_exactly() {
    let poly = single_term(1, 2);
    let mut exhausted = SosPolynomialBudget {
        monomial_work: MAX_SOS_MONOMIAL_WORK,
        ..SosPolynomialBudget::default()
    };
    assert!(checked_poly_add(&poly, &MultiPoly::zero(), &mut exhausted).is_none());
    let difference = checked_poly_sub(&poly, &poly, &mut SosPolynomialBudget::default())
        .expect("small exact subtraction");
    assert!(difference.terms.is_empty());
}

#[test]
fn lp_update_and_pivot_budgets_are_checked_and_do_not_wrap() {
    let mut budget = SosLpBudget {
        updates_left: 1,
        pivots_left: 1,
        ..SosLpBudget::default()
    };
    assert!(!budget.charge_updates(usize::MAX));
    assert!(budget.charge_updates(1));
    assert!(!budget.charge_updates(1));
    assert!(budget.charge_pivot());
    assert!(!budget.charge_pivot());
}

#[test]
fn lp_tableau_cell_boundary_and_dimension_overflow_are_checked() {
    assert_eq!(128 * (383 + 128 + 1), MAX_SOS_LP_CELLS);
    assert!(lp_dimensions_fit(128, 383));
    assert!(!lp_dimensions_fit(128, 384));
    assert!(lp_dimensions_fit(0, MAX_SOS_LP_CELLS));
    assert!(!lp_dimensions_fit(0, MAX_SOS_LP_CELLS + 1));
    assert!(!lp_dimensions_fit(usize::MAX, 0));
    assert!(!lp_dimensions_fit(usize::MAX / 2, 1));
    assert!(!lp_dimensions_fit(1, usize::MAX));
}
