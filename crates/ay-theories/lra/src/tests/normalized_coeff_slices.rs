// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The slice-level coefficient comparisons used by
//! `matching_slack_vars` must agree with the `LinearExpr` methods on
//! normalized expressions, and `coeffs_are_normalized` must accept
//! exactly the slices `LinearExpr::normalize` would leave unchanged
//! (sorted by variable, no duplicates, no zero coefficients) — the
//! fast path skips a per-row clone+normalize only under that check.

use crate::linear_expr::{
    coeffs_are_normalized, proportional_coeff_slice_ratio, same_coeff_slices,
};
use crate::rational::Rational;
use crate::LinearExpr;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

fn expr(pairs: &[(u32, i64)]) -> LinearExpr {
    LinearExpr {
        coeffs: pairs
            .iter()
            .map(|&(v, c)| (v, Rational::from_big(BigRational::from(BigInt::from(c)))))
            .collect(),
        constant: Rational::zero(),
    }
}

#[test]
fn normalized_slice_check_accepts_only_canonical_slices() {
    let one = Rational::one();
    let zero = Rational::zero();
    assert!(coeffs_are_normalized(&[]));
    assert!(coeffs_are_normalized(&[(3, one.clone())]));
    assert!(coeffs_are_normalized(&[(1, one.clone()), (4, one.clone())]));
    assert!(!coeffs_are_normalized(&[
        (4, one.clone()),
        (1, one.clone())
    ]));
    assert!(!coeffs_are_normalized(&[
        (2, one.clone()),
        (2, one.clone())
    ]));
    assert!(!coeffs_are_normalized(&[(2, zero)]));
}

#[test]
fn slice_comparisons_agree_with_linear_expr_methods() {
    let cases: [(&[(u32, i64)], &[(u32, i64)]); 5] = [
        (&[(1, 2), (3, -1)], &[(1, 2), (3, -1)]),
        (&[(1, 2), (3, -1)], &[(1, 4), (3, -2)]),
        (&[(1, 2), (3, -1)], &[(1, -2), (3, 1)]),
        (&[(1, 2), (3, -1)], &[(1, 2), (4, -1)]),
        (&[(1, 2)], &[(1, 2), (3, -1)]),
    ];
    for (a, b) in cases {
        let (ea, eb) = (expr(a).normalize(), expr(b).normalize());
        assert_eq!(
            same_coeff_slices(&ea.coeffs, &eb.coeffs),
            ea.same_coefficients(&eb),
            "same-coefficient agreement for {a:?} vs {b:?}"
        );
        assert_eq!(
            proportional_coeff_slice_ratio(&ea.coeffs, &eb.coeffs),
            ea.proportional_coefficient_ratio(&eb),
            "proportional agreement for {a:?} vs {b:?}"
        );
    }
}
