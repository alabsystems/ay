// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! GCD normalization for IntSat constraints.
//!
//! Every constraint is eagerly normalized: divide all coefficients by GCD
//! and floor the RHS. This produces a free Chvatal-Gomory cut at every step.

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{One, Signed, Zero};

use crate::types::Constraint;

/// Normalize a constraint in-place by dividing all coefficients by their GCD
/// and flooring the RHS.
///
/// Given `a1*x1 + ... + an*xn <= b`, if `g = gcd(|a1|, ..., |an|)` with g > 1,
/// then the constraint is equivalent to `(a1/g)*x1 + ... + (an/g)*xn <= floor(b/g)`
/// for integer variables. This is because the LHS is always a multiple of g.
pub(crate) fn normalize_constraint(c: &mut Constraint) {
    if c.coeffs.is_empty() {
        return;
    }

    // Compute GCD of absolute values of all coefficients.
    let mut g = BigInt::zero();
    for (_, coeff) in &c.coeffs {
        let abs_c = coeff.abs();
        if g.is_zero() {
            g = abs_c;
        } else {
            g = g.gcd(&abs_c);
        }
        if g.is_one() {
            return; // GCD is 1, nothing to normalize
        }
    }

    if g.is_zero() || g.is_one() {
        return;
    }

    // Divide all coefficients by GCD.
    for (_, coeff) in &mut c.coeffs {
        *coeff = &*coeff / &g;
    }

    // Floor the RHS: floor(b / g).
    // For integer division: if b >= 0, floor(b/g) = b / g (Rust truncates toward zero).
    // If b < 0, floor(b/g) = (b - g + 1) / g for positive g.
    c.rhs = floor_div(&c.rhs, &g);
}

/// Integer floor division: floor(a / b) for b > 0.
#[must_use]
pub(crate) fn floor_div(a: &BigInt, b: &BigInt) -> BigInt {
    debug_assert!(
        b > &BigInt::zero(),
        "invariant: floor_div requires positive divisor, got {b}"
    );
    a.div_floor(b)
}

/// Integer ceiling division: ceil(a / b) for b > 0.
#[must_use]
#[allow(dead_code)]
pub(crate) fn ceil_div(a: &BigInt, b: &BigInt) -> BigInt {
    debug_assert!(
        b > &BigInt::zero(),
        "invariant: ceil_div requires positive divisor, got {b}"
    );
    // ceil(a/b) = floor((a + b - 1) / b) for b > 0
    let adjusted = a + b - BigInt::one();
    adjusted.div_floor(b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::VarId;

    #[test]
    fn test_normalize_basic() {
        let mut c = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(4)), (VarId(1), BigInt::from(6))],
            rhs: BigInt::from(9),
        };
        normalize_constraint(&mut c);
        // GCD(4, 6) = 2, so coeffs become (2, 3), rhs = floor(9/2) = 4
        assert_eq!(c.coeffs[0].1, BigInt::from(2));
        assert_eq!(c.coeffs[1].1, BigInt::from(3));
        assert_eq!(c.rhs, BigInt::from(4));
    }

    #[test]
    fn test_normalize_negative_rhs() {
        let mut c = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(4)), (VarId(1), BigInt::from(6))],
            rhs: BigInt::from(-5),
        };
        normalize_constraint(&mut c);
        // GCD(4, 6) = 2, rhs = floor(-5/2) = -3
        assert_eq!(c.rhs, BigInt::from(-3));
    }

    #[test]
    fn test_normalize_gcd_one() {
        let mut c = Constraint {
            coeffs: vec![(VarId(0), BigInt::from(3)), (VarId(1), BigInt::from(5))],
            rhs: BigInt::from(7),
        };
        let original = c.clone();
        normalize_constraint(&mut c);
        // GCD(3, 5) = 1, no change
        assert_eq!(c, original);
    }

    #[test]
    fn test_floor_div_positive() {
        assert_eq!(
            floor_div(&BigInt::from(7), &BigInt::from(3)),
            BigInt::from(2)
        );
    }

    #[test]
    fn test_floor_div_negative() {
        assert_eq!(
            floor_div(&BigInt::from(-7), &BigInt::from(3)),
            BigInt::from(-3)
        );
    }

    #[test]
    fn test_ceil_div_positive() {
        assert_eq!(
            ceil_div(&BigInt::from(7), &BigInt::from(3)),
            BigInt::from(3)
        );
    }

    #[test]
    fn test_ceil_div_negative() {
        assert_eq!(
            ceil_div(&BigInt::from(-7), &BigInt::from(3)),
            BigInt::from(-2)
        );
    }

    #[test]
    fn test_ceil_div_exact() {
        assert_eq!(
            ceil_div(&BigInt::from(6), &BigInt::from(3)),
            BigInt::from(2)
        );
    }
}
