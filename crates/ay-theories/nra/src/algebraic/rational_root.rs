// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact recognition of rational values represented by algebraic roots.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::{RealAlgebraic, RealAlgebraicValue, RealScalar, Refined};

/// Bisection budget for the rational-root certificate. Each step halves the
/// interval; this covers every leading coefficient admitted below.
const MAX_RATIONAL_ROOT_STEPS: usize = 256;

/// Leading-coefficient size past which the certificate declines. This is a
/// cost guard only: declining does not classify the root, and introspection
/// callers fail closed.
const MAX_RATIONAL_ROOT_LC_BITS: u64 = 64;

/// Result of the bounded rational-root certificate.
///
/// `NotRational` is a proved classification: the isolating interval is
/// narrower than the rational-root lattice and contains no polynomial root on
/// that lattice. `Undetermined` instead means a cost or invariant guard
/// declined before the classification could be proved.
enum RationalRootCertification {
    Rational(BigRational),
    NotRational,
    Undetermined,
}

impl RealAlgebraic {
    /// The exact rational value of this root when the bounded certificate
    /// recognizes one.
    ///
    /// Every rational root `p/q` in lowest terms of an integer polynomial has
    /// `q | lc`, so `lc * root` is an integer. Bisecting the isolating interval
    /// below `1/|lc|` leaves at most one point of that lattice. The candidate
    /// is accepted only when exact polynomial evaluation vanishes there.
    ///
    /// `None` does not by itself prove irrationality: it also covers a
    /// certificate declined by the leading-coefficient or refinement guard.
    /// Output/introspection callers use the internal tri-state certificate so
    /// that such a decline propagates as `None` rather than being reported as
    /// an algebraic irrational.
    pub fn rational_value(&self) -> Option<BigRational> {
        match self.certify_rational_root() {
            RationalRootCertification::Rational(value) => Some(value),
            RationalRootCertification::NotRational | RationalRootCertification::Undetermined => {
                None
            }
        }
    }

    fn certify_rational_root(&self) -> RationalRootCertification {
        let Some(lc) = self.poly.leading() else {
            return RationalRootCertification::Undetermined;
        };
        if !lc.is_integer() || lc.is_zero() {
            return RationalRootCertification::Undetermined;
        }
        let lc_int = lc.to_integer();
        let lc_abs = BigInt::from(lc_int.magnitude().clone());
        if lc_abs.bits() > MAX_RATIONAL_ROOT_LC_BITS {
            return RationalRootCertification::Undetermined;
        }
        let lattice = BigRational::new(BigInt::one(), lc_abs.clone());
        let (mut lo, mut hi) = (self.lo.clone(), self.hi.clone());
        for _ in 0..MAX_RATIONAL_ROOT_STEPS {
            if &hi - &lo < lattice {
                break;
            }
            let Some(refined) = Self::refine_step(&self.poly, &lo, &hi) else {
                return RationalRootCertification::Undetermined;
            };
            match refined {
                Refined::Interval(next_lo, next_hi) => {
                    lo = next_lo;
                    hi = next_hi;
                }
                Refined::Exact(root) => {
                    return RationalRootCertification::Rational(root);
                }
            }
        }
        if &hi - &lo >= lattice {
            return RationalRootCertification::Undetermined;
        }
        let scaled_lo = &lo * BigRational::from_integer(lc_abs.clone());
        let numerator = scaled_lo.floor().to_integer() + BigInt::one();
        let candidate = BigRational::new(numerator, lc_abs);
        if candidate <= lo || candidate >= hi || !self.poly.eval(&candidate).is_zero() {
            return RationalRootCertification::NotRational;
        }
        RationalRootCertification::Rational(candidate)
    }

    /// Canonicalize an identity residue at an explicit output/introspection
    /// boundary; arithmetic inner loops do not call this certificate.
    pub(super) fn identity_scalar(&self, identity: &RealAlgebraicValue) -> Option<RealScalar> {
        match self.certify_rational_root() {
            RationalRootCertification::Rational(value) => Some(RealScalar::Rational(value)),
            RationalRootCertification::NotRational => Some(RealScalar::Algebraic(identity.clone())),
            RationalRootCertification::Undetermined => None,
        }
    }
}

impl RealAlgebraicValue {
    /// [`Self::to_number`], plus exact rational-root recognition for an
    /// identity value. This output boundary may spend the bounded bisection
    /// certificate; arithmetic inner loops keep `to_number` constant-time.
    /// Returns `None` when that certificate declines before proving whether an
    /// identity value is rational.
    pub fn to_number_for_output(&self) -> Option<RealScalar> {
        if self.is_identity() {
            return self.alpha.identity_scalar(self);
        }
        self.to_number()
    }
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use super::super::{RealAlgebraic, RealScalar, UniPoly};

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    fn ratf(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    fn poly(coeffs: &[i64]) -> UniPoly {
        UniPoly::from_coeffs(coeffs.iter().map(|&coefficient| rat(coefficient)).collect())
    }

    fn algebraic(coeffs: &[i64], lo: BigRational, hi: BigRational) -> RealAlgebraic {
        RealAlgebraic::from_isolating_interval(&poly(coeffs), &lo, &hi).expect("isolates root")
    }

    #[test]
    fn rational_root_of_square_free_poly_is_reported_as_rational() {
        let one = algebraic(&[-1, 0, 1], ratf(1, 2), rat(2));
        assert_eq!(one.root_index(), 2);
        assert_eq!(one.rational_value(), Some(rat(1)));
        assert!(matches!(
            one.as_value().to_number_for_output(),
            Some(RealScalar::Rational(value)) if value == rat(1)
        ));
        assert!(matches!(
            one.as_value().to_number(),
            Some(RealScalar::Algebraic(_))
        ));

        let minus_one = algebraic(&[-1, 1, 2], rat(-2), ratf(-1, 2));
        assert_eq!(minus_one.rational_value(), Some(rat(-1)));
        let half = algebraic(&[-1, 0, 4], rat(0), rat(1));
        assert_eq!(half.rational_value(), Some(ratf(1, 2)));
    }

    #[test]
    fn irrational_roots_have_no_rational_value() {
        for (coeffs, lo, hi) in [
            (vec![-2, 0, 1], rat(1), rat(2)),
            (vec![-2, 0, 1], rat(-2), rat(-1)),
            (vec![-3, 0, 4], rat(0), rat(1)),
            (vec![-2, 0, 0, 1], rat(1), rat(2)),
        ] {
            let root = algebraic(&coeffs, lo, hi);
            assert_eq!(root.rational_value(), None);
            assert!(matches!(
                root.as_value().to_number_for_output(),
                Some(RealScalar::Algebraic(_))
            ));
        }
    }
}
