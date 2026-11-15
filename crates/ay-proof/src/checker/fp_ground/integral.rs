// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent exact IEEE-754 integral rounding and remainder.
//! SMT-LIB FloatingPoint 2.7: https://smt-lib.org/theories-FloatingPoint.shtml
//! Remainder uses the nearest integer quotient, ties to even, independently
//! of any rounding mode. Neither operation uses the producer's FP evaluator.

use super::*;

#[cfg(test)]
pub(super) fn round_to_integral(mode: Rm, value: &Fp) -> Option<Fp> {
    with_local_meter(|meter| round_to_integral_owned(mode, value, meter))
}

pub(super) fn round_to_integral_owned(mode: Rm, value: &Fp, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
    if value.is_nan() {
        return Fp::nan(value.eb, value.sb);
    }
    if value.is_infinite() || value.is_zero() {
        return Some(*value);
    }
    let exact = value.to_rational_owned(meter)?;
    let absolute = meter.rational_abs(&exact)?;
    let magnitude = round_magnitude_owned(&absolute, mode, value.sign, meter)?;
    let rounded = if value.sign { -magnitude } else { magnitude };
    // Preserve the input sign when rounding a negative magnitude to zero.
    // Legal tiny exponent formats can overflow (e.g. (2,3), 3.5 -> 4);
    // the normal rounding kernel applies the selected IEEE overflow rule.
    let rounded = meter.from_integer(rounded)?;
    round_rational_owned(&rounded, value.sign, value.eb, value.sb, mode, meter)
}

#[cfg(test)]
pub(super) fn remainder(left: &Fp, right: &Fp) -> Option<Fp> {
    with_local_meter(|meter| remainder_owned(left, right, meter))
}

pub(super) fn remainder_owned(left: &Fp, right: &Fp, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
    if left.eb != right.eb || left.sb != right.sb {
        return None;
    }
    if left.is_nan() || right.is_nan() || left.is_infinite() || right.is_zero() {
        return Fp::nan(left.eb, left.sb);
    }
    if left.is_zero() || right.is_infinite() {
        return Some(*left);
    }
    let x = left.to_rational_owned(meter)?;
    let y = right.to_rational_owned(meter)?;
    let quotient = meter.rational_binary(&x, &y, Arithmetic::Divide)?;
    if !rational_is_bounded(&quotient) {
        return None;
    }
    let absolute = meter.rational_abs(&quotient)?;
    let magnitude = round_magnitude_owned(&absolute, Rm::Rne, quotient.is_negative(), meter)?;
    let nearest = if quotient.is_negative() {
        -magnitude
    } else {
        magnitude
    };
    let nearest = meter.from_integer(nearest)?;
    let product = meter.rational_binary(&y, &nearest, Arithmetic::Multiply)?;
    let exact = meter.rational_binary(&x, &product, Arithmetic::Subtract)?;
    if !rational_is_bounded(&exact) {
        return None;
    }
    let result = round_rational_owned(&exact, left.sign, left.eb, left.sb, Rm::Rne, meter)?;
    // IEEE remainder is exact. Refuse rather than silently admitting a
    // rounded approximation if a representation invariant ever fails.
    let represented = result.to_rational_owned(meter)?;
    (meter.rational_compare(&represented, &exact)? == std::cmp::Ordering::Equal).then_some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn value(n: i64, d: i64) -> Fp {
        round_rational(
            &BigRational::new(BigInt::from(n), BigInt::from(d)),
            n < 0,
            8,
            24,
            Rm::Rne,
        )
        .unwrap()
    }

    #[test]
    fn integral_ties_directed_modes_and_signed_zero() {
        for (mode, positive, negative) in [
            (Rm::Rne, 2, -2),
            (Rm::Rna, 3, -3),
            (Rm::Rtp, 3, -2),
            (Rm::Rtn, 2, -3),
            (Rm::Rtz, 2, -2),
        ] {
            assert_eq!(
                round_to_integral(mode, &value(5, 2)),
                Some(value(positive, 1))
            );
            assert_eq!(
                round_to_integral(mode, &value(-5, 2)),
                Some(value(negative, 1))
            );
        }
        assert_eq!(round_to_integral(Rm::Rne, &value(7, 2)), Some(value(4, 1)));
        assert_eq!(
            round_to_integral(Rm::Rne, &value(-1, 2)),
            Fp::zero(true, 8, 24)
        );
        let infinity = Fp::infinity(true, 8, 24).unwrap();
        assert_eq!(round_to_integral(Rm::Rtz, &infinity), Some(infinity));
        assert!(round_to_integral(Rm::Rne, &Fp::nan(8, 24).unwrap())
            .unwrap()
            .is_nan());
    }

    #[test]
    fn remainder_uses_nearest_even_quotient_and_dividend_zero_sign() {
        for (x, y, expected) in [(3, 2, -1), (5, 2, 1), (7, 2, -1), (-3, 2, 1), (3, -2, -1)] {
            assert_eq!(
                remainder(&value(x, 1), &value(y, 1)),
                Some(value(expected, 1))
            );
        }
        assert_eq!(
            remainder(&value(-4, 1), &value(2, 1)),
            Fp::zero(true, 8, 24)
        );
        let infinity = Fp::infinity(false, 8, 24).unwrap();
        assert_eq!(remainder(&value(3, 1), &infinity), Some(value(3, 1)));
        assert!(remainder(&infinity, &value(2, 1)).unwrap().is_nan());
        assert!(remainder(&value(2, 1), &Fp::zero(false, 8, 24).unwrap())
            .unwrap()
            .is_nan());
        assert!(remainder(&value(2, 1), &Fp::zero(false, 5, 11).unwrap()).is_none());
    }

    #[test]
    fn tiny_exponent_integral_rounding_uses_ieee_overflow() {
        let maximum = Fp::checked(false, 2, 3, 2, 3).unwrap();
        assert_eq!(
            maximum.to_rational(),
            Some(BigRational::new(BigInt::from(7), BigInt::from(2)))
        );
        assert_eq!(
            round_to_integral(Rm::Rne, &maximum),
            Fp::infinity(false, 2, 3)
        );
        assert_eq!(
            round_to_integral(Rm::Rtz, &maximum),
            Fp::checked(false, 2, 2, 2, 3)
        );
    }
}
