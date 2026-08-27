// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::model::{rceil, ref_ceil_at, ref_exponent, ref_floor_at, ref_poly_sign, rfloor, to_r};
use super::{Case, R};
use ay_nra::oracle_api::OBq;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

pub(super) fn check_canonical(n: u64, case: &Case) -> bool {
    for (value, reference) in [(&case.x, &case.rx), (&case.y, &case.ry)] {
        if to_r(value) != *reference {
            bad!(
                n,
                "value drifted: {}/2^{} != {}",
                value.numerator(),
                value.k(),
                reference
            );
        }
        if value.numerator().is_zero() && value.k() != 0 {
            bad!(n, "zero not canonical: k={}", value.k());
        }
        if value.k() != 0 && (&value.numerator() % BigInt::from(2)).is_zero() {
            bad!(n, "non-canonical: k={} numerator even", value.k());
        }
        match ref_exponent(reference) {
            Some(exponent) if exponent == value.k() => {}
            other => bad!(
                n,
                "exponent mismatch: packed {} vs recovered {:?}",
                value.k(),
                other
            ),
        }
    }

    let structural = case.x.numerator() == case.y.numerator() && case.x.k() == case.y.k();
    if structural != (case.rx == case.ry) {
        bad!(
            n,
            "PartialEq unsound: struct {} vs numeric {}",
            structural,
            case.rx == case.ry
        );
    }
    true
}

pub(super) fn check_arithmetic(n: u64, case: &Case, rng: &mut R) -> bool {
    let (x, y, rx, ry) = (&case.x, &case.y, &case.rx, &case.ry);
    if to_r(&x.add(y)) != rx + ry {
        bad!(n, "add wrong");
    }
    if to_r(&x.sub(y)) != rx - ry {
        bad!(n, "sub wrong");
    }
    match x.mul(y) {
        Some(product) if to_r(&product) != rx * ry => bad!(n, "mul wrong"),
        None if u32::try_from(u64::from(case.xk) + u64::from(case.yk)).is_ok() => {
            bad!(
                n,
                "mul declined without overflow (k {} + {})",
                case.xk,
                case.yk
            );
        }
        _ => {}
    }
    if to_r(&x.neg()) != -rx {
        bad!(n, "neg wrong");
    }
    if to_r(&x.abs()) != rx.abs() {
        bad!(n, "abs wrong");
    }
    if x.is_int() != rx.is_integer() {
        bad!(n, "is_int wrong at {}", rx);
    }
    if x.sign() != ref_poly_sign(&[BigInt::zero(), BigInt::one()], rx) {
        bad!(n, "sign wrong");
    }
    if x.cmp_bq(y) != rx.cmp(ry) {
        bad!(n, "cmp wrong: {:?} vs {:?}", x.cmp_bq(y), rx.cmp(ry));
    }
    if x.floor() != rfloor(rx) {
        bad!(n, "floor wrong at {}: {} vs {}", rx, x.floor(), rfloor(rx));
    }
    if x.ceil() != rceil(rx) {
        bad!(n, "ceil wrong at {}: {} vs {}", rx, x.ceil(), rceil(rx));
    }

    let exponent = rng.below(70) as u32;
    let scale = BigRational::from_integer(BigInt::one() << exponent);
    if to_r(&x.mul_two_pow(exponent)) != rx * &scale {
        bad!(n, "mul_two_pow({}) wrong", exponent);
    }
    match x.div_two_pow(exponent) {
        Some(value) if to_r(&value) != rx / &scale => {
            bad!(n, "div_two_pow({}) wrong", exponent);
        }
        None if u32::try_from(u64::from(case.xk) + u64::from(exponent)).is_ok()
            && !case.xa == 0 =>
        {
            bad!(n, "div_two_pow declined without overflow");
        }
        _ => {}
    }
    check_scaled_rounding(n, case, exponent)
}

fn check_scaled_rounding(n: u64, case: &Case, random_exponent: u32) -> bool {
    for exponent in [
        0,
        1,
        case.xk.saturating_sub(1),
        case.xk,
        case.xk + 1,
        case.xk + 17,
        random_exponent,
    ] {
        if case.x.floor_at(exponent) != ref_floor_at(&case.rx, exponent) {
            bad!(
                n,
                "floor_at({}) wrong at {}/2^{}",
                exponent,
                case.xa,
                case.xk
            );
        }
        if case.x.ceil_at(exponent) != ref_ceil_at(&case.rx, exponent) {
            bad!(
                n,
                "ceil_at({}) wrong at {}/2^{}",
                exponent,
                case.xa,
                case.xk
            );
        }
    }
    true
}

pub(super) fn check_representability(n: u64, rng: &mut R) -> bool {
    let exponent = rng.below(12) as u32;
    let numerator = rng.range(-400, 400);
    let dyadic = BigRational::new(BigInt::from(numerator) * 6, (BigInt::one() << exponent) * 6);
    if !OBq::is_representable(&dyadic) {
        bad!(n, "is_representable said NO to the dyadic {}", dyadic);
    }
    match OBq::from_rational(&dyadic) {
        Some(value) if to_r(&value) == dyadic => {}
        other => bad!(
            n,
            "from_rational lost the dyadic {} -> {:?}",
            dyadic,
            other.map(|value| to_r(&value))
        ),
    }

    let odd_factors = [3i64, 5, 7, 9, 11, 13, 15, 21, 25, 27, 33, 49];
    let odd = odd_factors[rng.below(odd_factors.len() as u64) as usize];
    let mut numerator = rng.range(1, 5000);
    while numerator % odd == 0 {
        numerator += 1;
    }
    let non_dyadic = BigRational::new(
        BigInt::from(numerator),
        BigInt::from(odd) * (BigInt::one() << rng.below(6)),
    );
    let truly_dyadic = ref_exponent(&non_dyadic).is_some();
    if OBq::is_representable(&non_dyadic) != truly_dyadic {
        bad!(
            n,
            "is_representable({}) = {} but truth is {}",
            non_dyadic,
            OBq::is_representable(&non_dyadic),
            truly_dyadic
        );
    }
    if OBq::from_rational(&non_dyadic).is_some() != truly_dyadic {
        bad!(
            n,
            "from_rational/is_representable DRIFTED on {}",
            non_dyadic
        );
    }
    true
}
