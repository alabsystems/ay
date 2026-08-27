// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::model::{
    r_of, ref_ceil_at, ref_floor_at, ref_poly_eval, ref_poly_sign, ref_step_bound, to_r,
};
use super::{Case, R};
use ay_nra::oracle_api::{
    obq_enclose_rational, obq_poly_eval_at, obq_poly_sign_at, obq_refine_step_bound,
    obq_refine_to_width, obq_refine_until_separated, obq_select_non_root, OBq, OBqInterval,
    ORefined, OSeparation,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::cmp::Ordering;

pub(super) fn random_polynomial(rng: &mut R) -> Vec<BigInt> {
    let degree = rng.below(5) as usize + 1;
    (0..=degree)
        .map(|_| BigInt::from(rng.range(-30, 30)))
        .collect()
}

pub(super) fn check_polynomial(n: u64, case: &Case, polynomial: &[BigInt]) -> bool {
    if let Some(sign) = obq_poly_sign_at(polynomial, &case.x) {
        let reference = ref_poly_sign(polynomial, &case.rx);
        if sign != reference {
            bad!(
                n,
                "poly_sign_at {} vs reference {} at {}",
                sign,
                reference,
                case.rx
            );
        }
    }
    if let Some(value) = obq_poly_eval_at(polynomial, &case.x) {
        if to_r(&value) != ref_poly_eval(polynomial, &case.rx) {
            bad!(n, "poly_eval_at wrong at {}", case.rx);
        }
    }
    true
}

pub(super) fn check_step_bound(n: u64, rng: &mut R) -> bool {
    let width_numerator = rng.range(1, 4096);
    let width_exponent = rng.below(40) as u32;
    let target_numerator = rng.range(-4, 4096);
    let target_exponent = rng.below(40) as u32;
    let width = OBq::new(BigInt::from(width_numerator), width_exponent);
    let target = OBq::new(BigInt::from(target_numerator), target_exponent);
    let width_ref = r_of(width_numerator, width_exponent);
    let target_ref = r_of(target_numerator, target_exponent);
    let got = obq_refine_step_bound(&width, &target);
    let expected = ref_step_bound(&width_ref, &target_ref, 16_384);
    match (got, expected) {
        (Some(got), Some(expected)) if got < expected => bad!(
            n,
            "step bound {} BELOW the exact minimum {} (w={} t={})",
            got,
            expected,
            width_ref,
            target_ref
        ),
        (Some(got), Some(expected)) if got > expected + 2 => bad!(
            n,
            "step bound {} far above the exact minimum {} (w={} t={})",
            got,
            expected,
            width_ref,
            target_ref
        ),
        (None, Some(expected)) if target_ref.is_positive() && expected <= 16_384 => bad!(
            n,
            "step bound declined but exact minimum is {} (w={} t={})",
            expected,
            width_ref,
            target_ref
        ),
        (Some(got), None) if !target_ref.is_positive() => {
            bad!(
                n,
                "step bound {} on a non-positive target {}",
                got,
                target_ref
            );
        }
        _ => {}
    }
    true
}

pub(super) fn check_refine_width(n: u64, rng: &mut R) -> bool {
    let radicand = [2i64, 3, 5, 6, 7, 10, 11, 13][rng.below(8) as usize];
    let polynomial = vec![BigInt::from(-radicand), BigInt::zero(), BigInt::one()];
    let integer_lo = (radicand as f64).sqrt().floor() as i64;
    let start = OBqInterval::new(
        &OBq::new(BigInt::from(integer_lo), 0),
        &OBq::new(BigInt::from(integer_lo + 1), 0),
    )
    .expect("isolating interval");
    let target = OBq::inv_two_pow(1 + rng.below(30) as u32);
    let Some((outcome, trace)) = obq_refine_to_width(&polynomial, &start, &target) else {
        bad!(
            n,
            "refine_to_width declined on a genuine isolating interval of x^2-{}",
            radicand
        );
    };
    if trace.steps > trace.bound {
        bad!(
            n,
            "steps {} EXCEEDS the derived bound {}",
            trace.steps,
            trace.bound
        );
    }
    match outcome {
        ORefined::Narrowed(interval) => {
            check_narrowed(n, radicand, &polynomial, &target, &interval, &trace)
        }
        ORefined::Exact(value) if ref_poly_sign(&polynomial, &to_r(&value)) != 0 => {
            bad!(
                n,
                "Exact({}) is NOT a root of x^2-{}",
                to_r(&value),
                radicand
            );
        }
        ORefined::Exact(_) => true,
    }
}

fn check_narrowed(
    n: u64,
    radicand: i64,
    polynomial: &[BigInt],
    target: &OBq,
    interval: &OBqInterval,
    trace: &ay_nra::oracle_api::ORefineTrace,
) -> bool {
    let (lo, hi) = (to_r(&interval.lo()), to_r(&interval.hi()));
    if ref_poly_sign(polynomial, &lo) * ref_poly_sign(polynomial, &hi) >= 0 {
        bad!(
            n,
            "refined interval ({}, {}) no longer brackets a root of x^2-{}",
            lo,
            hi,
            radicand
        );
    }
    if &hi - &lo > to_r(target) {
        bad!(
            n,
            "refined width {} exceeds target {}",
            &hi - &lo,
            to_r(target)
        );
    }
    let end_width = &hi - &lo;
    if end_width * BigRational::from_integer(BigInt::one() << trace.steps) != BigRational::one() {
        bad!(n, "width identity broken at steps={}", trace.steps);
    }
    if interval.max_k() != trace.end_max_k {
        bad!(
            n,
            "end_max_k {} vs interval max_k {}",
            trace.end_max_k,
            interval.max_k()
        );
    }
    if u64::from(interval.max_k()) > u64::from(trace.steps) {
        bad!(
            n,
            "k {} grew faster than steps {}",
            interval.max_k(),
            trace.steps
        );
    }
    true
}

pub(super) fn check_enclosure(n: u64, rng: &mut R) -> bool {
    let lo_numerator = rng.range(-300, 300);
    let denominator = rng.range(1, 40);
    let hi_numerator = lo_numerator + rng.range(1, 200);
    let lo = BigRational::new(BigInt::from(lo_numerator), BigInt::from(denominator));
    let hi = BigRational::new(BigInt::from(hi_numerator), BigInt::from(denominator));
    let exponent = rng.below(30) as u32;
    match obq_enclose_rational(&lo, &hi, exponent) {
        Some(interval) => check_enclosed_interval(n, &lo, &hi, exponent, &interval),
        None if lo < hi => {
            let rounded_lo =
                BigRational::new(ref_floor_at(&lo, exponent), BigInt::one() << exponent);
            let rounded_hi =
                BigRational::new(ref_ceil_at(&hi, exponent), BigInt::one() << exponent);
            if rounded_lo < rounded_hi {
                bad!(
                    n,
                    "enclose_rational declined on ({}, {}) at k={}",
                    lo,
                    hi,
                    exponent
                );
            }
            true
        }
        None => true,
    }
}

fn check_enclosed_interval(
    n: u64,
    source_lo: &BigRational,
    source_hi: &BigRational,
    exponent: u32,
    interval: &OBqInterval,
) -> bool {
    let (lo, hi) = (to_r(&interval.lo()), to_r(&interval.hi()));
    if lo > *source_lo || hi < *source_hi {
        bad!(
            n,
            "enclose_rational NARROWED: ({}, {}) does not contain ({}, {})",
            lo,
            hi,
            source_lo,
            source_hi
        );
    }
    if interval.lo().k() > exponent || interval.hi().k() > exponent {
        bad!(
            n,
            "enclose_rational produced k above the requested {}",
            exponent
        );
    }
    if lo != BigRational::new(ref_floor_at(source_lo, exponent), BigInt::one() << exponent) {
        bad!(n, "enclose_rational lo not floor-rounded");
    }
    if hi != BigRational::new(ref_ceil_at(source_hi, exponent), BigInt::one() << exponent) {
        bad!(n, "enclose_rational hi not ceil-rounded");
    }
    true
}

pub(super) fn check_non_root(n: u64, rng: &mut R, polynomial: &[BigInt]) -> bool {
    let interval = OBqInterval::new(
        &OBq::new(BigInt::from(rng.range(-40, 40)), rng.below(8) as u32),
        &OBq::new(BigInt::from(rng.range(41, 200)), rng.below(8) as u32),
    );
    if let Some(interval) = interval {
        if let Some(value) = obq_select_non_root(polynomial, &interval) {
            let rational = to_r(&value);
            if !interval.contains_open(&value) {
                bad!(n, "select_non_root outside the interval");
            }
            if ref_poly_sign(polynomial, &rational) == 0 {
                bad!(n, "select_non_root returned an actual ROOT {}", rational);
            }
        }
    }
    true
}

pub(super) fn check_separation(n: u64) -> bool {
    let polynomial_b = vec![BigInt::from(-7), BigInt::zero(), BigInt::one()];
    let interval_a =
        OBqInterval::new(&OBq::new(BigInt::from(1), 0), &OBq::new(BigInt::from(2), 0)).unwrap();
    let interval_b =
        OBqInterval::new(&OBq::new(BigInt::from(2), 0), &OBq::new(BigInt::from(3), 0)).unwrap();
    let polynomial_a = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    if let Some((separation, _, _, rounds)) =
        obq_refine_until_separated(&polynomial_a, &interval_a, &polynomial_b, &interval_b, 40)
    {
        match separation {
            OSeparation::Ordered(ordering) if ordering != Ordering::Less => {
                bad!(n, "sqrt(2) < sqrt(7) but separation said {:?}", ordering);
            }
            OSeparation::Inconclusive if rounds < 40 => {
                bad!(n, "Inconclusive after only {} rounds", rounds);
            }
            _ => {}
        }
    }
    true
}
