// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::model::{rceil, ref_candidate_at, ref_select_small, rfloor, to_r};
use super::Case;
use ay_nra::oracle_api::{obq_candidate_at, obq_select_int, obq_select_small, OBqInterval};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

pub(super) fn check(n: u64, case: &Case) -> bool {
    let interval = OBqInterval::new(&case.x, &case.y);
    let should_exist = case.rx < case.ry;
    if interval.is_some() != should_exist {
        bad!(
            n,
            "interval ctor: got {} expected {} for ({}, {})",
            interval.is_some(),
            should_exist,
            case.rx,
            case.ry
        );
    }
    let Some(interval) = interval else {
        return true;
    };
    check_geometry(n, case, &interval)
        && check_select_int(n, case)
        && check_select_small(n, case, &interval)
}

fn check_geometry(n: u64, case: &Case, interval: &OBqInterval) -> bool {
    let width = to_r(&interval.width());
    if width != &case.ry - &case.rx {
        bad!(n, "width wrong");
    }
    if !width.is_positive() {
        bad!(n, "width not positive");
    }
    let midpoint = interval
        .midpoint()
        .expect("midpoint of a non-empty interval");
    let reference = (&case.rx + &case.ry) / BigRational::from_integer(BigInt::from(2));
    if to_r(&midpoint) != reference {
        bad!(n, "midpoint wrong");
    }
    if !(case.rx < reference && reference < case.ry) {
        bad!(n, "midpoint not strictly inside");
    }
    if midpoint.k() > case.x.k().max(case.y.k()) + 1 {
        bad!(
            n,
            "midpoint k blew up: {} > max({},{})+1",
            midpoint.k(),
            case.x.k(),
            case.y.k()
        );
    }
    if interval.max_k() != case.x.k().max(case.y.k()) {
        bad!(n, "max_k wrong");
    }
    let (left, split, right) = interval.bisect().expect("bisect");
    if to_r(&split) != reference || to_r(&left.hi()) != reference || to_r(&right.lo()) != reference
    {
        bad!(n, "bisect wrong");
    }
    true
}

fn check_select_int(n: u64, case: &Case) -> bool {
    let selected = obq_select_int(&case.x, &case.y);
    let first: BigInt = rfloor(&case.rx) + 1;
    let last: BigInt = rceil(&case.ry) - 1;
    let expected = if first > last {
        None
    } else if first.is_positive() {
        Some(first)
    } else if last.is_negative() {
        Some(last)
    } else {
        Some(BigInt::zero())
    };
    if selected != expected {
        bad!(
            n,
            "select_int {:?} vs reference {:?} on ({}, {})",
            selected,
            expected,
            case.rx,
            case.ry
        );
    }
    if let Some(value) = selected {
        let rational = BigRational::from_integer(value.clone());
        if !(case.rx < rational && rational < case.ry) {
            bad!(
                n,
                "select_int {} NOT strictly inside ({}, {})",
                value,
                case.rx,
                case.ry
            );
        }
    }
    true
}

fn check_select_small(n: u64, case: &Case, interval: &OBqInterval) -> bool {
    let ceiling = interval.width().k() + 1;
    let Some((value, reported_ceiling)) = obq_select_small(interval) else {
        bad!(
            n,
            "select_small declined on the non-empty interval ({}, {})",
            case.rx,
            case.ry
        );
    };
    if reported_ceiling != ceiling {
        bad!(n, "k_ceiling {} vs derived {}", reported_ceiling, ceiling);
    }
    let rational = to_r(&value);
    if !(case.rx < rational && rational < case.ry) {
        bad!(n, "select_small {} not strictly inside", rational);
    }
    match ref_select_small(&case.rx, &case.ry, ceiling) {
        Some((exponent, numerator)) => {
            if exponent != value.k() {
                bad!(
                    n,
                    "select_small k={} but reference minimal k={} on ({}, {})",
                    value.k(),
                    exponent,
                    case.rx,
                    case.ry
                );
            }
            let reference = BigRational::new(numerator, BigInt::one() << exponent);
            if reference != rational {
                bad!(
                    n,
                    "select_small value {} vs reference {}",
                    rational,
                    reference
                );
            }
        }
        None => bad!(
            n,
            "reference found NO interior dyadic but module returned {}",
            rational
        ),
    }
    check_select_small_minimal(n, case, interval, &value, ceiling)
}

fn check_select_small_minimal(
    n: u64,
    case: &Case,
    interval: &OBqInterval,
    value: &ay_nra::oracle_api::OBq,
    ceiling: u32,
) -> bool {
    for exponent in 0..value.k() {
        if let Some(numerator) = ref_candidate_at(&case.rx, &case.ry, exponent) {
            bad!(
                n,
                "NOT minimal: answered k={} but {}/2^{} is inside ({}, {})",
                value.k(),
                numerator,
                exponent,
                case.rx,
                case.ry
            );
        }
        if obq_candidate_at(interval, exponent).is_some() {
            bad!(
                n,
                "candidate_at({}) is Some but select_small chose k={}",
                exponent,
                value.k()
            );
        }
    }
    for exponent in 0..=(value.k() + 3).min(ceiling + 3) {
        let got = obq_candidate_at(interval, exponent);
        let expected = ref_candidate_at(&case.rx, &case.ry, exponent);
        if got != expected {
            bad!(
                n,
                "candidate_at({}) {:?} vs reference {:?}",
                exponent,
                got,
                expected
            );
        }
    }
    true
}
