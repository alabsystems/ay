// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independently round an exact positive rational, not the word recipe or a
//! native/producer FP operation. This test oracle is NOT symbolic acceptance.

use super::*;
use num_rational::BigRational;
use num_traits::Signed;

fn power(exponent: i64) -> BigRational {
    if exponent >= 0 {
        BigRational::from_integer(BigInt::one() << exponent as usize)
    } else {
        BigRational::new(BigInt::one(), BigInt::one() << (-exponent) as usize)
    }
}

fn magnitude(eb: u32, p: u32, value: Raw) -> BigRational {
    let bias = (1i64 << (eb - 1)) - 1;
    let (exponent, significand) = if value.exponent == 0 {
        (1 - bias, value.fraction)
    } else {
        (
            value.exponent as i64 - bias,
            (1u128 << (p - 1)) + value.fraction,
        )
    };
    BigRational::from_integer(BigInt::from(significand)) * power(exponent - i64::from(p - 1))
}

pub(super) fn multiply(format: (u32, u32), x: Raw, y: Raw, mode: u64) -> Raw {
    let (eb, p) = format;
    assert!(eb < 20 && p < 128 && mode < 5, "bounded test oracle only");
    let max_exp = (1u64 << eb) - 1;
    let xn = x.exponent == max_exp && x.fraction != 0;
    let yn = y.exponent == max_exp && y.fraction != 0;
    let xi = x.exponent == max_exp && x.fraction == 0;
    let yi = y.exponent == max_exp && y.fraction == 0;
    let xz = x.exponent == 0 && x.fraction == 0;
    let yz = y.exponent == 0 && y.fraction == 0;
    let sign = x.sign ^ y.sign;
    if xn || yn || (xi && yz) || (yi && xz) {
        return raw(0, max_exp, 1);
    }
    if xi || yi {
        return raw(sign, max_exp, 0);
    }
    if xz || yz {
        return raw(sign, 0, 0);
    }
    let exact = magnitude(eb, p, x) * magnitude(eb, p, y);
    round_positive(format, exact, sign, mode)
}

pub(super) fn add_sub(format: (u32, u32), x: Raw, y: Raw, mode: u64, operation: Arithmetic) -> Raw {
    let (eb, p) = format;
    assert!(eb < 20 && p < 128 && mode < 5, "bounded test oracle only");
    assert!(matches!(operation, Arithmetic::Add | Arithmetic::Sub));
    let max_exp = (1u64 << eb) - 1;
    let ys = y.sign ^ u64::from(operation == Arithmetic::Sub);
    let xn = x.exponent == max_exp && x.fraction != 0;
    let yn = y.exponent == max_exp && y.fraction != 0;
    let xi = x.exponent == max_exp && x.fraction == 0;
    let yi = y.exponent == max_exp && y.fraction == 0;
    if xn || yn || (xi && yi && x.sign != ys) {
        return raw(0, max_exp, 1);
    }
    if xi {
        return raw(x.sign, max_exp, 0);
    }
    if yi {
        return raw(ys, max_exp, 0);
    }
    let left = magnitude(eb, p, x);
    let right = magnitude(eb, p, y);
    let left = if x.sign == 1 { -left } else { left };
    let right = if ys == 1 { -right } else { right };
    let exact = left + right;
    if exact.is_zero() {
        let both_zero = x.exponent == 0 && x.fraction == 0 && y.exponent == 0 && y.fraction == 0;
        let sign = if both_zero && x.sign == ys {
            x.sign
        } else {
            u64::from(mode == 3)
        };
        return raw(sign, 0, 0);
    }
    let sign = u64::from(exact.is_negative());
    round_positive(format, exact.abs(), sign, mode)
}

fn round_positive(format: (u32, u32), exact: BigRational, sign: u64, mode: u64) -> Raw {
    let (eb, p) = format;
    let max_exp = (1u64 << eb) - 1;
    let mut floor_log = exact.numer().bits() as i64 - exact.denom().bits() as i64;
    if exact < power(floor_log) {
        floor_log -= 1;
    }
    assert!(exact >= power(floor_log) && exact < power(floor_log + 1));
    let bias = (1i64 << (eb - 1)) - 1;
    let mut exponent = floor_log.max(1 - bias);
    let quantum = exponent - i64::from(p - 1);
    let scaled = exact / power(quantum);
    let lower = scaled.numer() / scaled.denom();
    let remainder = scaled.numer() % scaled.denom();
    let twice = &remainder * 2u8;
    let above_half = twice > *scaled.denom();
    let midpoint = twice == *scaled.denom();
    let odd = (&lower & BigInt::one()) != BigInt::zero();
    let increment = match mode {
        0 => above_half || (midpoint && odd),
        1 => above_half || midpoint,
        2 => sign == 0 && !remainder.is_zero(),
        3 => sign == 1 && !remainder.is_zero(),
        4 => false,
        _ => panic!("test mode"),
    };
    let mut integer = lower + u8::from(increment);
    if integer.is_zero() {
        return raw(sign, 0, 0);
    }
    if integer == (BigInt::one() << p) {
        integer >>= 1;
        exponent += 1;
    }
    if exponent > bias {
        let infinity = mode <= 1 || (mode == 2 && sign == 0) || (mode == 3 && sign == 1);
        return if infinity {
            raw(sign, max_exp, 0)
        } else {
            raw(sign, max_exp - 1, (1u128 << (p - 1)) - 1)
        };
    }
    let hidden = BigInt::one() << (p - 1);
    if integer < hidden {
        raw(sign, 0, integer.to_u128().expect("test subnormal"))
    } else {
        raw(
            sign,
            (exponent + bias) as u64,
            (integer - hidden).to_u128().expect("test normal fraction"),
        )
    }
}
