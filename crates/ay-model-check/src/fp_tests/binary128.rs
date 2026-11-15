// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const FRACTION: u128 = (1u128 << 112) - 1;
const MODES: [RoundingMode; 5] = [
    RoundingMode::Rne,
    RoundingMode::Rna,
    RoundingMode::Rtp,
    RoundingMode::Rtn,
    RoundingMode::Rtz,
];

fn quad(sign: bool, exponent: u64, significand: u128) -> ModelValue {
    ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits: 15,
        significand_bits: 113,
    }
}

fn assert_fields(value: &ModelValue, expected: (bool, u64, u128)) {
    let ModelValue::FloatingPoint {
        sign,
        exponent,
        significand,
        exponent_bits,
        significand_bits,
    } = value
    else {
        panic!("expected floating-point fields: {value:?}");
    };
    assert_eq!((*exponent_bits, *significand_bits), (15, 113));
    assert_eq!((*sign, *exponent, *significand), expected);
}

fn power(exponent: i32) -> BigRational {
    if exponent >= 0 {
        BigRational::from_integer(BigInt::one() << exponent as usize)
    } else {
        BigRational::new(BigInt::one(), BigInt::one() << (-exponent) as usize)
    }
}

fn rounded(value: &BigRational, rm: RoundingMode) -> ModelValue {
    round_to_format(value, 15, 113, rm, false)
        .unwrap()
        .to_value()
}

#[test]
fn adjacent_binary128_fields_and_ieee_bits_remain_distinct() {
    let witness = 0x3fff_8000_0000_0000_0000_0000_0000_0001u128;
    for raw in [witness - 1, witness, witness + 1] {
        let fraction = raw & FRACTION;
        let value = quad(false, 0x3fff, fraction);
        let exact = BigRational::from_integer(BigInt::one())
            + BigRational::new(BigInt::from(fraction), BigInt::one() << 112usize);
        assert_eq!(Fp::from_value(&value).unwrap().exact_value(), Some(exact));
        assert_eq!(
            bv_parts(&to_ieee_bv(&value).unwrap()),
            (BigInt::from(raw), 128)
        );
        let literal = crate::fp::from_field_bitvectors(&[
            ModelValue::bitvec(BigInt::from(0), 1),
            ModelValue::bitvec(BigInt::from(0x3fff), 15),
            ModelValue::bitvec(BigInt::from(fraction), 112),
        ])
        .unwrap();
        assert_fields(&literal, (false, 0x3fff, fraction));
    }
    let low = quad(false, 0x3fff, (witness - 1) & FRACTION);
    let high = quad(false, 0x3fff, witness & FRACTION);
    assert!(!same_element(&low, &high));
    assert_eq!(compare("fp.lt", &[low, high]).unwrap(), Some(true));
    let mixed_bits = (1u128 << 111) | (1u128 << 64) | (1u128 << 63) | 1;
    assert_eq!(
        bv_parts(&to_ieee_bv(&quad(true, 1, mixed_bits)).unwrap()),
        (
            BigInt::from((1u128 << 127) | (1u128 << 112) | mixed_bits),
            128
        )
    );
}

#[test]
fn binary128_field_boundaries_refuse_without_truncation() {
    assert!(Fp::from_value(&quad(false, 0x7fff, FRACTION)).is_ok());
    for malformed in [
        quad(false, 0x8000, 0),
        quad(false, 0, 1u128 << 112),
        quad(false, 0, u128::MAX),
    ] {
        assert!(Fp::from_value(&malformed).is_err());
    }
    let raw = |value: BigInt, width| ModelValue::BitVec { value, width };
    let valid = [
        raw(BigInt::from(0), 1),
        raw(BigInt::from(1), 15),
        raw(BigInt::from(FRACTION), 112),
    ];
    assert!(crate::fp::from_field_bitvectors(&valid).is_ok());
    for (index, bad) in [
        (0, raw(BigInt::from(2), 1)),
        (0, raw(BigInt::from(0), 2)),
        (1, raw(BigInt::from(1u128 << 64), 15)),
        (1, raw(BigInt::from(0x8000), 15)),
        (2, raw(BigInt::from(-1), 112)),
        (2, raw(BigInt::from(1u128 << 112), 112)),
        (2, raw(BigInt::from(0), u32::MAX)),
    ] {
        let mut fields = valid.clone();
        fields[index] = bad;
        assert!(crate::fp::from_field_bitvectors(&fields).is_err());
    }
    let mut wider_data = valid;
    wider_data[2] = raw(BigInt::from(0), 129);
    let value = crate::fp::from_field_bitvectors(&wider_data).expect("checked wider raw fields");
    assert!(matches!(value, ModelValue::FloatingPointExact { .. }));
    assert!(
        Fp::from_value(&value).is_err(),
        "raw admission must not grant wider arithmetic"
    );
}

#[test]
fn binary128_classes_nan_and_signed_zero_keep_smt_semantics() {
    use crate::fp::FpClass;
    for (exponent, fraction, class) in [
        (0, 0, FpClass::Zero),
        (0, 1, FpClass::Subnormal),
        (0, FRACTION, FpClass::Subnormal),
        (1, 0, FpClass::Normal),
        (0x7ffe, FRACTION, FpClass::Normal),
        (0x7fff, 0, FpClass::Infinite),
        (0x7fff, 1, FpClass::NaN),
        (0x7fff, 1u128 << 111, FpClass::NaN),
    ] {
        for sign in [false, true] {
            assert_eq!(
                Fp::from_value(&quad(sign, exponent, fraction))
                    .unwrap()
                    .class(),
                class
            );
        }
    }
    assert_eq!(
        Fp::from_value(&quad(false, 0, 1)).unwrap().exact_value(),
        Some(power(-16494))
    );
    assert_eq!(
        Fp::from_value(&quad(true, 1, 0)).unwrap().exact_value(),
        Some(-power(-16382))
    );
    let pz = quad(false, 0, 0);
    let nz = quad(true, 0, 0);
    assert!(!same_element(&pz, &nz));
    assert_eq!(
        compare("fp.eq", &[pz.clone(), nz.clone()]).unwrap(),
        Some(true)
    );
    assert_eq!(
        bv_parts(&to_ieee_bv(&nz).unwrap()),
        (BigInt::from(1u128 << 127), 128)
    );
    let operands = [pz, nz.clone()];
    crate::fp::check_min_max_choice(&operands, &nz).unwrap();
    assert!(crate::fp::check_min_max_choice(&operands, &quad(false, 0x3fff, 0)).is_err());
    let a = quad(false, 0x7fff, 1);
    let b = quad(true, 0x7fff, 1u128 << 111);
    assert!(same_element(&a, &b));
    assert_eq!(compare("fp.eq", &[a.clone(), b]).unwrap(), Some(false));
    assert_eq!(to_ieee_bv(&a).unwrap_err(), UNDERSPECIFIED);
    check_ieee_nan_encoding(
        &a,
        &ModelValue::bitvec(
            BigInt::from(0xffff_8000_0000_0000_0000_0000_0000_0001u128),
            128,
        ),
    )
    .unwrap();
    for bad in [
        ModelValue::bitvec(BigInt::from(0x7fffu128 << 112), 128),
        ModelValue::bitvec(BigInt::from(0), 128),
        ModelValue::Bool(true),
    ] {
        assert!(check_ieee_nan_encoding(&a, &bad).is_err());
    }
}

#[test]
fn binary128_rounding_modes_preserve_adjacent_midpoints() {
    let one = power(0);
    for negative in [false, true] {
        for (base, offset) in [(0u128, 1i32), (1, 3)] {
            let midpoint = &one + power(-113) * BigInt::from(offset);
            for rm in MODES {
                let up = match rm {
                    RoundingMode::Rne => base % 2 == 1,
                    RoundingMode::Rna => true,
                    RoundingMode::Rtp => !negative,
                    RoundingMode::Rtn => negative,
                    RoundingMode::Rtz => false,
                };
                let input = if negative {
                    -midpoint.clone()
                } else {
                    midpoint.clone()
                };
                assert_fields(
                    &rounded(&input, rm),
                    (negative, 0x3fff, base + u128::from(up)),
                );
            }
            for (epsilon, expected) in [(-power(-115), base), (power(-115), base + 1)] {
                let input = &midpoint + epsilon;
                let input = if negative { -input } else { input };
                assert_fields(
                    &rounded(&input, RoundingMode::Rne),
                    (negative, 0x3fff, expected),
                );
            }
        }
    }
    assert_fields(
        &rounded(&(power(1) - power(-113)), RoundingMode::Rne),
        (false, 0x4000, 0),
    );
}

#[test]
fn binary128_subnormal_normal_and_overflow_boundaries() {
    let min_half = power(-16495);
    let normal_mid = power(-16382) - &min_half;
    let max_finite = BigRational::from_integer((BigInt::one() << 113usize) - 1) * power(16271);
    let overflow_mid = &max_finite + power(16270);
    for negative in [false, true] {
        for rm in MODES {
            let directed_away =
                (rm == RoundingMode::Rtp && !negative) || (rm == RoundingMode::Rtn && negative);
            let nearest = matches!(rm, RoundingMode::Rne | RoundingMode::Rna);
            let signed = |x: &BigRational| if negative { -x.clone() } else { x.clone() };
            assert_fields(
                &rounded(&signed(&min_half), rm),
                (
                    negative,
                    0,
                    u128::from(directed_away || rm == RoundingMode::Rna),
                ),
            );
            assert_fields(
                &rounded(&signed(&normal_mid), rm),
                if nearest || directed_away {
                    (negative, 1, 0)
                } else {
                    (negative, 0, FRACTION)
                },
            );
            assert_fields(
                &rounded(&signed(&overflow_mid), rm),
                if nearest || directed_away {
                    (negative, 0x7fff, 0)
                } else {
                    (negative, 0x7ffe, FRACTION)
                },
            );
            assert_fields(
                &rounded(&signed(&max_finite), rm),
                (negative, 0x7ffe, FRACTION),
            );
        }
    }
    assert_fields(
        &rounded(&(&overflow_mid - power(16269)), RoundingMode::Rne),
        (false, 0x7ffe, FRACTION),
    );
    assert_fields(
        &rounded(&(&overflow_mid + power(16269)), RoundingMode::Rne),
        (false, 0x7fff, 0),
    );
}

#[test]
fn binary128_arithmetic_fma_and_conversion_use_exact_intermediates() {
    let one = quad(false, 0x3fff, 0);
    let next = quad(false, 0x3fff, 1);
    assert_fields(
        &arith("fp.sub", RoundingMode::Rne, &[next.clone(), one.clone()])
            .unwrap()
            .unwrap(),
        (false, 0x3fff - 112, 0),
    );
    assert_fields(
        &arith(
            "fp.add",
            RoundingMode::Rne,
            &[one.clone(), quad(false, 0x3fff - 112, 0)],
        )
        .unwrap()
        .unwrap(),
        (false, 0x3fff, 1),
    );
    let third = FRACTION / 3;
    for (rm, expected) in [(RoundingMode::Rne, third), (RoundingMode::Rtp, third + 1)] {
        assert_fields(
            &arith(
                "fp.div",
                rm,
                &[one.clone(), quad(false, 0x4000, 1u128 << 111)],
            )
            .unwrap()
            .unwrap(),
            (false, 0x3ffd, expected),
        );
    }
    let below = quad(false, 0x3ffe, FRACTION - 1);
    let neg_one = quad(true, 0x3fff, 0);
    assert_fields(
        &fma(
            RoundingMode::Rne,
            &[next.clone(), below.clone(), neg_one.clone()],
        )
        .unwrap(),
        (true, 0x3fff - 224, 0),
    );
    let product = arith("fp.mul", RoundingMode::Rne, &[next, below])
        .unwrap()
        .unwrap();
    assert_fields(&product, (false, 0x3fff, 0));
    assert_fields(
        &arith("fp.add", RoundingMode::Rne, &[product, neg_one])
            .unwrap()
            .unwrap(),
        (false, 0, 0),
    );
    assert_fields(
        &rem(&[
            quad(false, 0x4001, 1u128 << 110),
            quad(false, 0x4000, 1u128 << 111),
        ])
        .unwrap(),
        (true, 0x3fff, 0),
    );
    for rm in MODES {
        assert_fields(
            &sqrt(rm, &quad(false, 0x4001, 0)).unwrap(),
            (false, 0x4000, 0),
        );
    }
    let precise = quad(false, 0x3fff, (1u128 << 111) + 1);
    let narrow = to_fp_rounded(false, 11, 53, RoundingMode::Rne, &precise).unwrap();
    assert!(same_element(&narrow, &f64_bits(0x3ff8_0000_0000_0000)));
    assert_fields(
        &to_fp_rounded(false, 15, 113, RoundingMode::Rne, &narrow).unwrap(),
        (false, 0x3fff, 1u128 << 111),
    );
    let integer = ModelValue::bitvec((BigInt::one() << 113usize) + 1, 128);
    for (rm, fraction) in [(RoundingMode::Rne, 0), (RoundingMode::Rtp, 1)] {
        assert_fields(
            &to_fp_rounded(true, 15, 113, rm, &integer).unwrap(),
            (false, 0x3fff + 113, fraction),
        );
    }
}

#[test]
fn binary128_support_preserves_other_format_and_resource_refusals() {
    fn require_copy<T: Copy>() {}
    require_copy::<Fp>();
    for (eb, sb) in [(15, 130), (1, 24), (0, 113), (64, 113), (15, u32::MAX)] {
        assert!(round_to_format(&power(0), eb, sb, RoundingMode::Rne, false).is_err());
        let value = ModelValue::FloatingPoint {
            sign: false,
            exponent: 0,
            significand: 0,
            exponent_bits: eb,
            significand_bits: sb,
        };
        assert!(Fp::from_value(&value).is_err());
    }
    for (eb, sb) in [(2, 2), (5, 11), (11, 53), (15, 64), (63, 64), (15, 113)] {
        assert!(round_to_format(&power(0), eb, sb, RoundingMode::Rne, false).is_ok());
    }
    let huge = ModelValue::FloatingPoint {
        sign: false,
        exponent: (1u64 << 32) - 2,
        significand: 0,
        exponent_bits: 32,
        significand_bits: 24,
    };
    assert!(Fp::from_value(&huge).unwrap().exact_value().is_none());
}

#[test]
fn custom_full_fraction_rounding_preserves_low_bits_ties_and_overflow() {
    for (eb, sb) in [(2, 66), (15, 112), (16, 113), (2, 128), (3, 129), (63, 129)] {
        let bias = (1u64 << (eb - 1)) - 1;
        let expected = power(0) + power(-((sb - 1) as i32));
        for rm in MODES {
            let result = round_to_format(&expected, eb, sb, rm, false).unwrap();
            let ModelValue::FloatingPoint {
                exponent,
                significand,
                ..
            } = result.to_value()
            else {
                panic!("not FP")
            };
            assert_eq!((exponent, significand), (bias, 1));
        }
    }
    let tie = power(0) + power(-129);
    for rm in MODES {
        let result = round_to_format(&tie, 3, 129, rm, false).unwrap();
        let ModelValue::FloatingPoint {
            exponent,
            significand,
            ..
        } = result.to_value()
        else {
            panic!("not FP")
        };
        assert_eq!(exponent, 3);
        assert_eq!(
            significand,
            u128::from(matches!(rm, RoundingMode::Rna | RoundingMode::Rtp))
        );
    }
    let result = round_to_format(&power(2), 2, 129, RoundingMode::Rtz, false).unwrap();
    let ModelValue::FloatingPoint {
        exponent,
        significand,
        ..
    } = result.to_value()
    else {
        panic!("not FP")
    };
    assert_eq!((exponent, significand), (2, u128::MAX));
}
