// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_fp::FpPrecision;
use num_bigint::BigInt;

fn assigned(
    eb: u32,
    sb: u32,
    bits: u128,
    offset: usize,
    inverted: bool,
) -> (TermStore, TermId, FpDecomposed, Vec<bool>) {
    assigned_exact(eb, sb, bits.into(), offset, inverted)
}

fn assigned_exact(
    eb: u32,
    sb: u32,
    bits: BigInt,
    offset: usize,
    inverted: bool,
) -> (TermStore, TermId, FpDecomposed, Vec<bool>) {
    let mut terms = TermStore::new();
    let term = terms.mk_var("decoded", Sort::FloatingPoint(eb, sb));
    let (mut value, total) = {
        let mut solver = FpSolver::new(&terms);
        let value = solver.get_fp(term);
        (value, solver.num_vars() as usize)
    };
    if inverted {
        value.sign = -value.sign;
        for lit in value.exponent.iter_mut().chain(&mut value.significand) {
            *lit = -*lit;
        }
    }
    // The prefix differs deliberately, so accidentally ignoring offset fails.
    // This is a free-variable decoder fixture, not an asserted SAT certificate.
    let mut model = vec![true; offset + total];
    let mut set = |lit: i32, bit: bool| {
        model[offset + lit.unsigned_abs() as usize - 1] = if lit > 0 { bit } else { !bit };
    };
    set(value.sign, bits.bit(u64::from(eb + sb - 1)));
    for (i, &lit) in value.exponent.iter().enumerate() {
        set(lit, bits.bit(u64::from(sb - 1) + i as u64));
    }
    for (i, &lit) in value.significand.iter().enumerate() {
        set(lit, bits.bit(i as u64));
    }
    (terms, term, value, model)
}

#[test]
fn exact_199_fraction_bits_survive_signed_cnf_and_original_caller_cancellation() {
    let fraction = (BigInt::from(1) << 198usize) | BigInt::from(1);
    let magnitude = (BigInt::from(127) << 199usize) | &fraction;
    for sign in [false, true] {
        for inverted in [false, true] {
            let bits = &magnitude | (BigInt::from(u8::from(sign)) << 207usize);
            let (terms, term, value, model) = assigned_exact(8, 200, bits.clone(), 9, inverted);
            let decoded = decode(&terms, term, &value, &model, 9).unwrap();
            assert_eq!(decoded.to_ieee_bv(), (bits, 208));
            assert!(matches!(&decoded, FpModelValue::Exact(fields)
                if fields.sign() == sign && BigInt::from(fields.significand().clone()) == fraction));
            assert!(decode(&terms, term, &value, &model[..model.len() - 1], 9).is_none());
            let mut polls = 0;
            assert!(Executor::extract_fp_value_from_bits_controlled(
                &model,
                term,
                &value,
                9,
                &terms,
                &mut || {
                    polls += 1;
                    polls < 4
                },
            )
            .is_none());
            assert_eq!(polls, 4);
        }
    }
}

fn decode(
    terms: &TermStore,
    term: TermId,
    value: &FpDecomposed,
    model: &[bool],
    offset: i32,
) -> Option<FpModelValue> {
    Executor::extract_fp_value_from_bits(model, term, value, offset, terms)
}

#[test]
fn binary128_decoder_preserves_high_low_bits_signed_literals_and_offset() {
    let magnitude = 0x3fff8000000000000000000000000001u128;
    for sign in [false, true] {
        for inverted in [false, true] {
            for offset in [0, 9] {
                let bits = magnitude | (u128::from(sign) << 127);
                let (terms, term, value, model) = assigned(15, 113, bits, offset, inverted);
                let decoded = decode(&terms, term, &value, &model, offset as i32).unwrap();
                assert!(matches!(decoded, FpModelValue::Fp {
                    sign: actual_sign, exponent: 16383, significand, eb: 15, sb: 113
                } if actual_sign == sign && significand == (1u128 << 111) | 1));
                assert_eq!(decoded.to_ieee_bv(), (BigInt::from(bits), 128));
            }
        }
    }
}

#[test]
fn binary128_specials_subnormal_and_maximum_decode_without_truncation() {
    let cases = [
        0u128,
        1u128 << 127,
        1,
        (1u128 << 112) - 1,
        1u128 << 112,
        (32766u128 << 112) | ((1u128 << 112) - 1),
        32767u128 << 112,
        (1u128 << 127) | (32767u128 << 112),
    ];
    for bits in cases {
        let (terms, term, value, model) = assigned(15, 113, bits, 3, false);
        assert_eq!(
            decode(&terms, term, &value, &model, 3)
                .unwrap()
                .to_ieee_bv(),
            (bits.into(), 128)
        );
    }
    for fraction in [1, 1u128 << 111] {
        let bits = (32767u128 << 112) | fraction;
        let (terms, term, value, model) = assigned(15, 113, bits, 0, false);
        assert!(decode(&terms, term, &value, &model, 0).unwrap().is_nan());
    }
}

#[test]
fn checked_cnf_namespace_and_assignment_refusals_need_no_large_allocation() {
    assert_eq!(read_cnf_bit_checked(&[false, true], 1, 1), Some(true));
    assert_eq!(read_cnf_bit_checked(&[false, true], -1, 1), Some(false));
    assert_eq!(read_cnf_bit_checked(&[false], -1, 0), Some(true));
    for (lit, offset) in [
        (0, 0),
        (1, -1),
        (-1, -1),
        (i32::MIN, 0),
        (i32::MAX, 1),
        (-i32::MAX, 1),
        (1, i32::MAX),
        (-1, i32::MAX),
        (i32::MIN, i32::MAX),
    ] {
        assert_eq!(read_cnf_bit_checked(&[false, true], lit, offset), None);
    }
    assert_eq!(read_cnf_bit_checked(&[], i32::MAX, 0), None);
    assert_eq!(read_cnf_bit_checked(&[], -i32::MAX, 0), None);
    assert_eq!(read_cnf_bit_checked(&[false], 2, 0), None);
    assert_eq!(read_cnf_bit_checked(&[false], -2, 0), None);
}

#[test]
fn exact_sort_precision_lengths_and_live_term_are_required() {
    let (mut terms, term, valid, model) = assigned(15, 113, 1, 0, false);
    let mut shortened = valid.clone();
    shortened.exponent.pop();
    let mut extended = valid.clone();
    extended.significand.push(1);
    let mut precision = valid.clone();
    precision.precision = FpPrecision::Float64;
    for bad in [shortened, extended, precision] {
        assert!(decode(&terms, term, &bad, &model, 0).is_none());
    }
    let boolean = terms.mk_var("not_fp", Sort::Bool);
    assert!(decode(&terms, boolean, &valid, &model, 0).is_none());
    assert!(decode(&terms, TermId(u32::MAX), &valid, &model, 0).is_none());
    for bad_literal in [0, i32::MIN, i32::MAX] {
        let mut bad = valid.clone();
        bad.sign = bad_literal;
        assert!(decode(&terms, term, &bad, &model, 0).is_none());
    }
    assert!(decode(&terms, term, &valid, &model[..model.len() - 1], 0).is_none());
    assert!(decode(&terms, term, &valid, &model, -1).is_none());
    assert!(decode(&terms, term, &valid, &model, i32::MAX).is_none());
    assert_eq!(
        decode(&terms, term, &valid, &model, 0)
            .unwrap()
            .to_ieee_bv(),
        (1.into(), 128)
    );
}

#[test]
fn batch_refusal_is_atomic_and_does_not_publish_a_partial_model() {
    let (mut terms, term, valid, model) = assigned(15, 113, 1, 0, false);
    let other = terms.mk_var("other", Sort::FloatingPoint(15, 113));
    let mut entries = HashMap::default();
    entries.insert(term, valid.clone());
    let mut broken = valid.clone();
    broken.significand[111] = i32::MIN;
    entries.insert(other, broken);
    assert!(
        Executor::extract_fp_model_from_bits(&model, &entries, &HashMap::default(), 0, &terms)
            .is_none()
    );
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[&other].significand[111], i32::MIN);
    entries.insert(other, valid);
    let complete =
        Executor::extract_fp_model_from_bits(&model, &entries, &HashMap::default(), 0, &terms)
            .unwrap();
    assert_eq!(complete.values.len(), 2);
    for key in [term, other] {
        assert_eq!(complete.values[&key].to_ieee_bv(), (1.into(), 128));
    }
    assert!(Executor::extract_fp_model_from_bits(
        &model,
        &entries,
        &HashMap::default(),
        -1,
        &terms
    )
    .is_none());
}

#[test]
fn prior_narrow_and_full_u64_fraction_envelopes_remain_exact() {
    for (eb, sb, bits) in [
        (5, 11, 0x3e01u128),
        (8, 24, 0x3fc00001),
        (11, 53, 0x3ff8000000000001),
        (5, 65, (15u128 << 64) | (1u128 << 63) | 1),
        (
            63,
            65,
            (1u128 << 127) | (1u128 << 64) | u128::from(u64::MAX),
        ),
    ] {
        let (terms, term, value, model) = assigned(eb, sb, bits, 2, true);
        assert_eq!(
            decode(&terms, term, &value, &model, 2)
                .unwrap()
                .to_ieee_bv(),
            (bits.into(), eb + sb)
        );
    }
}

#[test]
fn model_decoder_rejects_invalid_native_formats() {
    for (eb, sb) in [(64, 11), (0, 11), (1, 11), (5, 1)] {
        let mut terms = TermStore::new();
        let term = terms.mk_var("unsupported", Sort::FloatingPoint(eb, sb));
        let value = FpDecomposed {
            sign: 1,
            exponent: vec![1; eb as usize],
            significand: vec![1; (sb - 1) as usize],
            precision: FpPrecision::Custom { eb, sb },
        };
        assert!(decode(&terms, term, &value, &[false], 0).is_none());
    }
}

#[test]
fn model_decoder_preserves_130_bit_format_and_129th_fraction_bit() {
    let bits = (BigInt::from(127) << 129usize) | (BigInt::from(1) << 128usize) | BigInt::from(1);
    let (terms, term, value, model) = assigned_exact(15, 130, bits.clone(), 2, true);
    let decoded = decode(&terms, term, &value, &model, 2).unwrap();
    assert_eq!(decoded.to_ieee_bv(), (bits, 145));
}
