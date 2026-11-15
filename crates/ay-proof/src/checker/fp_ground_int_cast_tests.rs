// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Defined conversions replay exactly; under-specified cases never invent bits.
use super::*;
use int_cast::{fp_to_bv, IntTarget};

fn fraction(n: i64, d: i64) -> Fp {
    round_rational(&BigRational::new(n.into(), d.into()), false, 8, 24, Rm::Rne)
        .expect("exact sample")
}

#[test]
fn all_rounding_modes_and_ties_use_the_signed_value() {
    for (n, d, expected) in [
        (7, 4, [2, 2, 2, 1, 1]),
        (-7, 4, [-2, -2, -1, -2, -1]),
        (5, 2, [2, 3, 3, 2, 2]),
        (-5, 2, [-2, -3, -2, -3, -2]),
    ] {
        for (mode, expected) in [Rm::Rne, Rm::Rna, Rm::Rtp, Rm::Rtn, Rm::Rtz]
            .into_iter()
            .zip(expected)
        {
            let expected = BigInt::from((expected + 256) % 256);
            assert_eq!(
                fp_to_bv(&fraction(n, d), mode, 8, IntTarget::Signed),
                Some(expected)
            );
        }
    }
}

#[test]
fn range_is_checked_after_rounding_and_nonfinite_values_refuse() {
    let min_fraction = fraction(-257, 2); // -128.5: ties-even gives -128.
    assert_eq!(
        fp_to_bv(&min_fraction, Rm::Rne, 8, IntTarget::Signed),
        Some(128.into())
    );
    for mode in [Rm::Rna, Rm::Rtn] {
        assert_eq!(fp_to_bv(&min_fraction, mode, 8, IntTarget::Signed), None);
    }
    let max_fraction = fraction(255, 2);
    assert_eq!(
        fp_to_bv(&max_fraction, Rm::Rtz, 8, IntTarget::Signed),
        Some(127.into())
    );
    for mode in [Rm::Rne, Rm::Rna, Rm::Rtp] {
        assert_eq!(fp_to_bv(&max_fraction, mode, 8, IntTarget::Signed), None);
    }
    assert_eq!(
        fp_to_bv(&fraction(-3, 4), Rm::Rtz, 8, IntTarget::Unsigned),
        Some(0.into())
    );
    assert_eq!(
        fp_to_bv(&fraction(-3, 4), Rm::Rtn, 8, IntTarget::Unsigned),
        None
    );
    for target in [IntTarget::Signed, IntTarget::Unsigned] {
        for value in [
            Fp::nan(8, 24).unwrap(),
            Fp::infinity(false, 8, 24).unwrap(),
            Fp::infinity(true, 8, 24).unwrap(),
        ] {
            for mode in [Rm::Rne, Rm::Rna, Rm::Rtp, Rm::Rtn, Rm::Rtz] {
                assert_eq!(fp_to_bv(&value, mode, 128, target), None);
            }
        }
        for width in [0, MAX_BV_WIDTH + 1, u32::MAX] {
            assert_eq!(fp_to_bv(&fraction(1, 1), Rm::Rtz, width, target), None);
        }
    }
}

#[test]
fn wide_integer_limits_keep_all_bits() {
    let positive = Fp::from_bits(&BigInt::from(0x47df_ffff_ffff_ffffu64), 11, 53).unwrap();
    let magnitude = (BigInt::one() << 127usize) - (BigInt::one() << 74usize);
    assert_eq!(
        fp_to_bv(&positive, Rm::Rtz, 128, IntTarget::Signed),
        Some(magnitude.clone())
    );
    let negative = positive.negated();
    assert_eq!(
        fp_to_bv(&negative, Rm::Rtz, 128, IntTarget::Signed),
        Some((BigInt::one() << 128usize) - magnitude)
    );
}

fn cast(terms: &mut TermStore, op: Symbol, bits: u64, result_width: u32) -> TermId {
    let raw = terms.mk_bitvec(BigInt::from(bits), 32);
    let value = terms.mk_app(
        Symbol::indexed("to_fp", vec![8, 24]),
        [raw],
        Sort::FloatingPoint(8, 24),
    );
    let rm = terms.mk_app(
        Symbol::named("RTZ"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    terms.mk_app(op, [rm, value], Sort::bitvec(result_width))
}

#[test]
fn clause_replay_accepts_only_true_defined_well_sorted_casts() {
    let mut terms = TermStore::new();
    for name in ["fp.to_sbv", "fp.to_ubv"] {
        let result = cast(&mut terms, Symbol::indexed(name, vec![8]), 0x3fe0_0000, 8); // 1.75
        let one = terms.mk_bitvec(1.into(), 8);
        let two = terms.mk_bitvec(2.into(), 8);
        let valid = terms.mk_app(Symbol::named("="), [result, one], Sort::Bool);
        let false_claim = terms.mk_app(Symbol::named("="), [result, two], Sort::Bool);
        assert!(recognize_fp_ground_eval(&terms, &[valid]));
        assert!(validate_fp_ground_eval(&terms, ProofId(0), &[valid]).is_ok());
        assert!(!recognize_fp_ground_eval(&terms, &[false_claim]));
        assert!(validate_fp_ground_eval(&terms, ProofId(0), &[false_claim]).is_err());
        for (symbol, bits, sort_width) in [
            (Symbol::named(name), 0x3fe0_0000, 8),
            (Symbol::indexed(name, vec![8]), 0x3fe0_0000, 16),
            (Symbol::indexed(name, vec![8]), 0x7fc0_0000, 8),
            (Symbol::indexed(name, vec![8]), 0x7f80_0000, 8),
            (Symbol::indexed(name, vec![8]), 0x4780_0000, 8),
        ] {
            let result = cast(&mut terms, symbol, bits, sort_width);
            let zero = terms.mk_bitvec(0.into(), sort_width);
            let invalid = terms.mk_app(Symbol::named("="), [result, zero], Sort::Bool);
            assert!(!recognize_fp_ground_eval(&terms, &[invalid]));
            assert!(validate_fp_ground_eval(&terms, ProofId(0), &[invalid]).is_err());
        }
    }
}

#[test]
fn every_binary16_pattern_matches_native_truncation_or_refuses() {
    for raw in 0..=u16::MAX {
        let value = Fp::from_bits(&BigInt::from(raw), 5, 11).unwrap();
        // Independent IEEE binary16 decode into an exact binary64 value.
        let exponent = (raw >> 10) & 31;
        let fraction = raw & 1023;
        let magnitude = if exponent == 0 {
            f64::from(fraction) * 2.0f64.powi(-24)
        } else {
            f64::from(fraction + 1024) * 2.0f64.powi(i32::from(exponent) - 25)
        };
        let rounded = if raw & 0x8000 == 0 {
            magnitude
        } else {
            -magnitude
        }
        .trunc();
        for width in [8u32, 16] {
            for target in [IntTarget::Signed, IntTarget::Unsigned] {
                let signed = matches!(target, IntTarget::Signed);
                let upper = 2.0f64.powi((width - u32::from(signed)) as i32);
                let lower = if signed { -upper } else { 0.0 };
                let expected = if exponent == 31 || rounded < lower || rounded >= upper {
                    None
                } else {
                    let integer = BigInt::from(rounded as i64);
                    Some(if integer.is_negative() {
                        integer + (BigInt::one() << width as usize)
                    } else {
                        integer
                    })
                };
                assert_eq!(
                    fp_to_bv(&value, Rm::Rtz, width, target),
                    expected,
                    "{raw:#06x} -> {width}, signed={signed}"
                );
            }
        }
    }
}
