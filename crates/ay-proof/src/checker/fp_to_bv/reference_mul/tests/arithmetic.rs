// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn independent_exact_rational_checks_all_smallest_format_products() {
    let f = Fixture::new(2, 2);
    // This is a regression oracle, NOT the symbolic certificate algorithm.
    for x in 0u32..16 {
        for y in 0u32..16 {
            f.compare(
                raw(
                    u64::from(x >> 3),
                    u64::from((x >> 1) & 3),
                    u128::from(x & 1),
                ),
                raw(
                    u64::from(y >> 3),
                    u64::from((y >> 1) & 3),
                    u128::from(y & 1),
                ),
            );
        }
    }
}

#[test]
fn actual_symbolic_modes_round_odd_even_midpoints_and_signs() {
    let f = Fixture::new(3, 4);
    for sign_x in 0..2 {
        for sign_y in 0..2 {
            // 1.125 * 1.5 = 1.6875: lower retained significand13 is odd.
            f.compare(raw(sign_x, 3, 1), raw(sign_y, 3, 4));
            // 1.25 * 1.25 = 1.5625: lower retained significand12 is even.
            f.compare(raw(sign_x, 3, 2), raw(sign_y, 3, 2));
            f.compare(raw(sign_x, 3, 1), raw(sign_y, 3, 1));
        }
    }
}

#[test]
fn direct_quantum_has_no_double_rounding_at_subnormal_boundaries() {
    let f = Fixture::new(3, 4);
    for sign in 0..2 {
        f.compare(raw(sign, 0, 1), raw(0, 2, 0)); // half of least subnormal
        f.compare(raw(sign, 0, 1), raw(0, 1, 0)); // strictly below half
        f.compare(raw(sign, 0, 1), raw(0, 2, 1)); // strictly above half
        f.compare(raw(sign, 1, 4), raw(0, 2, 2)); // largest-subnormal/min-normal tie
        f.compare(raw(sign, 0, 7), raw(0, 3, 1)); // promotion without preliminary rounding
    }
}

#[test]
fn full_product_carry_and_all_mode_overflow_are_not_truncated() {
    for (eb, p) in [(3, 4), (5, 11), (8, 24), (11, 53), (15, 113)] {
        let f = Fixture::new(eb, p);
        let bias = (1u64 << (eb - 1)) - 1;
        let max = (1u64 << eb) - 2;
        let fraction = (1u128 << (p - 1)) - 1;
        for sign in 0..2 {
            f.compare(raw(sign, bias, fraction), raw(0, bias, fraction));
            f.compare(raw(sign, max, fraction), raw(0, bias + 1, 0));
            f.compare(raw(sign, max, fraction), raw(0, bias, 1));
        }
    }
}

#[test]
fn specials_precede_finite_word_rounding_and_preserve_signed_zero() {
    let f = Fixture::new(8, 24);
    for sign_x in 0..2 {
        for sign_y in 0..2 {
            f.compare(raw(sign_x, 255, 0), raw(sign_y, 0, 0)); // Inf * zero = NaN
            f.compare(raw(sign_x, 255, 0), raw(sign_y, 127, 0));
            f.compare(raw(sign_x, 0, 0), raw(sign_y, 127, 1));
            f.compare(raw(sign_x, 255, 1), raw(sign_y, 255, 0));
            f.compare(raw(sign_x, 255, 0x400000), raw(sign_y, 0, 1));
        }
    }
}

#[test]
fn symbolic_rm_carrier_keeps_the_full_five_value_domain_obligation() {
    let f = Fixture::new(8, 24);
    let mut progress = |_, _| true;
    let mut reference = Reference::build(&f.terms, f.source, &mut progress).expect("reference");
    for mode in 0..8 {
        let inputs = f.assignments(raw(0, 127, 1), raw(0, 127, 1), mode);
        let (_, admitted) = reference.evaluate(&inputs).expect("word model");
        assert_eq!(
            admitted,
            mode < 5,
            "invalid encodings are NOT SMT rounding modes"
        );
    }
}

#[test]
fn literal_rounding_names_are_derived_from_the_actual_nullary_source() {
    for (mode, names) in [
        ["RNE", "roundNearestTiesToEven"],
        ["RNA", "roundNearestTiesToAway"],
        ["RTP", "roundTowardPositive"],
        ["RTN", "roundTowardNegative"],
        ["RTZ", "roundTowardZero"],
    ]
    .iter()
    .enumerate()
    {
        for name in names {
            let mut f = Fixture::new(3, 4);
            let TermData::App(_, args) = f.terms.get(f.source) else {
                panic!("mul fixture");
            };
            let args = args.clone();
            let rm = f.terms.mk_app(
                Symbol::named(*name),
                [],
                Sort::Uninterpreted("RoundingMode".into()),
            );
            let source = f.terms.mk_app(
                Symbol::named("fp.mul"),
                [rm, args[1], args[2]],
                Sort::FloatingPoint(3, 4),
            );
            let mut progress = |_, _| true;
            let mut reference =
                Reference::build(&f.terms, source, &mut progress).expect("actual literal");
            let inputs = f.assignments(raw(1, 3, 1), raw(0, 3, 4), 7);
            let (actual, domain) = reference.evaluate(&inputs).expect("literal word model");
            assert!(domain);
            assert_eq!(
                actual,
                oracle::multiply((3, 4), raw(1, 3, 1), raw(0, 3, 4), mode as u64)
            );
        }
    }
}

#[test]
fn format_metadata_has_no_invented_exponent_or_precision_ceiling() {
    let f = Fixture::new(8320, 113);
    let mut progress = |_, _| true;
    let reference =
        Reference::build(&f.terms, f.source, &mut progress).expect("word DAG has checked widths");
    assert!(reference.format.exponent_width >= 8324);
    assert_eq!(reference.format.product_width, 227);
    // No unverified BigInt mask, bit-blast, proof-search or answer is inferred
    // from constructing this small word-level metadata program.
}

#[test]
fn canonical_constant_fields_and_precision257_are_not_u128_limited() {
    let mut terms = TermStore::new();
    let rm = terms.mk_app(
        Symbol::named("RNE"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let sign = terms.mk_bitvec(BigInt::zero(), 1);
    let exponent = terms.mk_bitvec(BigInt::from(127u8), 8);
    let fraction = terms.mk_bitvec(BigInt::zero(), 256);
    let value = terms.mk_app(
        Symbol::named("fp"),
        [sign, exponent, fraction],
        Sort::FloatingPoint(8, 257),
    );
    let source = terms.mk_app(
        Symbol::named("fp.mul"),
        [rm, value, value],
        Sort::FloatingPoint(8, 257),
    );
    let mut progress = |_, _| true;
    let mut reference =
        Reference::build(&terms, source, &mut progress).expect("actual large canonical source");
    let (actual, domain) = reference.evaluate(&[]).expect("1 * 1 at precision257");
    assert!(domain);
    assert_eq!(actual, raw(0, 127, 0));
}
