// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed data decoding only: these tests do not assert native SAT authority.

use super::*;
use ay_core::Sort;

fn decode(text: &str, eb: u32, sb: u32) -> Result<ModelValue, TypedModelValueDecodeError> {
    let mut values = ModelValue::decode_typed_literals(&[(text, &Sort::FloatingPoint(eb, sb))])?;
    assert_eq!(values.len(), 1);
    Ok(values.remove(0))
}

#[test]
fn exact_199_bit_public_fields_roundtrip_without_native_truncation() {
    let literal = format!("(fp #b1 #b01111111 #b1{}1)", "0".repeat(197));
    let value = decode(&literal, 8, 200).unwrap();
    let fields = value.as_fp_exact().unwrap();
    assert!(fields.sign());
    assert_eq!(fields.exponent(), &num_bigint::BigUint::from(127u32));
    assert_eq!(
        fields.significand(),
        &((num_bigint::BigUint::from(1u32) << 198usize) | num_bigint::BigUint::from(1u32))
    );
    assert!(value.as_fp_wide().is_none());
    assert!(value.as_fp().is_none());
    assert_eq!(value.to_string(), literal);
    assert_eq!(decode(&value.to_string(), 8, 200).unwrap(), value);
    let indexed = format!(
        "(fp (_ bv1 1) (_ bv127 8) (_ bv{} 199))",
        fields.significand()
    );
    assert_eq!(decode(&indexed, 8, 200).unwrap(), value);
    let wrong_sign = literal.replacen("#b1", "#b0", 1);
    assert_ne!(decode(&wrong_sign, 8, 200).unwrap(), value);
    let short = format!("(fp #b1 #b01111111 #b1{}1)", "0".repeat(196));
    assert!(decode(&short, 8, 200).is_err());
}

#[test]
fn binary128_fields_survive_typed_decode_display_and_checked_extraction() {
    let fraction = (1u128 << 111) | (1u128 << 64) | (1u128 << 63) | 1;
    let literal = format!("(fp #b0 #b011111111111111 #x{fraction:028x})");
    let value = decode(&literal, 15, 113).unwrap();
    assert_eq!(value.variant_name(), "FloatingPointWide");
    assert_eq!(
        value.try_fp_wide().unwrap(),
        (false, 16383, fraction, 15, 113)
    );
    assert!(value.as_fp().is_none());
    assert!(value.try_fp().is_err());
    let printed = value.to_string();
    let expected = format!("(fp #b0 #b011111111111111 #b{fraction:0112b})");
    assert_eq!(printed, expected);
    assert_eq!(decode(&printed, 15, 113).unwrap(), value);
}

#[test]
fn declared_width_selects_wide_even_when_checked_narrowing_is_exact() {
    let value = decode(
        "(fp #b1 #b011111111111111 #x0000000000000000000000000001)",
        15,
        113,
    )
    .unwrap();
    assert!(matches!(value, ModelValue::FloatingPointWide { .. }));
    assert_eq!(value.as_fp(), Some((true, 16383, 1, 15, 113)));
    let narrow = ModelValue::FloatingPoint {
        sign: true,
        exponent: 16383,
        significand: 1,
        eb: 15,
        sb: 113,
    };
    assert_eq!(narrow.as_fp_wide(), value.as_fp_wide());
    assert_ne!(narrow, value); // Structural enum equality is not FP semantic equality.
}

#[test]
fn existing_narrow_fields_keep_their_variant_values_and_accessors() {
    let value = decode("(fp #b0 #x7f #b10000000000000000000001)", 8, 24).unwrap();
    assert!(matches!(value, ModelValue::FloatingPoint { .. }));
    assert_eq!(
        value.try_fp().unwrap(),
        (false, 127, (1u64 << 22) | 1, 8, 24)
    );
    assert_eq!(
        value.try_fp_wide().unwrap(),
        (false, 127, (1u128 << 22) | 1, 8, 24)
    );
    assert_eq!(value.unwrap_fp(), value.try_fp().unwrap());
    assert!(ModelValue::Bool(false).as_fp_wide().is_none());
    assert!(ModelValue::Bool(false).try_fp_wide().is_err());
}

#[test]
fn carrier_boundaries_refuse_overflow_instead_of_masking_it() {
    assert!(ModelValue::from_fp_fields(false, 0, (1u128 << 112) - 1, 15, 113).is_some());
    assert!(ModelValue::from_fp_fields(false, 0, 1u128 << 112, 15, 113).is_none());
    assert!(ModelValue::from_fp_fields(false, 1u64 << 15, 0, 15, 113).is_none());
    assert!(ModelValue::from_fp_fields(false, 0, u128::from(u64::MAX), 8, 65).is_some());
    assert!(ModelValue::from_fp_fields(false, 0, 1u128 << 64, 8, 65).is_none());
    let full = ModelValue::from_fp_fields(true, u64::MAX, u128::MAX, 64, 129).unwrap();
    assert_eq!(
        full.as_fp_wide(),
        Some((true, u64::MAX, u128::MAX, 64, 129))
    );
    assert_eq!(decode(&full.to_string(), 64, 129).unwrap(), full);
    for (eb, sb) in [
        (0, 113),
        (1, 113),
        (65, 113),
        (15, 0),
        (15, 1),
        (15, 130),
        (15, u32::MAX),
    ] {
        assert!(ModelValue::from_fp_fields(false, 0, 0, eb, sb).is_none());
    }
}

#[test]
fn strict_and_legacy_fp_literals_reject_malformed_widths_and_annotations() {
    use crate::api::model_parse_compound::parse_fp_value;
    use ay_frontend::sexp::parse_sexp;
    let valid = "(fp #b0 #b011111111111111 #x8000000000000000000000000001)";
    assert_eq!(
        parse_fp_value(&parse_sexp(valid).unwrap(), 15, 113),
        decode(valid, 15, 113).unwrap()
    );
    for text in [
        "(fp #b00 #b011111111111111 #x8000000000000000000000000001)",
        "(fp #b1 #x3fff #x8000000000000000000000000001)",
        "(fp #b0 #b011111111111111 #x18000000000000000000000000001)",
        "(fp #b0 #b011111111111111 #x800000000000000000000000001)",
        "(_ +zero 15 112)",
        "(_ NaN 16 113)",
    ] {
        assert_eq!(
            decode(text, 15, 113),
            Err(TypedModelValueDecodeError),
            "{text}"
        );
        assert_eq!(
            parse_fp_value(&parse_sexp(text).unwrap(), 15, 113),
            ModelValue::Unknown,
            "{text}"
        );
    }
}

#[test]
fn wide_special_literals_keep_separate_accessors_and_exact_sorts() {
    for (kind, spelling) in [
        (FpSpecialKind::PosZero, "+zero"),
        (FpSpecialKind::NegZero, "-zero"),
        (FpSpecialKind::PosInf, "+oo"),
        (FpSpecialKind::NegInf, "-oo"),
        (FpSpecialKind::NaN, "NaN"),
    ] {
        let literal = format!("(_ {spelling} 15 113)");
        let value = decode(&literal, 15, 113).unwrap();
        assert_eq!(value.try_fp_special().unwrap(), (&kind, 15, 113));
        assert!(value.as_fp_wide().is_none());
        assert_eq!(value.to_string(), literal);
    }
}

#[test]
fn one_bad_wide_literal_refuses_the_entire_ordered_batch() {
    let sort = Sort::FloatingPoint(15, 113);
    let good = "(fp #b0 #b011111111111111 #x8000000000000000000000000001)";
    let bad = "(fp #b0 #b011111111111111 #x18000000000000000000000000001)";
    assert_eq!(
        ModelValue::decode_typed_literals(&[(good, &sort), (bad, &sort), (good, &sort)]),
        Err(TypedModelValueDecodeError)
    );
    let values = ModelValue::decode_typed_literals(&[(good, &sort), (good, &sort)]).unwrap();
    assert_eq!(values.len(), 2);
    assert_eq!(values[0], values[1]);
}
