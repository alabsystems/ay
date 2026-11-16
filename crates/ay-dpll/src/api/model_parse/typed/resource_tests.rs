// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;

fn parsed(text: &str) -> SExpr {
    let mut values = ay_frontend::sexp::parse_sexps(text).unwrap();
    assert_eq!(values.len(), 1);
    values.pop().unwrap()
}

#[test]
fn shared_copy_allowance_is_exact_sticky_and_freshly_retryable() {
    let mut decoder = Decoder::new();
    assert_eq!(decoder.copy(MAX_COPY_BYTES), Some(()));
    assert_eq!(decoder.copy(0), Some(()));
    assert_eq!(decoder.copy(1), None);
    assert_eq!(decoder.copy(0), None);
    assert_eq!(decoder.decode(&SExpr::True, &Sort::Bool), None);
    assert_eq!(
        Decoder::new().decode(&SExpr::True, &Sort::Bool),
        Some(ModelValue::Bool(true))
    );
    let mut decoder = Decoder::new();
    assert_eq!(decoder.copy(usize::MAX), None);
    assert_eq!(decoder.copy(0), None);
}

#[test]
fn shared_work_allowance_and_public_decode_precharge_fail_closed() {
    let mut decoder = Decoder::new();
    assert_eq!(decoder.charge(MAX_WORK), Some(()));
    assert_eq!(decoder.charge(0), Some(()));
    assert_eq!(decoder.decode(&SExpr::True, &Sort::Bool), None);
    assert_eq!(decoder.charge(0), None);
    let mut decoder = Decoder::new();
    decoder.bytes = size_of::<&SExpr>() + size_of::<ModelValue>();
    assert_eq!(
        decoder.decode(&SExpr::True, &Sort::Bool),
        Some(ModelValue::Bool(true))
    );
    assert_eq!(decoder.bytes, 0);
    assert_eq!(decoder.decode(&SExpr::True, &Sort::Bool), None);
    let mut decoder = Decoder::new();
    decoder.bytes = size_of::<&SExpr>() + size_of::<ModelValue>() - 1;
    assert_eq!(decoder.decode(&SExpr::True, &Sort::Bool), None);
}

#[test]
fn complete_metadata_and_value_nesting_have_independent_depth_checks() {
    let mut sort = Sort::Bool;
    for _ in 0..MAX_DEPTH {
        sort = Sort::Seq(Box::new(sort));
    }
    let mut decoder = Decoder::new();
    assert!(decoder.sort(&sort, 0).is_some());
    let too_deep = Sort::Seq(Box::new(sort));
    assert!(Decoder::new()
        .decode(&SExpr::Symbol("seq.empty".into()), &too_deep)
        .is_none());
    let mut value = SExpr::Numeral("1".into());
    for _ in 0..MAX_DEPTH {
        value = SExpr::List(vec![SExpr::Symbol("-".into()), value]);
    }
    assert!(parse_typed_value(&value, &Sort::Int).is_some());
    let too_deep = SExpr::List(vec![SExpr::Symbol("-".into()), value]);
    assert!(parse_typed_value(&too_deep, &Sort::Int).is_none());
}

#[test]
fn primitive_real_decimals_are_exact_and_sequence_fields_stay_typed() {
    let expected = BigRational::new(BigInt::from(1), BigInt::from(10));
    assert_eq!(
        parse_typed_value(&parsed("0.1"), &Sort::Real),
        Some(ModelValue::Real(expected))
    );
    assert_eq!(
        parse_typed_value(&parsed("(/ 7.0 2.0)"), &Sort::Real),
        Some(ModelValue::Real(BigRational::new(
            BigInt::from(7),
            BigInt::from(2)
        )))
    );
    assert!(parse_typed_value(&parsed("(/ 1.0 0.0)"), &Sort::Real).is_none());
    let sort = Sort::Seq(Box::new(Sort::bitvec(8)));
    let input =
        parsed("(seq.++ (as seq.empty (Seq (_ BitVec 8))) (seq.unit #x07) (seq.unit #x08))");
    let word = |value| ModelValue::BitVec {
        value: BigInt::from(value),
        width: 8,
    };
    assert_eq!(
        parse_typed_value(&input, &sort),
        Some(ModelValue::Seq(vec![word(7), word(8)]))
    );
    assert!(parse_typed_value(&parsed("(as seq.empty (Seq Bool))"), &sort).is_none());
    assert!(parse_typed_value(&parsed("(seq.unit #x0007)"), &sort).is_none());
}

#[test]
fn floating_point_compatibility_checks_every_printed_width() {
    use crate::api::types::FpSpecialKind;
    let sort = Sort::FloatingPoint(8, 24);
    assert_eq!(
        parse_typed_value(&parsed("(_ +zero 8 24)"), &sort),
        Some(ModelValue::FloatingPointSpecial {
            kind: FpSpecialKind::PosZero,
            eb: 8,
            sb: 24
        })
    );
    assert!(parse_typed_value(&parsed("(_ +zero 11 53)"), &sort).is_none());
    let value = "(fp #b1 #b00000001 #b00000000000000000000010)";
    assert_eq!(
        parse_typed_value(&parsed(value), &sort),
        Some(ModelValue::FloatingPoint {
            sign: true,
            exponent: 1,
            significand: 2,
            eb: 8,
            sb: 24,
        })
    );
    for bad in [
        "(fp #b01 #b00000001 #b00000000000000000000010)",
        "(fp #b1 #b000000001 #b00000000000000000000010)",
        "(fp #b1 #b00000001 #b000000000000000000000010)",
    ] {
        assert!(parse_typed_value(&parsed(bad), &sort).is_none());
    }
    assert_eq!(
        parse_typed_value(&parsed("(fp #b0 #x1 #x2)"), &Sort::FloatingPoint(4, 5)),
        Some(ModelValue::FloatingPoint {
            sign: false,
            exponent: 1,
            significand: 2,
            eb: 4,
            sb: 5
        })
    );
}
