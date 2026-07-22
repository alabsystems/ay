// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use num_bigint::BigInt;
use num_rational::BigRational;

/// Regression test for #6266: parse_smt_value_str returns None on parse failure
/// instead of silently returning SmtValue::Int(0).
#[test]
fn test_parse_smt_value_str_malformed_int_returns_none_6266() {
    assert_eq!(parse_smt_value_str("not_a_number", &Sort::Int), None);
}

#[test]
fn test_parse_smt_value_str_malformed_bv_returns_none_6266() {
    let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
    assert_eq!(parse_smt_value_str("#xZZZ", &bv8), None);
    assert_eq!(parse_smt_value_str("#b222", &bv8), None);
    assert_eq!(parse_smt_value_str("not_a_bv", &bv8), None);
}

#[test]
fn test_parse_smt_value_str_malformed_neg_int_returns_none_6266() {
    assert_eq!(parse_smt_value_str("(- not_a_number)", &Sort::Int), None);
}

#[test]
fn test_parse_smt_value_str_valid_int() {
    assert_eq!(
        parse_smt_value_str("42", &Sort::Int),
        Some(SmtValue::Int(42))
    );
    assert_eq!(
        parse_smt_value_str("-7", &Sort::Int),
        Some(SmtValue::Int(-7))
    );
    assert_eq!(
        parse_smt_value_str("(- 100)", &Sort::Int),
        Some(SmtValue::Int(-100))
    );
}

#[test]
fn test_parse_smt_value_str_valid_bool() {
    assert_eq!(
        parse_smt_value_str("true", &Sort::Bool),
        Some(SmtValue::Bool(true))
    );
    assert_eq!(
        parse_smt_value_str("false", &Sort::Bool),
        Some(SmtValue::Bool(false))
    );
}

#[test]
fn test_parse_smt_value_str_valid_bv() {
    let bv8 = Sort::BitVec(ay_core::BitVecSort { width: 8 });
    assert_eq!(
        parse_smt_value_str("#xFF", &bv8),
        Some(SmtValue::BitVec(255, 8))
    );
    assert_eq!(
        parse_smt_value_str("#b11111111", &bv8),
        Some(SmtValue::BitVec(255, 8))
    );
    assert_eq!(
        parse_smt_value_str("255", &bv8),
        Some(SmtValue::BitVec(255, 8))
    );
}

#[test]
fn test_parse_smt_value_str_wide_bv_truncation_7040() {
    // 192-bit hex literal: 48 hex digits > 32 (128-bit limit).
    // Should truncate to low 128 bits.
    let bv192 = Sort::BitVec(ay_core::BitVecSort { width: 192 });
    let hex_192 = "#x000000000000000100000000000000020000000000000003";
    let result = parse_smt_value_str(hex_192, &bv192);
    // Low 128 bits = 0x00000000000000020000000000000003
    assert_eq!(
        result,
        Some(SmtValue::BitVec(0x00000000000000020000000000000003, 192))
    );

    // 256-bit binary literal: 256 chars > 128 limit.
    let bv256 = Sort::BitVec(ay_core::BitVecSort { width: 256 });
    let bin_256 = &format!("#b{}", "1".repeat(256));
    let result = parse_smt_value_str(bin_256, &bv256);
    // Low 128 bits = all ones = u128::MAX
    assert_eq!(result, Some(SmtValue::BitVec(u128::MAX, 256)));
}

#[test]
fn test_parse_smt_value_str_symbolic_bv_placeholder_6289() {
    let bv32 = Sort::BitVec(ay_core::BitVecSort { width: 32 });
    assert_eq!(
        parse_smt_value_str("@arr33", &bv32),
        Some(SmtValue::Opaque("@arr33".to_string()))
    );
}

#[test]
fn test_parse_smt_value_str_sort_qualified_symbol_6289() {
    let bv32 = Sort::BitVec(ay_core::BitVecSort { width: 32 });
    assert_eq!(
        parse_smt_value_str("__au_k0_(_ BitVec 32)", &bv32),
        Some(SmtValue::Opaque("__au_k0".to_string()))
    );
}

#[test]
fn test_parse_smt_value_str_real_integer() {
    assert_eq!(
        parse_smt_value_str("42", &Sort::Real),
        Some(SmtValue::Real(BigRational::from_integer(BigInt::from(
            42i64
        ))))
    );
}

#[test]
fn test_parse_smt_value_str_real_decimal() {
    let result = parse_smt_value_str("1.5", &Sort::Real);
    let expected = BigRational::new(BigInt::from(3i64), BigInt::from(2i64));
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_parse_smt_value_str_real_rational() {
    let result = parse_smt_value_str("(/ 3 2)", &Sort::Real);
    let expected = BigRational::new(BigInt::from(3i64), BigInt::from(2i64));
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_parse_smt_value_str_real_decimal_rational() {
    let result = parse_smt_value_str("(/ 1.0 2.0)", &Sort::Real);
    let expected = BigRational::new(BigInt::from(1i64), BigInt::from(2i64));
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_parse_smt_value_str_real_negative() {
    let result = parse_smt_value_str("(- 5)", &Sort::Real);
    let expected = BigRational::from_integer(BigInt::from(-5i64));
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_parse_smt_value_str_real_nested_negative_rationals() {
    let expected = BigRational::new(BigInt::from(-1i64), BigInt::from(2i64));
    assert_eq!(
        parse_smt_value_str("(/ (- 1) 2)", &Sort::Real),
        Some(SmtValue::Real(expected.clone()))
    );
    assert_eq!(
        parse_smt_value_str("(/ 1 (- 2))", &Sort::Real),
        Some(SmtValue::Real(expected.clone()))
    );
    assert_eq!(
        parse_smt_value_str("(- (/ 1.0 2.0))", &Sort::Real),
        Some(SmtValue::Real(expected))
    );
}

#[test]
fn test_parse_smt_value_str_real_large_integer() {
    let literal = "922337203685477580812345";
    let result = parse_smt_value_str(literal, &Sort::Real);
    let expected = BigRational::from_integer(literal.parse::<BigInt>().unwrap());
    assert_eq!(result, Some(SmtValue::Real(expected)));
}

#[test]
fn test_parse_smt_value_str_real_malformed_returns_none() {
    assert_eq!(parse_smt_value_str("not_a_real", &Sort::Real), None);
}

#[test]
fn test_default_smt_value_real_is_zero_rational() {
    let default = default_smt_value(&Sort::Real);
    assert_eq!(
        default,
        SmtValue::Real(BigRational::from_integer(BigInt::from(0i64)))
    );
}
