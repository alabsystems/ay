// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_chc::{testing, SmtValue};
use ay_core::Sort;
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn test_parse_smt_model_value_negative_decimal_regression_3857() {
    let result = testing::parse_smt_model_value_for_testing("-1.5", &Sort::Real);
    let expected = BigRational::new(BigInt::from(-3i64), BigInt::from(2i64));
    assert_eq!(result, Some(SmtValue::Real(expected)));

    let zero_crossing = testing::parse_smt_model_value_for_testing("-0.5", &Sort::Real);
    let zero_crossing_expected = BigRational::new(BigInt::from(-1i64), BigInt::from(2i64));
    assert_eq!(zero_crossing, Some(SmtValue::Real(zero_crossing_expected)));
}
