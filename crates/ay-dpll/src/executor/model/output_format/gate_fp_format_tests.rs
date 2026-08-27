// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact floating-point formatting regression.

use ay_core::Sort;
use ay_model_check::ModelValue;

use super::Executor;

#[test]
fn exact_fp_gate_value_round_trips_as_an_smt_fp_literal() {
    let exec = Executor::new();
    let value = ModelValue::FloatingPoint {
        sign: false,
        exponent: 16,
        significand: 256,
        exponent_bits: 5,
        significand_bits: 11,
    };
    assert_eq!(
        exec.format_gate_model_value(&value, &Sort::FloatingPoint(5, 11)),
        Some("(fp #b0 #b10000 #b0100000000)".to_string())
    );
    assert_eq!(
        exec.format_gate_model_value(&value, &Sort::FloatingPoint(8, 24)),
        None,
        "a mismatched carrier sort must fail closed"
    );
}
