// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Tests for exact continuous repair of externally rounded points.

use super::*;
use ay_milp::{Model, Sense};

fn thirds_model() -> Model {
    let mut model = Model::new();
    let integer = model.add_int_col(0.0, 1.0);
    let continuous = model.add_col(0.0, 1.0);
    model.add_row(0.0, 0.0, &[(integer, -1.0), (continuous, 3.0)]);
    model.set_objective(&[(continuous, 1.0)], Sense::Minimize);
    model
}

#[test]
fn rounded_continuous_value_is_repaired_with_integer_assignment_fixed() {
    let model = thirds_model();
    let supplied = vec![
        Some(BigRational::one()),
        Some(BigRational::new(
            BigInt::from(333_333_333_333_333_i64),
            BigInt::from(1_000_000_000_000_000_i64),
        )),
    ];
    assert!(model
        .check_point(
            &supplied
                .iter()
                .map(|value| value.clone().expect("complete point"))
                .collect::<Vec<_>>()
        )
        .is_err());

    let repaired =
        repair_continuous_completion(&model, &supplied, Duration::from_secs(2), Some(64 << 20))
            .expect("the exact LP completion exists");
    assert_eq!(repaired[0], BigRational::one());
    assert_eq!(
        repaired[1],
        BigRational::new(BigInt::from(1), BigInt::from(3))
    );
    assert!(model.check_point(&repaired).is_ok());
}

#[test]
fn repair_refuses_missing_or_fractional_integral_assignments() {
    let model = thirds_model();
    let missing = vec![None, Some(BigRational::zero())];
    assert!(
        repair_continuous_completion(&model, &missing, Duration::from_secs(2), Some(64 << 20),)
            .is_err()
    );

    let fractional = vec![
        Some(BigRational::new(BigInt::from(1), BigInt::from(2))),
        Some(BigRational::zero()),
    ];
    assert!(repair_continuous_completion(
        &model,
        &fractional,
        Duration::from_secs(2),
        Some(64 << 20),
    )
    .is_err());
}

#[test]
fn pure_lp_decimal_point_can_be_reconstructed_exactly() {
    let mut model = Model::new();
    let continuous = model.add_col(0.0, 1.0);
    model.add_row(1.0, 1.0, &[(continuous, 3.0)]);
    model.set_objective(&[(continuous, 1.0)], Sense::Minimize);
    let supplied = vec![Some(BigRational::new(
        BigInt::from(333_333_333_333_333_i64),
        BigInt::from(1_000_000_000_000_000_i64),
    ))];
    let repaired =
        repair_continuous_completion(&model, &supplied, Duration::from_secs(2), Some(64 << 20))
            .expect("the exact LP vertex exists");
    assert_eq!(
        repaired,
        vec![BigRational::new(BigInt::from(1), BigInt::from(3))]
    );
}

#[test]
fn repair_rejects_an_integer_the_numeric_model_cannot_represent() {
    let mut model = Model::new();
    model.add_int_col(f64::NEG_INFINITY, f64::INFINITY);
    let supplied = vec![Some(BigRational::from_integer(BigInt::from(
        9_007_199_254_740_993_u64,
    )))];
    let error =
        repair_continuous_completion(&model, &supplied, Duration::from_secs(2), Some(64 << 20))
            .expect_err("2^53 + 1 is not exactly representable as f64");
    assert!(error.contains("cannot be represented exactly"), "{error}");
}
