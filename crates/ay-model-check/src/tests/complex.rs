// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn complex_value(real: i64, imaginary: i64) -> ModelValue {
    ModelValue::Datatype {
        ctor: "complex.make".to_string(),
        args: vec![ModelValue::Int(int(real)), ModelValue::Int(int(imaginary))],
    }
}

#[test]
fn complex_model_components_are_checked_independently() {
    let mut terms = TermStore::new();
    let z = terms.mk_var("z".to_string(), Sort::Complex);
    let real = terms.mk_complex_real(z).unwrap();
    let imaginary = terms.mk_complex_imaginary(z).unwrap();
    let three = terms.mk_rational(BigRational::from_integer(int(3)));
    let four = terms.mk_rational(BigRational::from_integer(int(4)));
    let expected = terms.mk_complex(three, four).unwrap();
    // Preserve one raw Complex equality to exercise typed value comparison,
    // independently of the core's component-equality lowering.
    let equality = app(&mut terms, "=", &[z, expected], Sort::Bool);
    let real_equality = terms.mk_eq(real, three);
    let imaginary_equality = terms.mk_eq(imaginary, four);
    let square = terms.mk_complex_multiply(z, z).unwrap();
    let minus_seven = terms.mk_rational(BigRational::from_integer(int(-7)));
    let twenty_four = terms.mk_rational(BigRational::from_integer(int(24)));
    let expected_square = terms.mk_complex(minus_seven, twenty_four).unwrap();
    let square_equality = terms.mk_eq(square, expected_square);
    let assertions = [equality, real_equality, imaginary_equality, square_equality];
    assert_confirmed(&verdict(
        &terms,
        &StubModel::new().with(z, complex_value(3, 4)),
        &assertions,
    ));
    assert_violates(&verdict(
        &terms,
        &StubModel::new().with(z, complex_value(3, -4)),
        &assertions,
    ));
    assert_cannot(&verdict(&terms, &StubModel::new(), &assertions));
}

#[test]
fn complex_model_rejects_opaque_and_malformed_carriers() {
    let mut terms = TermStore::new();
    let z = terms.mk_var("z".to_string(), Sort::Complex);
    let zero = terms.mk_rational(BigRational::from_integer(int(0)));
    let expected = terms.mk_complex(zero, zero).unwrap();
    let equality = app(&mut terms, "=", &[z, expected], Sort::Bool);
    let malformed = [
        ModelValue::Uninterpreted("z!0".to_string()),
        ModelValue::Datatype {
            ctor: "foreign".to_string(),
            args: vec![ModelValue::Int(int(0)), ModelValue::Int(int(0))],
        },
        ModelValue::Datatype {
            ctor: "complex.make".to_string(),
            args: vec![ModelValue::Int(int(0))],
        },
        ModelValue::Datatype {
            ctor: "complex.make".to_string(),
            args: vec![ModelValue::Bool(false), ModelValue::Int(int(0))],
        },
    ];
    for value in malformed {
        assert_cannot(&verdict(
            &terms,
            &StubModel::new().with(z, value),
            &[equality],
        ));
    }
}
