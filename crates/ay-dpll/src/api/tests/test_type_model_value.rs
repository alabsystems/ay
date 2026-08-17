// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for `ModelValue` extraction methods, variant names, and display formatting.

#[allow(deprecated)]
use crate::api::types::{FpSpecialKind, ModelValue, SolverError};
use num_bigint::BigInt;
use num_rational::BigRational;

// --- try_bool ---

#[test]
fn test_try_bool_ok() {
    assert!(ModelValue::Bool(true).try_bool().unwrap());
    assert!(!ModelValue::Bool(false).try_bool().unwrap());
}

#[test]
fn test_try_bool_err_int() {
    let v = ModelValue::Int(BigInt::from(42));
    let err = v.try_bool().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "Bool");
            assert_eq!(actual, "Int");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
fn test_try_bool_err_unknown() {
    let err = ModelValue::Unknown.try_bool().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "Bool");
            assert_eq!(actual, "Unknown");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

// --- try_int ---

#[test]
fn test_try_int_ok() {
    let v = ModelValue::Int(BigInt::from(99));
    assert_eq!(*v.try_int().unwrap(), BigInt::from(99));
}

#[test]
fn test_try_int_err_bool() {
    let err = ModelValue::Bool(true).try_int().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "Int");
            assert_eq!(actual, "Bool");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

// --- try_real ---

#[test]
fn test_try_real_ok() {
    let r = BigRational::new(BigInt::from(1), BigInt::from(3));
    let v = ModelValue::Real(r.clone());
    assert_eq!(*v.try_real().unwrap(), r);
}

#[test]
fn test_try_real_err_bitvec() {
    let v = ModelValue::BitVec {
        value: BigInt::from(7),
        width: 4,
    };
    let err = v.try_real().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "Real");
            assert_eq!(actual, "BitVec");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

// --- try_bv ---

#[test]
fn test_try_bv_ok() {
    let v = ModelValue::BitVec {
        value: BigInt::from(255),
        width: 8,
    };
    let (val, w) = v.try_bv().unwrap();
    assert_eq!(*val, BigInt::from(255));
    assert_eq!(w, 8);
}

#[test]
fn test_try_bv_err_real() {
    let v = ModelValue::Real(BigRational::new(BigInt::from(1), BigInt::from(2)));
    let err = v.try_bv().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "BitVec");
            assert_eq!(actual, "Real");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

// --- variant_name ---

#[test]
fn test_variant_name_all() {
    assert_eq!(ModelValue::Bool(true).variant_name(), "Bool");
    assert_eq!(ModelValue::Int(BigInt::from(0)).variant_name(), "Int");
    assert_eq!(
        ModelValue::Real(BigRational::new(BigInt::from(1), BigInt::from(1))).variant_name(),
        "Real"
    );
    assert_eq!(
        ModelValue::BitVec {
            value: BigInt::from(0),
            width: 1
        }
        .variant_name(),
        "BitVec"
    );
    assert_eq!(ModelValue::String("a".to_string()).variant_name(), "String");
    assert_eq!(
        ModelValue::Uninterpreted("u".to_string()).variant_name(),
        "Uninterpreted"
    );
    assert_eq!(
        ModelValue::ArraySmtlib("arr".to_string()).variant_name(),
        "ArraySmtlib"
    );
    assert_eq!(
        ModelValue::FloatingPoint {
            sign: false,
            exponent: 0,
            significand: 0,
            eb: 5,
            sb: 11
        }
        .variant_name(),
        "FloatingPoint"
    );
    assert_eq!(
        ModelValue::FloatingPointSpecial {
            kind: FpSpecialKind::NaN,
            eb: 5,
            sb: 11
        }
        .variant_name(),
        "FloatingPointSpecial"
    );
    assert_eq!(
        ModelValue::Datatype {
            constructor: "Nil".to_string(),
            args: vec![]
        }
        .variant_name(),
        "Datatype"
    );
    assert_eq!(ModelValue::Unknown.variant_name(), "Unknown");
}

// --- unwrap_* delegation ---

#[test]
#[allow(deprecated)]
fn test_unwrap_bool_delegates_to_try() {
    assert!(ModelValue::Bool(true).unwrap_bool());
}

#[test]
#[should_panic(expected = "expected Bool ModelValue")]
#[allow(deprecated)]
fn test_unwrap_bool_panic_on_mismatch() {
    ModelValue::Int(BigInt::from(1)).unwrap_bool();
}

#[test]
#[allow(deprecated)]
fn test_unwrap_int_delegates_to_try() {
    let v = ModelValue::Int(BigInt::from(42));
    assert_eq!(*v.unwrap_int(), BigInt::from(42));
}

#[test]
#[should_panic(expected = "expected Int ModelValue")]
#[allow(deprecated)]
fn test_unwrap_int_panic_on_mismatch() {
    ModelValue::Bool(false).unwrap_int();
}

#[test]
#[allow(deprecated)]
fn test_unwrap_real_delegates_to_try() {
    let r = BigRational::new(BigInt::from(3), BigInt::from(7));
    let v = ModelValue::Real(r.clone());
    assert_eq!(*v.unwrap_real(), r);
}

#[test]
#[should_panic(expected = "expected Real ModelValue")]
#[allow(deprecated)]
fn test_unwrap_real_panic_on_mismatch() {
    ModelValue::Unknown.unwrap_real();
}

#[test]
#[allow(deprecated)]
fn test_unwrap_bv_delegates_to_try() {
    let v = ModelValue::BitVec {
        value: BigInt::from(15),
        width: 4,
    };
    let (val, w) = v.unwrap_bv();
    assert_eq!(*val, BigInt::from(15));
    assert_eq!(w, 4);
}

#[test]
#[should_panic(expected = "expected BitVec ModelValue")]
#[allow(deprecated)]
fn test_unwrap_bv_panic_on_mismatch() {
    ModelValue::Bool(true).unwrap_bv();
}

// --- as_fp / try_fp / unwrap_fp ---

#[test]
fn test_as_fp_some() {
    let v = ModelValue::FloatingPoint {
        sign: false,
        exponent: 15,
        significand: 0,
        eb: 5,
        sb: 11,
    };
    let (sign, exp, sig, eb, sb) = v.as_fp().unwrap();
    assert!(!sign);
    assert_eq!(exp, 15);
    assert_eq!(sig, 0);
    assert_eq!(eb, 5);
    assert_eq!(sb, 11);
}

#[test]
fn test_as_fp_none() {
    assert!(ModelValue::Bool(true).as_fp().is_none());
}

#[test]
fn test_try_fp_ok() {
    let v = ModelValue::FloatingPoint {
        sign: true,
        exponent: 31,
        significand: 512,
        eb: 5,
        sb: 11,
    };
    let (sign, exp, sig, eb, sb) = v.try_fp().unwrap();
    assert!(sign);
    assert_eq!(exp, 31);
    assert_eq!(sig, 512);
    assert_eq!(eb, 5);
    assert_eq!(sb, 11);
}

#[test]
fn test_try_fp_err() {
    let err = ModelValue::Int(BigInt::from(0)).try_fp().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "FloatingPoint");
            assert_eq!(actual, "Int");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
#[allow(deprecated)]
fn test_unwrap_fp_ok() {
    let v = ModelValue::FloatingPoint {
        sign: false,
        exponent: 0,
        significand: 1,
        eb: 8,
        sb: 24,
    };
    let (sign, exp, sig, eb, sb) = v.unwrap_fp();
    assert!(!sign);
    assert_eq!(exp, 0);
    assert_eq!(sig, 1);
    assert_eq!(eb, 8);
    assert_eq!(sb, 24);
}

#[test]
#[should_panic(expected = "expected FloatingPoint ModelValue")]
#[allow(deprecated)]
fn test_unwrap_fp_panic_on_mismatch() {
    ModelValue::Bool(false).unwrap_fp();
}

// --- as_fp_special / try_fp_special / unwrap_fp_special ---

#[test]
fn test_as_fp_special_some() {
    let v = ModelValue::FloatingPointSpecial {
        kind: FpSpecialKind::NaN,
        eb: 5,
        sb: 11,
    };
    let (kind, eb, sb) = v.as_fp_special().unwrap();
    assert_eq!(*kind, FpSpecialKind::NaN);
    assert_eq!(eb, 5);
    assert_eq!(sb, 11);
}

#[test]
fn test_as_fp_special_none() {
    assert!(ModelValue::Unknown.as_fp_special().is_none());
}

#[test]
fn test_try_fp_special_ok() {
    let v = ModelValue::FloatingPointSpecial {
        kind: FpSpecialKind::PosInf,
        eb: 8,
        sb: 24,
    };
    let (kind, eb, sb) = v.try_fp_special().unwrap();
    assert_eq!(*kind, FpSpecialKind::PosInf);
    assert_eq!(eb, 8);
    assert_eq!(sb, 24);
}

#[test]
fn test_try_fp_special_err() {
    let err = ModelValue::Bool(true).try_fp_special().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "FloatingPointSpecial");
            assert_eq!(actual, "Bool");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
#[should_panic(expected = "expected FloatingPointSpecial ModelValue")]
#[allow(deprecated)]
fn test_unwrap_fp_special_panic_on_mismatch() {
    ModelValue::Int(BigInt::from(0)).unwrap_fp_special();
}

mod symbolic_values;
