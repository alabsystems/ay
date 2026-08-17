// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Symbolic and structured model-value access regressions.

use super::*;

// --- as_datatype / try_datatype / unwrap_datatype ---

#[test]
fn test_as_datatype_some_nullary() {
    let v = ModelValue::Datatype {
        constructor: "Nil".to_string(),
        args: vec![],
    };
    let (ctor, args) = v.as_datatype().unwrap();
    assert_eq!(ctor, "Nil");
    assert!(args.is_empty());
}

#[test]
fn test_as_datatype_some_with_args() {
    let v = ModelValue::Datatype {
        constructor: "Cons".to_string(),
        args: vec![
            ModelValue::Int(BigInt::from(1)),
            ModelValue::Datatype {
                constructor: "Nil".to_string(),
                args: vec![],
            },
        ],
    };
    let (ctor, args) = v.as_datatype().unwrap();
    assert_eq!(ctor, "Cons");
    assert_eq!(args.len(), 2);
}

#[test]
fn test_as_datatype_none() {
    assert!(ModelValue::Bool(true).as_datatype().is_none());
}

#[test]
fn test_try_datatype_ok() {
    let v = ModelValue::Datatype {
        constructor: "Pair".to_string(),
        args: vec![ModelValue::Bool(true), ModelValue::Int(BigInt::from(42))],
    };
    let (ctor, args) = v.try_datatype().unwrap();
    assert_eq!(ctor, "Pair");
    assert_eq!(args.len(), 2);
}

#[test]
fn test_try_datatype_err() {
    let err = ModelValue::Unknown.try_datatype().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "Datatype");
            assert_eq!(actual, "Unknown");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
#[should_panic(expected = "expected Datatype ModelValue")]
#[allow(deprecated)]
fn test_unwrap_datatype_panic_on_mismatch() {
    ModelValue::Bool(false).unwrap_datatype();
}

// --- try_string / unwrap_string ---

#[test]
fn test_try_string_ok() {
    let v = ModelValue::String("hello".to_string());
    assert_eq!(v.try_string().unwrap(), "hello");
}

#[test]
fn test_try_string_err() {
    let err = ModelValue::Int(BigInt::from(0)).try_string().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "String");
            assert_eq!(actual, "Int");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
#[allow(deprecated)]
fn test_unwrap_string_ok() {
    let v = ModelValue::String("world".to_string());
    assert_eq!(v.unwrap_string(), "world");
}

#[test]
#[should_panic(expected = "expected String ModelValue")]
#[allow(deprecated)]
fn test_unwrap_string_panic_on_mismatch() {
    ModelValue::Bool(true).unwrap_string();
}

// --- try_uninterpreted / unwrap_uninterpreted ---

#[test]
fn test_try_uninterpreted_ok() {
    let v = ModelValue::Uninterpreted("elem_0".to_string());
    assert_eq!(v.try_uninterpreted().unwrap(), "elem_0");
}

#[test]
fn test_try_uninterpreted_err() {
    let err = ModelValue::Bool(false).try_uninterpreted().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "Uninterpreted");
            assert_eq!(actual, "Bool");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
#[should_panic(expected = "expected Uninterpreted ModelValue")]
#[allow(deprecated)]
fn test_unwrap_uninterpreted_panic_on_mismatch() {
    ModelValue::Int(BigInt::from(0)).unwrap_uninterpreted();
}

// --- try_array_smtlib / unwrap_array_smtlib ---

#[test]
fn test_try_array_smtlib_ok() {
    let v = ModelValue::ArraySmtlib("((as const (Array Int Int)) 0)".to_string());
    assert_eq!(
        v.try_array_smtlib().unwrap(),
        "((as const (Array Int Int)) 0)"
    );
}

#[test]
fn test_try_array_smtlib_err() {
    let err = ModelValue::Bool(true).try_array_smtlib().unwrap_err();
    match err {
        SolverError::ModelValueMismatch { expected, actual } => {
            assert_eq!(expected, "ArraySmtlib");
            assert_eq!(actual, "Bool");
        }
        other => panic!("wrong error variant: {other:?}"),
    }
}

#[test]
#[should_panic(expected = "expected ArraySmtlib ModelValue")]
#[allow(deprecated)]
fn test_unwrap_array_smtlib_panic_on_mismatch() {
    ModelValue::Unknown.unwrap_array_smtlib();
}
