// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_sort_error_display_preserved() {
    // Lock the Mismatch display format (#3039)
    let e1 = SortError::Mismatch {
        operation: "bvadd",
        expected: "BitVec(32)",
        actual: "Int".to_string(),
    };
    assert_eq!(e1.to_string(), "bvadd: expected BitVec(32), got Int");

    // Lock the StackUnderflow display format (#3039)
    let e2 = SortError::StackUnderflow {
        operation: "pop",
        requested: 3,
        available: 1,
    };
    assert_eq!(e2.to_string(), "pop: cannot pop 3 levels, only 1 available");
}

#[test]
fn test_sort_error_implements_std_error() {
    let err = SortError::Mismatch {
        operation: "eq",
        expected: "matching sorts",
        actual: "Bool and Int".to_string(),
    };
    // Verify SortError implements std::error::Error
    let _: &dyn std::error::Error = &err;
}
