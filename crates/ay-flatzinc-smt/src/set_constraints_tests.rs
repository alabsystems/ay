// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_set_literal_contains_present() {
    assert!(set_literal_contains(&[0, 2, 5], 2));
}

#[test]
fn test_set_literal_contains_absent() {
    assert!(!set_literal_contains(&[0, 2, 5], 3));
}

#[test]
fn test_set_literal_contains_empty() {
    assert!(!set_literal_contains(&[], 0));
}

#[test]
fn test_set_bit_name() {
    assert_eq!(set_bit_name("S_1", 0), "S_1__bit__0");
    assert_eq!(set_bit_name("S_1", 11), "S_1__bit__11");
}
