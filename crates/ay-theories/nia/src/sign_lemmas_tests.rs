// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_product_sign() {
    assert_eq!(product_sign(&[1, 1]), 1);
    assert_eq!(product_sign(&[1, -1]), -1);
    assert_eq!(product_sign(&[-1, 1]), -1);
    assert_eq!(product_sign(&[-1, -1]), 1);
    assert_eq!(product_sign(&[1, 0]), 0);
    assert_eq!(product_sign(&[0, -1]), 0);
    assert_eq!(product_sign(&[-1, -1, -1]), -1);
    assert_eq!(product_sign(&[-1, -1, 1]), 1);
}

/// Zero dominates: any factor being 0 makes the product 0.
#[test]
fn test_product_sign_zero_dominates() {
    assert_eq!(product_sign(&[0, 0]), 0);
    assert_eq!(product_sign(&[1, 1, 0, -1, -1]), 0);
    assert_eq!(product_sign(&[0]), 0);
}

/// Single factor: identity.
#[test]
fn test_product_sign_single_factor() {
    assert_eq!(product_sign(&[1]), 1);
    assert_eq!(product_sign(&[-1]), -1);
}

/// Long chains of negatives: even count -> positive, odd count -> negative.
#[test]
fn test_product_sign_even_odd_negative_chains() {
    // 4 negatives -> positive
    assert_eq!(product_sign(&[-1, -1, -1, -1]), 1);
    // 5 negatives -> negative
    assert_eq!(product_sign(&[-1, -1, -1, -1, -1]), -1);
    // 6 negatives -> positive
    assert_eq!(product_sign(&[-1, -1, -1, -1, -1, -1]), 1);
}

/// Empty factor list: product of empty set is 1 (identity element).
#[test]
fn test_product_sign_empty() {
    // product_sign of empty is an edge case. The function uses fold with 1.
    assert_eq!(product_sign(&[]), 1);
}

/// Mixed positives: all positive factors give positive product.
#[test]
fn test_product_sign_all_positive() {
    assert_eq!(product_sign(&[1, 1, 1, 1, 1]), 1);
}
