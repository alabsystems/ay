// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared number-theoretic helpers used across theory solvers.

use num_bigint::BigInt;
use num_integer::Integer;

/// Compute the extended greatest common divisor of two integers.
///
/// Returns `(g, x, y)` such that:
/// - `g = gcd(a, b)` with `g >= 0`
/// - `a * x + b * y = g`
pub fn extended_gcd_bigint(a: &BigInt, b: &BigInt) -> (BigInt, BigInt, BigInt) {
    let egcd = a.extended_gcd(b);
    (egcd.gcd, egcd.x, egcd.y)
}

#[cfg(test)]
#[path = "math_tests.rs"]
mod tests;
