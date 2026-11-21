// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The dividends of a quotient, against brute force over truncating
/// division.
#[test]
fn least_and_greatest_dividend_match_brute_force() {
    for y in 1..=7_i128 {
        for q in -6..=6_i128 {
            let xs: Vec<i128> = (-80..=80).filter(|x| x / y == q).collect();
            assert_eq!(least_dividend(q, y), xs[0], "q = {q}, y = {y}");
            assert_eq!(
                greatest_dividend(q, y),
                xs[xs.len() - 1],
                "q = {q}, y = {y}"
            );
        }
    }
}
