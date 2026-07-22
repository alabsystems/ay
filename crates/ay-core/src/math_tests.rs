// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::extended_gcd_bigint;
use num_bigint::BigInt;
use num_traits::Zero;

#[test]
fn extended_gcd_bezout_identity() {
    let (g, x, y) = extended_gcd_bigint(&BigInt::from(35), &BigInt::from(15));
    assert_eq!(g, BigInt::from(5));
    assert_eq!(BigInt::from(35) * x + BigInt::from(15) * y, g);
}

#[test]
fn extended_gcd_handles_zero() {
    let (g, x, y) = extended_gcd_bigint(&BigInt::zero(), &BigInt::from(7));
    assert_eq!(g, BigInt::from(7));
    assert_eq!(BigInt::from(0) * x + BigInt::from(7) * y, g);
}
