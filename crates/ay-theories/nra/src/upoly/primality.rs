// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// Deterministic Miller-Rabin for `u64`.
pub(crate) fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n == p {
            return true;
        }
        if n.is_multiple_of(p) {
            return false;
        }
    }
    let mut d = n - 1;
    let mut r = 0u32;
    while d.is_multiple_of(2) {
        d /= 2;
        r += 1;
    }
    'outer: for a in [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = mod_pow_u128(a, u128::from(d), u128::from(n));
        if x == 1 || x == u128::from(n) - 1 {
            continue;
        }
        for _ in 1..r {
            x = (x * x) % u128::from(n);
            if x == u128::from(n) - 1 {
                continue 'outer;
            }
        }
        return false;
    }
    true
}

fn mod_pow_u128(mut base: u128, mut e: u128, m: u128) -> u128 {
    let mut acc = 1u128;
    base %= m;
    while e > 0 {
        if e & 1 == 1 {
            acc = (acc * base) % m;
        }
        base = (base * base) % m;
        e >>= 1;
    }
    acc
}

/// The distinct prime divisors of a polynomial degree.
fn distinct_prime_divisors(n: usize) -> Vec<usize> {
    let mut out = Vec::new();
    let mut m = n;
    let mut d = 2usize;
    while d * d <= m {
        if m.is_multiple_of(d) {
            out.push(d);
            while m.is_multiple_of(d) {
                m /= d;
            }
        }
        d += 1;
    }
    if m > 1 {
        out.push(m);
    }
    out
}
