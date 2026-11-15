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
    let n_minus_one = n - 1;
    // `n >= 2`, so the modulus is nonzero and `n - 1` is its top residue.
    let Some(modulus) = std::num::NonZeroU128::new(u128::from(n)) else {
        return false;
    };
    let minus_one = u128::from(n_minus_one);
    let mut d = n_minus_one;
    let mut r = 0u32;
    while d.is_multiple_of(2) {
        d /= 2;
        // `d >= 1` halves at most 63 times: the count never saturates.
        r = r.saturating_add(1);
    }
    'outer: for a in [2u128, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = mod_pow_u128(a, u128::from(d), modulus.get());
        if x == 1 || x == minus_one {
            continue;
        }
        for _ in 1..r {
            // `x` is a residue mod `n <= u64::MAX`, so it always fits `u64`,
            // and the product of two widened `u64` values cannot overflow
            // `u128`. A value that does not fit fails closed: the caller
            // refuses a modulus that is not proven prime.
            let Ok(x64) = u64::try_from(x) else {
                return false;
            };
            x = (u128::from(x64) * u128::from(x64)) % modulus;
            if x == minus_one {
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
    // A square that overflows `usize` exceeds every `m`: the loop is done.
    while d.checked_mul(d).is_some_and(|square| square <= m) {
        if m.is_multiple_of(d) {
            out.push(d);
            while m.is_multiple_of(d) {
                // `d >= 2` here, so the quotient always exists.
                let Some(quotient) = m.checked_div(d) else {
                    break;
                };
                m = quotient;
            }
        }
        let Some(next) = d.checked_add(1) else {
            break;
        };
        d = next;
    }
    if m > 1 {
        out.push(m);
    }
    out
}
