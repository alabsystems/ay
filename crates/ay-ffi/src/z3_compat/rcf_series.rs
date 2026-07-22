// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rigorous rational enclosures of the transcendentals π and e for the RCF
//! surface (`Z3_rcf_mk_pi` / `Z3_rcf_mk_e`).
//!
//! Pure `BigRational` interval arithmetic — no floats, ever. Each function
//! returns an interval `(lo, hi)` with a MATHEMATICAL guarantee
//! `lo < value < hi`, derived from a convergent series with a rigorous tail
//! bound:
//!
//! * **π** — Machin's formula `π = 16·atan(1/5) − 4·atan(1/239)`, with each
//!   `atan(1/m)` enclosed by consecutive partial sums of its alternating
//!   Leibniz series (for an alternating series with strictly decreasing terms,
//!   the limit lies strictly between any two consecutive partial sums).
//! * **e** — `e = Σ 1/k!`, enclosed below by the partial sum `S_n` (all terms
//!   positive) and above by `S_n + 2/(n+1)!` (the tail is
//!   `Σ_{k>n} 1/k! < (1/(n+1)!)·Σ_{j≥0} (n+2)^{-j} ≤ 2/(n+1)!`).
//!
//! Widths shrink monotonically as `terms` grows, so callers can refine on
//! demand (sign decisions terminate whenever the compared values differ — and
//! against any rational/algebraic operand they always differ, because π and e
//! are transcendental). Enclosures are display/comparison scaffolding only:
//! every equality answer on the RCF surface still comes from exact symbolic
//! coefficient arithmetic, never from these intervals.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

/// Which transcendental a symbolic RCF value extends ℚ by.
///
/// `pub` (not `pub(crate)`) because it appears in the fields of the public
/// [`super::rcf::RcfNum`], the pointee of the public `Z3_rcf_num` handle type.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TransKind {
    /// π (Archimedes' constant).
    Pi,
    /// e (Euler's number).
    E,
}

impl TransKind {
    /// Z3-style display / symbol name.
    pub(crate) fn name(self) -> &'static str {
        match self {
            TransKind::Pi => "pi",
            TransKind::E => "e",
        }
    }
}

/// Rational `n`.
fn rat_int(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

/// Enclosure of `atan(1/m)` (`m ≥ 2`) from the alternating Leibniz series
/// `Σ_{k≥0} (−1)^k / ((2k+1)·m^(2k+1))`: the value lies strictly between the
/// partial sums `S_n` and `S_{n+1}` (terms strictly decrease in magnitude).
fn atan_inv_enclosure(m: u64, terms: usize) -> (BigRational, BigRational) {
    let m = BigInt::from(m);
    let m2 = &m * &m;
    // Running power m^(2k+1), starting at m^1.
    let mut mpow = m.clone();
    let mut partial = BigRational::new(BigInt::one(), mpow.clone());
    let mut last = partial.clone();
    let n = terms.max(1);
    for k in 1..=n {
        mpow *= &m2;
        let term = BigRational::new(BigInt::one(), BigInt::from(2 * k as u64 + 1) * &mpow);
        last = partial.clone();
        if k % 2 == 1 {
            partial -= term;
        } else {
            partial += term;
        }
    }
    // `partial` = S_n, `last` = S_{n-1}; the limit is strictly between them.
    if partial <= last {
        (partial, last)
    } else {
        (last, partial)
    }
}

/// Rigorous enclosure `(lo, hi)` of π with `lo < π < hi`, refined by `terms`.
pub(crate) fn pi_enclosure(terms: usize) -> (BigRational, BigRational) {
    let (a5_lo, a5_hi) = atan_inv_enclosure(5, terms);
    let (a239_lo, a239_hi) = atan_inv_enclosure(239, terms);
    // π = 16·atan(1/5) − 4·atan(1/239); monotone interval combination.
    let sixteen = rat_int(16);
    let four = rat_int(4);
    let lo = &sixteen * &a5_lo - &four * &a239_hi;
    let hi = &sixteen * &a5_hi - &four * &a239_lo;
    (lo, hi)
}

/// Rigorous enclosure `(lo, hi)` of e with `lo < e < hi`, refined by `terms`.
pub(crate) fn e_enclosure(terms: usize) -> (BigRational, BigRational) {
    let n = terms.max(1);
    let mut factorial = BigInt::one();
    let mut partial = BigRational::from_integer(BigInt::one()); // k = 0 term
    for k in 1..=n {
        factorial *= BigInt::from(k as u64);
        partial += BigRational::new(BigInt::one(), factorial.clone());
    }
    // Tail bound: 0 < e − S_n < 2/(n+1)!.
    let next_factorial = &factorial * BigInt::from(n as u64 + 1);
    let hi = &partial + BigRational::new(BigInt::from(2), next_factorial);
    (partial, hi)
}

/// Enclosure of the requested transcendental, refined by `terms`.
pub(crate) fn enclosure(kind: TransKind, terms: usize) -> (BigRational, BigRational) {
    match kind {
        TransKind::Pi => pi_enclosure(terms),
        TransKind::E => e_enclosure(terms),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;

    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn pi_enclosure_brackets_known_digits() {
        let (lo, hi) = pi_enclosure(12);
        assert!(lo < hi);
        // 3.14159265358979 < π < 3.14159265358980
        assert!(lo > rat(314159265358979, 100000000000000));
        assert!(hi < rat(314159265358980, 100000000000000));
    }

    #[test]
    fn e_enclosure_brackets_known_digits() {
        let (lo, hi) = e_enclosure(20);
        assert!(lo < hi);
        // 2.71828182845904 < e < 2.71828182845905
        assert!(lo > rat(271828182845904, 100000000000000));
        assert!(hi < rat(271828182845905, 100000000000000));
    }

    #[test]
    fn enclosures_shrink_with_more_terms() {
        let w = |lo: &BigRational, hi: &BigRational| hi - lo;
        let (plo1, phi1) = pi_enclosure(4);
        let (plo2, phi2) = pi_enclosure(8);
        assert!(w(&plo2, &phi2) < w(&plo1, &phi1));
        assert!(w(&plo2, &phi2) > BigRational::zero());
        let (elo1, ehi1) = e_enclosure(5);
        let (elo2, ehi2) = e_enclosure(10);
        assert!(w(&elo2, &ehi2) < w(&elo1, &ehi1));
        // Containment: the tighter interval sits inside the looser one.
        assert!(plo2 >= plo1 && phi2 <= phi1);
        assert!(elo2 >= elo1 && ehi2 <= ehi1);
    }
}
