// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/upoly.rs` — dense
//! univariate polynomials over `Z` and over `Z_p`, and factorization over
//! `Z_p`.
//!
//! # What z3 can and cannot be asked
//!
//! MEASURED, on the pinned 5.0.0 dylib:
//!
//! ```text
//!   $ nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c upolynomial   -> 0
//!   $ nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c '_Z3_.*factor' -> 0
//!   $ grep -c 'Z3_API' reference/z3/5.0.0/include/z3_polynomial.h        -> 1
//!                      (the one entry point is Z3_polynomial_subresultants)
//! ```
//!
//! So there is **no z3 entry point for univariate factorization, for `Z_p`
//! arithmetic, or for square-free decomposition**: `upolynomial` is an internal
//! C++ class whose symbols are not exported. Two of the four checks below can
//! therefore reach z3 and two cannot, and the two that cannot say so rather
//! than inventing a comparison.
//!
//! Where z3 is unreachable the reference is an EXACT ALGEBRAIC IDENTITY plus an
//! INDEPENDENT WITNESS:
//!
//!   * the product of the returned factors, with multiplicity, must equal the
//!     input exactly — not up to a unit, not up to normalization, exactly;
//!   * every returned factor must be irreducible according to **Rabin's test**,
//!     which shares `powmod`/`gcd`/`rem` with the factorizer but shares none of
//!     its control flow — no square-free split, no distinct-degree loop, no
//!     Cantor-Zassenhaus. A factorizer that under-factors (returns a reducible
//!     factor) still satisfies the product identity; only the witness catches
//!     it. A factorizer that over-factors violates the product identity. The
//!     two together pin the answer.
//!
//! # The counters are pinned, not printed
//!
//! `upoly::FactorStats` is exactly the shape of defect this campaign has
//! already found once — "a stored flag the headline metric was read off, which
//! could be hardwired with no divergence". So the checks do not print the
//! counters and move on:
//!
//!   * `ddf_iters` is **re-derived exactly** from the returned buckets by
//!     replaying the loop's own stopping condition (`deg(f*) >= 2i`) against
//!     the answer. Hardwiring it to any constant diverges.
//!   * `edf_splits` is **pinned to `factors - buckets`**: every successful
//!     Cantor-Zassenhaus split raises the factor count by exactly one, so the
//!     total number of splits is determined by the answer alone.
//!
//! `edf_attempts` and `powmod_mults` are NOT pinned — they are genuinely
//! path-dependent — and that gap is disclosed rather than papered over.

use ay_nra::oracle_api::{OUniZ, OUniZp, OZpMgr};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::Z3;

/// Primes the generator draws from.
///
/// Deliberately includes `2` (where Cantor-Zassenhaus cannot use
/// `(p^d - 1)/2` and must fall back to the trace map) and `3` (small enough
/// that a `p`-th power in characteristic `p` actually shows up at these
/// degrees), alongside larger ones where the generic path runs.
const PRIMES: [u64; 8] = [2, 3, 5, 7, 11, 13, 101, 65_537];

/// Maximum degree of a generated factor.
const MAX_FACTOR_DEG: usize = 3;

/// Maximum number of factors multiplied into one generated input.
const MAX_FACTORS: usize = 4;

/// One generated case for the `upoly` checks.
pub(crate) struct GenUp {
    /// Factors over `Z`, to be multiplied (with the multiplicities below).
    pub(crate) factors: Vec<(Vec<BigInt>, usize)>,
    /// A second, independent polynomial over `Z` for the two-argument checks.
    pub(crate) other: Vec<BigInt>,
    /// The modulus.
    pub(crate) p: u64,
    /// Shape label for reporting.
    pub(crate) shape: &'static str,
}

fn gen_coeffs(rng: &mut Rng, deg: usize) -> Vec<BigInt> {
    let mut c: Vec<BigInt> = (0..=deg).map(|_| BigInt::from(rng.range(-6, 6))).collect();
    // Force a non-zero leading coefficient so the degree is what was asked for.
    if c[deg].is_zero() {
        c[deg] = BigInt::one();
    }
    c
}

/// Draw a case.
///
/// Five shapes, chosen so that each of the branches that a purely random draw
/// would almost never reach gets exercised:
///
/// * `squares` — a factor is planted with multiplicity 2 or 3, so the
///   square-free decomposition has something to decompose;
/// * `split` — every factor is linear, the worst case for equal-degree
///   factorization because it requires the most splits;
/// * `pth-power` — the input is `g(x^p)` for a small `p`, so the derivative
///   vanishes modulo `p` and the characteristic-`p` branch runs;
/// * `gap` — a sparse dividend with internal zero coefficients exposes the
///   trailing leading-coefficient power in pseudo-division;
/// * `generic` — an unconstrained product.
pub(crate) fn gen_up(rng: &mut Rng) -> GenUp {
    let p = PRIMES[usize::try_from(rng.below(PRIMES.len() as u64)).unwrap_or(0)];
    let shape = match rng.below(5) {
        0 => "squares",
        1 => "split",
        2 => "pth-power",
        3 => "gap",
        _ => "generic",
    };
    let n = 1 + usize::try_from(rng.below(MAX_FACTORS as u64)).unwrap_or(0);
    let mut factors = Vec::new();
    match shape {
        "split" => {
            for _ in 0..=n {
                factors.push((vec![BigInt::from(rng.range(-8, 8)), BigInt::one()], 1));
            }
        }
        "squares" => {
            for i in 0..n {
                let deg = 1 + usize::try_from(rng.below(MAX_FACTOR_DEG as u64)).unwrap_or(0);
                let mult = if i == 0 {
                    2 + usize::try_from(rng.below(2)).unwrap_or(0)
                } else {
                    1
                };
                factors.push((gen_coeffs(rng, deg), mult));
            }
        }
        "pth-power" => {
            // g(x^p): every exponent is a multiple of p, so the derivative is
            // identically zero mod p.
            let small = if p <= 5 { p } else { 3 };
            let deg = 1 + usize::try_from(rng.below(2)).unwrap_or(0);
            let g = gen_coeffs(rng, deg);
            let mut spread =
                vec![BigInt::zero(); (g.len() - 1) * usize::try_from(small).unwrap_or(3) + 1];
            for (i, c) in g.iter().enumerate() {
                spread[i * usize::try_from(small).unwrap_or(3)] = c.clone();
            }
            factors.push((spread, 1));
        }
        "gap" => {
            // A dividend with HOLES: `x^k + c`. Pseudo-division against a
            // quadratic then takes a degree DROP, which is the only way the
            // trailing balancing power `lc(b)^e` with `e > 0` ever becomes
            // observable. Without this shape an injected defect that dropped
            // that scaling produced zero divergences: on dense inputs the loop
            // runs exactly `deg(a) - deg(b) + 1` times and `e` ends at 0, so
            // the balancing factor is 1 and deleting it is invisible.
            let k = 4 + usize::try_from(rng.below(3)).unwrap_or(0);
            let mut c = vec![BigInt::zero(); k + 1];
            c[k] = BigInt::one();
            c[0] = BigInt::from(rng.range(-5, 5));
            factors.push((c, 1));
        }
        _ => {
            for _ in 0..n {
                let deg = 1 + usize::try_from(rng.below(MAX_FACTOR_DEG as u64)).unwrap_or(0);
                factors.push((gen_coeffs(rng, deg), 1));
            }
        }
    }
    let other_deg = 1 + usize::try_from(rng.below(3)).unwrap_or(0);
    let mut other = gen_coeffs(rng, other_deg);
    // Half the divisors get a NON-UNIT leading coefficient. With `lc(b) == 1`
    // every power of `lc(b)` is 1 and the whole pseudo-division balancing is
    // invisible regardless of the degree pattern.
    if rng.chance(1, 2) {
        let last = other.len() - 1;
        other[last] = BigInt::from(rng.range(2, 5));
    }
    GenUp {
        factors,
        other,
        p,
        shape,
    }
}

fn build_z(g: &GenUp) -> OUniZ {
    let mut acc = OUniZ::from_coeffs(vec![BigInt::one()]);
    for (c, m) in &g.factors {
        let f = OUniZ::from_coeffs(c.clone());
        for _ in 0..*m {
            acc = acc.mul(&f);
        }
    }
    acc
}

fn render_z(p: &OUniZ) -> String {
    let c: Vec<BigRational> = p.coeffs().into_iter().map(BigRational::from).collect();
    crate::polygen::render(&c)
}

fn render_zp(m: &OZpMgr, p: &OUniZp) -> String {
    let c: Vec<BigRational> = p
        .coeffs()
        .into_iter()
        .map(|v| BigRational::from(BigInt::from(v)))
        .collect();
    format!("{} (mod {})", crate::polygen::render(&c), m.p())
}

fn to_rationals(p: &OUniZ) -> Vec<BigRational> {
    p.coeffs().into_iter().map(BigRational::from).collect()
}

fn add_matches(total: &mut u64, outcome: Outcome) -> Result<(), Outcome> {
    match outcome {
        Outcome::Match(n) => {
            *total += n;
            Ok(())
        }
        other => Err(other),
    }
}

mod cost;
mod ddf;
mod factor;
mod square_free;
mod substrate;

pub(crate) use cost::measure_cost;
pub(crate) use ddf::check_ddf;
pub(crate) use factor::check_factor;
pub(crate) use square_free::check_sqf_decomp;
pub(crate) use substrate::check_substrate;
