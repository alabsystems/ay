// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/mpbq.rs` — binary
//! rationals (`a / 2^k`), dyadic interval refinement, and the `select_small`
//! family.
//!
//! # What z3 can and cannot be asked
//!
//! MEASURED, on the pinned 5.0.0 distribution:
//!
//! ```text
//!   $ nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c mpbq            -> 0
//!   $ nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c binary_rational -> 0
//!   $ nm    reference/z3/5.0.0/bin/libz3.a      | grep -c mpbq            -> 224
//!   $ nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c Z3_algebraic    -> 21
//! ```
//!
//! `mpbq` is an internal C++ class. Its 224 symbols exist **only in the static
//! archive**, mangled as members of `mpbq_manager`; the dylib the oracle
//! `dlopen`s exports none of them. So there is no way to call z3's dyadic layer
//! directly, and no check below pretends to.
//!
//! What IS exported is `Z3_algebraic_*`, and that is a genuine leg for two of
//! the four checks:
//!
//!   * a dyadic is a rational, hence an algebraic number z3 can **add** and
//!     **multiply** (`Z3_algebraic_add` / `Z3_algebraic_mul`), so AY's exact
//!     dyadic arithmetic is compared against z3's own exact arithmetic;
//!   * an isolating interval refined by AY is checked against **z3's root**
//!     with `Z3_algebraic_lt` / `Z3_algebraic_gt` — the root z3 found must lie
//!     strictly inside AY's refined interval, and **no other z3 root may**.
//!     That is what makes `bq-refine` a differential check and not a
//!     self-consistency check.
//!
//! The other two checks (`bq-select`, `bq-degenerate`) cannot reach z3 at all
//! and say so. Their reference is an exact identity plus an **independent
//! witness**: `bq-select` re-derives the minimal exponent by a brute-force
//! search written over `BigRational` — different arithmetic, different rounding
//! path, no shared code with the `BigInt`-shift implementation under test — and
//! also asks the **negative** half of the certificate, that no simpler dyadic
//! is inside.
//!
//! # Counters
//!
//! `ORefineTrace` is exactly the "stored flag the headline metric is read off"
//! shape. It is handled as the `upoly` lane handled `FactorStats`:
//!
//!   * `end_max_k` is **derived inside `mpbq`** from the returned interval, so
//!     there is no code path that could hardwire it. The check re-derives it
//!     anyway, which costs nothing.
//!   * `steps` is a real counter, pinned by an exact identity computed from the
//!     answer alone: `width_end * 2^steps == width_start`. Hardwiring it to any
//!     constant diverges on the first case with a different true count.
//!   * `bound` is recomputed by the check from `(width_start, target)` through
//!     the facade, and `steps <= bound` is asserted.
//!
//! The disclosed gap: on an `Exact` outcome (a midpoint landed on a dyadic
//! root) the width identity does not apply and `steps` is pinned only by
//! `steps <= bound`.

use std::cmp::Ordering;

use ay_nra::oracle_api::{
    obq_candidate_at, obq_enclose_rational, obq_poly_eval_at, obq_poly_sign_at,
    obq_refine_step_bound, obq_refine_to_width, obq_refine_until_separated, obq_select_int,
    obq_select_non_root, obq_select_small, OBq, OBqInterval, ORefined, OSeparation,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ast, Z3};

/// Maximum denominator exponent the generator draws for a raw dyadic.
const MAX_GEN_K: u32 = 12;

/// Degrees of the planted irrational factors used by the refinement check.
/// `x^2 - d` for a non-square `d` gives a root that no bisection midpoint can
/// ever hit, so the `Narrowed` path is the one that runs.
const IRRATIONALS: [i64; 6] = [2, 3, 5, 6, 7, 10];

/// One generated case for the `mpbq` checks.
pub(crate) struct GenBq {
    /// Two dyadics, as `(numerator, exponent)` before normalization.
    pub(crate) x: (BigInt, u32),
    /// Second dyadic.
    pub(crate) y: (BigInt, u32),
    /// A rational that is deliberately NOT dyadic (odd factor in the
    /// denominator) — the negative control for the representability predicate.
    pub(crate) non_dyadic: BigRational,
    /// A rational that IS dyadic, written unreduced so the predicate has to
    /// reduce rather than pattern-match.
    pub(crate) dyadic: BigRational,
    /// Integer polynomial (low-to-high) with at least one real root.
    pub(crate) poly: Vec<BigInt>,
    /// A second integer polynomial, for the separation check.
    pub(crate) poly2: Vec<BigInt>,
    /// Target width exponent for refinement: the target is `2^-t`.
    pub(crate) target_k: u32,
    /// ODD multiplier applied to the refinement target.
    ///
    /// Without this the target is always `width / 2^target_k` — an EXACT
    /// power-of-two fraction of the width — so the two scaled quantities inside
    /// `refine_step_bound` always differ in bit length by exactly `target_k`,
    /// and the equal-bit-length branch is structurally unreachable from this
    /// corpus. A real off-by-one shipped in that branch precisely because
    /// nothing could reach it. Multiplying the target by an odd `3..=15`
    /// destroys the exact-power-of-two relationship and lets the bit lengths
    /// land equal.
    pub(crate) target_mul: u32,
    /// A raw interval `(lo, hi)` for the selection check — deliberately allowed
    /// to be degenerate.
    pub(crate) iv: ((BigInt, u32), (BigInt, u32)),
    /// Shape label for reporting.
    pub(crate) shape: &'static str,
}

fn bq(a: &(BigInt, u32)) -> OBq {
    OBq::new(a.0.clone(), a.1)
}

/// Draw a case.
///
/// Five shapes, chosen so that the branches a purely random draw would almost
/// never reach are each exercised:
///
/// * `tiny` — exponents 0..2 and small numerators, where `k == 0`, zero, and
///   sign changes all actually occur;
/// * `wide-k` — exponents up to `MAX_GEN_K`, where the shift paths matter;
/// * `straddle` — the interval is built to straddle a **simple** point (an
///   integer or a low-exponent dyadic) while its endpoints carry high
///   precision. This is the only shape where `select_small` and the midpoint
///   DIFFER, so without it the minimality certificate would be vacuous;
/// * `adjacent` — the interval endpoints are consecutive on the `2^-k` grid,
///   the case bisection actually produces, where the simplest interior dyadic
///   IS the midpoint;
/// * `degenerate` — `lo == hi` (written two different ways), `lo > hi`, and
///   zero numerators, so the guards fire.
pub(crate) fn gen_bq(rng: &mut Rng) -> GenBq {
    let shape = match rng.below(5) {
        0 => "tiny",
        1 => "wide-k",
        2 => "straddle",
        3 => "adjacent",
        _ => "degenerate",
    };

    let (x, y) = match shape {
        "tiny" => (
            (
                BigInt::from(rng.range(-6, 6)),
                u32::try_from(rng.below(3)).unwrap_or(0),
            ),
            (
                BigInt::from(rng.range(-6, 6)),
                u32::try_from(rng.below(3)).unwrap_or(0),
            ),
        ),
        _ => (
            (
                BigInt::from(rng.range(-4096, 4096)),
                u32::try_from(rng.below(u64::from(MAX_GEN_K) + 1)).unwrap_or(0),
            ),
            (
                BigInt::from(rng.range(-4096, 4096)),
                u32::try_from(rng.below(u64::from(MAX_GEN_K) + 1)).unwrap_or(0),
            ),
        ),
    };

    // NEGATIVE CONTROL for `is_representable`: an odd denominator factor, so
    // the answer must be `false`. Written with a random even part too, so the
    // predicate cannot pass by only looking at the low bit.
    //
    // THE NUMERATOR MUST NOT BE A MULTIPLE OF `odd`. `BigRational::new`
    // REDUCES, so `18 / (9 * 4)` is `1/2` — a perfectly good dyadic. The first
    // version of this generator missed that and the negative control fired 17
    // times in 2,000 cases against a module that was answering CORRECTLY; the
    // divergences were in the oracle, not in `mpbq`. `odd | n` is exactly the
    // condition under which the odd factor cancels, since the reduced
    // denominator keeps `odd / gcd(odd, n)`.
    let odd = [3i64, 5, 7, 9, 11, 15, 21, 25][usize::try_from(rng.below(8)).unwrap_or(0)];
    let two_part = 1i64 << rng.below(5);
    let mut num = rng.range(1, 200);
    if num % odd == 0 {
        num += 1;
    }
    debug_assert_ne!(num % odd, 0);
    let non_dyadic = BigRational::new(
        BigInt::from(num),
        BigInt::from(odd) * BigInt::from(two_part),
    );
    // POSITIVE control, written unreduced (numerator and denominator share a
    // factor of 2) so the predicate has to reduce.
    let dk = u32::try_from(rng.below(10)).unwrap_or(0);
    let dyadic = BigRational::new(
        BigInt::from(rng.range(-500, 500)) * 2,
        (BigInt::one() << dk) * 2,
    );

    // Integer polynomial: an irrational quadratic times a linear factor, so
    // there is always at least one root a bisection can never hit exactly, and
    // usually a rational root as well.
    let d = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let r = rng.range(-5, 5);
    // (x^2 - d) * (x - r) = x^3 - r x^2 - d x + d r
    let poly = vec![
        BigInt::from(d * r),
        BigInt::from(-d),
        BigInt::from(-r),
        BigInt::one(),
    ];
    let d2 = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let poly2 = vec![BigInt::from(-d2), BigInt::zero(), BigInt::one()];

    let target_k = 1 + u32::try_from(rng.below(24)).unwrap_or(0);
    // Odd, so it can never be absorbed into the power of two.
    let target_mul = 1 + 2 * u32::try_from(rng.below(8)).unwrap_or(0);

    let iv = gen_interval(rng, shape);

    GenBq {
        x,
        y,
        non_dyadic,
        dyadic,
        poly,
        poly2,
        target_k,
        target_mul,
        iv,
        shape,
    }
}

/// Build the raw interval for the selection check, per shape.
fn gen_interval(rng: &mut Rng, shape: &'static str) -> ((BigInt, u32), (BigInt, u32)) {
    match shape {
        "straddle" => {
            // A high-precision pair straddling a low-exponent dyadic. The
            // simple point is `s / 2^sk`; the endpoints sit at exponent
            // `sk + gap` on either side of it.
            let sk = u32::try_from(rng.below(4)).unwrap_or(0);
            let s = BigInt::from(rng.range(-30, 30));
            let gap = 4 + u32::try_from(rng.below(24)).unwrap_or(0);
            let hi_k = sk + gap;
            let centre = &s << gap; // s / 2^sk == centre / 2^hi_k
            let left = 1 + rng.below(1 << 10);
            let right = 1 + rng.below(1 << 10);
            (
                (&centre - BigInt::from(left), hi_k),
                (&centre + BigInt::from(right), hi_k),
            )
        }
        "adjacent" => {
            // Consecutive on the 2^-k grid, exactly what bisection produces.
            let k = u32::try_from(rng.below(u64::from(MAX_GEN_K) + 1)).unwrap_or(0);
            let a = BigInt::from(rng.range(-4096, 4096));
            ((a.clone(), k), (a + 1, k))
        }
        "degenerate" => {
            let k = u32::try_from(rng.below(6)).unwrap_or(0);
            let a = BigInt::from(rng.range(-40, 40));
            match rng.below(3) {
                // lo == hi, written two different ways (`2a / 2^(k+1)`).
                0 => ((&a * 2, k + 1), (a, k)),
                // lo > hi.
                1 => ((&a + BigInt::from(rng.range(1, 20)), k), (a, k)),
                // zero-width at zero.
                _ => ((BigInt::zero(), k), (BigInt::zero(), 0)),
            }
        }
        _ => {
            let k = u32::try_from(rng.below(u64::from(MAX_GEN_K) + 1)).unwrap_or(0);
            let a = BigInt::from(rng.range(-500, 500));
            let w = 1 + rng.below(64);
            ((a.clone(), k), (a + BigInt::from(w), k))
        }
    }
}

fn render_bq(v: &OBq) -> String {
    format!("{}/2^{}", v.numerator(), v.k())
}

fn render_poly(p: &[BigInt]) -> String {
    let parts: Vec<String> = p
        .iter()
        .enumerate()
        .map(|(i, c)| format!("{c}*x^{i}"))
        .collect();
    parts.join(" + ")
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

mod arithmetic;
mod degenerate;
mod growth;
mod refine;
mod select;

pub(crate) use arithmetic::check_arith;
pub(crate) use degenerate::check_degenerate;
pub(crate) use growth::measure_growth;
pub(crate) use refine::check_refine;
pub(crate) use select::check_select;
/// Small extension trait so the check code can ask "is this odd" without
/// pulling `num_integer` into the oracle's check module for one call.
trait IsOdd {
    fn is_odd(&self) -> bool;
}

impl IsOdd for BigInt {
    fn is_odd(&self) -> bool {
        num_integer::Integer::is_odd(self)
    }
}
