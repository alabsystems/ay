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
use crate::z3::Z3;

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
///   * `tiny`      — exponents 0..2 and small numerators, where `k == 0`, zero
///                   and sign changes all actually occur;
///   * `wide-k`    — exponents up to `MAX_GEN_K`, where the shift paths matter;
///   * `straddle`  — the interval is built to straddle a **simple** point
///                   (an integer, or a low-exponent dyadic) while its endpoints
///                   carry high precision. This is the only shape where
///                   `select_small` and the midpoint DIFFER, so without it the
///                   minimality certificate would be vacuous;
///   * `adjacent`  — the interval endpoints are consecutive on the `2^-k` grid,
///                   the case bisection actually produces, where the simplest
///                   interior dyadic IS the midpoint;
///   * `degenerate`— `lo == hi` (written two different ways), `lo > hi`, and
///                   zero numerators, so the guards fire.
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

// ===========================================================================
// Check 1 — `bq-arith`: the dyadic type itself
// ===========================================================================

/// Dyadic arithmetic against **two** independent references.
///
/// 1. **z3**, through `Z3_algebraic_add` / `Z3_algebraic_mul` on the two values
///    as rational numerals: a real differential leg on the arithmetic.
/// 2. **`BigRational`**, a gcd-reduced representation that shares no code and
///    no representation with `a / 2^k`: `add`, `sub`, `mul`, the ordering,
///    `floor`, `ceil` and both shift directions.
///
/// Plus the invariants that are the type's whole contract: canonical form
/// (`k == 0` or numerator odd), structural equality being numeric equality, and
/// the representability predicate with **both** a positive and a negative
/// control. Without the negative control an `is_representable` that returned
/// `true` unconditionally would satisfy every other assertion here — the exact
/// hole this campaign found in `is_irreducible`.
pub(crate) fn check_arith(z3: &Z3, g: &GenBq, sab: Sabotage) -> Outcome {
    let x = bq(&g.x);
    let y = bq(&g.y);
    let (rx, ry) = (x.to_rational(), y.to_rational());
    let mut n = 0u64;

    // --- canonical form -----------------------------------------------------
    for v in [&x, &y] {
        if v.k() > 0 && !v.numerator().is_odd() {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!(
                    "non-canonical: {} has k>0 and an even numerator",
                    render_bq(v)
                ),
                vec![("value".into(), render_bq(v))],
            );
        }
        if v.numerator().is_zero() && v.k() != 0 {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!("non-canonical zero: k = {}", v.k()),
                vec![("value".into(), render_bq(v))],
            );
        }
        n += 2;
    }

    // --- structural equality IS numeric equality ---------------------------
    if (x == y) != (rx == ry) {
        return Divergence::new(
            "bq-arith",
            "identity",
            format!(
                "structural equality {} disagrees with numeric equality {}",
                x == y,
                rx == ry
            ),
            vec![("x".into(), render_bq(&x)), ("y".into(), render_bq(&y))],
        );
    }
    n += 1;

    // --- arithmetic vs BigRational -----------------------------------------
    let mut sum = x.add(&y);
    if sab.on() {
        // Minimal corruption of AY's ANSWER, at the comparison point.
        sum = OBq::new(sum.numerator() + BigInt::one(), sum.k());
    }
    let checks: [(&str, BigRational, BigRational); 3] = [
        ("add", sum.to_rational(), &rx + &ry),
        ("sub", x.sub(&y).to_rational(), &rx - &ry),
        (
            "mul",
            match x.mul(&y) {
                Some(v) => v.to_rational(),
                None => return Outcome::Declined("bq mul exponent overflow"),
            },
            &rx * &ry,
        ),
    ];
    for (name, got, want) in checks {
        if got != want {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!("{name}: AY {got} vs BigRational {want}"),
                vec![("x".into(), render_bq(&x)), ("y".into(), render_bq(&y))],
            );
        }
        n += 1;
    }

    // --- ordering ----------------------------------------------------------
    if x.cmp_bq(&y) != rx.cmp(&ry) {
        return Divergence::new(
            "bq-arith",
            "identity",
            format!(
                "ordering: AY {:?} vs BigRational {:?}",
                x.cmp_bq(&y),
                rx.cmp(&ry)
            ),
            vec![("x".into(), render_bq(&x)), ("y".into(), render_bq(&y))],
        );
    }
    n += 1;

    // --- floor / ceil, including negatives ---------------------------------
    for (v, r) in [(&x, &rx), (&y, &ry)] {
        if v.floor() != r.floor().to_integer() || v.ceil() != r.ceil().to_integer() {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!(
                    "floor/ceil: AY ({}, {}) vs BigRational ({}, {})",
                    v.floor(),
                    v.ceil(),
                    r.floor().to_integer(),
                    r.ceil().to_integer()
                ),
                vec![("value".into(), render_bq(v))],
            );
        }
        n += 2;
    }

    // --- abs / is_int / neg, and the scaled rounding pair ------------------
    // These three were `tests only` in the coverage audit: exercised by the
    // unit tests but by no differential check, which is a weaker form of the
    // "entry point no check ever calls" pattern. They are pinned here against
    // `BigRational` so a wrong answer cannot survive a fuzz campaign.
    for (v, r) in [(&x, &rx), (&y, &ry)] {
        if v.abs().to_rational() != r.abs() {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!(
                    "abs: AY {} vs BigRational {}",
                    v.abs().to_rational(),
                    r.abs()
                ),
                vec![("value".into(), render_bq(v))],
            );
        }
        if v.neg().to_rational() != -r.clone() {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!(
                    "neg: AY {} vs BigRational {}",
                    v.neg().to_rational(),
                    -r.clone()
                ),
                vec![("value".into(), render_bq(v))],
            );
        }
        if v.is_int() != r.is_integer() {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!(
                    "is_int: AY {} vs BigRational {}",
                    v.is_int(),
                    r.is_integer()
                ),
                vec![("value".into(), render_bq(v))],
            );
        }
        // `floor_at` / `ceil_at` at several target precisions, against scaling
        // the rational and rounding it. In an honest run these are otherwise
        // reached only indirectly, through `candidate_at`.
        for t in [0u32, 1, 5, 20] {
            let scaled = r * BigRational::from(BigInt::one() << t);
            if v.floor_at(t) != scaled.floor().to_integer()
                || v.ceil_at(t) != scaled.ceil().to_integer()
            {
                return Divergence::new(
                    "bq-arith",
                    "identity",
                    format!(
                        "floor_at/ceil_at at 2^{t}: AY ({}, {}) vs BigRational ({}, {})",
                        v.floor_at(t),
                        v.ceil_at(t),
                        scaled.floor().to_integer(),
                        scaled.ceil().to_integer()
                    ),
                    vec![("value".into(), render_bq(v))],
                );
            }
            n += 2;
        }
        n += 3;
    }

    // --- shifts by powers of two, both directions --------------------------
    for e in [0u32, 1, 3, 17] {
        let up = x.mul_two_pow(e);
        let Some(down) = x.div_two_pow(e) else {
            return Outcome::Declined("bq div_two_pow exponent overflow");
        };
        let two_e = BigRational::from(BigInt::one() << e);
        if up.to_rational() != &rx * &two_e || down.to_rational() != &rx / &two_e {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!("shift by 2^{e} is not exact"),
                vec![("x".into(), render_bq(&x))],
            );
        }
        // The property the layer exists for: `k` moves by at most `e`, never
        // more, and multiplying can only lower it.
        if up.k() > x.k() || down.k() > x.k() + e {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!(
                    "shift by 2^{e} moved k out of bounds: {} -> up {} / down {}",
                    x.k(),
                    up.k(),
                    down.k()
                ),
                vec![("x".into(), render_bq(&x))],
            );
        }
        // Round trip.
        if down.mul_two_pow(e) != x {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!("div then mul by 2^{e} is not the identity"),
                vec![("x".into(), render_bq(&x))],
            );
        }
        n += 4;
    }

    // --- representability: POSITIVE and NEGATIVE controls ------------------
    if !OBq::is_representable(&g.dyadic) {
        return Divergence::new(
            "bq-arith",
            "identity",
            format!("dyadic {} was rejected as non-representable", g.dyadic),
            vec![("r".into(), g.dyadic.to_string())],
        );
    }
    match OBq::from_rational(&g.dyadic) {
        Some(v) if v.to_rational() == g.dyadic => n += 1,
        other => {
            return Divergence::new(
                "bq-arith",
                "identity",
                format!("from_rational({}) round-trip failed: {:?}", g.dyadic, other),
                vec![("r".into(), g.dyadic.to_string())],
            )
        }
    }
    if OBq::is_representable(&g.non_dyadic) || OBq::from_rational(&g.non_dyadic).is_some() {
        return Divergence::new(
            "bq-arith",
            "identity",
            format!("non-dyadic {} was accepted as representable", g.non_dyadic),
            vec![("r".into(), g.non_dyadic.to_string())],
        );
    }
    n += 2;

    // --- the z3 leg: exact arithmetic on the same two values ---------------
    let ax = z3.rational(&rx);
    let ay = z3.rational(&ry);
    if z3.errored() {
        return Outcome::Skipped("z3 could not build the numerals");
    }
    let z_sum = z3.add(ax, ay);
    let z_prod = z3.mul(ax, ay);
    if z3.errored() {
        return Outcome::Skipped("z3 errored on algebraic add/mul");
    }
    let (Some(zs), Some(zp)) = (z3.numeral_value(z_sum), z3.numeral_value(z_prod)) else {
        return Outcome::Skipped("z3 did not return numerals");
    };
    if sum.to_rational() != zs {
        return Divergence::new(
            "bq-arith",
            "z3",
            format!("add: AY {} vs z3 {}", sum.to_rational(), zs),
            vec![("x".into(), render_bq(&x)), ("y".into(), render_bq(&y))],
        );
    }
    let prod = match x.mul(&y) {
        Some(v) => v,
        None => return Outcome::Declined("bq mul exponent overflow"),
    };
    if prod.to_rational() != zp {
        return Divergence::new(
            "bq-arith",
            "z3",
            format!("mul: AY {} vs z3 {}", prod.to_rational(), zp),
            vec![("x".into(), render_bq(&x)), ("y".into(), render_bq(&y))],
        );
    }
    n += 2;

    Outcome::Match(n)
}

// ===========================================================================
// Check 2 — `bq-refine`: the loop nlsat calls most
// ===========================================================================

/// Refinement of an isolating interval, checked against **z3's own root**.
///
/// The differential content: z3 isolates the roots of the same integer
/// polynomial; AY refines a dyadic interval around one of them; then
/// `Z3_algebraic_lt` / `Z3_algebraic_gt` are asked whether z3's root is strictly
/// inside AY's refined interval, and whether any of z3's **other** roots is.
/// A refinement that drifts off the root, or that keeps two roots, is caught by
/// z3 rather than by AY's own arithmetic.
///
/// The self-consistency content, which z3 cannot supply: the exact width
/// identity that pins `steps`, the recomputed liveness bound, the derived
/// `end_max_k`, and the endpoint sign invariant.
pub(crate) fn check_refine(z3: &Z3, g: &GenBq, sab: Sabotage) -> Outcome {
    let coeffs: Vec<BigRational> = g
        .poly
        .iter()
        .map(|c| BigRational::from(c.clone()))
        .collect();
    let Some(roots) = z3.roots(&coeffs) else {
        return Outcome::Skipped("z3 declined to isolate roots");
    };
    if roots.is_empty() {
        return Outcome::Skipped("no real roots");
    }

    let mut n = 0u64;
    let mut ran = false;

    // (0) `refine_step_bound` IS A PURE FUNCTION — test it as one, on the
    //     generator's ARBITRARY dyadics, not only on widths that happen to
    //     arise from root brackets.
    //
    // This leg exists because a real off-by-one shipped in the equal-bit-length
    // branch and nothing could reach it. Reaching it through the refinement
    // path is structurally impossible, not merely unlikely: a bracket-derived
    // width has a power-of-two numerator, and for `wa = 1` the two scaled bit
    // lengths differ by exactly 1 for EVERY target of the form
    // `width * (2^j - 1)/2^j`. Two earlier attempts to reach it by reshaping
    // the target failed for that reason — measured, 128 of 128 pairs unequal.
    // Arbitrary `(x, y)` pairs have no such structure.
    //
    // The asserted property is SUFFICIENCY, stated in arithmetic that does not
    // call the function under test: `width / 2^bound <= target`. Minimality is
    // deliberately NOT asserted — the bound comes from bit lengths and can
    // overshoot the true minimum by one, and asserting it produced 64
    // divergences in 2,000 cases against correct code.
    {
        let (a, b) = (
            OBq::new(g.x.0.clone(), g.x.1),
            OBq::new(g.y.0.clone(), g.y.1),
        );
        // Order them so the wider one is the width and both are positive.
        let (wide, narrow) = if a.cmp_bq(&b) == std::cmp::Ordering::Greater {
            (a, b)
        } else {
            (b, a)
        };
        if narrow.sign() > 0 && wide.cmp_bq(&narrow) == std::cmp::Ordering::Greater {
            if let Some(bound) = obq_refine_step_bound(&wide, &narrow) {
                n += 1;
                match wide.div_two_pow(bound) {
                    Some(shrunk) if shrunk.cmp_bq(&narrow) != std::cmp::Ordering::Greater => {}
                    _ => {
                        return Divergence::new(
                            "bq-refine",
                            "identity",
                            format!(
                                "step bound {bound} is INSUFFICIENT: width/2^{bound} still \
                                 exceeds the target"
                            ),
                            vec![
                                (
                                    "width".into(),
                                    format!("{}/2^{}", wide.numerator(), wide.k()),
                                ),
                                (
                                    "target".into(),
                                    format!("{}/2^{}", narrow.numerator(), narrow.k()),
                                ),
                            ],
                        );
                    }
                }
            }
        }
    }

    // Bracket each z3 root in rationals, then move that bracket onto the dyadic
    // grid WITHOUT narrowing it (`enclose_rational` rounds outward).
    for (idx, &root) in roots.iter().enumerate() {
        let Some((rlo, rhi)) = z3.bracket(root, 40) else {
            continue;
        };
        // z3 reports an EXACT rational root by returning the value twice.
        //
        // The first version of this check skipped those, and that made
        // `Refined::Exact` — a whole arm of the function under test —
        // unreachable. MEASURED with a temporary `eprintln!` in that arm:
        // **0 hits across 40,000 fuzz cases at two seeds**. The generated
        // polynomial `(x^2 - d)(x - r)` always has the integer root `r`, so the
        // arm was not merely rare, it was structurally excluded.
        //
        // Instead, build a SYMMETRIC dyadic bracket `(r - 2^-j, r + 2^-j)`
        // around it. Its first midpoint is exactly `r`, so the exact-root arm
        // runs on the very first bisection.
        if rlo == rhi {
            let Some(centre) = OBq::from_rational(&rlo) else {
                // A non-dyadic rational root cannot be hit by any midpoint;
                // there is nothing for the exact arm to find.
                continue;
            };
            let mut sym = None;
            for j in 0..=24u32 {
                let d = OBq::inv_two_pow(j);
                let Some(cand) = OBqInterval::new(&centre.sub(&d), &centre.add(&d)) else {
                    continue;
                };
                match (
                    obq_poly_sign_at(&g.poly, &cand.lo()),
                    obq_poly_sign_at(&g.poly, &cand.hi()),
                ) {
                    (Some(a), Some(b)) if a != 0 && b != 0 => {}
                    _ => continue,
                }
                let lo_ast = z3.rational(&cand.lo().to_rational());
                let hi_ast = z3.rational(&cand.hi().to_rational());
                if z3.errored() {
                    return Outcome::Skipped("z3 could not build endpoint numerals");
                }
                let inside: Vec<usize> = roots
                    .iter()
                    .enumerate()
                    .filter(|(_, &r)| z3.lt(lo_ast, r) && z3.lt(r, hi_ast))
                    .map(|(i, _)| i)
                    .collect();
                if inside == vec![idx] {
                    sym = Some(cand);
                    break;
                }
            }
            let Some(iv) = sym else {
                continue;
            };
            // A target the first bisection cannot already satisfy.
            let Some(target) = iv.width().div_two_pow(g.target_k) else {
                return Outcome::Declined("target underflow");
            };
            let Some((out, trace)) = obq_refine_to_width(&g.poly, &iv, &target) else {
                return Outcome::Declined("refine_to_width declined on the exact-root bracket");
            };
            ran = true;
            let ORefined::Exact(v) = out else {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    "a symmetric bracket around an exact dyadic root did not report Exact".into(),
                    vec![
                        ("poly".into(), render_poly(&g.poly)),
                        ("root".into(), render_bq(&centre)),
                    ],
                );
            };
            if v != centre {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!(
                        "Exact reported {} but the root is {}",
                        render_bq(&v),
                        render_bq(&centre)
                    ),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            if obq_poly_sign_at(&g.poly, &v) != Some(0) {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!(
                        "claimed exact root {} does not zero the polynomial",
                        render_bq(&v)
                    ),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            // z3 must agree it is exactly this value.
            let ast = z3.rational(&v.to_rational());
            if z3.errored() {
                return Outcome::Skipped("z3 could not build the exact-root numeral");
            }
            if !z3.eq(ast, root) {
                return Divergence::new(
                    "bq-refine",
                    "z3",
                    format!("AY says the root is exactly {}", render_bq(&v)),
                    vec![
                        ("poly".into(), render_poly(&g.poly)),
                        ("z3 root".into(), z3.ast_string(root)),
                    ],
                );
            }
            // The midpoint of a symmetric bracket IS the centre, so the arm must
            // fire on step one. Pinning this is what stops the check from
            // silently going back to never reaching the arm.
            if trace.steps != 1 {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!("exact root found after {} steps, expected 1", trace.steps),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            if trace.end_max_k != v.k() {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!(
                        "end_max_k {} != the exact root's k {}",
                        trace.end_max_k,
                        v.k()
                    ),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            n += 5;
            continue;
        }
        // THE COARSEST isolating dyadic enclosure, not the tightest.
        //
        // This is where an earlier version of this check was BLIND. It enclosed
        // z3's own bracket at exponent 48; `z3.bracket(root, 40)` already
        // returns something narrower than `2^-40`, and the targets drawn here
        // are `2^-1 .. 2^-24`, so `refine_to_width` met the target on entry and
        // performed **zero bisections in every case**. The loop body under test
        // never executed. Measured: an injected defect that keeps the WRONG
        // half of every bisection produced 0 divergences over 193 `bq-refine`
        // cases.
        //
        // So: walk the grid from coarse to fine and take the FIRST exponent
        // whose outward-rounded enclosure still isolates exactly this root.
        // That is the interval a real CAD would start from, and it leaves the
        // refinement genuine work to do.
        let mut iv = None;
        for k in 0..=48u32 {
            let Some(cand) = obq_enclose_rational(&rlo, &rhi, k) else {
                continue;
            };
            // The endpoints must not themselves be roots. A coarse enclosure
            // rounds onto integers, and the generated polynomial
            // `(x^2 - d)(x - r)` has an INTEGER root `r`, so an endpoint landing
            // exactly on it is common — the interval is then not isolating in
            // the module's sense and `refine_to_width` correctly declines.
            // Measured before this filter: 480 of 1,290 `bq-refine` cases
            // (37.2%) declined for exactly this reason, i.e. more than a third
            // of the corpus was testing the entry guard instead of the loop.
            match (
                obq_poly_sign_at(&g.poly, &cand.lo()),
                obq_poly_sign_at(&g.poly, &cand.hi()),
            ) {
                (Some(a), Some(b)) if a != 0 && b != 0 => {}
                _ => continue,
            }
            let lo_ast = z3.rational(&cand.lo().to_rational());
            let hi_ast = z3.rational(&cand.hi().to_rational());
            if z3.errored() {
                return Outcome::Skipped("z3 could not build endpoint numerals");
            }
            let inside: Vec<usize> = roots
                .iter()
                .enumerate()
                .filter(|(_, &r)| z3.lt(lo_ast, r) && z3.lt(r, hi_ast))
                .map(|(i, _)| i)
                .collect();
            if inside == vec![idx] {
                iv = Some(cand);
                break;
            }
        }
        let Some(iv) = iv else {
            continue;
        };

        // The target is derived from the ACTUAL starting width, so the loop
        // always has at least `target_k` bisections to perform. A fixed
        // absolute target is what let the previous version measure nothing.
        let Some(base_target) = iv.width().div_two_pow(g.target_k) else {
            return Outcome::Declined("target underflow");
        };
        // Scale by an ODD multiplier so the target is not an exact power-of-two
        // fraction of the width — see `GenBq::target_mul`. Kept strictly below
        // the width so at least one bisection is still mandatory.
        // Two target shapes, and the second one is load-bearing.
        //
        // `target_mul` odd breaks the exact-power-of-two relationship, but on
        // its own it only RARELY lands the two scaled quantities at equal bit
        // length — that needs `width / target` in `[1, 2)`, which the uniform
        // `(target_k, target_mul)` draw hits a few percent of the time. So one
        // case in four constructs it directly: `target = width * (2^j - 1)/2^j`
        // for `j` in 2..=4 gives ratios 4/3, 8/7 and 16/15, all inside `[1, 2)`.
        //
        // Without this the equal-bit-length branch of `refine_step_bound` is
        // structurally unreachable from the corpus, and a real off-by-one
        // shipped in it precisely because nothing could reach it.
        let w = iv.width();
        let target = if g.target_mul % 4 == 1 {
            let j = 2 + (g.target_k % 3);
            match w.div_two_pow(j) {
                Some(sliver) => {
                    let t = w.sub(&sliver);
                    if t.sign() > 0 && t.cmp_bq(&w) == std::cmp::Ordering::Less {
                        t
                    } else {
                        base_target
                    }
                }
                None => base_target,
            }
        } else {
            let mul = OBq::new(BigInt::from(g.target_mul), 0);
            match base_target.mul(&mul) {
                Some(scaled) if scaled.cmp_bq(&w) == std::cmp::Ordering::Less => scaled,
                _ => base_target,
            }
        };
        let Some(bound) = obq_refine_step_bound(&iv.width(), &target) else {
            return Outcome::Declined("refine_step_bound declined");
        };
        // THE BOUND IS CERTIFIED, NOT RECOMPUTED.
        //
        // The comparison above calls the SAME `refine_step_bound` and checks it
        // against itself, so it is a tautology: a verifier inflated the bound to
        // `(lb - rb + 1) * 3 + 11` and got 0 divergences over 4,000 cases, then
        // DEFLATED it to `lb - rb` — one step too few in general — and got 0
        // divergences again. The bound's sufficiency was never tested in either
        // direction, which is how a real off-by-one shipped in it.
        //
        // These two legs state the property directly, in arithmetic that does
        // not go through the function under test:
        //   SUFFICIENT — `width / 2^bound <= target`
        //   MINIMAL    — `width / 2^(bound-1) >  target`   (when bound >= 1)
        let w0 = iv.width();
        n += 1;
        match w0.div_two_pow(bound) {
            Some(shrunk) if shrunk.cmp_bq(&target) != std::cmp::Ordering::Greater => {}
            _ => {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!(
                        "step bound {bound} is INSUFFICIENT: width/2^{bound} still exceeds the \
                         target"
                    ),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
        }
        // MINIMALITY IS DELIBERATELY NOT ASSERTED. The bound is derived from
        // BIT LENGTHS, which is conservative: `bits(L) - bits(R) + 1` can
        // overshoot the true minimum by one whenever `L` and `R` sit at
        // opposite ends of their respective binades. Measured: asserting
        // `width/2^(bound-1) > target` produced 64 divergences in 2,000 cases
        // on correct code. The function documents an upper bound that is
        // REACHED, not a least one, so sufficiency above is the whole contract.
        let Some((out, trace)) = obq_refine_to_width(&g.poly, &iv, &target) else {
            return Outcome::Declined("refine_to_width declined");
        };
        ran = true;

        // The recomputed liveness bound.
        if trace.bound != bound || trace.steps > trace.bound {
            return Divergence::new(
                "bq-refine",
                "identity",
                format!(
                    "step bound: trace {} / recomputed {} / steps {}",
                    trace.bound, bound, trace.steps
                ),
                vec![("poly".into(), render_poly(&g.poly))],
            );
        }
        // THE LOOP BODY MUST HAVE RUN. The target is `width / 2^target_k` with
        // `target_k >= 1`, so at least one bisection is mandatory. Asserting it
        // turns "the refinement was exercised" from an assumption into a
        // checked property — the exact assumption that was silently false
        // before.
        if trace.steps == 0 {
            return Divergence::new(
                "bq-refine",
                "identity",
                format!(
                    "zero bisections for target width/2^{}: the loop under test did not run",
                    g.target_k
                ),
                vec![
                    ("poly".into(), render_poly(&g.poly)),
                    ("start width".into(), render_bq(&iv.width())),
                    ("target".into(), render_bq(&target)),
                ],
            );
        }
        n += 3;

        let refined = match out {
            ORefined::Exact(v) => {
                // A dyadic root. z3 must agree it is exactly this value.
                let ast = z3.rational(&v.to_rational());
                if z3.errored() {
                    return Outcome::Skipped("z3 could not build the exact-root numeral");
                }
                if !z3.eq(ast, root) {
                    return Divergence::new(
                        "bq-refine",
                        "z3",
                        format!("AY says the root is exactly {}", render_bq(&v)),
                        vec![
                            ("poly".into(), render_poly(&g.poly)),
                            ("z3 root".into(), z3.ast_string(root)),
                        ],
                    );
                }
                if obq_poly_sign_at(&g.poly, &v) != Some(0) {
                    return Divergence::new(
                        "bq-refine",
                        "identity",
                        format!(
                            "claimed exact root {} does not zero the polynomial",
                            render_bq(&v)
                        ),
                        vec![("poly".into(), render_poly(&g.poly))],
                    );
                }
                n += 2;
                continue;
            }
            ORefined::Narrowed(iv2) => iv2,
        };

        // Sabotage: shift the refined interval by one grid step, so the root
        // falls outside. Applied to AY's ANSWER, at the comparison point.
        let refined = if sab.on() {
            let step = OBq::inv_two_pow(refined.max_k());
            match OBqInterval::new(&refined.lo().add(&step), &refined.hi().add(&step)) {
                Some(v) => v,
                None => refined,
            }
        } else {
            refined
        };

        // --- THE z3 LEG, FIRST ---------------------------------------------
        // Consulted before the self-consistency identities on purpose: z3 is
        // the stronger reference, so when both would fire the report should
        // name z3. (Measured: with an injected defect that keeps the wrong
        // half of every bisection, this leg alone catches 52/52.)
        let lo2 = z3.rational(&refined.lo().to_rational());
        let hi2 = z3.rational(&refined.hi().to_rational());
        if z3.errored() {
            return Outcome::Skipped("z3 could not build refined endpoints");
        }
        if !z3.lt(lo2, root) || !z3.gt(hi2, root) {
            return Divergence::new(
                "bq-refine",
                "z3",
                format!(
                    "z3's root is NOT inside AY's refined interval ({}, {})",
                    render_bq(&refined.lo()),
                    render_bq(&refined.hi())
                ),
                vec![
                    ("poly".into(), render_poly(&g.poly)),
                    ("z3 root".into(), z3.ast_string(root)),
                    ("target".into(), format!("width/2^{}", g.target_k)),
                ],
            );
        }
        // No OTHER z3 root may be inside: refinement must not lose isolation.
        for (j, &other) in roots.iter().enumerate() {
            if j != idx && z3.lt(lo2, other) && z3.lt(other, hi2) {
                return Divergence::new(
                    "bq-refine",
                    "z3",
                    format!("root #{j} is also inside AY's refined interval for root #{idx}"),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            n += 1;
        }
        n += 2;

        // --- the exact width identity that pins `steps` --------------------
        if !sab.on() {
            if refined.width().mul_two_pow(trace.steps) != iv.width() {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!(
                        "steps {} does not reproduce the width: {} * 2^{} != {}",
                        trace.steps,
                        render_bq(&refined.width()),
                        trace.steps,
                        render_bq(&iv.width())
                    ),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            if trace.end_max_k != refined.max_k() {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!("end_max_k {} != {}", trace.end_max_k, refined.max_k()),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            if refined.width().cmp_bq(&target) == Ordering::Greater {
                return Divergence::new(
                    "bq-refine",
                    "identity",
                    format!(
                        "target not met: width {} > target {}",
                        render_bq(&refined.width()),
                        render_bq(&target)
                    ),
                    vec![("poly".into(), render_poly(&g.poly))],
                );
            }
            // Endpoint signs must still bracket.
            let (s_lo, s_hi) = (
                obq_poly_sign_at(&g.poly, &refined.lo()),
                obq_poly_sign_at(&g.poly, &refined.hi()),
            );
            match (s_lo, s_hi) {
                (Some(a), Some(b)) if a != 0 && b != 0 && a != b => n += 1,
                _ => {
                    return Divergence::new(
                        "bq-refine",
                        "identity",
                        format!("refined endpoints no longer bracket: {s_lo:?} / {s_hi:?}"),
                        vec![("poly".into(), render_poly(&g.poly))],
                    )
                }
            }
            n += 3;
        }
    }

    if !ran {
        return Outcome::Skipped("no usable isolating enclosure");
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 3 — `bq-select`: minimality, with the negative half
// ===========================================================================

/// An INDEPENDENT minimal-exponent search, written over `BigRational`.
///
/// Shares no code and no representation with `mpbq`'s `BigInt`-shift
/// implementation: it scales by a rational `2^k`, rounds with `BigRational`'s
/// own `floor`/`ceil`, and compares as rationals. If both agree on the minimal
/// `k` for thousands of intervals, the shift arithmetic and the rounding are
/// pinned together.
fn witness_min_k(lo: &BigRational, hi: &BigRational, ceiling: u32) -> Option<(u32, BigInt)> {
    for k in 0..=ceiling {
        let scale = BigRational::from(BigInt::one() << k);
        let ls = lo * &scale;
        let hs = hi * &scale;
        let m0: BigInt = ls.floor().to_integer() + 1;
        let m1: BigInt = hs.ceil().to_integer() - 1;
        if m0 > m1 {
            continue;
        }
        let pick = if m0.is_positive() {
            m0
        } else if m1.is_negative() {
            m1
        } else {
            BigInt::zero()
        };
        return Some((k, pick));
    }
    None
}

/// A point strictly inside the interval whose exponent is **strictly greater**
/// than `v`'s — a valid but non-minimal answer, which is exactly the defect
/// `select_small` can have.
///
/// It exists at `j = width.k() + 2`: at that scale the interval spans at least
/// four grid units, so it contains at least three interior integers and hence
/// at least one **odd** one, and an odd numerator survives normalization with
/// its exponent intact. Since `select_small`'s own answer has
/// `k <= width.k() + 1`, that `j` is always strictly larger.
fn sabotage_point(iv: &OBqInterval, v: &OBq) -> Option<OBq> {
    let top = (iv.width().k() + 2).max(v.k() + 3);
    for j in (v.k() + 1)..=top {
        let m0: BigInt = iv.lo().floor_at(j) + 1;
        let m1: BigInt = iv.hi().ceil_at(j) - 1;
        if m0 > m1 {
            continue;
        }
        let cand = if m0.is_odd() {
            m0.clone()
        } else {
            m0.clone() + 1
        };
        if cand <= m1 {
            let out = OBq::new(cand, j);
            if out.k() > v.k() && iv.contains_open(&out) {
                return Some(out);
            }
        }
    }
    None
}

/// `select_small` / `select_int` / `select_non_root`.
///
/// z3's dyadic layer is not reachable (see the module header), so the reference
/// is an exact identity plus two independent witnesses:
///
///   * **containment**, checked in `BigRational`;
///   * **minimality, both halves**. The positive half is that the answer sits
///     at exponent `k`. The negative half — the one that stops the check from
///     being satisfiable by "always return the midpoint" — is that
///     `candidate_at(iv, j)` is `None` for **every** `j < k`. The `straddle`
///     shape exists so that a simpler point genuinely does exist most of the
///     time; on the `adjacent` shape the midpoint IS the minimal answer and the
///     certificate is trivially satisfied, which is why the shape counts are
///     reported.
///   * an **independent minimal-`k` search over `BigRational`**
///     ([`witness_min_k`]), which must return the same `k` and the same value.
/// The interval `(-hi, -lo)` — the mirror image of `iv` through zero.
fn mirror_interval(iv: &OBqInterval) -> OBqInterval {
    OBqInterval::new(&iv.hi().neg(), &iv.lo().neg()).expect("negation reverses a strict order")
}

/// `p(-x)`: negate every odd-degree coefficient.
fn mirror_poly(p: &[BigInt]) -> Vec<BigInt> {
    p.iter()
        .enumerate()
        .map(|(i, c)| if i % 2 == 1 { -c.clone() } else { c.clone() })
        .collect()
}

pub(crate) fn check_select(g: &GenBq, sab: Sabotage) -> Outcome {
    let lo = bq(&g.iv.0);
    let hi = bq(&g.iv.1);
    let Some(iv) = OBqInterval::new(&lo, &hi) else {
        // The degenerate shapes land here; `bq-degenerate` is where they are
        // asserted, not merely tolerated.
        return Outcome::Skipped("interval is empty or inverted");
    };
    let mut n = 0u64;

    let Some((value, ceiling)) = obq_select_small(&iv) else {
        return Outcome::Declined("select_small declined");
    };
    // Sabotage: return a point that is INSIDE and correct in every respect
    // except simplicity — one grid step finer than it had to be. Containment,
    // the ceiling test and every other assertion still pass; only the
    // minimality certificate and the independent witness can see it.
    //
    // The first attempt here was "return the midpoint", which caught only
    // 69.2% (18/26): on a bisection-produced interval the midpoint already IS
    // the minimal answer, so the corruption was a no-op on that whole shape.
    // [`sabotage_point`] is constructed to always raise the exponent.
    let value = if sab.on() {
        sabotage_point(&iv, &value).unwrap_or(value)
    } else {
        value
    };

    // --- containment, in the other representation --------------------------
    let (rlo, rhi, rv) = (lo.to_rational(), hi.to_rational(), value.to_rational());
    if !(rlo < rv && rv < rhi) {
        return Divergence::new(
            "bq-select",
            "identity",
            format!(
                "selected {} is not strictly inside ({rlo}, {rhi})",
                render_bq(&value)
            ),
            vec![("lo".into(), render_bq(&lo)), ("hi".into(), render_bq(&hi))],
        );
    }
    if !iv.contains_open(&value) {
        return Divergence::new(
            "bq-select",
            "identity",
            "contains_open disagrees with the BigRational comparison".into(),
            vec![("lo".into(), render_bq(&lo)), ("hi".into(), render_bq(&hi))],
        );
    }
    n += 2;

    // --- the derived ceiling -----------------------------------------------
    if ceiling != iv.width().k() + 1 {
        return Divergence::new(
            "bq-select",
            "identity",
            format!("ceiling {ceiling} != width.k()+1 = {}", iv.width().k() + 1),
            vec![("width".into(), render_bq(&iv.width()))],
        );
    }
    if value.k() > ceiling {
        return Divergence::new(
            "bq-select",
            "identity",
            format!(
                "answer exponent {} exceeds the derived ceiling {ceiling}",
                value.k()
            ),
            vec![("lo".into(), render_bq(&lo)), ("hi".into(), render_bq(&hi))],
        );
    }
    n += 2;

    // --- MINIMALITY: the negative half -------------------------------------
    for j in 0..value.k() {
        if let Some(m) = obq_candidate_at(&iv, j) {
            return Divergence::new(
                "bq-select",
                "identity",
                format!(
                    "NOT minimal: answered k={} but {}/2^{j} is inside",
                    value.k(),
                    m
                ),
                vec![("lo".into(), render_bq(&lo)), ("hi".into(), render_bq(&hi))],
            );
        }
        n += 1;
    }

    // --- the independent BigRational witness -------------------------------
    match witness_min_k(&rlo, &rhi, ceiling) {
        Some((wk, wm)) => {
            if wk != value.k() || OBq::new(wm.clone(), wk) != value {
                return Divergence::new(
                    "bq-select",
                    "identity",
                    format!(
                        "witness picked {wm}/2^{wk}, AY picked {}",
                        render_bq(&value)
                    ),
                    vec![("lo".into(), render_bq(&lo)), ("hi".into(), render_bq(&hi))],
                );
            }
            n += 2;
        }
        None => {
            return Divergence::new(
                "bq-select",
                "identity",
                format!(
                    "the independent witness found NO dyadic below the derived ceiling {ceiling}, \
                     but AY answered {}",
                    render_bq(&value)
                ),
                vec![("lo".into(), render_bq(&lo)), ("hi".into(), render_bq(&hi))],
            )
        }
    }

    // --- select_int agrees with the exponent-0 candidate -------------------
    if obq_select_int(&lo, &hi) != obq_candidate_at(&iv, 0) {
        return Divergence::new(
            "bq-select",
            "identity",
            "select_int disagrees with candidate_at(iv, 0)".into(),
            vec![("lo".into(), render_bq(&lo)), ("hi".into(), render_bq(&hi))],
        );
    }
    n += 1;

    // --- select_non_root: THE ADVERSARIAL POLYNOMIAL ------------------------
    //
    // `g.poly` is a degree-3 `(x^2 - d)(x - r)`. It has far fewer roots than the
    // scan has probe levels, so the scan never runs out of candidates and a
    // truncated walk is invisible. A verifier proved it: injecting an
    // unconditional `return None` on every wholly-negative interval produced 0
    // divergences and 0 declines over 6,000 cases.
    //
    // So this leg builds a polynomial whose roots sit EXACTLY on the dyadic
    // points the scan probes inside `iv` — the only shape that can exhaust it —
    // and requires an answer anyway, because the interval always holds more
    // interior dyadics than the polynomial has roots.
    //
    // It is run on BOTH `iv` and its mirror image. The shipped defect was an
    // ASYMMETRY: the walk started at the interior integer closest to zero and
    // stepped only upward, which has room on a positive interval and none on a
    // negative one, so the negative side made a single probe per level instead
    // of `deg + 1`.
    {
        let lo_i = iv.lo().floor_at(0) + BigInt::from(1);
        let hi_i = iv.hi().ceil_at(0) - BigInt::from(1);
        if lo_i <= hi_i {
            // Plant a root at the FIRST PROBE of every level, for as many
            // levels as the scan will visit.
            //
            // The scan's ceiling is `wk + 1 + bits(deg + 2)`, so planting `r`
            // roots pushes the ceiling to about `wk + 5` — it grows like
            // log(deg) while the roots grow linearly, which is why this
            // converges instead of chasing itself. Covering levels `0..=wk+5`
            // with one root each is therefore enough to exhaust a walk that
            // probes ONCE per level.
            //
            // The first probe is the interior candidate closest to zero: `m0`
            // on a positive interval, `m1` on a negative one. Two earlier
            // versions of this leg missed the defect — one planted from the
            // smallest candidate upward, the other covered only four levels —
            // and both left the truncated walk with an unplanted level to
            // succeed at.
            let wk = iv.width().k();
            let levels = (wk + 5).min(10);
            let mut adv: Vec<BigInt> = vec![BigInt::from(1)];
            let mut planted = 0u32;
            for jj in 0u32..=levels {
                let a0 = iv.lo().floor_at(jj) + BigInt::from(1);
                let a1 = iv.hi().ceil_at(jj) - BigInt::from(1);
                if a0 > a1 {
                    continue;
                }
                // closest to zero
                let m = if a1 <= BigInt::from(0) {
                    a1.clone()
                } else if a0 >= BigInt::from(0) {
                    a0.clone()
                } else {
                    BigInt::from(0)
                };
                let scale = BigInt::from(1i64) << jj;
                let f = [-m, scale];
                let mut out = vec![BigInt::from(0); adv.len() + 1];
                for (i2, c) in adv.iter().enumerate() {
                    out[i2] += c * &f[0];
                    out[i2 + 1] += c * &f[1];
                }
                adv = out;
                planted += 1;
            }
            if planted > 0 {
                for (label, interval) in [("iv", iv.clone()), ("mirror", mirror_interval(&iv))] {
                    let poly = if label == "mirror" {
                        mirror_poly(&adv)
                    } else {
                        adv.clone()
                    };
                    n += 1;
                    match obq_select_non_root(&poly, &interval) {
                        Some(v) => {
                            if !interval.contains_open(&v) || obq_poly_sign_at(&poly, &v) == Some(0)
                            {
                                return Divergence::new(
                                    "bq-select",
                                    "identity",
                                    format!(
                                        "select_non_root on the adversarial polynomial ({label}) \
                                         returned {} — outside, or a root",
                                        render_bq(&v)
                                    ),
                                    vec![("poly".into(), render_poly(&poly))],
                                );
                            }
                        }
                        None => {
                            return Divergence::new(
                                "bq-select",
                                "identity",
                                format!(
                                    "select_non_root DECLINED on the {label} interval: the scan \
                                     has more probe levels than the polynomial has roots, so a \
                                     non-root exists"
                                ),
                                vec![("poly".into(), render_poly(&poly))],
                            );
                        }
                    }
                }
            }
        }
    }

    // --- select_non_root ---------------------------------------------------
    if let Some(v) = obq_select_non_root(&g.poly, &iv) {
        if !iv.contains_open(&v) {
            return Divergence::new(
                "bq-select",
                "identity",
                format!(
                    "select_non_root returned {} outside the interval",
                    render_bq(&v)
                ),
                vec![("poly".into(), render_poly(&g.poly))],
            );
        }
        match obq_poly_sign_at(&g.poly, &v) {
            Some(0) | None => {
                return Divergence::new(
                    "bq-select",
                    "identity",
                    format!("select_non_root returned the ROOT {}", render_bq(&v)),
                    vec![("poly".into(), render_poly(&g.poly))],
                )
            }
            Some(_) => n += 2,
        }
        // The value it returns must agree with a direct evaluation.
        match (obq_poly_eval_at(&g.poly, &v), obq_poly_sign_at(&g.poly, &v)) {
            (Some(val), Some(s)) if val.sign() == s => n += 1,
            (val, s) => {
                return Divergence::new(
                    "bq-select",
                    "identity",
                    format!("poly_eval_at {val:?} and poly_sign_at {s:?} disagree"),
                    vec![("poly".into(), render_poly(&g.poly))],
                )
            }
        }
    }

    Outcome::Match(n)
}

// ===========================================================================
// Check 4 — `bq-degenerate`: the guards, and the liveness bound
// ===========================================================================

/// Every guard in the module, fired on purpose, each paired with a positive
/// control on a neighbouring well-formed input.
///
/// This check exists because of the campaign's second blind-spot pattern: **a
/// guard that never fires on the corpus, so deleting it is invisible**. Each
/// assertion below is written so that deleting the guard it targets makes this
/// check diverge.
///
/// It also carries the **liveness** assertion for the one loop whose bound is
/// not derivable from the input: `refine_until_separated` on two *identical*
/// roots can never separate them, and must return `Inconclusive` after exactly
/// the budget rather than spinning.
pub(crate) fn check_degenerate(g: &GenBq, sab: Sabotage) -> Outcome {
    let mut n = 0u64;

    // The sabotage model for a guard check is "the guard was deleted", i.e. the
    // module ANSWERED where it should have declined. `answered` is the single
    // place that reading is made, so `Sabotage::On` corrupts every guard
    // uniformly and each one has to be caught by its own assertion.
    //
    // DISCLOSED: because the corruption is uniform, this check's `selftest`
    // catch rate is 100% BY CONSTRUCTION and is not evidence that any
    // individual guard is sensitive. What IS evidence is that every guard below
    // is paired with a positive control on a neighbouring well-formed input, so
    // an implementation that declined on everything would fail this check too.
    let answered = |declined: bool| -> bool {
        if sab.on() {
            true
        } else {
            !declined
        }
    };

    // Helper: report a guard that failed to fire.
    macro_rules! must_decline {
        ($opt_is_some:expr, $what:expr) => {
            if answered(!$opt_is_some) {
                return Divergence::new(
                    "bq-degenerate",
                    "identity",
                    format!("guard did not fire: {}", $what),
                    vec![("shape".into(), g.shape.to_string())],
                );
            }
            n += 1;
        };
    }

    // --- interval constructor: lo == hi, in two spellings, and lo > hi -----
    let a = bq(&g.x);
    // The SAME value written at a coarser and a finer exponent.
    let a2 = OBq::new(a.numerator() * 2, a.k() + 1);
    must_decline!(
        OBqInterval::new(&a, &a2).is_some(),
        "lo == hi written as a/2^k and 2a/2^(k+1)"
    );
    must_decline!(OBqInterval::new(&a, &a).is_some(), "lo == hi, identical");
    let below = a.sub(&OBq::from_int(BigInt::one()));
    must_decline!(OBqInterval::new(&a, &below).is_some(), "lo > hi");
    // POSITIVE CONTROL: the same endpoints the right way round must succeed,
    // so the constructor cannot pass by rejecting everything.
    let ok = OBqInterval::new(&below, &a);
    if ok.is_none() {
        return Divergence::new(
            "bq-degenerate",
            "identity",
            "the constructor rejected a well-formed interval".into(),
            vec![
                ("lo".into(), render_bq(&below)),
                ("hi".into(), render_bq(&a)),
            ],
        );
    }
    let ok = ok.unwrap();
    n += 1;

    // --- representability: negative and positive --------------------------
    must_decline!(
        OBq::is_representable(&g.non_dyadic),
        format!("non-dyadic {} accepted", g.non_dyadic)
    );
    if !OBq::is_representable(&g.dyadic) {
        return Divergence::new(
            "bq-degenerate",
            "identity",
            format!("dyadic {} rejected", g.dyadic),
            vec![("r".into(), g.dyadic.to_string())],
        );
    }
    n += 1;

    // --- refinement targets: zero and negative ----------------------------
    must_decline!(
        obq_refine_step_bound(&ok.width(), &OBq::zero()).is_some(),
        "refine_step_bound with target 0"
    );
    must_decline!(
        obq_refine_step_bound(&ok.width(), &OBq::inv_two_pow(3).neg()).is_some(),
        "refine_step_bound with a negative target"
    );
    must_decline!(
        obq_refine_to_width(&g.poly, &ok, &OBq::zero()).is_some(),
        "refine_to_width with target 0"
    );
    // POSITIVE CONTROL: a sane target on a genuinely bracketing interval must
    // NOT decline. Build one around sqrt(2) in (1, 2) for `x^2 - 2`.
    let sq2 = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let unit = OBqInterval::new(
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(2)),
    )
    .expect("(1, 2) is a well-formed interval");
    let refined = obq_refine_to_width(&sq2, &unit, &OBq::inv_two_pow(20));
    if refined.is_none() {
        return Divergence::new(
            "bq-degenerate",
            "identity",
            "refine_to_width declined on a well-formed sqrt(2) bracket".into(),
            vec![("target".into(), "2^-20".into())],
        );
    }
    n += 1;

    // --- broken brackets ---------------------------------------------------
    // Same sign at both ends: (2, 3) for x^2 - 2.
    let no_root = OBqInterval::new(
        &OBq::from_int(BigInt::from(2)),
        &OBq::from_int(BigInt::from(3)),
    )
    .expect("(2, 3) is well formed");
    must_decline!(
        obq_refine_to_width(&sq2, &no_root, &OBq::inv_two_pow(8)).is_some(),
        "refine_to_width on an interval with no sign change"
    );
    // Endpoint IS a root: x^2 - 4 on (2, 3).
    let sq4 = vec![BigInt::from(-4), BigInt::zero(), BigInt::one()];
    must_decline!(
        obq_refine_to_width(&sq4, &no_root, &OBq::inv_two_pow(8)).is_some(),
        "refine_to_width with a root at an endpoint"
    );

    // --- select_non_root on the zero polynomial ---------------------------
    must_decline!(
        obq_select_non_root(&[], &ok).is_some(),
        "select_non_root on the empty polynomial"
    );
    must_decline!(
        obq_select_non_root(&[BigInt::zero(), BigInt::zero()], &ok).is_some(),
        "select_non_root on the zero polynomial"
    );

    // --- enclose_rational degeneracies ------------------------------------
    let r = BigRational::new(BigInt::one(), BigInt::from(3));
    must_decline!(
        obq_enclose_rational(&r, &r, 8).is_some(),
        "enclose_rational with lo == hi"
    );
    must_decline!(
        obq_enclose_rational(&(&r + BigRational::one()), &r, 8).is_some(),
        "enclose_rational with lo > hi"
    );
    // POSITIVE CONTROL: a proper rational interval must enclose without
    // narrowing.
    let r2 = &r + BigRational::one();
    match obq_enclose_rational(&r, &r2, 10) {
        Some(e) => {
            if e.lo().to_rational() > r || e.hi().to_rational() < r2 {
                return Divergence::new(
                    "bq-degenerate",
                    "identity",
                    "enclose_rational NARROWED the interval".into(),
                    vec![("lo".into(), r.to_string()), ("hi".into(), r2.to_string())],
                );
            }
            n += 1;
        }
        None => {
            return Divergence::new(
                "bq-degenerate",
                "identity",
                "enclose_rational declined on a well-formed rational interval".into(),
                vec![("lo".into(), r.to_string()), ("hi".into(), r2.to_string())],
            )
        }
    }

    // --- LIVENESS: two identical roots can never separate ------------------
    // The one loop whose bound is a caller budget rather than a derived
    // quantity. It MUST return, and it must return `Inconclusive` after
    // exactly the budget.
    let budget = 64u32;
    match obq_refine_until_separated(&sq2, &unit, &sq2, &unit, budget) {
        Some((OSeparation::Inconclusive, _, _, rounds)) => {
            if rounds != budget {
                return Divergence::new(
                    "bq-degenerate",
                    "identity",
                    format!("inconclusive after {rounds} rounds, budget was {budget}"),
                    vec![],
                );
            }
            n += 2;
        }
        other => {
            return Divergence::new(
                "bq-degenerate",
                "identity",
                format!("the same root separated from itself: {other:?}"),
                vec![],
            )
        }
    }
    // POSITIVE CONTROL: two DIFFERENT roots must separate, and in the right
    // order. sqrt(2) < sqrt(d2) iff 2 < d2.
    let other_poly = &g.poly2;
    let d2 = -other_poly[0].clone();
    if d2 > BigInt::from(2) {
        let wide = OBqInterval::new(
            &OBq::from_int(BigInt::one()),
            &OBq::from_int(BigInt::from(4)),
        )
        .expect("(1, 4) is well formed");
        match obq_refine_until_separated(&sq2, &wide, other_poly, &wide, 200) {
            Some((OSeparation::Ordered(Ordering::Less), ia, ib, _)) => {
                if !ia.disjoint(&ib) {
                    return Divergence::new(
                        "bq-degenerate",
                        "identity",
                        "separated intervals are not disjoint".into(),
                        vec![],
                    );
                }
                n += 2;
            }
            other => {
                return Divergence::new(
                    "bq-degenerate",
                    "identity",
                    format!("sqrt(2) vs sqrt({d2}) did not separate as Less: {other:?}"),
                    vec![],
                )
            }
        }
    }

    Outcome::Match(n)
}

// ===========================================================================
// Denominator growth — the `bq-growth` harness
// ===========================================================================

/// One row of the growth measurement.
pub(crate) struct GrowthRow {
    /// Number of bisections performed.
    pub(crate) steps: u32,
    /// `max_k` of the dyadic interval after `steps` bisections.
    pub(crate) dyadic_k: u32,
    /// Total bits stored by the dyadic interval (both numerators plus the two
    /// exponents' worth of implied denominator).
    pub(crate) dyadic_bits: u64,
    /// Bits in the widest numerator/denominator the `BigRational` bisection
    /// reached over the same run.
    pub(crate) rational_bits: u64,
    /// Wall time of the dyadic run, microseconds.
    pub(crate) dyadic_us: u128,
    /// Wall time of the `BigRational` run, microseconds.
    pub(crate) rational_us: u128,
    /// `k` of the point `select_small` returns at this depth.
    pub(crate) select_k: u32,
    /// `k` of the midpoint at this depth.
    pub(crate) mid_k: u32,
    /// Both runs agree on the interval, as rationals.
    pub(crate) agree: bool,
}

/// Measure denominator growth across a long refinement, dyadic vs
/// `BigRational`.
///
/// The rule this answers: *a refine loop that doubles `k` every step is correct
/// and useless.* The dyadic column must grow by exactly one per step; the
/// `BigRational` column is the same bisection over `num_rational`, and its
/// growth is what the dyadic layer is here to avoid.
///
/// Both runs bisect the same isolating interval of `x^2 - 2` and must stay
/// numerically identical throughout, which is checked (`agree`).
pub(crate) fn measure_growth(depths: &[u32]) -> Vec<GrowthRow> {
    let p_int = vec![BigInt::from(-2), BigInt::zero(), BigInt::one()];
    let p_rat: Vec<BigRational> = p_int.iter().map(|c| BigRational::from(c.clone())).collect();
    let mut rows = Vec::new();

    for &steps in depths {
        // --- dyadic run ----------------------------------------------------
        let t0 = std::time::Instant::now();
        let mut iv = OBqInterval::new(
            &OBq::from_int(BigInt::one()),
            &OBq::from_int(BigInt::from(2)),
        )
        .expect("(1, 2)");
        for _ in 0..steps {
            let Some((left, mid, right)) = iv.bisect() else {
                break;
            };
            let s = obq_poly_sign_at(&p_int, &mid).unwrap_or(0);
            // p(1) < 0, so keep the half whose lower end is still negative.
            iv = if s < 0 { right } else { left };
        }
        let dyadic_us = t0.elapsed().as_micros();
        let dyadic_bits = iv.lo().numerator_bits()
            + iv.hi().numerator_bits()
            + u64::from(iv.lo().k())
            + u64::from(iv.hi().k());
        let select_k = obq_select_small(&iv).map_or(u32::MAX, |(v, _)| v.k());
        let mid_k = iv.midpoint().map_or(u32::MAX, |m| m.k());

        // --- BigRational run, the same bisection -------------------------
        let t1 = std::time::Instant::now();
        let two = BigRational::from(BigInt::from(2));
        let mut lo = BigRational::one();
        let mut hi = BigRational::from(BigInt::from(2));
        let mut rational_bits = 0u64;
        for _ in 0..steps {
            let mid = (&lo + &hi) / &two;
            let mut acc = BigRational::zero();
            let mut pow = BigRational::one();
            for c in &p_rat {
                acc += c * &pow;
                pow *= &mid;
            }
            if acc.numer().is_negative() {
                lo = mid;
            } else {
                hi = mid;
            }
            let w = lo.numer().bits() + lo.denom().bits() + hi.numer().bits() + hi.denom().bits();
            rational_bits = rational_bits.max(w);
        }
        let rational_us = t1.elapsed().as_micros();

        let agree = iv.lo().to_rational() == lo && iv.hi().to_rational() == hi;

        rows.push(GrowthRow {
            steps,
            dyadic_k: iv.max_k(),
            dyadic_bits,
            rational_bits,
            dyadic_us,
            rational_us,
            select_k,
            mid_k,
            agree,
        });
    }
    rows
}

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
