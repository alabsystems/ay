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
/// Four shapes, chosen so that each of the branches that a purely random draw
/// would almost never reach gets exercised:
///
///   * `squares`  — a factor is planted with multiplicity 2 or 3, so the
///                  square-free decomposition has something to decompose.
///   * `split`    — every factor is linear, the worst case for equal-degree
///                  factorization (the most splits it will ever have to do).
///   * `pth-power`— the input is `g(x^p)` for a small `p`, so the derivative
///                  vanishes mod `p` and the characteristic-`p` branch runs.
///   * `generic`  — an unconstrained product.
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
            for _ in 0..n + 1 {
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

// ---------------------------------------------------------------------------
// Check 1: the Z / Z_p arithmetic substrate
// ---------------------------------------------------------------------------

/// The `Z` substrate identities, plus the `Z -> Z_p` reduction as a RING
/// HOMOMORPHISM, plus a z3-backed leg on pseudo-division.
///
/// Four statements:
///
///   (a) `content(f) * pp(f) == f` exactly, `pp` primitive with positive `lc`.
///   (b) `lc(b)^d * a == q*b + r` with `deg r < deg b` — the pseudo-division
///       identity, exactly.
///   (c) reduction mod `p` commutes with `+` and `*`. This is what makes every
///       modular algorithm legal, and it is the statement that a sloppy
///       `reduce` (say, `%` instead of `mod_floor`, which differs on negative
///       coefficients) violates.
///   (d) **z3-backed**: at a real root `alpha` of `b`, the pseudo-division
///       identity collapses to `lc(b)^d * a(alpha) == r(alpha)`, so the two
///       signs z3 computes must agree. `alpha` and both signs come from z3;
///       AY supplies only `q`, `r` and `d`.
pub(crate) fn check_substrate(z3: &Z3, g: &GenUp, sab: Sabotage) -> Outcome {
    let a = build_z(g);
    let b = OUniZ::from_coeffs(g.other.clone());
    if a.is_zero() || b.is_zero() {
        return Outcome::Skipped("degenerate operand");
    }
    let mut comparisons = 0u64;

    // (a) content / primitive part
    let Some((c, pp)) = a.split_content() else {
        return Outcome::Declined("split_content refused");
    };
    comparisons += 1;
    if pp.scale(&c) != a {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            "content * primitive_part != input".to_string(),
            vec![
                ("a".to_string(), render_z(&a)),
                ("content".to_string(), c.to_string()),
                ("pp".to_string(), render_z(&pp)),
            ],
        );
    }
    comparisons += 1;
    if !pp.content().is_one() || pp.lc().is_some_and(|l| l.is_negative()) {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            format!(
                "primitive part is not primitive/positive: content = {}",
                pp.content()
            ),
            vec![
                ("a".to_string(), render_z(&a)),
                ("pp".to_string(), render_z(&pp)),
            ],
        );
    }

    // (a'') The GCD's INTEGER CONTENT, via `gcd(k*a, k*b) == k * gcd(a, b)`.
    //
    // This leg exists because of an injected defect. `ZPoly::gcd` multiplies its
    // primitive answer back by `gcd(content(a), content(b))`; deleting that
    // multiplication produced ZERO divergences in 2,700 cases, because every
    // other call site in the module passes at least one PRIMITIVE argument
    // (Yun's `prim.gcd(&dp)`, the pairwise-coprimality leg below), so the
    // common content is 1 and the scaling never fires. Scaling both arguments
    // by a shared constant is the only way to make that line observable.
    let k = BigInt::from(6);
    let (Some(g0), Some(gk)) = (a.gcd(&b), a.scale(&k).gcd(&b.scale(&k))) else {
        return Outcome::Declined("gcd refused");
    };
    comparisons += 1;
    if gk != g0.scale(&k) {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            "gcd(k*a, k*b) != k * gcd(a, b): the integer content was dropped".to_string(),
            vec![
                ("a".to_string(), render_z(&a)),
                ("b".to_string(), render_z(&b)),
                ("k".to_string(), k.to_string()),
                ("gcd(a,b)".to_string(), render_z(&g0)),
                ("gcd(ka,kb)".to_string(), render_z(&gk)),
            ],
        );
    }

    // (b) pseudo-division
    let Some((d, q, mut r)) = a.pseudo_div(&b) else {
        return Outcome::Declined("pseudo_div refused");
    };
    if sab.on() {
        // Minimal corruption: bump the remainder's constant term by one.
        let mut rc = r.coeffs();
        if rc.is_empty() {
            rc.push(BigInt::one());
        } else {
            rc[0] += BigInt::one();
        }
        r = OUniZ::from_coeffs(rc);
    }
    let mut lhs = a.clone();
    let lb = b.lc().unwrap_or_else(BigInt::one);
    for _ in 0..d {
        lhs = lhs.scale(&lb);
    }
    comparisons += 1;
    if lhs != q.mul(&b).add(&r) {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            format!("pseudo-division identity fails: lc(b)^{d} * a != q*b + r"),
            vec![
                ("a".to_string(), render_z(&a)),
                ("b".to_string(), render_z(&b)),
                ("d".to_string(), d.to_string()),
                ("q".to_string(), render_z(&q)),
                ("r".to_string(), render_z(&r)),
            ],
        );
    }
    comparisons += 1;
    if let (Some(rd), Some(bd)) = (r.degree(), b.degree()) {
        if rd >= bd {
            return Divergence::new(
                "up-z-substrate",
                "identity",
                format!("pseudo-remainder degree {rd} >= divisor degree {bd}"),
                vec![
                    ("a".to_string(), render_z(&a)),
                    ("b".to_string(), render_z(&b)),
                    ("r".to_string(), render_z(&r)),
                ],
            );
        }
    }

    // (b') the same identity, EVALUATED at integer points. `eval` had no
    // caller at all until this leg was added — it was reachable from the
    // facade and asserted on by nothing, the same shape as the `square_free`
    // blind spot this campaign already found once.
    for t in [-3i64, -1, 0, 2, 7] {
        let t = BigInt::from(t);
        let mut lv = a.eval(&t);
        for _ in 0..d {
            lv *= &lb;
        }
        comparisons += 1;
        if lv != q.eval(&t) * b.eval(&t) + r.eval(&t) {
            return Divergence::new(
                "up-z-substrate",
                "identity",
                format!("pseudo-division identity fails when evaluated at x = {t}"),
                vec![
                    ("a".to_string(), render_z(&a)),
                    ("b".to_string(), render_z(&b)),
                    ("q".to_string(), render_z(&q)),
                    ("r".to_string(), render_z(&r)),
                ],
            );
        }
    }

    // (c) reduction is a ring homomorphism
    let Some(m) = OZpMgr::new(g.p) else {
        return Outcome::Declined("modulus refused");
    };
    let (ra, rb) = (m.reduce(&a), m.reduce(&b));

    // (c') lift is a section of reduce: `reduce . lift == id` on Z_p, and the
    // lifted coefficients really do land in [0, p). `lift` also had no caller.
    let lifted = m.lift(&ra);
    comparisons += 1;
    if m.reduce(&lifted) != ra {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            format!("reduce(lift(x)) != x mod {}", g.p),
            vec![("a".to_string(), render_z(&a))],
        );
    }
    comparisons += 1;
    if lifted
        .coeffs()
        .iter()
        .any(|c| c.is_negative() || *c >= BigInt::from(g.p))
    {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            format!("lift produced a coefficient outside [0, {})", g.p),
            vec![("lifted".to_string(), render_z(&lifted))],
        );
    }
    comparisons += 1;
    if m.reduce(&a.add(&b)) != m.add(&ra, &rb) {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            format!("reduce is not additive mod {}", g.p),
            vec![
                ("a".to_string(), render_z(&a)),
                ("b".to_string(), render_z(&b)),
            ],
        );
    }
    comparisons += 1;
    if m.reduce(&a.mul(&b)) != m.mul(&ra, &rb) {
        return Divergence::new(
            "up-z-substrate",
            "identity",
            format!("reduce is not multiplicative mod {}", g.p),
            vec![
                ("a".to_string(), render_z(&a)),
                ("b".to_string(), render_z(&b)),
            ],
        );
    }

    // (d) the z3 leg: evaluate the pseudo-division identity at a real root of b.
    let Some(roots) = z3.roots(&to_rationals(&b)) else {
        return Outcome::Skipped("z3 declined the divisor");
    };
    if roots.is_empty() {
        return Outcome::Match(comparisons);
    }
    // sign(lc(b)^d * a(alpha)) must equal sign(r(alpha)).
    let mut scaled = to_rationals(&a);
    let lbr = BigRational::from(lb.clone());
    for _ in 0..d {
        for c in &mut scaled {
            *c *= &lbr;
        }
    }
    let rr = to_rationals(&r);
    for (i, alpha) in roots.iter().enumerate() {
        let (Some(s_lhs), Some(s_rhs)) = (z3.eval_sign(&scaled, *alpha), z3.eval_sign(&rr, *alpha))
        else {
            return Outcome::Skipped("z3 declined an evaluation");
        };
        comparisons += 1;
        if s_lhs != s_rhs {
            return Divergence::new(
                "up-z-substrate",
                "z3",
                format!(
                    "at real root #{i} of b: sign(lc(b)^{d} * a) = {s_lhs} but sign(r) = {s_rhs}"
                ),
                vec![
                    ("a".to_string(), render_z(&a)),
                    ("b".to_string(), render_z(&b)),
                    ("r".to_string(), render_z(&r)),
                    ("d".to_string(), d.to_string()),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// Check 2: Yun's square-free decomposition over Z
// ---------------------------------------------------------------------------

/// Yun's decomposition `f == c * prod f_i^i`.
///
/// Three statements:
///
///   (a) the EXACT identity — `c * prod f_i^i` reproduces the input coefficient
///       for coefficient. This is the statement that a "square-free part"
///       cannot make: `p / gcd(p, p')` throws the multiplicities away, and
///       AY's existing `univariate::square_free_part` returns exactly that.
///   (b) each `f_i` is square-free (`gcd(f_i, f_i') `is constant) and the `f_i`
///       are pairwise coprime.
///   (c) **z3-backed**: `prod f_i` (the radical) has the same real ROOT SET as
///       the input, compared root by root with `Z3_algebraic_eq`. The integer
///       content is a unit for this leg, so (a) is what pins it — the lesson
///       the `pm-square-free-all` defect taught.
pub(crate) fn check_sqf_decomp(z3: &Z3, g: &GenUp, sab: Sabotage) -> Outcome {
    let f = build_z(g);
    if f.is_zero() || f.degree() == Some(0) {
        return Outcome::Skipped("degenerate input");
    }
    let Some((c, factors)) = f.square_free_decomposition() else {
        return Outcome::Declined("square_free_decomposition refused");
    };
    let mut factors = factors;
    if sab.on() {
        // Minimal corruption: drop one unit of multiplicity from the first
        // factor with multiplicity > 1, else duplicate a factor.
        if let Some(slot) = factors.iter_mut().find(|(_, m)| *m > 1) {
            slot.1 -= 1;
        } else if let Some((f0, _)) = factors.first().cloned() {
            factors.push((f0, 1));
        } else {
            return Outcome::Skipped("nothing to sabotage");
        }
    }
    let mut comparisons = 0u64;

    // (a) the exact identity
    let mut prod = OUniZ::from_coeffs(vec![c.clone()]);
    let mut radical = OUniZ::from_coeffs(vec![BigInt::one()]);
    for (fac, m) in &factors {
        radical = radical.mul(fac);
        for _ in 0..*m {
            prod = prod.mul(fac);
        }
    }
    comparisons += 1;
    if prod != f {
        return Divergence::new(
            "up-z-sqf-decomp",
            "identity",
            "c * prod f_i^i != input".to_string(),
            vec![
                ("f".to_string(), render_z(&f)),
                ("c".to_string(), c.to_string()),
                (
                    "factors".to_string(),
                    factors
                        .iter()
                        .map(|(a, m)| format!("({})^{m}", render_z(a)))
                        .collect::<Vec<_>>()
                        .join(" * "),
                ),
                ("product".to_string(), render_z(&prod)),
            ],
        );
    }

    // (b) each factor square-free, pairwise coprime
    for (fac, m) in &factors {
        comparisons += 1;
        let Some(gg) = fac.gcd(&fac.derivative()) else {
            return Outcome::Declined("gcd refused");
        };
        if gg.degree() != Some(0) {
            return Divergence::new(
                "up-z-sqf-decomp",
                "identity",
                format!("factor with multiplicity {m} is not square-free"),
                vec![
                    ("f".to_string(), render_z(&f)),
                    ("factor".to_string(), render_z(fac)),
                    ("gcd(fac,fac')".to_string(), render_z(&gg)),
                ],
            );
        }
    }
    for i in 0..factors.len() {
        for j in i + 1..factors.len() {
            comparisons += 1;
            let Some(gg) = factors[i].0.gcd(&factors[j].0) else {
                return Outcome::Declined("gcd refused");
            };
            if gg.degree() != Some(0) {
                return Divergence::new(
                    "up-z-sqf-decomp",
                    "identity",
                    format!("factors {i} and {j} share a non-trivial gcd"),
                    vec![
                        ("f".to_string(), render_z(&f)),
                        ("f_i".to_string(), render_z(&factors[i].0)),
                        ("f_j".to_string(), render_z(&factors[j].0)),
                        ("gcd".to_string(), render_z(&gg)),
                    ],
                );
            }
        }
    }

    // (c) the z3 leg: the radical has the same real roots as the input.
    let (Some(fr), Some(rr)) = (
        z3.roots(&to_rationals(&f)),
        z3.roots(&to_rationals(&radical)),
    ) else {
        return Outcome::Skipped("z3 declined");
    };
    comparisons += 1;
    if fr.len() != rr.len() {
        return Divergence::new(
            "up-z-sqf-decomp",
            "z3",
            format!(
                "root counts differ: input has {} distinct real roots, the radical has {}",
                fr.len(),
                rr.len()
            ),
            vec![
                ("f".to_string(), render_z(&f)),
                ("radical".to_string(), render_z(&radical)),
            ],
        );
    }
    for (i, (x, y)) in fr.iter().zip(rr.iter()).enumerate() {
        comparisons += 1;
        if !z3.eq(*x, *y) {
            return Divergence::new(
                "up-z-sqf-decomp",
                "z3",
                format!("root #{i} of the input and of the radical differ"),
                vec![
                    ("f".to_string(), render_z(&f)),
                    ("radical".to_string(), render_z(&radical)),
                ],
            );
        }
    }
    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// Check 3: distinct-degree factorization over Z_p
// ---------------------------------------------------------------------------

/// Distinct-degree factorization, in ISOLATION.
///
/// It gets its own check rather than being covered through `factor` because a
/// bucket that is assigned the WRONG degree label still multiplies back
/// correctly — the product identity is blind to `d`. What is not blind to `d`
/// is the field-theoretic characterization, which this check applies directly:
///
///   (a) `prod g_d == a` exactly;
///   (b) `deg(g_d)` is divisible by `d`;
///   (c) **the independent witness**: every root of `g_d` lies in `F_(p^d)`,
///       i.e. `x^(p^d) == x (mod g_d)`, and in NO smaller field, i.e.
///       `gcd(x^(p^e) - x, g_d) == 1` for every proper divisor `e` of `d`.
///       That is computed here in the oracle from `powmod`/`gcd` alone and
///       never touches AY's distinct-degree loop.
///   (d) **the counter pin**: `ddf_iters` is re-derived exactly by replaying
///       the loop's stopping condition against the returned buckets.
pub(crate) fn check_ddf(g: &GenUp, sab: Sabotage) -> Outcome {
    let Some(m) = OZpMgr::new(g.p) else {
        return Outcome::Declined("modulus refused");
    };
    let f = build_z(g);
    let reduced = m.reduce(&f);
    if reduced.is_zero() || reduced.degree() == Some(0) {
        return Outcome::Skipped("reduction collapsed the input");
    }
    let Some((_, monic)) = m.monic(&reduced) else {
        return Outcome::Declined("monic refused");
    };
    // DDF requires a square-free input; take the square-free part first.
    let Some(sqf) = m.square_free_decomposition(&monic) else {
        return Outcome::Declined("square-free decomposition refused");
    };
    let mut radical = m.one();
    for (h, _) in &sqf {
        radical = m.mul(&radical, h);
    }
    if radical.degree().unwrap_or(0) == 0 {
        return Outcome::Skipped("radical is constant");
    }
    let mut comparisons = 0u64;

    // (a0) EVERY square-free-decomposition factor must actually be square-free,
    // and the decomposition must reproduce the input exactly.
    //
    // This leg exists because a deliberately injected characteristic-`p` defect
    // — treating `g' == 0` as "already square-free" instead of recognising a
    // `p`-th power — satisfied the product identity and merely made the
    // downstream `distinct_degree` DECLINE. A decline is not a catch. In
    // characteristic `p` the witness has to be `gcd(g, g')` directly, because
    // `g' == 0` is precisely the case the product identity cannot see.
    let mut sqf_prod = m.one();
    for (h, e) in &sqf {
        comparisons += 1;
        let dh = m.derivative(h);
        let gg = m.gcd(h, &dh);
        if dh.is_zero() || gg.degree() != Some(0) {
            return Divergence::new(
                "up-zp-ddf",
                "identity",
                format!(
                    "square-free factor with multiplicity {e} is NOT square-free: \
                     gcd(g, g') has degree {:?} (g' zero: {})",
                    gg.degree(),
                    dh.is_zero()
                ),
                vec![
                    ("input".to_string(), render_zp(&m, &monic)),
                    ("factor".to_string(), render_zp(&m, h)),
                ],
            );
        }
        for _ in 0..*e {
            sqf_prod = m.mul(&sqf_prod, h);
        }
    }
    comparisons += 1;
    if sqf_prod != monic {
        return Divergence::new(
            "up-zp-ddf",
            "identity",
            "prod g_i^m_i != the monic input".to_string(),
            vec![
                ("input".to_string(), render_zp(&m, &monic)),
                ("product".to_string(), render_zp(&m, &sqf_prod)),
            ],
        );
    }

    m.reset_stats();
    let Some(mut buckets) = m.distinct_degree(&radical) else {
        return Outcome::Declined("distinct_degree refused");
    };
    let stats = m.stats();
    if sab.on() {
        // Minimal corruption: relabel one bucket's degree.
        if let Some(b) = buckets.first_mut() {
            b.1 += 1;
        } else {
            return Outcome::Skipped("nothing to sabotage");
        }
    }

    // (a) the exact product identity
    let mut prod = m.one();
    for (h, _) in &buckets {
        prod = m.mul(&prod, h);
    }
    comparisons += 1;
    if prod != radical {
        return Divergence::new(
            "up-zp-ddf",
            "identity",
            "prod of distinct-degree buckets != input".to_string(),
            vec![
                ("input".to_string(), render_zp(&m, &radical)),
                ("product".to_string(), render_zp(&m, &prod)),
            ],
        );
    }

    // (b) + (c) degree divisibility and the field-theoretic witness
    let x = m.from_u64(vec![0, 1]);
    let pbig = BigInt::from(g.p);
    for (h, d) in &buckets {
        let Some(hd) = h.degree() else {
            return Outcome::Skipped("empty bucket");
        };
        comparisons += 1;
        if *d == 0 || hd % *d != 0 {
            return Divergence::new(
                "up-zp-ddf",
                "identity",
                format!("bucket of degree {hd} labelled with d = {d}"),
                vec![("bucket".to_string(), render_zp(&m, h))],
            );
        }
        // x^(p^d) mod h, by d repeated p-th powers.
        let mut cur = x.clone();
        for _ in 0..*d {
            let Some(next) = m.powmod(&cur, &pbig, h) else {
                return Outcome::Declined("powmod refused");
            };
            cur = next;
        }
        // Compare against `x` REDUCED MOD h, not against `x`. `powmod` returns
        // a residue, so for a degree-1 bucket both sides are constants and the
        // unreduced comparison is a false alarm: `x + 2` mod 5 gives
        // `x^5 == 3` and `x == 3`, which agree. (241 of these were reported
        // before the reduction was added; the module was right every time.)
        let Some((_, xr)) = m.div_rem(&x, h) else {
            return Outcome::Declined("div_rem refused");
        };
        comparisons += 1;
        if cur != xr {
            return Divergence::new(
                "up-zp-ddf",
                "identity",
                format!("bucket labelled d = {d} does not satisfy x^(p^{d}) == x"),
                vec![
                    ("bucket".to_string(), render_zp(&m, h)),
                    ("x^(p^d)".to_string(), render_zp(&m, &cur)),
                ],
            );
        }
        // and in no smaller field
        for e in 1..*d {
            if d % e != 0 {
                continue;
            }
            let mut cur = x.clone();
            for _ in 0..e {
                let Some(next) = m.powmod(&cur, &pbig, h) else {
                    return Outcome::Declined("powmod refused");
                };
                cur = next;
            }
            let gg = m.gcd(&m.sub(&cur, &x), h);
            comparisons += 1;
            if gg.degree() != Some(0) {
                return Divergence::new(
                    "up-zp-ddf",
                    "identity",
                    format!(
                        "bucket labelled d = {d} has a factor of degree {e}: it is not \
                         degree-{d}-pure"
                    ),
                    vec![
                        ("bucket".to_string(), render_zp(&m, h)),
                        ("gcd".to_string(), render_zp(&m, &gg)),
                    ],
                );
            }
        }
    }

    // (c') equal-degree factorization DIRECTLY on each bucket. Until this leg
    // existed, `equal_degree` was reachable only through `factor`, so none of
    // its own preconditions were ever exercised by a check.
    for (h, d) in &buckets {
        let Some(parts) = m.equal_degree(h, *d) else {
            return Outcome::Declined("equal_degree refused");
        };
        let mut prod = m.one();
        for f in &parts {
            comparisons += 1;
            if f.degree() != Some(*d) {
                return Divergence::new(
                    "up-zp-ddf",
                    "identity",
                    format!(
                        "equal_degree on a d = {d} bucket returned a factor of degree {:?}",
                        f.degree()
                    ),
                    vec![
                        ("bucket".to_string(), render_zp(&m, h)),
                        ("factor".to_string(), render_zp(&m, f)),
                    ],
                );
            }
            prod = m.mul(&prod, f);
        }
        comparisons += 1;
        if prod != *h {
            return Divergence::new(
                "up-zp-ddf",
                "identity",
                "the equal-degree factors do not multiply back to the bucket".to_string(),
                vec![
                    ("bucket".to_string(), render_zp(&m, h)),
                    ("product".to_string(), render_zp(&m, &prod)),
                ],
            );
        }
    }

    // (d) the counter pin: replay the loop's stopping condition.
    let mut remaining = radical.degree().unwrap_or(0);
    let mut expected = 0u64;
    let mut i = 1usize;
    while remaining >= 2 * i {
        expected += 1;
        if let Some((h, _)) = buckets.iter().find(|(_, d)| *d == i) {
            remaining -= h.degree().unwrap_or(0);
        }
        i += 1;
    }
    comparisons += 1;
    if stats.ddf_iters != expected {
        return Divergence::new(
            "up-zp-ddf",
            "identity",
            format!(
                "ddf_iters counter says {} but the returned buckets imply exactly {expected}",
                stats.ddf_iters
            ),
            vec![
                ("input".to_string(), render_zp(&m, &radical)),
                (
                    "buckets".to_string(),
                    buckets
                        .iter()
                        .map(|(h, d)| format!("(deg {}, d={d})", h.degree().unwrap_or(0)))
                        .collect::<Vec<_>>()
                        .join(", "),
                ),
            ],
        );
    }
    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// Check 4: complete factorization over Z_p
// ---------------------------------------------------------------------------

/// Complete factorization over `Z_p`, against the perfect identity plus the
/// independent irreducibility witness.
///
///   (a) `lc * prod f_i^{e_i} == input`, EXACTLY;
///   (b) every `f_i` is monic of degree `>= 1`, and the `f_i` are pairwise
///       distinct — a factorizer that returns the same factor twice instead of
///       raising its multiplicity still satisfies (a);
///   (c) every `f_i` is irreducible by **Rabin's test**, which is what catches
///       an under-factorization that (a) cannot see;
///   (d) `sum deg(f_i) * e_i == deg(input)`;
///   (e) the counter pin: `edf_splits == (number of factors produced by
///       equal-degree) - (number of buckets fed to it)`.
pub(crate) fn check_factor(g: &GenUp, sab: Sabotage) -> Outcome {
    let Some(m) = OZpMgr::new(g.p) else {
        return Outcome::Declined("modulus refused");
    };
    let f = build_z(g);
    let reduced = m.reduce(&f);
    if reduced.is_zero() {
        return Outcome::Skipped("reduction vanished");
    }
    let Some(n) = reduced.degree() else {
        return Outcome::Skipped("reduction vanished");
    };
    if n == 0 {
        return Outcome::Skipped("reduction is a constant");
    }
    m.reset_stats();
    let Some((lc, mut factors)) = m.factor(&reduced) else {
        return Outcome::Declined("factor refused");
    };
    let stats = m.stats();
    if sab.on() {
        // Minimal corruption: merge the two smallest factors into their
        // product. The product identity still holds; only the irreducibility
        // witness (c) can see it — which is exactly the point of having it.
        if factors.len() >= 2 && factors[0].1 == factors[1].1 {
            let merged = m.mul(&factors[0].0, &factors[1].0);
            let mult = factors[0].1;
            factors.drain(0..2);
            factors.push((merged, mult));
        } else if let Some(first) = factors.first().cloned() {
            // Fall back to a corruption the product identity does see.
            factors.push(first);
        } else {
            return Outcome::Skipped("nothing to sabotage");
        }
    }
    let mut comparisons = 0u64;

    // (a) the exact identity
    let mut prod = m.from_u64(vec![lc]);
    for (h, e) in &factors {
        for _ in 0..*e {
            prod = m.mul(&prod, h);
        }
    }
    comparisons += 1;
    if prod != reduced {
        return Divergence::new(
            "up-zp-factor",
            "identity",
            "lc * prod f_i^e_i != input".to_string(),
            vec![
                ("input".to_string(), render_zp(&m, &reduced)),
                ("lc".to_string(), lc.to_string()),
                (
                    "factors".to_string(),
                    factors
                        .iter()
                        .map(|(h, e)| format!("({})^{e}", render_zp(&m, h)))
                        .collect::<Vec<_>>()
                        .join(" * "),
                ),
                ("product".to_string(), render_zp(&m, &prod)),
            ],
        );
    }

    // (b) monic, degree >= 1, pairwise distinct
    let mut total = 0usize;
    for (h, e) in &factors {
        comparisons += 1;
        if h.lc() != Some(1) || h.degree().unwrap_or(0) == 0 || *e == 0 {
            return Divergence::new(
                "up-zp-factor",
                "identity",
                "a factor is non-monic, constant, or has zero multiplicity".to_string(),
                vec![
                    ("input".to_string(), render_zp(&m, &reduced)),
                    ("factor".to_string(), render_zp(&m, h)),
                    ("mult".to_string(), e.to_string()),
                ],
            );
        }
        total += h.degree().unwrap_or(0) * *e;
    }
    for i in 0..factors.len() {
        for j in i + 1..factors.len() {
            comparisons += 1;
            if factors[i].0 == factors[j].0 {
                return Divergence::new(
                    "up-zp-factor",
                    "identity",
                    format!("factors {i} and {j} are equal; multiplicities must be merged"),
                    vec![
                        ("input".to_string(), render_zp(&m, &reduced)),
                        ("factor".to_string(), render_zp(&m, &factors[i].0)),
                    ],
                );
            }
        }
    }

    // (c) the independent irreducibility witness
    for (h, _) in &factors {
        let Some(irr) = m.is_irreducible(h) else {
            return Outcome::Declined("irreducibility test refused");
        };
        comparisons += 1;
        if !irr {
            return Divergence::new(
                "up-zp-factor",
                "identity",
                "a returned factor is REDUCIBLE by Rabin's test".to_string(),
                vec![
                    ("input".to_string(), render_zp(&m, &reduced)),
                    ("factor".to_string(), render_zp(&m, h)),
                ],
            );
        }
    }

    // (c2) THE WITNESS ITSELF IS WITNESSED — a negative control.
    //
    // Leg (c) only ever asks `is_irreducible` about polynomials that ARE
    // irreducible, so it is satisfied by a test that answers `true`
    // unconditionally. A verifier proved that: hardwiring
    // `Zp::is_irreducible -> Some(true)` produced ZERO divergences over 5,400
    // fuzz cases while quietly dropping `selftest` detection for this check
    // from 39 of 39 to 17 of 39. An independent witness that is never asked a
    // question it could answer wrongly is not a witness.
    //
    // The product of two DISTINCT returned factors is reducible by
    // construction, so the test must say so.
    if factors.len() >= 2 {
        let composite = m.mul(&factors[0].0, &factors[1].0);
        let Some(irr) = m.is_irreducible(&composite) else {
            return Outcome::Declined("irreducibility test refused a composite");
        };
        comparisons += 1;
        if irr {
            return Divergence::new(
                "up-zp-factor",
                "identity",
                "the irreducibility test called a PRODUCT OF TWO FACTORS irreducible — the \
                 witness leg above is vacuous"
                    .to_string(),
                vec![
                    ("input".to_string(), render_zp(&m, &reduced)),
                    ("f0".to_string(), render_zp(&m, &factors[0].0)),
                    ("f1".to_string(), render_zp(&m, &factors[1].0)),
                ],
            );
        }
    }

    // (d) degrees sum
    comparisons += 1;
    if total != n {
        return Divergence::new(
            "up-zp-factor",
            "identity",
            format!("degrees sum to {total} but the input has degree {n}"),
            vec![("input".to_string(), render_zp(&m, &reduced))],
        );
    }

    // (e) the counter pin. Re-derive the number of equal-degree inputs and
    // outputs from the answer: run square-free + distinct-degree again (both
    // deterministic) and count buckets; every split adds exactly one factor.
    let Some((_, monic)) = m.monic(&reduced) else {
        return Outcome::Declined("monic refused");
    };
    let Some(sqf) = m.square_free_decomposition(&monic) else {
        return Outcome::Declined("square-free decomposition refused");
    };
    let mut buckets = 0usize;
    let mut produced = 0usize;
    for (h, _) in &sqf {
        let Some(bs) = m.distinct_degree(h) else {
            return Outcome::Declined("distinct_degree refused");
        };
        for (bucket, d) in bs {
            buckets += 1;
            produced += bucket.degree().unwrap_or(0) / d.max(1);
        }
    }
    let expected_splits = u64::try_from(produced.saturating_sub(buckets)).unwrap_or(0);
    comparisons += 1;
    if stats.edf_splits != expected_splits {
        return Divergence::new(
            "up-zp-factor",
            "identity",
            format!(
                "edf_splits counter says {} but {produced} factors from {buckets} buckets \
                 imply exactly {expected_splits}",
                stats.edf_splits
            ),
            vec![("input".to_string(), render_zp(&m, &reduced))],
        );
    }
    Outcome::Match(comparisons)
}

// ---------------------------------------------------------------------------
// Cost measurement on ADVERSARIAL inputs
// ---------------------------------------------------------------------------

/// One row of the factorization cost table.
pub(crate) struct CostRow {
    pub(crate) family: &'static str,
    pub(crate) p: u64,
    pub(crate) degree: usize,
    pub(crate) factors: usize,
    pub(crate) us: u128,
    pub(crate) ddf_iters: u64,
    pub(crate) edf_attempts: u64,
    pub(crate) edf_splits: u64,
    pub(crate) powmods: u64,
    pub(crate) powmod_mults: u64,
    pub(crate) ok: bool,
}

/// Build `prod_{i=0}^{n-1} (x - i)` over `Z_p`: `n` distinct LINEAR factors.
///
/// This is the worst case for equal-degree factorization and the one that
/// hides an exponential: distinct-degree finishes in a single iteration and
/// hands Cantor-Zassenhaus one bucket containing all `n` factors, so every
/// factor has to be separated by random splitting.
fn split_family(m: &OZpMgr, n: usize) -> OUniZp {
    let mut f = m.one();
    for i in 0..n as u64 {
        let c = (m.p() - (i % m.p())) % m.p();
        f = m.mul(&f, &m.from_u64(vec![c, 1]));
    }
    f
}

/// An IRREDUCIBLE polynomial of degree `n` over `Z_p`, found by scanning.
///
/// This is the worst case for distinct-degree factorization: the loop cannot
/// exit early, so it runs the full `n/2` iterations, each doing a `powmod`
/// with exponent `p` on a degree-`n` modulus. Nothing is ever removed.
fn irreducible_family(m: &OZpMgr, n: usize) -> Option<OUniZp> {
    for seed in 1..4000u64 {
        let mut c = vec![0u64; n + 1];
        c[n] = 1;
        let mut s = seed;
        for slot in c.iter_mut().take(n) {
            s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
            *slot = (s >> 33) % m.p();
        }
        let f = m.from_u64(c);
        if f.degree() != Some(n) {
            continue;
        }
        if m.is_irreducible(&f) == Some(true) {
            return Some(f);
        }
    }
    None
}

/// `(x^d + 1)^k`: a high multiplicity, which forces the square-free
/// decomposition to iterate before factorization starts.
fn power_family(m: &OZpMgr, base_deg: usize, k: usize) -> OUniZp {
    let mut c = vec![0u64; base_deg + 1];
    c[base_deg] = 1;
    c[0] = 1;
    let base = m.from_u64(c);
    let mut f = m.one();
    for _ in 0..k {
        f = m.mul(&f, &base);
    }
    f
}

fn measure(family: &'static str, m: &OZpMgr, f: &OUniZp) -> CostRow {
    let degree = f.degree().unwrap_or(0);
    m.reset_stats();
    let t0 = std::time::Instant::now();
    let res = m.factor(f);
    let us = t0.elapsed().as_micros();
    let s = m.stats();
    let (factors, ok) = match &res {
        Some((lc, fs)) => {
            // Verify the identity here too: a cost number for a WRONG answer
            // is worse than no number.
            let mut prod = m.from_u64(vec![*lc]);
            for (h, e) in fs {
                for _ in 0..*e {
                    prod = m.mul(&prod, h);
                }
            }
            (fs.len(), prod == *f)
        }
        None => (0, false),
    };
    CostRow {
        family,
        p: m.p(),
        degree,
        factors,
        us,
        ddf_iters: s.ddf_iters,
        edf_attempts: s.edf_attempts,
        edf_splits: s.edf_splits,
        powmods: s.powmods,
        powmod_mults: s.powmod_mults,
        ok,
    }
}

/// Measure factorization cost on adversarial families.
///
/// Not a differential check — there is nothing to compare against. It exists
/// because "the factorization is correct" says nothing about whether it is
/// exponential, and this campaign has already shipped a correct multivariate
/// GCD that took 20 seconds on a 25-term input because only coefficient width
/// was being measured.
pub(crate) fn measure_cost(max_n: usize) -> Vec<CostRow> {
    let mut rows = Vec::new();
    for p in [3u64, 101, 65_537] {
        let Some(m) = OZpMgr::new(p) else { continue };
        // Family 1: fully split — worst case for equal-degree.
        let mut n = 8;
        while n <= max_n {
            if u64::try_from(n).unwrap_or(u64::MAX) <= p {
                let f = split_family(&m, n);
                if f.degree() == Some(n) {
                    rows.push(measure("split-linear", &m, &f));
                }
            }
            n *= 2;
        }
        // Family 2: irreducible — worst case for distinct-degree.
        let mut n = 8;
        while n <= max_n {
            if let Some(f) = irreducible_family(&m, n) {
                rows.push(measure("irreducible", &m, &f));
            }
            n *= 2;
        }
        // Family 3: a high power — worst case for square-free decomposition.
        let mut k = 8;
        while k * 2 <= max_n {
            let f = power_family(&m, 2, k);
            rows.push(measure("power-of-quadratic", &m, &f));
            k *= 2;
        }
    }
    rows
}
