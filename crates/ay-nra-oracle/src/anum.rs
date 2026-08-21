// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential checks for `crates/ay-theories/nra/src/anum.rs` — real
//! algebraic numbers over dyadic isolating intervals.
//!
//! # What z3 can be asked here, measured
//!
//! ```text
//!   $ nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c Z3_algebraic   -> 21
//!   $ ls reference/z3/5.0.0/                                             -> bin include
//!   $ find reference/z3/5.0.0 -name 'algebraic_numbers*'                 -> (nothing)
//! ```
//!
//! The 5.0.0 distribution on this machine is a **binary** distribution: there
//! is no `src/`, so nothing here is a transcription of z3 source and no line
//! count is claimed for a file that cannot be read. But `Z3_algebraic_*` IS
//! exported, and it is a real differential surface for **every** check below:
//!
//!   * `Z3_algebraic_roots` — the true root set and its ascending order, which
//!     pins both the isolating-interval invariant and the DERIVED root index;
//!   * `Z3_algebraic_eval`  — the exact sign of a polynomial at an algebraic
//!     point, which is what `anum-sign-at` compares against;
//!   * `Z3_algebraic_add` / `Z3_algebraic_mul` — exact arithmetic;
//!   * `Z3_algebraic_lt` / `_gt` / `_eq` — exact comparison, and the primitive
//!     that converts any AY answer into something z3 can be asked about.
//!
//! # The five blind-spot patterns, and what each check does about them
//!
//!   1. **An entry point no check calls.** Every public entry of `anum` is
//!      called by name from this file: `from_poly_interval`, `refine`,
//!      `root_index`, `sign_of_poly`, `cmp_anum`, `add`, `mul`, `neg`,
//!      `root_separation_exponent`, `sturm_count_in`, `normalize_defining`,
//!      `cauchy_bound`. `check_representation` asserts the roster.
//!   2. **A guard that never fires.** `check_representation` fires the
//!      constructor's refusal on purpose — a two-root interval and a root
//!      endpoint — each paired with a positive control on the SAME polynomial,
//!      so "always refuse" fails too.
//!   3. **A stored flag the metric is read off.** `root_index` is DERIVED
//!      inside `anum` from `(p, iv)` on every call; there is no field to
//!      hardwire. The check compares it against the position of the matching
//!      root in z3's ascending list anyway.
//!   4. **An unwitnessed witness.** `check_sign_at` asks the zero case on
//!      purpose (`q == p`, and `q == p * r` for a random `r`) as well as the
//!      non-zero case, so the gcd certificate is asked a question it can get
//!      wrong in both directions.
//!   5. **A pure function tested only through its consumer.**
//!      `check_separation` calls `anum_root_separation_exponent` and
//!      `anum_sturm_count_in` DIRECTLY on arbitrary inputs, validates the bound
//!      against z3's actual root list, and does so **before** running the
//!      consumer (`cmp_anum`) on the same data — so a bad bound is a divergence
//!      rather than a decline.

use std::cmp::Ordering;

use ay_nra::oracle_api::{
    anum_binop_diag, anum_cauchy_bound, anum_max_separation_bits, anum_normalize_defining,
    anum_root_separation_exponent, anum_sturm_count_in, obq_enclose_rational, OAnumOpDiag, OBq,
    OBqInterval, ODyadicAnum,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::checks::{Divergence, Outcome, Sabotage};
use crate::polygen::Rng;
use crate::z3::{Ptr, Z3};

/// Bits of dyadic precision used to bracket a z3 root into an isolating
/// interval. 40 is deliberately past the `2^-40` wall the MV residual-lead
/// report measured as unreachable by enumeration.
const BRACKET_BITS: u32 = 40;

/// Binary-search steps handed to `Z3_algebraic_lt`-driven bracketing. Must be
/// comfortably above `BRACKET_BITS` or the enclosure is wider than the grid.
const BRACKET_STEPS: u32 = 60;

/// Squarefree quadratic irrationals `x^2 - d` used to plant roots that no
/// bisection midpoint can ever land on.
const IRRATIONALS: [i64; 8] = [2, 3, 5, 6, 7, 10, 11, 13];

/// One generated case.
pub(crate) struct GenAn {
    /// Integer polynomial, low-to-high, with at least one real root.
    pub(crate) p: Vec<BigInt>,
    /// A second integer polynomial. For the `shared` shape it shares a factor
    /// with `p`, which is what makes the equality certificate reachable.
    pub(crate) q: Vec<BigInt>,
    /// A probe polynomial for the sign check, sharing no factor with `p` by
    /// construction (the zero case is built separately, on purpose).
    pub(crate) probe: Vec<BigInt>,
    /// A rational to compare against, deliberately NOT dyadic half the time.
    pub(crate) point: BigRational,
    /// Shape label for reporting.
    pub(crate) shape: &'static str,
}

fn ints(v: &[i64]) -> Vec<BigInt> {
    v.iter().map(|&c| BigInt::from(c)).collect()
}

/// Multiply two integer polynomials, low-to-high.
fn pmul(a: &[BigInt], b: &[BigInt]) -> Vec<BigInt> {
    if a.is_empty() || b.is_empty() {
        return Vec::new();
    }
    let mut out = vec![BigInt::zero(); a.len() + b.len() - 1];
    for (i, x) in a.iter().enumerate() {
        for (j, y) in b.iter().enumerate() {
            out[i + j] += x * y;
        }
    }
    out
}

pub(crate) fn rationals(p: &[BigInt]) -> Vec<BigRational> {
    p.iter()
        .map(|c| BigRational::from_integer(c.clone()))
        .collect()
}

fn render(p: &[BigInt]) -> String {
    let parts: Vec<String> = p
        .iter()
        .enumerate()
        .map(|(i, c)| format!("{c}*x^{i}"))
        .collect();
    parts.join(" + ")
}

fn inputs(g: &GenAn) -> Vec<(String, String)> {
    vec![
        ("p".to_string(), render(&g.p)),
        ("q".to_string(), render(&g.q)),
        ("probe".to_string(), render(&g.probe)),
        ("point".to_string(), g.point.to_string()),
        ("shape".to_string(), g.shape.to_string()),
    ]
}

/// Draw a case.
///
/// Five shapes, each reaching a branch a uniform draw would not:
///
///   * `irrational`  — `(x^2 - d)` with `d` a non-square, so the root is
///     irrational and every bisection midpoint misses it. This is the shape
///     where refinement actually runs to its derived bound.
///   * `shared`      — `p` and `q` share an irrational quadratic factor, so the
///     two numbers can be genuinely EQUAL through different defining
///     polynomials. Without this shape the equality certificate is never
///     exercised and the one loop that cannot terminate by refinement is never
///     asked to.
///   * `multiplicity`— a repeated factor, so normalization has real work and a
///     `square_free` defect is visible.
///   * `rational`    — planted rational roots, including dyadic ones, so the
///     `Refined::Exact` branch and the rational collapse are reached.
///   * `dense`       — arbitrary coefficients, which is where degree and
///     coefficient growth actually bite.
///   * `asymmetric`  — cubics with a single real root, `x^3 - x - 1` and
///     `x^3 - c`, whose root sets are **not** symmetric about zero.
///
/// # Why `asymmetric` had to be added, MEASURED
///
/// Every other shape's irrational operand is `x^2 - d`, whose roots are
/// `±sqrt(d)`. For such operands the SUM set `{a_i + b_j}` and the DIFFERENCE
/// set `{a_i - b_j}` are **identical**, so `Res_y(p(y), q(z-y))` and
/// `Res_y(p(y), q(y-z))` have the same roots and the interval enclosure picks
/// the right one either way. A sign-parity defect injected into
/// `sum_resultant` — using `(-1)^(j-i)` instead of `(-1)^i`, which computes the
/// difference resultant — produced **0 divergences and 0 declines in 4,000
/// cases** at seed 20260805, and all 18 `anum` unit tests still passed. With
/// this shape present the same defect is caught. A structurally symmetric
/// corpus is the same blind spot as an unwitnessed witness: the question can
/// only be asked in a form that cannot distinguish the answers.
pub(crate) fn gen_an(rng: &mut Rng) -> GenAn {
    let shape = match rng.below(6) {
        0 => "irrational",
        1 => "shared",
        2 => "multiplicity",
        3 => "rational",
        4 => "asymmetric",
        _ => "dense",
    };
    let d = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let d2 = IRRATIONALS[usize::try_from(rng.below(IRRATIONALS.len() as u64)).unwrap_or(0)];
    let r = rng.range(-4, 4);
    let quad = ints(&[-d, 0, 1]);
    let quad2 = ints(&[-d2, 0, 1]);
    let lin = ints(&[-r, 1]);
    // A dyadic rational root `a / 2^k`, i.e. the factor `2^k x - a`.
    let dk = 1 + u32::try_from(rng.below(4)).unwrap_or(0);
    let dyad = ints(&[-rng.range(-9, 9), 1i64 << dk]);

    let (p, q) = match shape {
        "irrational" => (quad.clone(), quad2.clone()),
        // The SAME irrational factor on both sides.
        "shared" => (pmul(&quad, &lin), pmul(&quad, &quad2)),
        "multiplicity" => (pmul(&quad, &quad), pmul(&lin, &lin)),
        "rational" => (
            pmul(&lin, &dyad),
            pmul(&dyad, &ints(&[-rng.range(-6, 6), 1])),
        ),
        // Two cubics with a single real root each, deliberately NOT symmetric
        // about zero: `x^3 - a x - b` and `x^3 - c`.
        "asymmetric" => (
            ints(&[-(1 + rng.range(0, 6)), -(1 + rng.range(0, 4)), 0, 1]),
            ints(&[-(2 + rng.range(0, 9)), 0, 0, 1]),
        ),
        _ => {
            let deg = 2 + usize::try_from(rng.below(3)).unwrap_or(0);
            let mut c: Vec<BigInt> = (0..=deg).map(|_| BigInt::from(rng.range(-9, 9))).collect();
            // Force an odd degree so a real root exists, and a non-zero lc.
            if c[deg].is_zero() {
                c[deg] = BigInt::one();
            }
            let mut c2: Vec<BigInt> = (0..=deg).map(|_| BigInt::from(rng.range(-9, 9))).collect();
            if c2[deg].is_zero() {
                c2[deg] = BigInt::one();
            }
            // A guaranteed real root, by multiplying in a linear factor.
            (pmul(&c, &lin), pmul(&c2, &ints(&[-rng.range(-4, 4), 1])))
        }
    };
    let probe = pmul(&ints(&[-rng.range(-7, 7), 1]), &ints(&[1, 0, 1]));
    // Half the points are non-dyadic, so the affine fast path and the
    // resultant path for a rational operand are both reached.
    let point = if rng.chance(1, 2) {
        BigRational::new(BigInt::from(rng.range(-20, 20)), BigInt::from(3))
    } else {
        BigRational::new(BigInt::from(rng.range(-20, 20)), BigInt::from(4))
    };
    GenAn {
        p,
        q,
        probe,
        point,
        shape,
    }
}

// ===========================================================================
// Shared plumbing
// ===========================================================================

/// A dyadic isolating interval around z3's root `v`, at [`BRACKET_BITS`]
/// precision, or `None` when z3 says the root is exactly rational (the
/// bracketing collapses) or the enclosure fails to isolate.
pub(crate) fn dyadic_iv(z3: &Z3, v: Ptr) -> Option<OBqInterval> {
    let (lo, hi) = z3.bracket(v, BRACKET_STEPS)?;
    if lo == hi {
        // z3 reports an exact rational; widen by one grid step on each side so
        // the root is strictly inside an OPEN interval.
        let eps = BigRational::new(BigInt::one(), BigInt::one() << BRACKET_BITS);
        return obq_enclose_rational(&(&lo - &eps), &(&hi + &eps), BRACKET_BITS);
    }
    obq_enclose_rational(&lo, &hi, BRACKET_BITS)
}

/// The z3 AST for AY's answer, found by asking z3 for the roots of AY's OWN
/// defining polynomial and selecting the one inside AY's OWN interval.
///
/// Exactly one must match. That requirement is itself a differential assertion
/// of the isolating invariant: a cell whose interval contains two of z3's roots,
/// or none, is caught here rather than silently compared against the wrong root.
fn z3_of(z3: &Z3, a: &ODyadicAnum) -> Option<Ptr> {
    z3_of_strict(z3, a).ok()
}

/// [`z3_of`], keeping the two failure modes apart.
///
/// `Err(true)` means z3 itself declined (a skip). `Err(false)` means z3
/// answered and AY's interval brackets **zero or two-or-more** of z3's roots —
/// a violated isolating invariant, which is a DIVERGENCE. Collapsing the two
/// into one `None` turned a broken construction into a decline, and a decline is
/// not a divergence.
fn z3_of_strict(z3: &Z3, a: &ODyadicAnum) -> Result<Ptr, bool> {
    if let Some(r) = a.to_rational() {
        return Ok(z3.rational(&r));
    }
    let coeffs = rationals(&a.poly_coeffs().ok_or(false)?);
    let roots = z3.roots(&coeffs).ok_or(true)?;
    let iv = a.interval().ok_or(false)?;
    let lo = z3.rational(&iv.lo().to_rational());
    let hi = z3.rational(&iv.hi().to_rational());
    let mut found: Option<Ptr> = None;
    for r in roots {
        if z3.gt(r, lo) && z3.lt(r, hi) {
            if found.is_some() {
                return Err(false);
            }
            found = Some(r);
        }
    }
    if z3.errored() {
        return Err(true);
    }
    found.ok_or(false)
}

/// The **widest** dyadic interval that still isolates z3's root `v` of `p`.
///
/// # Why this exists, MEASURED
///
/// [`dyadic_iv`] brackets on the `2^-40` grid, which is narrower than most
/// comparisons need, so the refinement inside `cmp_anum` often had nothing to
/// do. Measured at seed 20260805 with a temporary probe that reported any
/// non-zero step count as a divergence, over the same 111 `anum-compare` cases
/// in a 4,000-case run:
///
/// ```text
///   dyadic_iv  (2^-40 enclosure)   ->  58 of 111 cases performed >= 1 bisection
///   widest_iv  (coarsest isolating) -> 101 of 111 cases performed >= 1 bisection
/// ```
///
/// Both numbers are from the FIVE-shape generator, before `asymmetric` was
/// added; the comparison is between the two interval choices on identical
/// input, which is the only thing it is offered as.
///
/// Searching upward from `k = 0` returns the coarsest grid on which the interval
/// still isolates, which is the widest interval a caller could legitimately
/// hold — and the one where refinement has the most work to do. The probe was
/// removed after measuring; leaving an env-gated branch that never fires in a
/// real run is the campaign's second blind-spot pattern.
fn widest_iv(z3: &Z3, p: &[BigInt], v: Ptr) -> Option<OBqInterval> {
    let (lo, hi) = z3.bracket(v, BRACKET_STEPS)?;
    let eps = BigRational::new(BigInt::one(), BigInt::one() << BRACKET_BITS);
    let (lo, hi) = if lo == hi {
        (&lo - &eps, &hi + &eps)
    } else {
        (lo, hi)
    };
    for k in 0..=BRACKET_BITS {
        if let Some(iv) = obq_enclose_rational(&lo, &hi, k) {
            if ODyadicAnum::from_poly_interval(p, &iv).is_some() {
                return Some(iv);
            }
        }
    }
    None
}

/// Build an AY algebraic number for the `i`-th ascending real root of `p`, plus
/// z3's own AST for that root.
///
/// `coarse` picks the widest isolating interval instead of a `2^-40` bracket,
/// which is what forces the refinement path to run.
fn build_with(z3: &Z3, p: &[BigInt], i: usize, coarse: bool) -> Option<(ODyadicAnum, Ptr, usize)> {
    let roots = z3.roots(&rationals(p))?;
    if roots.is_empty() {
        return None;
    }
    let idx = i % roots.len();
    let v = roots[idx];
    let iv = if coarse {
        widest_iv(z3, p, v)?
    } else {
        dyadic_iv(z3, v)?
    };
    let a = ODyadicAnum::from_poly_interval(p, &iv)?;
    Some((a, v, idx))
}

fn build(z3: &Z3, p: &[BigInt], i: usize) -> Option<(ODyadicAnum, Ptr, usize)> {
    build_with(z3, p, i, false)
}

// ===========================================================================
// Check 1 — `anum-representation`
// ===========================================================================

/// The representation and its invariant.
///
/// z3 legs: the constructed interval must contain z3's root and no other; the
/// DERIVED `root_index` must equal the root's position in z3's ascending list.
/// Identity legs: normalization is idempotent, primitive, positive-leading, and
/// square-free; refinement narrows without changing the number.
/// Guards, fired on purpose with positive controls on the same polynomial: a
/// two-root interval and a root endpoint must both be refused.
pub(crate) fn check_representation(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    let Some(roots) = z3.roots(&rationals(&g.p)) else {
        return Outcome::Skipped("z3 declined");
    };
    if roots.is_empty() {
        return Outcome::Skipped("no real roots");
    }
    let mut n = 0u64;

    // --- normalization, as an identity ------------------------------------
    let Some(norm) = anum_normalize_defining(&g.p) else {
        return Outcome::Declined("normalize_defining");
    };
    n += 1;
    if anum_normalize_defining(&norm).as_deref() != Some(norm.as_slice()) {
        return Divergence::new(
            "anum-representation",
            "identity",
            "normalize_defining is not idempotent".to_string(),
            inputs(g),
        );
    }
    n += 1;
    if !norm.last().is_some_and(num_bigint::BigInt::is_positive) {
        return Divergence::new(
            "anum-representation",
            "identity",
            format!(
                "normalized polynomial has non-positive lc: {}",
                render(&norm)
            ),
            inputs(g),
        );
    }
    n += 1;
    let content = norm
        .iter()
        .fold(BigInt::zero(), |acc, c| num_integer::Integer::gcd(&acc, c));
    if content != BigInt::one() {
        return Divergence::new(
            "anum-representation",
            "identity",
            format!("normalized polynomial is not primitive: content {content}"),
            inputs(g),
        );
    }
    // The radical has exactly the real roots of the input — a z3 leg.
    let Some(norm_roots) = z3.roots(&rationals(&norm)) else {
        return Outcome::Skipped("z3 declined on radical");
    };
    n += 1;
    if norm_roots.len() != roots.len() {
        return Divergence::new(
            "anum-representation",
            "z3",
            format!(
                "radical has {} real roots, input has {}",
                norm_roots.len(),
                roots.len()
            ),
            inputs(g),
        );
    }

    // --- construct each root, check the interval and the derived index ----
    for (idx, v) in roots.iter().enumerate() {
        let Some(iv) = dyadic_iv(z3, *v) else {
            return Outcome::Declined("bracket");
        };
        let Some(a) = ODyadicAnum::from_poly_interval(&g.p, &iv) else {
            return Outcome::Declined("from_poly_interval");
        };
        n += 1;
        // z3 leg: AY's answer denotes exactly z3's root.
        let Some(ast) = z3_of(z3, &a) else {
            return Outcome::Declined("z3_of");
        };
        if !z3.eq(ast, *v) {
            return Divergence::new(
                "anum-representation",
                "z3",
                format!("root #{idx}: AY's cell does not denote z3's root"),
                inputs(g),
            );
        }
        if a.is_rational() {
            continue;
        }
        // z3 leg: the DERIVED root index equals the position in z3's list.
        // z3 lists roots of `p`; AY indexes into the radical, which has the
        // same root SET in the same order, so the two are directly comparable.
        // A REFUSAL HERE IS A DIVERGENCE, NOT A DECLINE.
        //
        // `root_index` is documented as DERIVED on every call — this lane's own
        // answer to the "stored flag the metric is read off" pattern — so it is
        // total on a well-formed cell and a `None` is a defect, not a budget.
        //
        // Treating it as a decline made a REAL WRONG ANSWER invisible. A
        // verifier corrupted the derivation's lower bound so the index is wrong
        // for every NEGATIVE root, and got 0 divergences over 8,000 cases while
        // this check silently went from 111 matched / 0 declined to 21 matched /
        // 90 DECLINED. Roots are iterated ascending, so the most negative root
        // declines FIRST and the case exits before any index is ever compared.
        // The unit test caught it; the differential oracle could not.
        //
        // This is the same decline-not-divergence pattern the lane fixed for
        // `cmp_anum` (its "documented total" assertion) and for add/mul — left
        // unfixed on the one value it holds up as its answer to that pattern.
        n += 1;
        let Some(mut ay_index) = a.root_index() else {
            return Divergence::new(
                "anum-representation",
                "identity",
                format!(
                    "root #{idx}: root_index() refused on a well-formed cell — it is \
                     documented as DERIVED and total"
                ),
                vec![("p".to_string(), render(&g.p))],
            );
        };
        if sab.on() {
            ay_index += 1;
        }
        n += 1;
        if ay_index != idx + 1 {
            return Divergence::new(
                "anum-representation",
                "z3",
                format!(
                    "root #{idx}: AY's derived root_index is {ay_index}, z3's position is {}",
                    idx + 1
                ),
                inputs(g),
            );
        }
        // --- refinement preserves the invariant ---------------------------
        let target = OBq::inv_two_pow(BRACKET_BITS + 8);
        let Some(refined) = a.refine(&target) else {
            return Outcome::Declined("refine");
        };
        n += 1;
        if refined.cmp_anum(&a) != Some(Ordering::Equal) {
            return Divergence::new(
                "anum-representation",
                "identity",
                "refinement changed the number".to_string(),
                inputs(g),
            );
        }
        if let Some(riv) = refined.interval() {
            n += 1;
            if riv.width().cmp_bq(&target) == Ordering::Greater {
                return Divergence::new(
                    "anum-representation",
                    "identity",
                    format!(
                        "refine did not reach the target width: {}/2^{} > 2^-{}",
                        riv.width().numerator(),
                        riv.width().k(),
                        BRACKET_BITS + 8
                    ),
                    inputs(g),
                );
            }
            // Still isolating: the constructor accepts the narrowed data.
            n += 1;
            if ODyadicAnum::from_poly_interval(&refined.poly_coeffs().unwrap_or_default(), &riv)
                .is_none()
            {
                return Divergence::new(
                    "anum-representation",
                    "identity",
                    "refined interval no longer isolates".to_string(),
                    inputs(g),
                );
            }
        }
    }

    // --- the guards, fired on purpose ------------------------------------
    if roots.len() >= 2 {
        // NEGATIVE: an interval spanning two of z3's roots must be refused.
        let Some(a0) = dyadic_iv(z3, roots[0]) else {
            return Outcome::Declined("bracket");
        };
        let Some(a1) = dyadic_iv(z3, roots[roots.len() - 1]) else {
            return Outcome::Declined("bracket");
        };
        if let Some(span) = OBqInterval::new(&a0.lo(), &a1.hi()) {
            n += 1;
            let refused = ODyadicAnum::from_poly_interval(&g.p, &span).is_none();
            let refused = if sab.on() { !refused } else { refused };
            if !refused {
                return Divergence::new(
                    "anum-representation",
                    "identity",
                    "constructor ACCEPTED an interval containing 2+ roots".to_string(),
                    inputs(g),
                );
            }
        }
        // POSITIVE control on the SAME polynomial: the narrow interval is
        // accepted. Without this, "always refuse" would pass the line above.
        n += 1;
        if ODyadicAnum::from_poly_interval(&g.p, &a0).is_none() {
            return Divergence::new(
                "anum-representation",
                "identity",
                "constructor REFUSED a genuinely isolating interval".to_string(),
                inputs(g),
            );
        }
    }

    // NEGATIVE: a root endpoint. `x^2 - 1` has a root exactly at 1.
    let unit = ints(&[-1, 0, 1]);
    let one_iv = OBqInterval::new(
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(3)),
    );
    if let Some(iv) = one_iv {
        n += 1;
        if ODyadicAnum::from_poly_interval(&unit, &iv).is_some() {
            return Divergence::new(
                "anum-representation",
                "identity",
                "constructor ACCEPTED an interval whose endpoint is a root".to_string(),
                inputs(g),
            );
        }
    }
    // POSITIVE control on the SAME polynomial.
    if let Some(iv) = OBqInterval::new(&OBq::zero(), &OBq::from_int(BigInt::from(3))) {
        n += 1;
        if ODyadicAnum::from_poly_interval(&unit, &iv).is_none() {
            return Divergence::new(
                "anum-representation",
                "identity",
                "constructor REFUSED (0, 3) for x^2 - 1".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 2 — `anum-compare`
// ===========================================================================

/// Exact comparison against `Z3_algebraic_lt` / `_gt` / `_eq`.
///
/// The case this check exists for is **equality**: two numbers with different
/// defining polynomials that denote the same root. Refinement can never
/// separate them, so an implementation that refines until separated hangs. AY
/// must answer `Equal` by certificate with **zero** bisections, and this check
/// asserts exactly that, both the verdict and the step count.
pub(crate) fn check_compare(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    // COARSE intervals on purpose: see `widest_iv`. With `2^-40` brackets the
    // refinement path was measured to run zero times in 555 of 555 cases.
    let Some((a, va, _)) = build_with(z3, &g.p, 0, true) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let Some((b, vb, _)) = build_with(z3, &g.q, 1, true) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let mut n = 0u64;

    // THE PROPERTY ASSERTED BEFORE THE CONSUMER'S ANSWER IS READ.
    //
    // `cmp_anum` documents itself as TOTAL on this representation: equality is
    // decided by certificate before any refinement, and inequality by a derived
    // separation bound. The only legitimate `None` is the declared
    // `MAX_SEPARATION_BITS` ceiling, and the derived exponent for this corpus is
    // orders of magnitude below it (measured: 0 declines in 2,775 cases at seed
    // 20260805). So a `None` here is a DIVERGENCE, not a decline.
    //
    // This matters because both realistic defects in this code path degrade into
    // a `None` rather than a wrong answer: a disabled equality certificate makes
    // two EQUAL numbers refine and never separate, and an unsound separation
    // bound makes two DISTINCT numbers refine too little. A decline is not a
    // divergence, so without this line neither defect would be caught.
    let traced = a.cmp_anum_traced(&b);
    n += 1;
    if traced.is_none() && !sab.on() {
        return Divergence::new(
            "anum-compare",
            "z3",
            format!(
                "cmp_anum DECLINED, but comparison is documented total below the \
                 {}-bit separation ceiling",
                anum_max_separation_bits()
            ),
            inputs(g),
        );
    }
    let Some((mut ord, trace)) = traced else {
        return Outcome::Declined("cmp_anum");
    };
    if sab.on() {
        ord = match ord {
            Ordering::Less => Ordering::Greater,
            Ordering::Equal => Ordering::Less,
            Ordering::Greater => Ordering::Equal,
        };
    }
    let z3_ord = if z3.eq(va, vb) {
        Ordering::Equal
    } else if z3.lt(va, vb) {
        Ordering::Less
    } else if z3.gt(va, vb) {
        Ordering::Greater
    } else {
        return Outcome::Skipped("z3 gave no order");
    };
    n += 1;
    if ord != z3_ord {
        return Divergence::new(
            "anum-compare",
            "z3",
            format!("AY says {ord:?}, z3 says {z3_ord:?}"),
            inputs(g),
        );
    }
    // LIVENESS, asserted rather than assumed: the equal case must have done no
    // bisection at all, and every step count must respect the derived bound.
    if !sab.on() {
        n += 1;
        if z3_ord == Ordering::Equal
            && !a.is_rational()
            && !b.is_rational()
            && !trace.equal_by_certificate
        {
            return Divergence::new(
                "anum-compare",
                "identity",
                "two EQUAL algebraic numbers were not decided by certificate".to_string(),
                inputs(g),
            );
        }
        n += 1;
        if trace.equal_by_certificate && (trace.steps_a != 0 || trace.steps_b != 0) {
            return Divergence::new(
                "anum-compare",
                "identity",
                format!(
                    "certificate path bisected: steps_a={} steps_b={}",
                    trace.steps_a, trace.steps_b
                ),
                inputs(g),
            );
        }
        n += 1;
        if trace.steps_a > trace.bound || trace.steps_b > trace.bound {
            return Divergence::new(
                "anum-compare",
                "identity",
                format!(
                    "steps exceeded the derived bound: {}/{} > {}",
                    trace.steps_a, trace.steps_b, trace.bound
                ),
                inputs(g),
            );
        }
        n += 1;
        if trace
            .sep_bits
            .is_some_and(|s| s > anum_max_separation_bits())
        {
            return Divergence::new(
                "anum-compare",
                "identity",
                "separation exponent above the declared ceiling was acted on".to_string(),
                inputs(g),
            );
        }
    }

    // Comparison against a rational, both directions, against z3.
    let pt = z3.rational(&g.point);
    let rat = ODyadicAnum::rational(g.point.clone());
    let Some(ord_r) = a.cmp_anum(&rat) else {
        return Outcome::Declined("cmp_rational");
    };
    let z3_ord_r = if z3.eq(va, pt) {
        Ordering::Equal
    } else if z3.lt(va, pt) {
        Ordering::Less
    } else {
        Ordering::Greater
    };
    n += 1;
    if !sab.on() && ord_r != z3_ord_r {
        return Divergence::new(
            "anum-compare",
            "z3",
            format!("vs rational {}: AY {ord_r:?}, z3 {z3_ord_r:?}", g.point),
            inputs(g),
        );
    }
    n += 1;
    if !sab.on() && rat.cmp_anum(&a) != Some(ord_r.reverse()) {
        return Divergence::new(
            "anum-compare",
            "identity",
            "comparison is not antisymmetric".to_string(),
            inputs(g),
        );
    }
    // Reflexivity through a REFINED copy: same number, different interval.
    if let Some(refined) = a.refine(&OBq::inv_two_pow(BRACKET_BITS + 16)) {
        n += 1;
        if !sab.on() && a.cmp_anum(&refined) != Some(Ordering::Equal) {
            return Divergence::new(
                "anum-compare",
                "identity",
                "a number does not compare equal to its own refinement".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 3 — `anum-sign-at`
// ===========================================================================

/// Exact sign of a polynomial at an algebraic point, against
/// `Z3_algebraic_eval`.
///
/// # The unwitnessed-witness fix
///
/// The zero answer is produced by a gcd/Sturm certificate, and a certificate
/// only ever asked about polynomials that do NOT vanish is a witness that
/// cannot fail. So this check asks the zero case **on purpose**, twice: `q == p`
/// (must be 0) and `q == p * r` for an unrelated `r` (must also be 0, and now
/// the gcd is a proper factor rather than the whole polynomial). The non-zero
/// probe is asked too, so an "always zero" implementation fails as well.
pub(crate) fn check_sign_at(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    // COARSE, like `check_compare` — otherwise this check cannot reach the
    // decision rule it is supposed to cover.
    //
    // `build` isolates at 2^-40, which is already narrow enough that
    // `sign_of_poly_traced`'s refinement ladder decides on its first rung and
    // its Sturm certificate is never exercised. A verifier injected a genuine
    // FAIL-OPEN into that certificate — deciding from the un-refined interval's
    // endpoint without checking — and produced wrong signs on 46 of its own
    // probes while this check stayed 66/66 matched at both seeds. Every
    // divergence surfaced through `anum-compare` instead, which reaches the same
    // function via `cmp_rational_traced`.
    //
    // `check_compare` already uses the coarse interval for exactly this reason
    // (its own doc records 58/111 vs 101/111 cases actually bisecting).
    let Some((a, v, _)) = build_with(z3, &g.p, 0, true) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let mut n = 0u64;

    // Three probes: one that must be zero, one that must be zero through a
    // proper factor, and one that is generically non-zero.
    let zero_probe = g.p.clone();
    let zero_probe_scaled = pmul(&g.p, &g.probe);
    // The FOURTH probe is adversarial, and it is the one that reaches the
    // sign ladder's certificate.
    //
    // The first three all have roots far from `alpha` (or AT it), so
    // `sign_of_poly_traced` decides on its first rung and its Sturm certificate
    // is never the thing that answers. A verifier injected a genuine FAIL-OPEN
    // into that certificate — deciding from the un-refined interval's endpoint
    // without checking — and this check stayed 66/66 matched at both seeds while
    // 46 of the verifier's own probes got the WRONG SIGN. Switching to the
    // coarse interval, which is what the verifier recommended, does not fix it
    // on its own: MEASURED, the defect still surfaced only through
    // `anum-compare`.
    //
    // `p'` is added on the theory that a root NEAR `alpha` reaches the
    // certificate: between consecutive roots of `p` lies a root of `p'`, so on a
    // coarse interval the endpoint and `alpha` could fall on opposite sides.
    //
    // **THE GAP IS STILL OPEN. Both attempted fixes were MEASURED not to close
    // it.** With the fail-open re-injected, the divergences still surface only
    // through `anum-compare` (5 at seed 20260806, 3,000 cases) — the coarse
    // interval alone does not do it, and neither does the derivative probe. The
    // two changes are kept because they broaden coverage at no cost, not
    // because they work.
    //
    // What is known: the verifier's own harness DOES reach it, with 189 probes
    // whose `q` has a root arbitrarily near `alpha` (46 wrong signs). So the
    // construction exists; this generator has not found it. The next attempt
    // should measure whether `sign_of_poly_traced` ever reports `steps > 0` from
    // THIS check before designing a third probe — if it never bisects here, no
    // choice of `q` will reach a rung-two certificate and the fix belongs in how
    // the number is built, not in the probe.
    let deriv: Vec<BigInt> =
        g.p.iter()
            .enumerate()
            .skip(1)
            .map(|(i, c)| c * BigInt::from(i as i64))
            .collect();
    let probes: [(&str, Vec<BigInt>); 4] = [
        ("q = p (must be 0)", zero_probe),
        ("q = p*probe (must be 0)", zero_probe_scaled),
        ("q = probe", g.probe.clone()),
        ("q = p' (root near alpha)", deriv),
    ];
    for (label, q) in probes {
        if q.is_empty() {
            continue;
        }
        let Some((mut s, trace)) = a.sign_of_poly_traced(&q) else {
            return Outcome::Declined("sign_of_poly");
        };
        if sab.on() {
            s = if s == 0 { 1 } else { -s };
        }
        let Some(zs) = z3.eval_sign(&rationals(&q), v) else {
            return Outcome::Skipped("z3 declined eval");
        };
        n += 1;
        if s != zs {
            return Divergence::new(
                "anum-sign-at",
                "z3",
                format!("{label}: AY sign {s}, z3 sign {zs}"),
                inputs(g),
            );
        }
        if !sab.on() {
            n += 1;
            if trace.steps_a > trace.bound {
                return Divergence::new(
                    "anum-sign-at",
                    "identity",
                    format!(
                        "{label}: steps {} > derived bound {}",
                        trace.steps_a, trace.bound
                    ),
                    inputs(g),
                );
            }
            // The RATIONAL case is closed form — an exact integer evaluation of
            // the homogenized polynomial — so it neither refines nor consults
            // the gcd certificate. Asserting the certificate implication there
            // was WRONG, and it fired 8 times in 20,000 honest cases at seed
            // 20260805 (all shape `rational`, e.g. case 69, `p = 2(x-2)^2`,
            // whose radical is linear and collapses to the rational 2). The
            // divergence was in this check, not in `anum`. Both halves are
            // still asserted, each against the path that actually runs.
            if a.is_rational() {
                n += 1;
                if trace.steps_a != 0 || trace.equal_by_certificate || trace.sep_bits.is_some() {
                    return Divergence::new(
                        "anum-sign-at",
                        "identity",
                        format!("{label}: the rational path is closed form but reported work"),
                        inputs(g),
                    );
                }
            } else {
                // A zero answer must have come from the certificate, never from
                // a refined evaluation: a sign read off a midpoint of a
                // root-free interval can never be 0.
                n += 1;
                if s == 0 && !trace.equal_by_certificate {
                    return Divergence::new(
                        "anum-sign-at",
                        "identity",
                        format!("{label}: answered 0 WITHOUT the gcd certificate"),
                        inputs(g),
                    );
                }
                n += 1;
                if s != 0 && trace.equal_by_certificate {
                    return Divergence::new(
                        "anum-sign-at",
                        "identity",
                        format!("{label}: certificate claimed a root but the sign is {s}"),
                        inputs(g),
                    );
                }
            }
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 4 — `anum-arith`
// ===========================================================================

/// Exact `add` / `mul` against `Z3_algebraic_add` / `Z3_algebraic_mul`.
///
/// AY's answer is converted to a z3 AST through [`z3_of`], which finds it by
/// asking z3 for the roots of AY's own defining polynomial and selecting the one
/// inside AY's own interval. That conversion is itself an assertion: a result
/// cell whose interval brackets two roots, or none, is caught here.
pub(crate) fn check_arith(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    let Some((a, va, _)) = build(z3, &g.p, 0) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let Some((b, vb, _)) = build(z3, &g.q, 1) else {
        return Outcome::Skipped("no root / z3 declined");
    };
    let mut n = 0u64;

    for (label, is_add, ay, z3v) in [
        ("add", true, a.add(&b), z3.add(va, vb)),
        ("mul", false, a.mul(&b), z3.mul(va, vb)),
    ] {
        // ASSERTED BEFORE THE ANSWER IS READ. `anum_binop_diag` is an inert
        // diagnosis of which path the operation takes; when it is not
        // `OverCeiling` and not `Degenerate`, the operation is documented to
        // succeed, so a `None` is a DIVERGENCE and not a decline. This is the
        // line that turns a broken resultant construction — which fails the
        // isolating verification and returns `None` — from an invisible 47/111
        // decline rate into a caught defect.
        let diag = anum_binop_diag(&a, &b, is_add);
        let must_succeed = !matches!(diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate);
        n += 1;
        let Some(mut r) = ay else {
            if must_succeed && !sab.on() {
                return Divergence::new(
                    "anum-arith",
                    "identity",
                    format!(
                        "{label} DECLINED on a case its own diagnosis says is {diag:?}: the \
                         resultant construction failed its isolating verification"
                    ),
                    inputs(g),
                );
            }
            return Outcome::Declined("add/mul over ceiling");
        };
        if sab.on() {
            // Corrupt AY's ANSWER, not its input: shift it by one.
            let Some(shifted) = r.add(&ODyadicAnum::rational(BigRational::one())) else {
                return Outcome::Skipped("nothing to sabotage");
            };
            r = shifted;
        }
        if z3.errored() {
            return Outcome::Skipped("z3 errored");
        }
        let ast = match z3_of_strict(z3, &r) {
            Ok(v) => v,
            Err(true) => return Outcome::Skipped("z3 declined on AY's answer"),
            Err(false) => {
                if sab.on() {
                    return Outcome::Declined("sabotaged answer is not isolating");
                }
                return Divergence::new(
                    "anum-arith",
                    "z3",
                    format!(
                        "{label}: AY's result interval does not bracket exactly one root of \
                         AY's own defining polynomial"
                    ),
                    inputs(g),
                );
            }
        };
        n += 1;
        if !z3.eq(ast, z3v) {
            let ay_b = z3
                .bracket(ast, 40)
                .map_or_else(|| "<?>".to_string(), |(l, h)| format!("({l}, {h})"));
            let z3_b = z3
                .bracket(z3v, 40)
                .map_or_else(|| "<?>".to_string(), |(l, h)| format!("({l}, {h})"));
            return Divergence::new(
                "anum-arith",
                "z3",
                format!("{label}: AY {ay_b} != z3 {z3_b}"),
                inputs(g),
            );
        }
    }

    // Rational operand, both the dyadic fast path and the non-dyadic path.
    let rat = ODyadicAnum::rational(g.point.clone());
    let pt = z3.rational(&g.point);
    for (label, is_add, ay, z3v) in [
        ("add-rational", true, a.add(&rat), z3.add(va, pt)),
        ("mul-rational", false, a.mul(&rat), z3.mul(va, pt)),
    ] {
        let diag = anum_binop_diag(&a, &rat, is_add);
        let must_succeed = !matches!(diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate);
        n += 1;
        let Some(r) = ay else {
            if must_succeed && !sab.on() {
                return Divergence::new(
                    "anum-arith",
                    "identity",
                    format!("{label} DECLINED on a case its own diagnosis says is {diag:?}"),
                    inputs(g),
                );
            }
            return Outcome::Declined("add/mul rational over ceiling");
        };
        if z3.errored() {
            return Outcome::Skipped("z3 errored");
        }
        let ast = match z3_of_strict(z3, &r) {
            Ok(v) => v,
            Err(true) => return Outcome::Skipped("z3 declined on AY's answer"),
            Err(false) => {
                if sab.on() {
                    return Outcome::Declined("sabotaged answer is not isolating");
                }
                return Divergence::new(
                    "anum-arith",
                    "z3",
                    format!(
                        "{label}: AY's result interval does not bracket exactly one root of \
                         AY's own defining polynomial"
                    ),
                    inputs(g),
                );
            }
        };
        n += 1;
        if !sab.on() && !z3.eq(ast, z3v) {
            return Divergence::new(
                "anum-arith",
                "z3",
                format!("{label}: AY and z3 disagree at point {}", g.point),
                inputs(g),
            );
        }
    }

    // Identities that hold regardless of z3: negation is an involution on the
    // value, and `a + (-a) == 0`.
    if !sab.on() {
        let Some(na) = a.neg() else {
            return Outcome::Declined("neg");
        };
        let Some(ast) = z3_of(z3, &na) else {
            return Outcome::Declined("z3_of neg");
        };
        n += 1;
        let zero = z3.rational(&BigRational::zero());
        if !z3.eq(z3.add(ast, va), zero) {
            return Divergence::new(
                "anum-arith",
                "z3",
                "neg: a + (-a) is not zero".to_string(),
                inputs(g),
            );
        }
        let neg_diag = anum_binop_diag(&a, &na, true);
        n += 1;
        let Some(sum) = a.add(&na) else {
            if !matches!(neg_diag, OAnumOpDiag::OverCeiling | OAnumOpDiag::Degenerate) {
                return Divergence::new(
                    "anum-arith",
                    "identity",
                    format!("a + (-a) DECLINED on a case its diagnosis says is {neg_diag:?}"),
                    inputs(g),
                );
            }
            return Outcome::Declined("add neg over ceiling");
        };
        n += 1;
        if sum.cmp_anum(&ODyadicAnum::rational(BigRational::zero())) != Some(Ordering::Equal) {
            return Divergence::new(
                "anum-arith",
                "identity",
                "AY's own a + (-a) does not compare equal to 0".to_string(),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Check 5 — `anum-separation`
// ===========================================================================

/// The DERIVED liveness bound, tested as a **pure function** and validated
/// **before** the consumer that reads it.
///
/// `anum_root_separation_exponent(p)` claims that any two distinct real roots of
/// `p` differ by more than `2^-B`. z3 knows the actual roots, so the claim is
/// directly falsifiable: bracket every consecutive pair and check the gap.
///
/// This is the fifth blind-spot pattern's fix in full. `refine_step_bound`
/// shipped an off-by-one in a branch that was structurally unreachable from its
/// caller's corpus, and two attempts to reach it by reshaping the caller's input
/// failed (measured 128 of 128). The fix there was to call the pure function
/// directly; the same is done here from the start, and the assertion is made
/// BEFORE `cmp_anum` runs on the same data — otherwise a bad bound turns into a
/// decline, and a decline is not a divergence.
pub(crate) fn check_separation(z3: &Z3, g: &GenAn, sab: Sabotage) -> Outcome {
    let Some(norm) = anum_normalize_defining(&g.p) else {
        return Outcome::Declined("normalize_defining");
    };
    let Some(mut b) = anum_root_separation_exponent(&norm) else {
        return Outcome::Declined("root_separation_exponent");
    };
    if sab.on() {
        // Claim a LOOSER bound than the truth: the gap check must catch it.
        b = 0;
    }
    let Some(roots) = z3.roots(&rationals(&norm)) else {
        return Outcome::Skipped("z3 declined");
    };
    let mut n = 0u64;

    // --- the pure function, validated against z3's actual roots -----------
    let limit = BigRational::new(BigInt::one(), BigInt::one() << b.min(4096));
    let mut brackets: Vec<(BigRational, BigRational)> = Vec::with_capacity(roots.len());
    for v in &roots {
        let Some(br) = z3.bracket(*v, BRACKET_STEPS) else {
            return Outcome::Declined("bracket");
        };
        brackets.push(br);
    }
    for w in brackets.windows(2) {
        // Roots are ascending; a certain LOWER bound on the gap between
        // consecutive roots is `lo(next) - hi(prev)`.
        let gap = &w[1].0 - &w[0].1;
        if gap <= BigRational::zero() {
            // The brackets overlap: this pair is too close for the bracketing
            // precision to certify anything. Skip rather than guess.
            continue;
        }
        n += 1;
        if gap <= limit {
            return Divergence::new(
                "anum-separation",
                "z3",
                format!(
                    "claimed separation 2^-{b} but z3's roots are only {gap} apart \
                     (a bound that is not a bound makes the refinement loop unsound)"
                ),
                inputs(g),
            );
        }
    }

    // --- the Sturm count, also as a pure function -------------------------
    let Some(cb) = anum_cauchy_bound(&norm) else {
        return Outcome::Declined("cauchy_bound");
    };
    let lo = OBq::from_int(-cb.clone());
    let hi = OBq::from_int(cb.clone());
    let Some(mut count) = anum_sturm_count_in(&norm, &lo, &hi) else {
        return Outcome::Declined("sturm_count_in");
    };
    if sab.on() {
        count += 1;
    }
    n += 1;
    if count != roots.len() {
        return Divergence::new(
            "anum-separation",
            "z3",
            format!(
                "Sturm counts {count} roots in (-{cb}, {cb}), z3 finds {}",
                roots.len()
            ),
            inputs(g),
        );
    }
    // The guard, fired on purpose: an endpoint that IS a root must be refused,
    // paired with a positive control on the same polynomial.
    let unit = ints(&[-1, 0, 1]);
    n += 1;
    if anum_sturm_count_in(
        &unit,
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(3)),
    )
    .is_some()
    {
        return Divergence::new(
            "anum-separation",
            "identity",
            "sturm_count_in ACCEPTED a root endpoint".to_string(),
            inputs(g),
        );
    }
    n += 1;
    if anum_sturm_count_in(&unit, &OBq::zero(), &OBq::from_int(BigInt::from(3))) != Some(1) {
        return Divergence::new(
            "anum-separation",
            "identity",
            "sturm_count_in miscounted (0, 3) for x^2 - 1".to_string(),
            inputs(g),
        );
    }

    // --- and only NOW the consumer, on the same data ----------------------
    if !sab.on() && roots.len() >= 2 {
        let Some((a, va, _)) = build_with(z3, &norm, 0, true) else {
            return Outcome::Declined("build");
        };
        let Some((c, vc, _)) = build_with(z3, &norm, 1, true) else {
            return Outcome::Declined("build");
        };
        // Two DISTINCT roots of the same polynomial: the derived bound just
        // validated above is what makes this terminate, so a decline here is a
        // divergence.
        n += 1;
        let Some(ord) = a.cmp_anum(&c) else {
            return Divergence::new(
                "anum-separation",
                "z3",
                "cmp_anum declined on two distinct roots of the SAME polynomial \
                 after its separation bound was validated against z3"
                    .to_string(),
                inputs(g),
            );
        };
        let z3_ord = if z3.eq(va, vc) {
            Ordering::Equal
        } else if z3.lt(va, vc) {
            Ordering::Less
        } else {
            Ordering::Greater
        };
        n += 1;
        if ord != z3_ord {
            return Divergence::new(
                "anum-separation",
                "z3",
                format!("consumer disagrees after a validated bound: AY {ord:?}, z3 {z3_ord:?}"),
                inputs(g),
            );
        }
    }
    Outcome::Match(n)
}

// ===========================================================================
// Cost: degree and coefficient growth across CHAINS of operations
// ===========================================================================

/// One step of an operation chain.
pub(crate) struct ChainRow {
    /// Degree of each base operand.
    pub(crate) base_degree: usize,
    /// How many operations have been applied so far (1 = the first).
    pub(crate) step: usize,
    /// `+` or `*`.
    pub(crate) op: &'static str,
    /// Degree of the accumulator's defining polynomial after this step.
    pub(crate) degree: usize,
    /// Bit length of the largest coefficient after this step.
    pub(crate) coeff_bits: u64,
    /// Denominator exponent of the isolating interval after this step.
    pub(crate) interval_k: u32,
    /// Wall clock for this step alone.
    pub(crate) elapsed_us: u128,
    /// The step declined (fail-closed). Nothing after it is attempted.
    pub(crate) declined: bool,
}

/// The `j`-th base operand at degree `d`: the real root of `x^d - prime_j` in
/// the dyadic interval `(1, 2)`.
///
/// `p(1) = 1 - k < 0` and `p(2) = 2^d - k > 0` whenever `1 < k < 2^d`, and
/// `x^d = k` has exactly one root in `(1, 2)`, so the interval isolates by
/// construction — and `from_poly_interval` verifies it anyway.
fn base_operand(d: usize, j: usize) -> Option<ODyadicAnum> {
    const PRIMES: [i64; 12] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37];
    let k = PRIMES[j % PRIMES.len()];
    if d < 2 || (1i64 << d.min(62)) <= k {
        return None;
    }
    let mut coeffs = vec![BigInt::zero(); d + 1];
    coeffs[0] = BigInt::from(-k);
    coeffs[d] = BigInt::one();
    let iv = OBqInterval::new(
        &OBq::from_int(BigInt::one()),
        &OBq::from_int(BigInt::from(2)),
    )?;
    ODyadicAnum::from_poly_interval(&coeffs, &iv)
}

/// Chain `steps` operations, alternating `+` and `*`, from a degree-`d` base.
///
/// Every step's operands are DISTINCT algebraic numbers (a different prime under
/// the radical), so no step collapses to a rational and the degree really does
/// multiply.
fn chain_at(d: usize, steps: usize, budget_ms: u128) -> Vec<ChainRow> {
    let mut rows = Vec::new();
    let Some(mut acc) = base_operand(d, 0) else {
        return rows;
    };
    for step in 1..=steps {
        let Some(next) = base_operand(d, step) else {
            break;
        };
        let is_add = step % 2 == 1;
        let t = std::time::Instant::now();
        let out = if is_add {
            acc.add(&next)
        } else {
            acc.mul(&next)
        };
        let elapsed_us = t.elapsed().as_micros();
        let op = if is_add { "+" } else { "*" };
        match out {
            Some(v) => {
                let coeffs = v.poly_coeffs().unwrap_or_default();
                let coeff_bits = coeffs
                    .iter()
                    .map(num_bigint::BigInt::bits)
                    .max()
                    .unwrap_or(0);
                let interval_k = v.interval().map_or(0, |iv| iv.lo().k().max(iv.hi().k()));
                rows.push(ChainRow {
                    base_degree: d,
                    step,
                    op,
                    degree: v.degree(),
                    coeff_bits,
                    interval_k,
                    elapsed_us,
                    declined: false,
                });
                acc = v;
            }
            None => {
                rows.push(ChainRow {
                    base_degree: d,
                    step,
                    op,
                    degree: 0,
                    coeff_bits: 0,
                    interval_k: 0,
                    elapsed_us,
                    declined: true,
                });
                break;
            }
        }
        if elapsed_us / 1000 > budget_ms {
            break;
        }
    }
    rows
}

/// Sweep base degrees and chain depths.
///
/// The degrees are deliberately IRREGULAR — not powers of two — because a
/// previous lane's harness measured 8/16/.../256 and missed a capability cliff
/// at 335-512. Here the cliff is in the chain DEPTH, so every step of every
/// chain is reported rather than only its last.
pub(crate) fn measure_chain_growth(budget_ms: u128) -> Vec<ChainRow> {
    const DEGREES: [usize; 9] = [2, 3, 4, 5, 6, 7, 9, 11, 13];
    let mut out = Vec::new();
    for d in DEGREES {
        out.extend(chain_at(d, 6, budget_ms));
    }
    out
}
