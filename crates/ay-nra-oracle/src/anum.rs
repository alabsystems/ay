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
use crate::z3::{Ast, Z3};

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
pub(crate) fn dyadic_iv(z3: &Z3, v: Ast) -> Option<OBqInterval> {
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
fn z3_of(z3: &Z3, a: &ODyadicAnum) -> Option<Ast> {
    z3_of_strict(z3, a).ok()
}

/// [`z3_of`], keeping the two failure modes apart.
///
/// `Err(true)` means z3 itself declined (a skip). `Err(false)` means z3
/// answered and AY's interval brackets **zero or two-or-more** of z3's roots —
/// a violated isolating invariant, which is a DIVERGENCE. Collapsing the two
/// into one `None` turned a broken construction into a decline, and a decline is
/// not a divergence.
fn z3_of_strict(z3: &Z3, a: &ODyadicAnum) -> Result<Ast, bool> {
    if let Some(r) = a.to_rational() {
        return z3.rational(&r).ok_or(true);
    }
    let coeffs = rationals(&a.poly_coeffs().ok_or(false)?);
    let roots = z3.roots(&coeffs).ok_or(true)?;
    let iv = a.interval().ok_or(false)?;
    let lo = z3.rational(&iv.lo().to_rational()).ok_or(true)?;
    let hi = z3.rational(&iv.hi().to_rational()).ok_or(true)?;
    let mut found: Option<Ast> = None;
    for r in roots {
        if z3.gt(r, lo).ok_or(true)? && z3.lt(r, hi).ok_or(true)? {
            if found.is_some() {
                return Err(false);
            }
            found = Some(r);
        }
    }
    found.ok_or(false)
}

fn z3_cmp(z3: &Z3, a: Ast, b: Ast) -> Option<Ordering> {
    if z3.eq(a, b)? {
        Some(Ordering::Equal)
    } else if z3.lt(a, b)? {
        Some(Ordering::Less)
    } else if z3.gt(a, b)? {
        Some(Ordering::Greater)
    } else {
        None
    }
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
fn widest_iv(z3: &Z3, p: &[BigInt], v: Ast) -> Option<OBqInterval> {
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

/// Isolating-interval resolution requested by an oracle check.
#[derive(Clone, Copy)]
enum BracketStyle {
    Fine,
    Widest,
}

/// Build an AY algebraic number for the `i`-th ascending real root of `p`, plus
/// z3's own AST for that root.
fn build_with(
    z3: &Z3,
    p: &[BigInt],
    i: usize,
    style: BracketStyle,
) -> Option<(ODyadicAnum, Ast, usize)> {
    let roots = z3.roots(&rationals(p))?;
    if roots.is_empty() {
        return None;
    }
    let idx = i % roots.len();
    let v = roots[idx];
    let iv = match style {
        BracketStyle::Fine => dyadic_iv(z3, v)?,
        BracketStyle::Widest => widest_iv(z3, p, v)?,
    };
    let a = ODyadicAnum::from_poly_interval(p, &iv)?;
    Some((a, v, idx))
}

fn build(z3: &Z3, p: &[BigInt], i: usize) -> Option<(ODyadicAnum, Ast, usize)> {
    build_with(z3, p, i, BracketStyle::Fine)
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
mod compare;
mod growth;
mod representation;
mod separation;
mod sign;

pub(crate) use arithmetic::check_arith;
pub(crate) use compare::check_compare;
pub(crate) use growth::measure_chain_growth;
pub(crate) use representation::check_representation;
pub(crate) use separation::check_separation;
pub(crate) use sign::check_sign_at;
