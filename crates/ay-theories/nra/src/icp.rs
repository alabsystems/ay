// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval branch-and-prune (ICP) decision procedure for SMALL MULTIVARIATE
//! polynomial systems over the reals — the QF_NRA fragment produced by
//! sketch-geometry constraint clusters (distance / tangency / closure loops,
//! typically 2–12 unknowns).
//!
//! The exact pre-phases in `univariate.rs` decide the univariate,
//! linear-substitution and two-variable-grid fragments; genuinely coupled
//! systems like
//!
//! ```smt
//! x2^2 = 100 ; x3^2 + y3^2 = 64 ; (x3-x2)^2 + y3^2 = 49 ; y3 > 0
//! ```
//!
//! fall through all of them to the tangent linearization and come back
//! `unknown`. This module decides them with a dReal-style INTERVAL
//! branch-and-prune, made *exact* (dReal's verdict is `delta-sat`; ours is a
//! genuine `sat`/`unsat`):
//!
//!  1. Every asserted atom is normalized to `poly REL 0` ([`MultiConstraint`]).
//!  2. Each variable gets a rational interval seeded from its explicit linear
//!     bounds ([`collect_variable_bounds`]); a HC4-revise-style *projection
//!     contractor* then tightens the box: for each constraint and each monomial
//!     `c * x^k * m` of it, the monomial's feasible range is `REL-range minus
//!     the interval of the remaining terms`, and dividing by the interval of
//!     `c * m` and taking outward-rounded k-th roots contracts `x`.
//!  3. Boxes whose constraint intervals lie entirely on the wrong side of a
//!     relation are REFUTED; otherwise the widest variable is bisected and both
//!     halves are pushed (branch and prune).
//!  4. SAT is claimed only through one of two *certificates*: either (a) a
//!     concrete rational point verified by EXACT substitution into every
//!     original asserted atom ([`NraSolver::verify_model`]); or (b) a
//!     Krawczyk interval-Newton EXISTENCE certificate — for a square system
//!     of equalities `F = 0` over a box `X`, if the Krawczyk image
//!     `K(X) = m - Y*F(m) + (I - Y*J(X))(X - m)` is STRICTLY contained in
//!     the interior of `X` (with `m` the rational midpoint, `Y` the exact
//!     rational inverse of the midpoint Jacobian, and `J(X)` the interval
//!     Jacobian), then `F` has a zero in `X` (Krawczyk 1969; Neumaier,
//!     "Interval Methods for Systems of Equations", Thm. 5.1.8). Every
//!     remaining (inequality / disequality) constraint is then shown to
//!     hold over ALL of `X` by interval evaluation, so the certified zero
//!     satisfies the whole system. The witness is typically IRRATIONAL
//!     (e.g. `y3 = 3*sqrt(55)/4` above); the result is reported through
//!     the existing [`UniResult::SatAlgebraic`] channel exactly like the
//!     univariate Sturm/IVT certificate.
//!  5. UNSAT is claimed only when the box tree is EXHAUSTED with every leaf
//!     refuted by interval arithmetic. Any budget/width/precision give-up
//!     poisons exhaustiveness and the phase returns `Unknown` — fail-closed.
//!
//! Underdetermined systems (fewer equalities than variables — e.g. a
//! slider-crank sketch with a free driving angle) additionally get a SAT-ONLY
//! *pinned* search: enough variables are pinned to heuristically chosen exact
//! rational values to square the system (the pin set is the complement of a
//! maximum structural matching between equalities and variables), and the
//! branch-and-prune runs on the reduced system. Pins are a heuristic, so this
//! path NEVER claims UNSAT.
//!
//! ## Numeric hygiene
//!
//! All interval endpoints are exact `BigRational` (arbitrary-precision
//! `num/den`), reusing the sound [`Interval`] primitives of the interval
//! UNSAT pre-phase — no `f64` anywhere, no epsilon comparisons. The only
//! rounding is the OUTWARD rounding of k-th roots (`kth_root_lower` /
//! `kth_root_upper`, exact when the argument is a perfect k-th power, else
//! directed to a dyadic rational with denominator `2^ROOT_SCALE_BITS`), which
//! only ever WIDENS an interval and therefore preserves soundness of both
//! refutation and certification. Unbounded variables keep genuinely infinite
//! endpoints during contraction; a variable still unbounded when the search
//! starts is clamped to the large initial box `[-2^20, 2^20]` for
//! SEARCHABILITY ONLY — the clamp forfeits the right to answer UNSAT (the
//! whole tree is then marked non-exhaustive), never soundness.
//!
//! ## Proof obligations
//!
//! Like the other exact NRA pre-phases (`try_interval_unsat`, `try_sos_unsat`,
//! the Sturm/IVT univariate decider), an UNSAT verdict is returned as a theory
//! conflict over the asserted atoms without a replayable proof certificate; no
//! certificate is fabricated. SAT verdicts carry either a concrete rational
//! model or a full mixed witness assignment (exact rationals for the pinned
//! variables plus an exact `RealAlgebraic` root for the free variable) that
//! the executor stores in its model, exactly like the univariate Sturm/IVT
//! path.

use ay_core::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::univariate::{
    collect_variable_bounds, constraint_is_infeasible, eval_poly_interval, intersect_intervals,
    isolate_roots, negate_endpoint_to_hi, negate_endpoint_to_lo, rational_sign, scale_interval,
    square_free_part, sturm_count, sturm_sequence, Endpoint, Interval, LinExpr, MultiAtom,
    MultiConstraint, MultiPoly, Rel, RootMarker, UniPoly, UniResult, UniWitness,
};
use crate::NraSolver;

/// Maximum number of distinct variables the procedure attempts (sketch-scale).
const MAX_ICP_VARS: usize = 12;

/// Maximum number of parsed polynomial constraints.
const MAX_ICP_CONSTRAINTS: usize = 256;

/// Budget of boxes processed by the main branch-and-prune tree. Debug builds
/// use a smaller budget because unoptimized `BigRational` arithmetic is ~100x
/// slower (same rationale as the check-loop iteration cap, #6785).
#[cfg(debug_assertions)]
const MAX_BOXES: usize = 512;
#[cfg(not(debug_assertions))]
const MAX_BOXES: usize = 2048;

/// Budget of boxes for each SAT-only pinned attempt (small: a good pin
/// collapses the box in a handful of contractions).
const PIN_SEARCH_MAX_BOXES: usize = 128;

/// Total pinned (pin-variable, pin-value) attempts per call.
const MAX_PIN_ATTEMPTS: usize = 12;

/// Budget of boxes when variables had to be CLAMPED to the large initial box:
/// such trees cannot prove UNSAT and only the first few boxes plausibly yield
/// a rational candidate, so a long search is wasted work.
const CLAMPED_MAX_BOXES: usize = 64;

/// Contraction passes per box before bisecting.
const MAX_CONTRACT_PASSES: usize = 10;

/// Above this many constraints, a single `contract_box` call is pass-bounded
/// (see [`contract_passes`]).
const DENSE_CONSTRAINT_THRESHOLD: usize = 32;

/// Pass budget for one [`contract_box`] call, as a function of the constraint
/// count. A BOUNDED infeasibility surfaces within the first pass or two — the
/// dense ASME virtual-gauge pin-fit clusters refute at pass 0, the
/// over-constrained triangle at pass 1 — after which extra passes over a large
/// constraint set only chase the SAT-side fixpoint that the tangent/relaxation
/// path reaches far faster. So the budget SHRINKS on dense systems, bounding the
/// `O(passes × constraints × monomials)` exact-rational cost of those dozens-of-
/// atoms feasibility queries. This never changes a verdict: fewer passes only
/// UNDER-tighten the box (sound — a refutation is a proven-empty interval, which
/// still fires; a SAT box still falls through to the certifying paths), so at
/// worst a give-up returns the honest `Unknown`. Small systems keep the full
/// budget so the coupled sketch clusters contract to their fixpoint as before.
fn contract_passes(n_constraints: usize) -> usize {
    if n_constraints > DENSE_CONSTRAINT_THRESHOLD {
        2
    } else {
        MAX_CONTRACT_PASSES
    }
}

/// Dyadic outward-rounding precision for k-th roots: denominators `2^24`.
const ROOT_SCALE_BITS: usize = 24;

/// Boxes narrower than this in EVERY dimension stop bisecting (give up on the
/// box, poisoning exhaustiveness): `2^-16`.
const MIN_WIDTH_LOG2: i32 = -16;

/// Clamp magnitude for variables still unbounded after initial contraction:
/// `2^20`. Documented SAT-search box only (see module docs).
const UNBOUNDED_CLAMP_LOG2: usize = 20;

/// Krawczyk attempts are gated to boxes whose widest free dimension is at most
/// this wide (the operator is quadratically convergent only near a root; on
/// wide boxes the containment test just fails after an O(n^3) exact-rational
/// matrix inversion, so we do not pay for it until the box is plausible).
fn krawczyk_max_width() -> BigRational {
    BigRational::from_integer(BigInt::from(2))
}

fn min_width() -> BigRational {
    BigRational::new(BigInt::one(), BigInt::one() << (-MIN_WIDTH_LOG2 as usize))
}

// ============================================================================
// Interval helpers on top of the sound `Interval` primitives.
// ============================================================================

/// Negate an interval: `-[a,b] = [-b,-a]` (endpoint inclusivity preserved).
fn neg_interval(iv: &Interval) -> Interval {
    Interval {
        lo: negate_endpoint_to_lo(&iv.hi),
        hi: negate_endpoint_to_hi(&iv.lo),
    }
}

/// Interval subtraction `a - b`.
fn sub_interval(a: &Interval, b: &Interval) -> Interval {
    a.add(&neg_interval(b))
}

/// Is the interval PROVABLY empty? Conservative: only `lo > hi` by value, or
/// `lo == hi` with a PROVEN-open endpoint (the inclusivity discipline of the
/// interval primitives guarantees `inclusive = false` implies genuine
/// non-attainment). Degenerate infinite shapes report non-empty (sound: we
/// never refute on them).
fn interval_is_empty(iv: &Interval) -> bool {
    match (&iv.lo, &iv.hi) {
        (Endpoint::Finite(l, li), Endpoint::Finite(h, hi_inc)) => {
            l > h || (l == h && (!*li || !*hi_inc))
        }
        _ => false,
    }
}

/// Exact rational point of a degenerate interval `[c, c]` (both closed).
fn interval_point(iv: &Interval) -> Option<&BigRational> {
    match (&iv.lo, &iv.hi) {
        (Endpoint::Finite(l, true), Endpoint::Finite(h, true)) if l == h => Some(l),
        _ => None,
    }
}

/// Width `hi - lo` of a finite interval, or `None` if unbounded.
fn interval_width(iv: &Interval) -> Option<BigRational> {
    match (&iv.lo, &iv.hi) {
        (Endpoint::Finite(l, _), Endpoint::Finite(h, _)) => Some(h - l),
        _ => None,
    }
}

/// Midpoint of a finite interval.
fn interval_midpoint(iv: &Interval) -> Option<BigRational> {
    match (&iv.lo, &iv.hi) {
        (Endpoint::Finite(l, _), Endpoint::Finite(h, _)) => {
            Some((l + h) / BigRational::from_integer(BigInt::from(2)))
        }
        _ => None,
    }
}

/// Inclusivity-aware membership test.
fn interval_contains(iv: &Interval, x: &BigRational) -> bool {
    let lo_ok = match &iv.lo {
        Endpoint::NegInf => true,
        Endpoint::PosInf => false,
        Endpoint::Finite(v, inc) => {
            if *inc {
                x >= v
            } else {
                x > v
            }
        }
    };
    let hi_ok = match &iv.hi {
        Endpoint::PosInf => true,
        Endpoint::NegInf => false,
        Endpoint::Finite(v, inc) => {
            if *inc {
                x <= v
            } else {
                x < v
            }
        }
    };
    lo_ok && hi_ok
}

/// Multiplicative inverse `1/iv` when the interval PROVABLY excludes 0,
/// otherwise `None`. `1/(+inf)` is the OPEN endpoint 0 (proven non-attained:
/// `1/y > 0` for every finite `y > 0`); symmetric on the negative side.
fn invert_interval(iv: &Interval) -> Option<Interval> {
    if iv.contains_zero() || interval_is_empty(iv) {
        return None;
    }
    // Reciprocal of a finite non-zero endpoint (inclusivity preserved). Zero
    // and infinite endpoints are handled explicitly by the callers below;
    // this fallback arm is unreachable there and stays conservative.
    let recip = |e: &Endpoint| -> Endpoint {
        match e {
            Endpoint::Finite(v, inc) if !v.is_zero() => {
                Endpoint::Finite(BigRational::one() / v, *inc)
            }
            e => e.clone(),
        }
    };
    // Positive side: lo >= 0 (0 excluded). 1/[lo, hi] = [1/hi, 1/lo].
    let positive = match &iv.lo {
        Endpoint::Finite(v, _) => !v.is_negative(),
        Endpoint::NegInf => false,
        Endpoint::PosInf => return None,
    };
    if positive {
        let lo = match &iv.hi {
            // 1/(+inf) = 0, PROVEN not attained (1/y > 0 for all finite y).
            Endpoint::PosInf => Endpoint::Finite(BigRational::zero(), false),
            e => recip(e),
        };
        let hi = match &iv.lo {
            // Reciprocal of the excluded 0 endpoint: +infinity.
            Endpoint::Finite(v, _) if v.is_zero() => Endpoint::PosInf,
            e => recip(e),
        };
        Some(Interval { lo, hi })
    } else {
        // Negative side: hi <= 0 (0 excluded). 1/[lo, hi] = [1/hi, 1/lo].
        let lo = match &iv.hi {
            Endpoint::Finite(v, _) if v.is_zero() => Endpoint::NegInf,
            e => recip(e),
        };
        let hi = match &iv.lo {
            Endpoint::NegInf => Endpoint::Finite(BigRational::zero(), false),
            e => recip(e),
        };
        Some(Interval { lo, hi })
    }
}

/// Interval division `a / d`, defined only when `d` provably excludes 0.
fn div_interval(a: &Interval, d: &Interval) -> Option<Interval> {
    Some(a.mul(&invert_interval(d)?))
}

/// The feasible range of `poly` under `poly REL 0` (the relation's value set).
/// `Ne` has no single-interval range and returns `None`.
fn rel_range(rel: Rel) -> Option<Interval> {
    let zero_closed = Endpoint::Finite(BigRational::zero(), true);
    let zero_open = Endpoint::Finite(BigRational::zero(), false);
    Some(match rel {
        Rel::Eq => Interval {
            lo: zero_closed.clone(),
            hi: zero_closed,
        },
        Rel::Le => Interval {
            lo: Endpoint::NegInf,
            hi: zero_closed,
        },
        Rel::Lt => Interval {
            lo: Endpoint::NegInf,
            hi: zero_open,
        },
        Rel::Ge => Interval {
            lo: zero_closed,
            hi: Endpoint::PosInf,
        },
        Rel::Gt => Interval {
            lo: zero_open,
            hi: Endpoint::PosInf,
        },
        Rel::Ne => return None,
    })
}

/// Does `poly REL 0` hold for EVERY value of `poly` in `iv`? Conservative dual
/// of [`constraint_is_infeasible`]: openness (`inclusive = false`) is a proven
/// non-attainment, so an open 0 endpoint still admits strict relations.
fn constraint_holds_everywhere(rel: Rel, iv: &Interval) -> bool {
    let lo_val = match &iv.lo {
        Endpoint::NegInf => None,
        Endpoint::PosInf => return false, // degenerate; never certify
        Endpoint::Finite(v, inc) => Some((v, *inc)),
    };
    let hi_val = match &iv.hi {
        Endpoint::PosInf => None,
        Endpoint::NegInf => return false,
        Endpoint::Finite(v, inc) => Some((v, *inc)),
    };
    match rel {
        Rel::Lt => match hi_val {
            Some((v, inc)) => v.is_negative() || (v.is_zero() && !inc),
            None => false,
        },
        Rel::Le => match hi_val {
            Some((v, _)) => !v.is_positive(),
            None => false,
        },
        Rel::Gt => match lo_val {
            Some((v, inc)) => v.is_positive() || (v.is_zero() && !inc),
            None => false,
        },
        Rel::Ge => match lo_val {
            Some((v, _)) => !v.is_negative(),
            None => false,
        },
        // Every value is 0 (regardless of endpoint attainment flags the value
        // set collapses to {0} only when both endpoint VALUES are 0).
        Rel::Eq => {
            matches!((lo_val, hi_val), (Some((l, _)), Some((h, _))) if l.is_zero() && h.is_zero())
        }
        Rel::Ne => !iv.contains_zero(),
    }
}

// ============================================================================
// Outward-rounded rational k-th roots (k >= 1).
// ============================================================================

/// Floor integer k-th root of `n >= 0` (largest `r` with `r^k <= n`).
fn integer_kth_root_floor(n: &BigInt, k: usize) -> BigInt {
    debug_assert!(k >= 1 && !n.is_negative());
    if n.is_zero() || k == 1 {
        return n.clone();
    }
    let mut lo = BigInt::zero();
    // 2^(ceil(bits/k)) is an upper bound on the root.
    let bits = n.bits() as usize;
    let mut hi = BigInt::one() << (bits / k + 1);
    while lo < hi {
        // invariant: lo^k <= n < (hi+1)^k
        let mid: BigInt = (&lo + &hi + BigInt::one()) / BigInt::from(2);
        if mid.pow(k as u32) <= *n {
            lo = mid;
        } else {
            hi = mid - BigInt::one();
        }
    }
    lo
}

/// Ceiling integer k-th root of `n >= 0` (smallest `r` with `r^k >= n`).
fn integer_kth_root_ceil(n: &BigInt, k: usize) -> BigInt {
    let f = integer_kth_root_floor(n, k);
    if f.pow(k as u32) == *n {
        f
    } else {
        f + BigInt::one()
    }
}

/// Exact rational k-th root of `u >= 0` when it is a perfect k-th power of a
/// rational (numerator and denominator both perfect k-th powers in lowest
/// terms), else `None`.
fn exact_rational_kth_root(u: &BigRational, k: usize) -> Option<BigRational> {
    debug_assert!(!u.is_negative());
    let rn = integer_kth_root_floor(u.numer(), k);
    if rn.pow(k as u32) != *u.numer() {
        return None;
    }
    let rd = integer_kth_root_floor(u.denom(), k);
    if rd.pow(k as u32) != *u.denom() {
        return None;
    }
    Some(BigRational::new(rn, rd))
}

/// A SOUND rational lower bound on `u^(1/k)` for `u >= 0`: exact when `u` is a
/// perfect k-th power, else the dyadic `p/2^ROOT_SCALE_BITS` rounded DOWN.
/// Guarantees `result^k <= u` and `result >= 0`.
fn kth_root_lower(u: &BigRational, k: usize) -> BigRational {
    if let Some(r) = exact_rational_kth_root(u, k) {
        return r;
    }
    let scale = BigInt::one() << ROOT_SCALE_BITS;
    // floor(u * 2^(k*S)) as an integer.
    let scaled = u * BigRational::from_integer(scale.pow(k as u32));
    let m = scaled.floor().to_integer();
    BigRational::new(integer_kth_root_floor(&m, k), scale)
}

/// A SOUND rational upper bound on `u^(1/k)` for `u >= 0`: exact when `u` is a
/// perfect k-th power, else the dyadic `p/2^ROOT_SCALE_BITS` rounded UP.
/// Guarantees `result^k >= u`.
fn kth_root_upper(u: &BigRational, k: usize) -> BigRational {
    if let Some(r) = exact_rational_kth_root(u, k) {
        return r;
    }
    let scale = BigInt::one() << ROOT_SCALE_BITS;
    let scaled = u * BigRational::from_integer(scale.pow(k as u32));
    let m = scaled.ceil().to_integer();
    BigRational::new(integer_kth_root_ceil(&m, k), scale)
}

/// Signed k-th root lower bound for ODD k (monotone over all reals).
fn odd_root_lower(v: &BigRational, k: usize) -> BigRational {
    if v.is_negative() {
        -kth_root_upper(&(-v), k)
    } else {
        kth_root_lower(v, k)
    }
}

/// Signed k-th root upper bound for ODD k.
fn odd_root_upper(v: &BigRational, k: usize) -> BigRational {
    if v.is_negative() {
        -kth_root_lower(&(-v), k)
    } else {
        kth_root_upper(v, k)
    }
}

// ============================================================================
// Simplest-rational selection (small pin values / bisection points).
// ============================================================================

/// The rational with the smallest denominator in the CLOSED interval
/// `[lo, hi]` (Stern-Brocot / continued-fraction descent). Requires `lo <= hi`.
fn simplest_rational_between(lo: &BigRational, hi: &BigRational) -> BigRational {
    debug_assert!(lo <= hi);
    // 0 is the simplest rational of all; prefer it (and mirror negative
    // intervals) so symmetric ranges yield 0 rather than `ceil(lo)`.
    if !lo.is_positive() && !hi.is_negative() {
        return BigRational::zero();
    }
    if hi.is_negative() {
        return -simplest_rational_between(&(-hi), &(-lo));
    }
    let c = lo.ceil();
    if &c <= hi {
        return c;
    }
    // lo and hi lie strictly inside one integer gap: recurse on inverses.
    let n = lo.floor();
    let inv = simplest_rational_between(
        &(BigRational::one() / (hi - &n)),
        &(BigRational::one() / (lo - &n)),
    );
    n + BigRational::one() / inv
}

/// A "nice" rational strictly inside the interval: the simplest rational of
/// the closed hull if it is a member, else the simplest of the middle half,
/// else the midpoint. `None` for unbounded/degenerate-empty intervals.
fn nice_point_in(iv: &Interval) -> Option<BigRational> {
    let (lo, hi) = match (&iv.lo, &iv.hi) {
        (Endpoint::Finite(l, _), Endpoint::Finite(h, _)) if l <= h => (l.clone(), h.clone()),
        _ => return None,
    };
    let cand = simplest_rational_between(&lo, &hi);
    if interval_contains(iv, &cand) {
        return Some(cand);
    }
    let quarter = (&hi - &lo) / BigRational::from_integer(BigInt::from(4));
    let cand2 = simplest_rational_between(&(&lo + &quarter), &(&hi - &quarter));
    if interval_contains(iv, &cand2) {
        return Some(cand2);
    }
    let mid = interval_midpoint(iv)?;
    interval_contains(iv, &mid).then_some(mid)
}

// ============================================================================
// The box: per-variable intervals.
// ============================================================================

type VarBox = crate::HashMap<TermId, Interval>;

/// Result of contracting a box against the constraint set.
enum Contraction {
    /// Some constraint is infeasible over the box: the box contains no
    /// solution (PROVEN by sound interval arithmetic).
    Refuted,
    /// Contraction finished (fixpoint or pass budget); box updated in place.
    Done,
}

/// HC4-revise-style projection contraction of `bx` against all constraints,
/// interleaved with whole-constraint interval refutation tests. Sound: every
/// step only removes points that PROVABLY violate some constraint.
fn contract_box(constraints: &[MultiConstraint], vars: &[TermId], bx: &mut VarBox) -> Contraction {
    for _pass in 0..contract_passes(constraints.len()) {
        let mut changed = false;
        for c in constraints {
            // (a) Whole-constraint refutation over the current box.
            if let Some(iv) = eval_poly_interval(&c.poly, bx) {
                if constraint_is_infeasible(c.rel, &iv) {
                    return Contraction::Refuted;
                }
            }
            // (b) Projection contraction, one monomial occurrence at a time.
            let Some(range) = rel_range(c.rel) else {
                continue; // Ne contributes refutation tests only
            };
            for j in 0..c.poly.terms.len() {
                if contract_via_monomial(c, j, &range, vars, bx, &mut changed) {
                    return Contraction::Refuted;
                }
            }
        }
        if !changed {
            break;
        }
    }
    Contraction::Done
}

/// Contract every variable of monomial `j` of constraint `c` using
/// `t_j ∈ range - (sum of the other terms)`. Returns `true` iff the box was
/// PROVEN empty (refuted). Sets `changed` when an interval tightened.
fn contract_via_monomial(
    c: &MultiConstraint,
    j: usize,
    range: &Interval,
    vars: &[TermId],
    bx: &mut VarBox,
    changed: &mut bool,
) -> bool {
    let (mono, coeff) = &c.poly.terms[j];
    if mono.is_empty() {
        return false; // constant term: nothing to contract
    }
    // rest = poly minus term j; S = interval of rest over the box.
    let rest = MultiPoly {
        terms: c
            .poly
            .terms
            .iter()
            .enumerate()
            .filter(|(i, _)| *i != j)
            .map(|(_, t)| t.clone())
            .collect(),
    };
    let Some(s) = eval_poly_interval(&rest, bx) else {
        return false;
    };
    // t_j must lie in range - S.
    let tj_range = sub_interval(range, &s);

    // Contract each DISTINCT variable of the monomial in turn.
    let mut i = 0;
    while i < mono.len() {
        let v = mono[i];
        let mut k = 0usize;
        while i < mono.len() && mono[i] == v {
            k += 1;
            i += 1;
        }
        // D = coeff * (product of the OTHER variables' powers in this monomial).
        let mut d = Interval::point(coeff.clone());
        let mut m = 0;
        while m < mono.len() {
            let w = mono[m];
            let mut p = 0usize;
            while m < mono.len() && mono[m] == w {
                p += 1;
                m += 1;
            }
            if w != v {
                let wiv = bx.get(&w).cloned().unwrap_or_else(Interval::whole);
                d = d.mul(&wiv.pow(p));
            }
        }
        let Some(q) = div_interval(&tj_range, &d) else {
            continue; // divisor straddles 0: no sound contraction here
        };
        let cur = bx.get(&v).cloned().unwrap_or_else(Interval::whole);
        match contract_power(&cur, &q, k) {
            None => return true, // proven empty
            Some(new_iv) => {
                // Outward-round runaway denominators BEFORE storing (see
                // `round_interval_outward`): the rounded interval is a
                // superset, so emptiness/refutation conclusions are unchanged.
                let new_iv = round_interval_outward(new_iv);
                if !intervals_equal(&cur, &new_iv) {
                    if interval_is_empty(&new_iv) {
                        return true;
                    }
                    *changed = true;
                    bx.insert(v, new_iv);
                }
            }
        }
    }
    debug_assert!(vars.contains(&mono[0]));
    false
}

/// Structural interval equality (values + inclusivity) for change detection.
fn intervals_equal(a: &Interval, b: &Interval) -> bool {
    a.lo == b.lo && a.hi == b.hi
}

/// Endpoint denominators larger than this many bits are rounded OUTWARD to
/// dyadics with denominator `2^ROOT_SCALE_BITS` before being stored in the
/// box. Without this, `k = 1` projections store raw division quotients whose
/// denominators MULTIPLY through the polynomial products of the next pass —
/// exponential bit-growth that turns exact arithmetic into the bottleneck.
/// Rounding only ever WIDENS the interval, so soundness is untouched; the
/// precision floor `2^-ROOT_SCALE_BITS` is far below `MIN_WIDTH`. Endpoints
/// with small denominators (exact rational roots like `x = 10` or pins) are
/// stored EXACTLY so the point-substitution and pin logic keep working.
const MAX_ENDPOINT_DENOM_BITS: u64 = 64;

/// Round `v` down (toward -inf) to a dyadic with denominator `2^ROOT_SCALE_BITS`.
fn dyadic_floor(v: &BigRational) -> BigRational {
    let scale = BigInt::one() << ROOT_SCALE_BITS;
    let scaled = v * BigRational::from_integer(scale.clone());
    BigRational::new(scaled.floor().to_integer(), scale)
}

/// Round `v` up (toward +inf) to a dyadic with denominator `2^ROOT_SCALE_BITS`.
fn dyadic_ceil(v: &BigRational) -> BigRational {
    let scale = BigInt::one() << ROOT_SCALE_BITS;
    let scaled = v * BigRational::from_integer(scale.clone());
    BigRational::new(scaled.ceil().to_integer(), scale)
}

/// Outward-round an interval's endpoints when their denominators have grown
/// past [`MAX_ENDPOINT_DENOM_BITS`]. The result is a SUPERSET of the input
/// (lower endpoint rounded down, upper rounded up); rounded endpoints are
/// marked CLOSED (attainment unknown after rounding — conservative).
fn round_interval_outward(iv: Interval) -> Interval {
    let round_lo = |e: Endpoint| -> Endpoint {
        match e {
            Endpoint::Finite(v, _) if v.denom().bits() > MAX_ENDPOINT_DENOM_BITS => {
                Endpoint::Finite(dyadic_floor(&v), true)
            }
            e => e,
        }
    };
    let round_hi = |e: Endpoint| -> Endpoint {
        match e {
            Endpoint::Finite(v, _) if v.denom().bits() > MAX_ENDPOINT_DENOM_BITS => {
                Endpoint::Finite(dyadic_ceil(&v), true)
            }
            e => e,
        }
    };
    Interval {
        lo: round_lo(iv.lo),
        hi: round_hi(iv.hi),
    }
}

/// Contract `cur` under the constraint `x^k ∈ q`. Returns `None` when the
/// intersection is PROVABLY empty, else the (possibly tightened) interval.
fn contract_power(cur: &Interval, q: &Interval, k: usize) -> Option<Interval> {
    let cand = if k == 1 {
        q.clone()
    } else if k.is_multiple_of(2) {
        // x^k is non-negative: intersect q with [0, +inf).
        let nonneg = Interval {
            lo: Endpoint::Finite(BigRational::zero(), true),
            hi: Endpoint::PosInf,
        };
        let q = intersect_intervals(q, &nonneg);
        if interval_is_empty(&q) {
            return None; // x^k >= 0 has no value in q: box empty
        }
        // |x| <= sup(q)^(1/k); additionally |x| >= inf(q)^(1/k) when inf > 0.
        let hi_root = match &q.hi {
            Endpoint::PosInf => None,
            Endpoint::Finite(v, _) => Some(kth_root_upper(v, k)),
            Endpoint::NegInf => return None,
        };
        let lo_root = match &q.lo {
            Endpoint::Finite(v, _) if v.is_positive() => Some(kth_root_lower(v, k)),
            _ => None,
        };
        // Which side of 0 does the CURRENT interval live on?
        let cur_nonneg = matches!(&cur.lo, Endpoint::Finite(v, _) if !v.is_negative());
        let cur_nonpos = matches!(&cur.hi, Endpoint::Finite(v, _) if !v.is_positive());
        if cur_nonneg {
            Interval {
                lo: Endpoint::Finite(lo_root.unwrap_or_else(BigRational::zero), true),
                hi: hi_root
                    .map(|r| Endpoint::Finite(r, true))
                    .unwrap_or(Endpoint::PosInf),
            }
        } else if cur_nonpos {
            Interval {
                lo: hi_root
                    .clone()
                    .map(|r| Endpoint::Finite(-r, true))
                    .unwrap_or(Endpoint::NegInf),
                hi: Endpoint::Finite(-lo_root.unwrap_or_else(BigRational::zero), true),
            }
        } else {
            // Straddles 0: the feasible set is the UNION of the negative and
            // positive root branches `[-sup_root, -inf_root] ∪ [inf_root,
            // sup_root]`. Intersect each branch with `cur` separately; if both
            // are empty the box is refuted, if one survives we contract to it,
            // and only if both survive do we fall back to their hull (the
            // inner hole is not representable in a single interval — sound).
            let pos_branch = Interval {
                lo: Endpoint::Finite(lo_root.clone().unwrap_or_else(BigRational::zero), true),
                hi: hi_root
                    .clone()
                    .map(|r| Endpoint::Finite(r, true))
                    .unwrap_or(Endpoint::PosInf),
            };
            let neg_branch = Interval {
                lo: hi_root
                    .map(|r| Endpoint::Finite(-r, true))
                    .unwrap_or(Endpoint::NegInf),
                hi: Endpoint::Finite(-lo_root.unwrap_or_else(BigRational::zero), true),
            };
            let pos = intersect_intervals(cur, &pos_branch);
            let neg = intersect_intervals(cur, &neg_branch);
            match (interval_is_empty(&neg), interval_is_empty(&pos)) {
                (true, true) => return None,
                (true, false) => pos,
                (false, true) => neg,
                (false, false) => Interval {
                    lo: neg.lo,
                    hi: pos.hi,
                },
            }
        }
    } else {
        // Odd k: x = q^(1/k), monotone over the whole line.
        let lo = match &q.lo {
            Endpoint::NegInf => Endpoint::NegInf,
            Endpoint::PosInf => return None,
            Endpoint::Finite(v, _) => Endpoint::Finite(odd_root_lower(v, k), true),
        };
        let hi = match &q.hi {
            Endpoint::PosInf => Endpoint::PosInf,
            Endpoint::NegInf => return None,
            Endpoint::Finite(v, _) => Endpoint::Finite(odd_root_upper(v, k), true),
        };
        Interval { lo, hi }
    };
    let out = intersect_intervals(cur, &cand);
    if interval_is_empty(&out) {
        None
    } else {
        Some(out)
    }
}

// ============================================================================
// Polynomial helpers over MultiPoly.
// ============================================================================

/// Substitute `var := c` (an exact rational constant).
fn substitute_point(p: &MultiPoly, var: TermId, c: &BigRational) -> MultiPoly {
    p.substitute(
        var,
        &LinExpr {
            constant: c.clone(),
            terms: Vec::new(),
        },
    )
}

/// Formal partial derivative `∂p/∂var` (exact).
fn partial_derivative(p: &MultiPoly, var: TermId) -> MultiPoly {
    let mut out = MultiPoly { terms: Vec::new() };
    for (mono, coeff) in &p.terms {
        let k = mono.iter().filter(|&&v| v == var).count();
        if k == 0 {
            continue;
        }
        let mut m = mono.clone();
        let pos = m.iter().position(|&v| v == var).expect("k >= 1 occurrence");
        let _removed: TermId = m.remove(pos);
        out.add_term(m, coeff * BigRational::from_integer(BigInt::from(k)));
    }
    out
}

/// Exact evaluation of `p` at a full rational point.
fn eval_poly_at(p: &MultiPoly, point: &crate::HashMap<TermId, BigRational>) -> Option<BigRational> {
    let mut acc = BigRational::zero();
    for (mono, coeff) in &p.terms {
        let mut term = coeff.clone();
        for v in mono {
            term *= point.get(v)?;
        }
        acc += term;
    }
    Some(acc)
}

/// The constant value of a variable-free polynomial.
fn constant_value(p: &MultiPoly) -> Option<BigRational> {
    if p.terms.is_empty() {
        return Some(BigRational::zero());
    }
    if p.terms.len() == 1 && p.terms[0].0.is_empty() {
        return Some(p.terms[0].1.clone());
    }
    None
}

// ============================================================================
// Krawczyk interval-Newton existence certificate.
// ============================================================================

/// Exact rational matrix inverse by Gauss-Jordan elimination with partial
/// pivoting (first non-zero pivot). Returns `None` for a singular matrix.
fn invert_rational_matrix(a: &[Vec<BigRational>]) -> Option<Vec<Vec<BigRational>>> {
    let n = a.len();
    let mut m: Vec<Vec<BigRational>> = a
        .iter()
        .enumerate()
        .map(|(i, row)| {
            debug_assert_eq!(row.len(), n);
            let mut r = row.clone();
            for j in 0..n {
                r.push(if i == j {
                    BigRational::one()
                } else {
                    BigRational::zero()
                });
            }
            r
        })
        .collect();
    for col in 0..n {
        let pivot_row = (col..n).find(|&r| !m[r][col].is_zero())?;
        m.swap(col, pivot_row);
        let pivot = m[col][col].clone();
        for x in m[col].iter_mut() {
            *x /= &pivot;
        }
        for r in 0..n {
            if r == col || m[r][col].is_zero() {
                continue;
            }
            let factor = m[r][col].clone();
            let pivot_row: Vec<BigRational> = m[col].clone();
            for (x, pv) in m[r].iter_mut().zip(pivot_row.iter()) {
                let sub = &factor * pv;
                *x -= sub;
            }
        }
    }
    Some(m.into_iter().map(|row| row[n..].to_vec()).collect())
}

/// Krawczyk existence test for the square system `eqs = 0` over the box
/// restricted to `vars` (all intervals must be finite and non-degenerate).
/// Returns `true` only when `K(X)` is STRICTLY inside the interior of `X`,
/// which proves a real zero of the system exists in `X`.
fn krawczyk_test(eqs: &[MultiPoly], vars: &[TermId], bx: &VarBox) -> bool {
    let n = eqs.len();
    debug_assert_eq!(n, vars.len());
    if n == 0 {
        return false;
    }
    // Midpoint m and the interval vector X.
    let mut mid: crate::HashMap<TermId, BigRational> = crate::HashMap::default();
    let mut xs: Vec<Interval> = Vec::with_capacity(n);
    for &v in vars {
        let Some(iv) = bx.get(&v) else { return false };
        let Some(m) = interval_midpoint(iv) else {
            return false;
        };
        mid.insert(v, m);
        xs.push(iv.clone());
    }
    // F(m), exact.
    let mut fm: Vec<BigRational> = Vec::with_capacity(n);
    for e in eqs {
        let Some(val) = eval_poly_at(e, &mid) else {
            return false; // an equality mentions a variable outside `vars`
        };
        fm.push(val);
    }
    // Midpoint Jacobian J(m) and interval Jacobian J(X).
    let mut jm: Vec<Vec<BigRational>> = Vec::with_capacity(n);
    let mut jx: Vec<Vec<Interval>> = Vec::with_capacity(n);
    for e in eqs {
        let mut jm_row = Vec::with_capacity(n);
        let mut jx_row = Vec::with_capacity(n);
        for &v in vars {
            let d = partial_derivative(e, v);
            let Some(dm) = eval_poly_at(&d, &mid) else {
                return false;
            };
            let Some(dx) = eval_poly_interval(&d, bx) else {
                return false;
            };
            jm_row.push(dm);
            jx_row.push(dx);
        }
        jm.push(jm_row);
        jx.push(jx_row);
    }
    let Some(y) = invert_rational_matrix(&jm) else {
        return false;
    };
    // C = I - Y * J(X)  (interval matrix, exact rational scaling).
    let mut c: Vec<Vec<Interval>> = Vec::with_capacity(n);
    // Matrix operations use indices for multi-array access (same pattern as
    // the exact linear algebra elsewhere in the workspace).
    #[allow(clippy::needless_range_loop)]
    for i in 0..n {
        let mut row = Vec::with_capacity(n);
        for j in 0..n {
            let mut acc = Interval::point(BigRational::zero());
            for k in 0..n {
                acc = acc.add(&scale_interval(&jx[k][j], &y[i][k]));
            }
            let identity = if i == j {
                BigRational::one()
            } else {
                BigRational::zero()
            };
            row.push(sub_interval(&Interval::point(identity), &acc));
        }
        c.push(row);
    }
    // K_i = m_i - (Y F(m))_i + sum_j C_ij * (X_j - m_j).
    #[allow(clippy::needless_range_loop)] // multi-array index access
    for i in 0..n {
        let mut yf = BigRational::zero();
        for k in 0..n {
            yf += &y[i][k] * &fm[k];
        }
        let mut ki = Interval::point(mid[&vars[i]].clone() - yf);
        for j in 0..n {
            let xj_minus_mj = sub_interval(&xs[j], &Interval::point(mid[&vars[j]].clone()));
            ki = ki.add(&c[i][j].mul(&xj_minus_mj));
        }
        // Strict interior containment K_i ⊂ int(X_i), by VALUE.
        let (Endpoint::Finite(klo, _), Endpoint::Finite(khi, _)) = (&ki.lo, &ki.hi) else {
            return false;
        };
        let (Endpoint::Finite(xlo, _), Endpoint::Finite(xhi, _)) = (&xs[i].lo, &xs[i].hi) else {
            return false;
        };
        if !(xlo < klo && khi < xhi) {
            return false;
        }
    }
    true
}

// ============================================================================
// The decision procedure.
// ============================================================================

impl NraSolver<'_> {
    /// Interval branch-and-prune decision pre-phase for small multivariate
    /// polynomial systems. Fail-closed: SAT only with a verified rational
    /// point or a Krawczyk existence certificate; UNSAT only when the box tree
    /// is exhausted with every leaf refuted; otherwise
    /// [`UniResult::Unknown`] (fall through unchanged).
    pub(crate) fn try_icp_branch_and_prune(&self) -> UniResult {
        // 1. Normalize atoms. Unsupported atoms only forfeit SAT claims (a
        //    refutation of the parsed subset still refutes the conjunction).
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        let mut all_parsed = true;
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value) {
                Some(MultiAtom::ConstFalse) => return UniResult::Unsat,
                Some(MultiAtom::ConstTrue) => {}
                Some(MultiAtom::Constraint(c)) => constraints.push(c),
                None => all_parsed = false,
            }
        }
        if constraints.is_empty() || constraints.len() > MAX_ICP_CONSTRAINTS {
            return UniResult::Unknown;
        }
        // 2. Variable support, deterministic order.
        let mut vars: Vec<TermId> = Vec::new();
        for c in &constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars.sort_unstable_by_key(|t| t.0);
        if vars.len() < 2 || vars.len() > MAX_ICP_VARS {
            return UniResult::Unknown; // univariate cases are decided earlier
        }
        // All variables must be Real-sorted: a rational/algebraic witness for
        // an Int variable would be unsound, and integrality is NIA's province.
        for &v in &vars {
            if !matches!(self.terms.sort(v), ay_core::Sort::Real) {
                return UniResult::Unknown;
            }
        }
        // 3. Require genuine nonlinearity — purely linear systems are LRA's.
        if !constraints
            .iter()
            .any(|c| c.poly.terms.iter().any(|(m, _)| m.len() >= 2))
        {
            return UniResult::Unknown;
        }
        // 4. Root box: explicit linear bounds, then contraction.
        let mut root: VarBox = collect_variable_bounds(&constraints);
        for &v in &vars {
            root.entry(v).or_insert_with(Interval::whole);
        }
        if matches!(
            contract_box(&constraints, &vars, &mut root),
            Contraction::Refuted
        ) {
            return UniResult::Unsat;
        }
        let eq_count = constraints
            .iter()
            .filter(|c| matches!(c.rel, Rel::Eq))
            .count();
        // 5. Dense, HIGH-DIMENSIONAL PURE-INEQUALITY systems (the ASME
        //    virtual-gauge pin-fit clusters: 6 pose unknowns × dozens of
        //    `x'^2 + y'^2 >= r^2` atoms). For this shape the root contraction in
        //    step 4 IS the whole decision procedure: UNSAT is a BOUNDED
        //    infeasibility it refutes directly (returned above), while SAT is a
        //    full-measure feasible pose region that the downstream
        //    tangent/relaxation path certifies far faster than any box search.
        //    The box TREE can add nothing here — with no equality subsystem it
        //    can never emit a Krawczyk existence certificate, and it cannot
        //    exhaust a high-dimensional box within budget (~2^dim leaves) — so
        //    return Unknown now and fall through, rather than pay for a fruitless
        //    bisection. Honest: no verdict is claimed on the give-up. Low-
        //    dimensional pure-inequality systems still run the tree below (they
        //    CAN exhaust, and a rational witness may land in an early box).
        const PURE_INEQ_LOW_DIM: usize = 4;
        if eq_count == 0 && vars.len() > PURE_INEQ_LOW_DIM {
            // The box tree can neither exhaust these dims within budget nor
            // Krawczyk-certify (no equality subsystem). But a full-measure
            // feasible region has rational INTERIOR points: try the contracted
            // root box's exact candidate points (simplest-in-interval + midpoint,
            // each re-verified against every original atom) as a SAT witness
            // before giving up. This recovers SAT on feasible dense-inequality
            // systems — e.g. the constrained-fit `residual ≤ tol` regions — that
            // the give-up otherwise dropped to Unknown (a regression the
            // geometry_consumer-solve coaxial co-fit surfaced). UNSAT is unaffected: it is
            // refuted above by root contraction, or left an honest Unknown here.
            if let Some(res) = self.try_certify_box(&constraints, &vars, &root) {
                return res;
            }
            return UniResult::Unknown;
        }
        // 6. Underdetermined systems: SAT-only pinned search first (cheap,
        //    and the main tree cannot certify a solution MANIFOLD anyway).
        if all_parsed && eq_count < vars.len() {
            if let Some(res) = self.pinned_sat_search(&constraints, &vars, &root) {
                return res;
            }
        }
        // 7. Main branch-and-prune (SAT + exhaustive-refutation UNSAT).
        // Non-square systems get a smaller budget: their SAT side was already
        // attempted by the pinned search (a solution MANIFOLD cannot be
        // certified by bisection), so the tree is mostly useful for quick
        // exhaustive refutations.
        let budget = if eq_count == vars.len() {
            MAX_BOXES
        } else {
            MAX_BOXES / 8
        };
        self.branch_and_prune(&constraints, &vars, root, all_parsed, false, budget)
    }

    /// Branch-and-prune over a box tree. `sat_only` (pinned/heuristic boxes)
    /// suppresses UNSAT claims. Returns `Unknown` unless a certificate fires
    /// or the tree is exhausted with every leaf refuted.
    fn branch_and_prune(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        mut root: VarBox,
        all_parsed: bool,
        sat_only: bool,
        max_boxes: usize,
    ) -> UniResult {
        let mut sat_only = sat_only;
        let mut max_boxes = max_boxes;
        // Clamp still-unbounded variables to the large initial search box.
        // The clamp is a SEARCH heuristic: solutions may exist outside it, so
        // it forfeits UNSAT (see module docs) and gets a short budget.
        let clamp = BigRational::from_integer(BigInt::one() << UNBOUNDED_CLAMP_LOG2);
        for &v in vars {
            let iv = root.entry(v).or_insert_with(Interval::whole);
            if matches!(iv.lo, Endpoint::NegInf) {
                iv.lo = Endpoint::Finite(-(&clamp), true);
                sat_only = true;
                max_boxes = max_boxes.min(CLAMPED_MAX_BOXES);
            }
            if matches!(iv.hi, Endpoint::PosInf) {
                iv.hi = Endpoint::Finite(clamp.clone(), true);
                sat_only = true;
                max_boxes = max_boxes.min(CLAMPED_MAX_BOXES);
            }
        }
        let min_w = min_width();
        let mut stack: Vec<VarBox> = vec![root];
        let mut processed = 0usize;
        let mut exhaustive = true;
        while let Some(mut bx) = stack.pop() {
            processed += 1;
            if processed > max_boxes {
                exhaustive = false;
                break;
            }
            if matches!(
                contract_box(constraints, vars, &mut bx),
                Contraction::Refuted
            ) {
                continue; // leaf PROVABLY empty
            }
            if all_parsed {
                if let Some(res) = self.try_certify_box(constraints, vars, &bx) {
                    return res;
                }
            }
            // Bisect the widest dimension; give up on boxes below MIN_WIDTH.
            match widest_splittable_var(vars, &bx, &min_w) {
                Some(v) => {
                    let iv = bx.get(&v).cloned().unwrap_or_else(Interval::whole);
                    let Some(split) = bisection_point(&iv) else {
                        exhaustive = false;
                        continue;
                    };
                    let mut left = bx.clone();
                    left.insert(
                        v,
                        Interval {
                            lo: iv.lo.clone(),
                            hi: Endpoint::Finite(split.clone(), true),
                        },
                    );
                    let mut right = bx;
                    right.insert(
                        v,
                        Interval {
                            lo: Endpoint::Finite(split, true),
                            hi: iv.hi.clone(),
                        },
                    );
                    stack.push(left);
                    stack.push(right);
                }
                None => {
                    // Too small to split and not certified: unresolved leaf.
                    exhaustive = false;
                }
            }
        }
        if exhaustive && !sat_only && stack.is_empty() {
            UniResult::Unsat
        } else {
            UniResult::Unknown
        }
    }

    /// Try to certify SAT on a contracted box: first exact rational candidate
    /// points (verified against EVERY original atom), then the Krawczyk
    /// existence certificate for an irrational witness.
    fn try_certify_box(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        bx: &VarBox,
    ) -> Option<UniResult> {
        // (a) Rational candidates: simplest-in-interval and midpoint vectors.
        'cand: for use_mid in [false, true] {
            let mut model: Vec<(TermId, BigRational)> = Vec::with_capacity(vars.len());
            for &v in vars {
                let iv = bx.get(&v)?;
                let val = if use_mid {
                    let m = interval_midpoint(iv)?;
                    if !interval_contains(iv, &m) {
                        continue 'cand;
                    }
                    m
                } else {
                    match nice_point_in(iv) {
                        Some(p) => p,
                        None => continue 'cand,
                    }
                };
                model.push((v, val));
            }
            // SOUNDNESS GATE: exact substitution into every asserted atom.
            if self.verify_model(&model) {
                return Some(UniResult::Sat(model));
            }
        }
        // (b) Krawczyk existence certificate, with an exact witness.
        if let Some(result) = self.krawczyk_certify(constraints, vars, bx) {
            return Some(result);
        }
        None
    }

    /// Krawczyk certification of a box: substitute exact point-intervals as
    /// pins, require the remaining equalities to form a SQUARE system over the
    /// free variables, verify every other constraint holds over the WHOLE
    /// (slightly inflated) box by interval evaluation, and run the Krawczyk
    /// containment test.
    ///
    /// A certificate alone is not enough to report SAT: the model must carry
    /// honest values. For a SINGLE free variable the certified zero is the
    /// unique root of the pinned equality in the box — an exact rational or an
    /// exact [`crate::algebraic::RealAlgebraic`] — and the assembled witness
    /// assignment is re-verified exactly before returning `Sat`/`SatAlgebraic`
    /// with the full model. With TWO OR MORE coupled free variables the zero's
    /// coordinates are not representable as independent univariate algebraic
    /// numbers (that requires elimination theory), so NO model can honestly be
    /// emitted and certification declines (`None`) — the search continues and
    /// at worst the verdict degrades to a sound `unknown`, never to a model
    /// with fabricated values.
    fn krawczyk_certify(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        bx: &VarBox,
    ) -> Option<UniResult> {
        // Split into exact pins (degenerate intervals) and free variables.
        let mut pins: Vec<(TermId, BigRational)> = Vec::new();
        let mut free: Vec<TermId> = Vec::new();
        for &v in vars {
            let iv = bx.get(&v)?;
            match interval_point(iv) {
                Some(p) => pins.push((v, p.clone())),
                None => {
                    // Krawczyk needs finite, reasonably tight boxes.
                    match interval_width(iv) {
                        Some(w) if w <= krawczyk_max_width() => free.push(v),
                        _ => return None,
                    }
                }
            }
        }
        if free.is_empty() {
            return None; // fully rational point: candidate path handles it
        }
        // ε-inflate the free dimensions so a zero sitting ON a contracted
        // boundary still lies in the STRICT interior (sound: the certificate
        // is with respect to the inflated box, and the side-constraint check
        // below is performed over the same inflated box).
        let mut ibox: VarBox = bx.clone();
        for &v in &free {
            let iv = ibox.get_mut(&v).expect("free var in box");
            let (Endpoint::Finite(lo, _), Endpoint::Finite(hi, _)) = (&iv.lo, &iv.hi) else {
                return None;
            };
            let delta = (hi - lo) / BigRational::from_integer(BigInt::from(8))
                + BigRational::new(BigInt::one(), BigInt::one() << ROOT_SCALE_BITS);
            *iv = Interval {
                lo: Endpoint::Finite(lo - &delta, true),
                hi: Endpoint::Finite(hi + &delta, true),
            };
        }
        // Substitute pins; collect the square equality system and the side
        // constraints.
        let mut eqs: Vec<MultiPoly> = Vec::new();
        let mut side: Vec<(MultiPoly, Rel)> = Vec::new();
        for c in constraints {
            let mut p = c.poly.clone();
            for (v, val) in &pins {
                p = substitute_point(&p, *v, val);
            }
            if let Some(cv) = constant_value(&p) {
                // Fully pinned constraint: must hold EXACTLY at the pins.
                if !c.rel.holds_for_sign(rational_sign(&cv)) {
                    return None;
                }
                continue;
            }
            match c.rel {
                Rel::Eq => eqs.push(p),
                rel => side.push((p, rel)),
            }
        }
        if eqs.len() != free.len() {
            return None; // not square: no existence certificate
        }
        // Side constraints must hold over the ENTIRE inflated box, so the
        // certified zero (wherever it is in the box) satisfies them.
        for (p, rel) in &side {
            let iv = eval_poly_interval(p, &ibox)?;
            if !constraint_holds_everywhere(*rel, &iv) {
                return None;
            }
        }
        if !krawczyk_test(&eqs, &free, &ibox) {
            return None;
        }
        if free.len() == 2 {
            // Two coupled free variables: try exact resultant elimination. If
            // one coordinate of the certified zero is RATIONAL (common in
            // sketch geometry — e.g. the triangle-by-distances x-coordinate),
            // pinning it reduces the system to the single-variable case below
            // and a fully honest witness is emitted. Otherwise decline.
            return self.krawczyk_witness_bivariate(constraints, &pins, &eqs, &free, &ibox);
        }
        if free.len() != 1 {
            // Existence is certified, but with >= 3 coupled free variables no
            // honest per-variable witness is representable here (that needs
            // full elimination theory). Decline certification: the search
            // continues and at worst the verdict degrades to a sound
            // `unknown`, never to a model with fabricated values.
            return None;
        }
        // Exactly one free variable: the certified zero is the unique root of
        // the (univariate after pinning) equality inside the inflated box.
        let fv = free[0];
        let uni = eqs.first()?.to_unipoly()?;
        let iv = ibox.get(&fv)?;
        let (Endpoint::Finite(blo, _), Endpoint::Finite(bhi, _)) = (&iv.lo, &iv.hi) else {
            return None;
        };
        match unique_root_witness_in(&uni, blo, bhi)? {
            RootInInterval::Rational(r) => {
                // Rational root: emit a plain rational model, re-verified by
                // exact substitution into EVERY original asserted atom.
                let mut model = pins;
                model.push((fv, r));
                if self.verify_model(&model) {
                    Some(UniResult::Sat(model))
                } else {
                    None
                }
            }
            RootInInterval::Algebraic(alg) => {
                // Exact algebraic witness: re-verify EVERY parsed constraint
                // at the pinned + algebraic assignment by exact Sturm sign
                // determination before claiming SAT.
                for c in constraints {
                    let mut p = c.poly.clone();
                    for (v, val) in &pins {
                        p = substitute_point(&p, *v, val);
                    }
                    let sign = match constant_value(&p) {
                        Some(cv) => rational_sign(&cv),
                        None => alg.sign_of_poly(&p.to_unipoly()?)?,
                    };
                    if !c.rel.holds_for_sign(sign) {
                        return None;
                    }
                }
                let mut witnesses: Vec<(TermId, UniWitness)> = pins
                    .into_iter()
                    .map(|(v, val)| (v, UniWitness::Rational(val)))
                    .collect();
                witnesses.push((fv, UniWitness::Algebraic(alg.as_value())));
                Some(UniResult::SatAlgebraic(witnesses))
            }
        }
    }

    /// Exact witness construction for a Krawczyk-certified box with TWO
    /// coupled free variables `{u, v}` and a square 2-equation system.
    ///
    /// Two exact strategies, both fully re-verified before claiming SAT:
    ///
    ///   1. TRIANGULAR-LINEAR: if some equation is linear in one variable with
    ///      a nonzero RATIONAL coefficient — `a*v + b(u) = 0` — then
    ///      `v = -b(u)/a` is a POLYNOMIAL of `u`. Substituting it into the
    ///      other equation gives a univariate polynomial whose unique root in
    ///      the box is `u`'s exact witness (rational or algebraic); `v`'s
    ///      value is a residue over the SAME algebraic point, so joint atoms
    ///      still evaluate exactly (a triangular assignment, as in z3's
    ///      nlsat).
    ///   2. RESULTANT-RATIONAL: eliminate one variable with the exact
    ///      bivariate resultant `R(u) = Res_v(p1, p2)` (fixed-dimension
    ///      Sylvester determinants + Lagrange interpolation). When the
    ///      certified zero's `u`-coordinate is RATIONAL, pin it and the
    ///      system reduces to the single-variable case.
    ///
    /// When neither applies (both coordinates irrational AND nonlinearly
    /// coupled) the pair lives in an extension this representation cannot
    /// evaluate jointly, so certification declines (`None`) — sound, at worst
    /// `unknown`, never a model with fabricated values.
    fn krawczyk_witness_bivariate(
        &self,
        constraints: &[MultiConstraint],
        pins: &[(TermId, BigRational)],
        eqs: &[MultiPoly],
        free: &[TermId],
        ibox: &VarBox,
    ) -> Option<UniResult> {
        if eqs.len() != 2 || free.len() != 2 {
            return None;
        }
        // Strategy 1: triangular-linear.
        for (keep, elim) in [(free[0], free[1]), (free[1], free[0])] {
            for (eq_lin, eq_other) in [(&eqs[0], &eqs[1]), (&eqs[1], &eqs[0])] {
                if let Some(result) = self.triangular_linear_witness(
                    constraints,
                    pins,
                    eq_lin,
                    eq_other,
                    keep,
                    elim,
                    ibox,
                ) {
                    return Some(result);
                }
            }
        }
        // Strategy 2: resultant elimination with a rational coordinate.
        for (keep, elim) in [(free[0], free[1]), (free[1], free[0])] {
            let Some(resultant) = resultant_eliminate(&eqs[0], &eqs[1], keep, elim) else {
                continue;
            };
            let Some(kiv) = ibox.get(&keep) else { continue };
            let (Endpoint::Finite(klo, _), Endpoint::Finite(khi, _)) = (&kiv.lo, &kiv.hi) else {
                continue;
            };
            let Some(RootInInterval::Rational(c)) = unique_root_witness_in(&resultant, klo, khi)
            else {
                continue;
            };
            // Pin `keep = c`; the system becomes univariate in `elim`.
            let q1 = substitute_point(&eqs[0], keep, &c).to_unipoly();
            let q2 = substitute_point(&eqs[1], keep, &c).to_unipoly();
            let Some(eiv) = ibox.get(&elim) else { continue };
            let (Endpoint::Finite(elo, _), Endpoint::Finite(ehi, _)) = (&eiv.lo, &eiv.hi) else {
                continue;
            };
            // Isolate the elim root from whichever pinned equality is
            // non-degenerate; full re-verification below covers the other.
            let cand = [q1, q2]
                .into_iter()
                .flatten()
                .filter(|q| !q.is_zero() && q.degree().unwrap_or(0) >= 1)
                .find_map(|q| unique_root_witness_in(&q, elo, ehi));
            let Some(wit) = cand else { continue };
            match wit {
                RootInInterval::Rational(rv) => {
                    // Fully rational model: re-verify by exact substitution
                    // into EVERY original asserted atom.
                    let mut model = pins.to_vec();
                    model.push((keep, c));
                    model.push((elim, rv));
                    if self.verify_model(&model) {
                        return Some(UniResult::Sat(model));
                    }
                }
                RootInInterval::Algebraic(alg) => {
                    // Re-verify EVERY parsed constraint at pins + keep=c +
                    // elim=alg by exact Sturm sign determination.
                    let mut all_ok = true;
                    for con in constraints {
                        let mut poly = con.poly.clone();
                        for (v, val) in pins {
                            poly = substitute_point(&poly, *v, val);
                        }
                        poly = substitute_point(&poly, keep, &c);
                        let sign = match constant_value(&poly) {
                            Some(cv) => rational_sign(&cv),
                            None => match poly.to_unipoly().and_then(|u| alg.sign_of_poly(&u)) {
                                Some(sg) => sg,
                                None => {
                                    all_ok = false;
                                    break;
                                }
                            },
                        };
                        if !con.rel.holds_for_sign(sign) {
                            all_ok = false;
                            break;
                        }
                    }
                    if all_ok {
                        let mut witnesses: Vec<(TermId, UniWitness)> = pins
                            .iter()
                            .map(|(v, val)| (*v, UniWitness::Rational(val.clone())))
                            .collect();
                        witnesses.push((keep, UniWitness::Rational(c)));
                        witnesses.push((elim, UniWitness::Algebraic(alg.as_value())));
                        return Some(UniResult::SatAlgebraic(witnesses));
                    }
                }
            }
        }
        None
    }

    /// TRIANGULAR-LINEAR witness (see [`Self::krawczyk_witness_bivariate`]):
    /// `eq_lin` must be `a*elim + b(keep) = 0` with a nonzero RATIONAL `a`,
    /// making `elim = w(keep)` a polynomial. Substituting into `eq_other`
    /// yields the univariate defining polynomial for `keep`; its unique root
    /// in the box is the exact witness. `elim`'s value is `w` evaluated at
    /// that root — a residue over the SAME algebraic point. Every parsed
    /// constraint is re-verified exactly before SAT is claimed.
    #[allow(clippy::too_many_arguments)]
    fn triangular_linear_witness(
        &self,
        constraints: &[MultiConstraint],
        pins: &[(TermId, BigRational)],
        eq_lin: &MultiPoly,
        eq_other: &MultiPoly,
        keep: TermId,
        elim: TermId,
        ibox: &VarBox,
    ) -> Option<UniResult> {
        // eq_lin as a polynomial in `elim` with UniPoly-in-`keep` coefficients.
        let lin = to_bipoly(eq_lin, keep, elim)?;
        if lin.len() != 2 {
            return None; // not linear in `elim`
        }
        let a = &lin[1];
        if a.degree() != Some(0) {
            return None; // coefficient of `elim` must be a nonzero rational
        }
        let a_val = a.coeffs()[0].clone();
        // elim = w(keep) = -b(keep) / a.
        let w = lin[0].scale(&(-BigRational::one() / &a_val));
        // Substitute into the other equation: q(keep) = sum c_j(keep) * w^j.
        let other = to_bipoly(eq_other, keep, elim)?;
        let mut q = UniPoly::zero();
        let mut w_pow = UniPoly::constant(BigRational::one());
        for c_j in &other {
            q = q.add(&c_j.mul(&w_pow));
            w_pow = w_pow.mul(&w);
        }
        if q.is_zero() || q.degree().unwrap_or(0) < 1 {
            return None; // degenerate: no isolated root to certify
        }
        let kiv = ibox.get(&keep)?;
        let (Endpoint::Finite(klo, _), Endpoint::Finite(khi, _)) = (&kiv.lo, &kiv.hi) else {
            return None;
        };
        match unique_root_witness_in(&q, klo, khi)? {
            RootInInterval::Rational(c) => {
                // Both coordinates rational: plain model, fully re-verified by
                // exact substitution into EVERY original asserted atom.
                let mut model = pins.to_vec();
                model.push((keep, c.clone()));
                model.push((elim, w.eval(&c)));
                if self.verify_model(&model) {
                    Some(UniResult::Sat(model))
                } else {
                    None
                }
            }
            RootInInterval::Algebraic(alg) => {
                // The elim value must lie in ITS box interval too (the root
                // was only isolated within keep's box) — check exactly.
                let eiv = ibox.get(&elim)?;
                let (Endpoint::Finite(elo, _), Endpoint::Finite(ehi, _)) = (&eiv.lo, &eiv.hi)
                else {
                    return None;
                };
                let w_minus_lo = w.sub(&UniPoly::constant(elo.clone()));
                let hi_minus_w = UniPoly::constant(ehi.clone()).sub(&w);
                if alg.sign_of_poly(&w_minus_lo)? < 0 || alg.sign_of_poly(&hi_minus_w)? < 0 {
                    return None;
                }
                // Re-verify EVERY parsed constraint at the triangular
                // assignment: substitute pins, then elim -> w(keep), then
                // determine the exact sign at the algebraic root.
                for con in constraints {
                    let mut poly = con.poly.clone();
                    for (v, val) in pins {
                        poly = substitute_point(&poly, *v, val);
                    }
                    let bip = to_bipoly(&poly, keep, elim)?;
                    let mut uni = UniPoly::zero();
                    let mut w_pow = UniPoly::constant(BigRational::one());
                    for c_j in &bip {
                        uni = uni.add(&c_j.mul(&w_pow));
                        w_pow = w_pow.mul(&w);
                    }
                    let sign = alg.sign_of_poly(&uni)?;
                    if !con.rel.holds_for_sign(sign) {
                        return None;
                    }
                }
                let mut witnesses: Vec<(TermId, UniWitness)> = pins
                    .iter()
                    .map(|(v, val)| (*v, UniWitness::Rational(val.clone())))
                    .collect();
                // elim's value: the SAME algebraic point with residue w.
                let elim_value = match crate::algebraic::RealAlgebraicValue::reduce(&alg, &w) {
                    crate::algebraic::RealScalar::Rational(r) => UniWitness::Rational(r),
                    crate::algebraic::RealScalar::Algebraic(v) => UniWitness::Algebraic(v),
                };
                witnesses.push((keep, UniWitness::Algebraic(alg.as_value())));
                witnesses.push((elim, elim_value));
                Some(UniResult::SatAlgebraic(witnesses))
            }
        }
    }

    /// SAT-only search for UNDERDETERMINED systems: pin `#vars - #eqs` free
    /// variables to heuristically chosen exact rationals (the complement of a
    /// maximum structural matching between active equalities and non-point
    /// variables), then branch-and-prune the reduced system. Pins are guesses:
    /// this NEVER claims UNSAT.
    fn pinned_sat_search(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        root: &VarBox,
    ) -> Option<UniResult> {
        // Active equalities: those not already reduced to constants by the
        // point-intervals of the contracted root box.
        let point_vars: Vec<(TermId, BigRational)> = vars
            .iter()
            .filter_map(|&v| {
                root.get(&v)
                    .and_then(interval_point)
                    .map(|p| (v, p.clone()))
            })
            .collect();
        let free_vars: Vec<TermId> = vars
            .iter()
            .copied()
            .filter(|v| !point_vars.iter().any(|(pv, _)| pv == v))
            .collect();
        let mut active_eqs: Vec<Vec<TermId>> = Vec::new(); // variable support sets
        for c in constraints {
            if !matches!(c.rel, Rel::Eq) {
                continue;
            }
            let mut p = c.poly.clone();
            for (v, val) in &point_vars {
                p = substitute_point(&p, *v, val);
            }
            let support = p.variables();
            if !support.is_empty() {
                active_eqs.push(support);
            }
        }
        if active_eqs.len() >= free_vars.len() || active_eqs.is_empty() {
            return None; // square/overdetermined handled by the main tree
        }
        // Candidate FIRST pin variables, narrowest interval first: sketch
        // parameters that drive a mechanism (angles, unit-circle coordinates)
        // have naturally tight ranges, and a pin inside a tight range is far
        // more likely to intersect the solution manifold than a pin on a wide
        // dependent coordinate. For each candidate whose removal still leaves
        // a PERFECT matching of the equalities into the remaining variables,
        // the rest of the pin set is that matching's complement.
        let mut by_width: Vec<TermId> = free_vars.clone();
        by_width.sort_by(|a, b| {
            let wa = root.get(a).and_then(interval_width);
            let wb = root.get(b).and_then(interval_width);
            match (wa, wb) {
                (Some(x), Some(y)) => x.cmp(&y),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => std::cmp::Ordering::Equal,
            }
        });
        let mut attempts = 0usize;
        for &first_pin in &by_width {
            if attempts >= MAX_PIN_ATTEMPTS {
                break;
            }
            let remaining: Vec<TermId> = free_vars
                .iter()
                .copied()
                .filter(|&v| v != first_pin)
                .collect();
            let Some(matched) = match_eqs_to_vars(&active_eqs, &remaining) else {
                continue; // removing this variable breaks the matching
            };
            let mut pin_vars: Vec<TermId> = vec![first_pin];
            pin_vars.extend(remaining.iter().copied().filter(|v| !matched.contains(v)));
            // Up to 3 pin-value assignments: simplest rational, midpoint, and
            // the simplest rational of the lower half of each pinned interval.
            for attempt in 0..3usize {
                if attempts >= MAX_PIN_ATTEMPTS {
                    break;
                }
                attempts += 1;
                let mut bx = root.clone();
                let mut ok = true;
                for &v in &pin_vars {
                    let iv = root.get(&v)?;
                    let val = match attempt {
                        0 => nice_point_in(iv),
                        1 => interval_midpoint(iv).filter(|m| interval_contains(iv, m)),
                        _ => lower_half_point(iv),
                    };
                    match val {
                        Some(val) => {
                            bx.insert(v, Interval::point(val));
                        }
                        None => {
                            ok = false;
                            break;
                        }
                    }
                }
                if !ok {
                    continue;
                }
                match self.branch_and_prune(
                    constraints,
                    vars,
                    bx,
                    true, // pinned search runs only when all atoms parsed
                    true, // SAT only
                    PIN_SEARCH_MAX_BOXES,
                ) {
                    UniResult::Sat(model) => return Some(UniResult::Sat(model)),
                    UniResult::SatAlgebraic(w) => return Some(UniResult::SatAlgebraic(w)),
                    UniResult::Unsat | UniResult::Unknown => {}
                }
            }
        }
        None
    }
}

/// Lower a bivariate [`MultiPoly`] over `{keep, elim}` to coefficient form in
/// `elim`: entry `j` is the (univariate in `keep`) coefficient of `elim^j`.
/// `None` if the polynomial mentions any other variable.
fn to_bipoly(p: &MultiPoly, keep: TermId, elim: TermId) -> Option<Vec<UniPoly>> {
    let mut out: Vec<Vec<BigRational>> = Vec::new();
    for (mono, coeff) in &p.terms {
        let mut kp = 0usize;
        let mut ep = 0usize;
        for &v in mono {
            if v == keep {
                kp += 1;
            } else if v == elim {
                ep += 1;
            } else {
                return None;
            }
        }
        if out.len() <= ep {
            out.resize(ep + 1, Vec::new());
        }
        if out[ep].len() <= kp {
            out[ep].resize(kp + 1, BigRational::zero());
        }
        out[ep][kp] += coeff;
    }
    Some(out.into_iter().map(UniPoly::from_coeffs).collect())
}

/// Exact bivariate resultant `Res_elim(p1, p2)` as a univariate polynomial in
/// `keep`, computed by evaluating fixed-dimension Sylvester determinants at
/// integer sample points and Lagrange-interpolating (all `BigRational`; the
/// fixed dimensions keep specialization sound when a leading coefficient
/// vanishes at a sample point). `None` when either polynomial does not
/// genuinely involve `elim`, mentions other variables, or the resultant is
/// identically zero (shared component — no isolation possible).
fn resultant_eliminate(
    p1: &MultiPoly,
    p2: &MultiPoly,
    keep: TermId,
    elim: TermId,
) -> Option<UniPoly> {
    let b1 = to_bipoly(p1, keep, elim)?;
    let b2 = to_bipoly(p2, keep, elim)?;
    let d1 = b1.len().checked_sub(1)?;
    let d2 = b2.len().checked_sub(1)?;
    if d1 == 0 || d2 == 0 {
        return None; // not genuinely coupled through `elim`
    }
    let ku = b1
        .iter()
        .map(|c| c.degree().unwrap_or(0))
        .max()
        .unwrap_or(0);
    let kv = b2
        .iter()
        .map(|c| c.degree().unwrap_or(0))
        .max()
        .unwrap_or(0);
    // Degree bound of Res_elim(p1, p2) in `keep`.
    let bound = d1 * kv + d2 * ku;
    let mut points: Vec<(BigRational, BigRational)> = Vec::with_capacity(bound + 1);
    for t in 0..=bound {
        let tv = BigRational::from_integer(BigInt::from(t as i64));
        let fc: Vec<BigRational> = b1.iter().map(|c| c.eval(&tv)).collect();
        let gc: Vec<BigRational> = b2.iter().map(|c| c.eval(&tv)).collect();
        let det = crate::algebraic::sylvester_det_fixed(&fc, &gc)?;
        points.push((tv, det));
    }
    let r = crate::algebraic::lagrange_interpolate(&points)?;
    if r.is_zero() {
        return None;
    }
    Some(r)
}

/// The unique root of `p` in the closed interval `[blo, bhi]`, as an exact
/// witness: a rational when the root is rational (including a root sitting on
/// a box endpoint), else an exact [`crate::algebraic::RealAlgebraic`] built
/// from the Sturm root isolation. Returns `None` — fail closed — unless the
/// interval contains EXACTLY one root of `p` (the Krawczyk containment test
/// guarantees uniqueness for a genuine certificate, so a mismatch here means
/// the caller must not certify).
fn unique_root_witness_in(
    p: &UniPoly,
    blo: &BigRational,
    bhi: &BigRational,
) -> Option<RootInInterval> {
    if blo >= bhi {
        return None;
    }
    let sf = square_free_part(p)?;
    if sf.degree().unwrap_or(0) < 1 {
        return None;
    }
    // A root sitting exactly on a box endpoint is that rational endpoint.
    if sf.eval(blo).is_zero() {
        return Some(RootInInterval::Rational(blo.clone()));
    }
    if sf.eval(bhi).is_zero() {
        return Some(RootInInterval::Rational(bhi.clone()));
    }
    let seq = sturm_sequence(&sf);
    if sturm_count(&seq, blo, bhi) != 1 {
        return None; // not uniquely isolated: fail closed
    }
    let markers = isolate_roots(&sf)?;
    for m in &markers {
        match m {
            RootMarker::Rational(r) => {
                if r > blo && r < bhi {
                    return Some(RootInInterval::Rational(r.clone()));
                }
            }
            RootMarker::Interval(mlo, mhi) => {
                let ilo = if mlo > blo { mlo.clone() } else { blo.clone() };
                let ihi = if mhi < bhi { mhi.clone() } else { bhi.clone() };
                if ilo < ihi && sturm_count(&seq, &ilo, &ihi) == 1 {
                    let alg =
                        crate::algebraic::RealAlgebraic::from_isolating_interval(&sf, &ilo, &ihi)?;
                    return Some(RootInInterval::Algebraic(alg));
                }
            }
        }
    }
    None
}

/// The unique root of a univariate polynomial inside a box interval: an exact
/// rational, or an exact algebraic number (the point itself, no residue).
enum RootInInterval {
    Rational(BigRational),
    Algebraic(crate::algebraic::RealAlgebraic),
}

/// A "nice" rational in the lower half of the interval (third pin attempt).
fn lower_half_point(iv: &Interval) -> Option<BigRational> {
    let (Endpoint::Finite(lo, _), Endpoint::Finite(hi, _)) = (&iv.lo, &iv.hi) else {
        return None;
    };
    let mid = (lo + hi) / BigRational::from_integer(BigInt::from(2));
    let half = Interval {
        lo: iv.lo.clone(),
        hi: Endpoint::Finite(mid, true),
    };
    nice_point_in(&half).filter(|p| interval_contains(iv, p))
}

/// Maximum bipartite matching (augmenting paths) of equality support sets to
/// free variables. Returns the matched variable set only when EVERY equality
/// is matched (a structurally deficient system has no pin-based squaring).
fn match_eqs_to_vars(eq_supports: &[Vec<TermId>], free_vars: &[TermId]) -> Option<Vec<TermId>> {
    let n_eq = eq_supports.len();
    let n_var = free_vars.len();
    // matched_var[j] = eq index matched to free_vars[j].
    let mut matched_var: Vec<Option<usize>> = vec![None; n_var];

    fn augment(
        eq: usize,
        eq_supports: &[Vec<TermId>],
        free_vars: &[TermId],
        matched_var: &mut Vec<Option<usize>>,
        visited: &mut Vec<bool>,
    ) -> bool {
        for (j, &v) in free_vars.iter().enumerate() {
            if visited[j] || !eq_supports[eq].contains(&v) {
                continue;
            }
            visited[j] = true;
            if matched_var[j].is_none()
                || augment(
                    matched_var[j].expect("checked some"),
                    eq_supports,
                    free_vars,
                    matched_var,
                    visited,
                )
            {
                matched_var[j] = Some(eq);
                return true;
            }
        }
        false
    }

    for eq in 0..n_eq {
        let mut visited = vec![false; n_var];
        if !augment(eq, eq_supports, free_vars, &mut matched_var, &mut visited) {
            return None; // an equality cannot be matched: give up
        }
    }
    Some(
        matched_var
            .iter()
            .enumerate()
            .filter_map(|(j, m)| m.map(|_| free_vars[j]))
            .collect(),
    )
}

/// The widest splittable variable (finite width `>= min_w`), or `None`.
fn widest_splittable_var(vars: &[TermId], bx: &VarBox, min_w: &BigRational) -> Option<TermId> {
    let mut best: Option<(TermId, BigRational)> = None;
    for &v in vars {
        let Some(iv) = bx.get(&v) else { continue };
        let Some(w) = interval_width(iv) else {
            continue;
        };
        if &w < min_w {
            continue;
        }
        match &best {
            Some((_, bw)) if bw >= &w => {}
            _ => best = Some((v, w)),
        }
    }
    best.map(|(v, _)| v)
}

/// Bisection point: a simple rational from the middle half of the interval
/// (small denominators keep the exact arithmetic fast), falling back to the
/// midpoint. Must be STRICTLY inside `(lo, hi)`.
fn bisection_point(iv: &Interval) -> Option<BigRational> {
    let (Endpoint::Finite(lo, _), Endpoint::Finite(hi, _)) = (&iv.lo, &iv.hi) else {
        return None;
    };
    if lo >= hi {
        return None;
    }
    let quarter = (hi - lo) / BigRational::from_integer(BigInt::from(4));
    let cand = simplest_rational_between(&(lo + &quarter), &(hi - &quarter));
    if &cand > lo && &cand < hi {
        return Some(cand);
    }
    let mid = (lo + hi) / BigRational::from_integer(BigInt::from(2));
    (&mid > lo && &mid < hi).then_some(mid)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(n: i64) -> BigRational {
        BigRational::from_integer(BigInt::from(n))
    }

    fn ratfrac(n: i64, d: i64) -> BigRational {
        BigRational::new(BigInt::from(n), BigInt::from(d))
    }

    #[test]
    fn integer_kth_roots() {
        assert_eq!(
            integer_kth_root_floor(&BigInt::from(100), 2),
            BigInt::from(10)
        );
        assert_eq!(
            integer_kth_root_floor(&BigInt::from(99), 2),
            BigInt::from(9)
        );
        assert_eq!(
            integer_kth_root_ceil(&BigInt::from(99), 2),
            BigInt::from(10)
        );
        assert_eq!(
            integer_kth_root_floor(&BigInt::from(27), 3),
            BigInt::from(3)
        );
        assert_eq!(
            integer_kth_root_floor(&BigInt::from(26), 3),
            BigInt::from(2)
        );
        assert_eq!(integer_kth_root_ceil(&BigInt::from(28), 3), BigInt::from(4));
        assert_eq!(integer_kth_root_floor(&BigInt::zero(), 5), BigInt::zero());
    }

    #[test]
    fn outward_rounded_roots_bracket() {
        // sqrt(9100): irrational; lower^2 <= 9100 <= upper^2 with strict
        // bracketing (9100 is not a perfect square).
        let u = rat(9100);
        let lo = kth_root_lower(&u, 2);
        let hi = kth_root_upper(&u, 2);
        assert!(&lo * &lo < u);
        assert!(&hi * &hi > u);
        assert!(lo < hi);
        // Exact perfect square stays exact.
        assert_eq!(kth_root_lower(&rat(100), 2), rat(10));
        assert_eq!(kth_root_upper(&rat(100), 2), rat(10));
        // Exact rational square: (3/2)^2 = 9/4.
        assert_eq!(kth_root_upper(&ratfrac(9, 4), 2), ratfrac(3, 2));
    }

    #[test]
    fn simplest_rational_selection() {
        // Simplest in [1/10, 1] is 1 (an integer in range).
        assert_eq!(simplest_rational_between(&ratfrac(1, 10), &rat(1)), rat(1));
        // Simplest in [0.3, 0.4] is 1/3.
        assert_eq!(
            simplest_rational_between(&ratfrac(3, 10), &ratfrac(4, 10)),
            ratfrac(1, 3)
        );
        // Simplest in [5.08, 6.53] is 6.
        assert_eq!(
            simplest_rational_between(&ratfrac(508, 100), &ratfrac(653, 100)),
            rat(6)
        );
        // Zero-containing intervals prefer 0; negative intervals mirror.
        assert_eq!(simplest_rational_between(&rat(-10), &rat(10)), rat(0));
        assert_eq!(
            simplest_rational_between(&ratfrac(-653, 100), &ratfrac(-508, 100)),
            rat(-6)
        );
    }

    #[test]
    fn invert_interval_positive_and_negative() {
        // 1/[2, 4] = [1/4, 1/2]
        let iv = Interval {
            lo: Endpoint::Finite(rat(2), true),
            hi: Endpoint::Finite(rat(4), true),
        };
        let inv = invert_interval(&iv).expect("invertible");
        assert_eq!(inv.lo, Endpoint::Finite(ratfrac(1, 4), true));
        assert_eq!(inv.hi, Endpoint::Finite(ratfrac(1, 2), true));
        // 1/[-4, -2] = [-1/2, -1/4]
        let iv = Interval {
            lo: Endpoint::Finite(rat(-4), true),
            hi: Endpoint::Finite(rat(-2), true),
        };
        let inv = invert_interval(&iv).expect("invertible");
        assert_eq!(inv.lo, Endpoint::Finite(ratfrac(-1, 2), true));
        assert_eq!(inv.hi, Endpoint::Finite(ratfrac(-1, 4), true));
        // Straddling zero: no sound inverse.
        let iv = Interval {
            lo: Endpoint::Finite(rat(-1), true),
            hi: Endpoint::Finite(rat(1), true),
        };
        assert!(invert_interval(&iv).is_none());
        // 1/[2, +inf) = (0, 1/2]: zero endpoint PROVEN open.
        let iv = Interval {
            lo: Endpoint::Finite(rat(2), true),
            hi: Endpoint::PosInf,
        };
        let inv = invert_interval(&iv).expect("invertible");
        assert_eq!(inv.lo, Endpoint::Finite(rat(0), false));
        assert_eq!(inv.hi, Endpoint::Finite(ratfrac(1, 2), true));
    }

    #[test]
    fn contract_power_even_sign_aware() {
        // x^2 ∈ [100, 100], x ∈ [0, 10]: x contracts to exactly [10, 10].
        let cur = Interval {
            lo: Endpoint::Finite(rat(0), true),
            hi: Endpoint::Finite(rat(10), true),
        };
        let q = Interval::point(rat(100));
        let out = contract_power(&cur, &q, 2).expect("non-empty");
        assert_eq!(interval_point(&out), Some(&rat(10)));
        // x^2 ∈ [100, 100], x ∈ [-4, 4]: PROVEN empty.
        let cur = Interval {
            lo: Endpoint::Finite(rat(-4), true),
            hi: Endpoint::Finite(rat(4), true),
        };
        assert!(contract_power(&cur, &q, 2).is_none());
        // x^2 ∈ [-8, -1]: impossible (even power is non-negative).
        let cur = Interval::whole();
        let q = Interval {
            lo: Endpoint::Finite(rat(-8), true),
            hi: Endpoint::Finite(rat(-1), true),
        };
        assert!(contract_power(&cur, &q, 2).is_none());
        // x^3 ∈ [8, 27]: x ∈ [2, 3] exactly (odd root, perfect cubes).
        let cur = Interval::whole();
        let q = Interval {
            lo: Endpoint::Finite(rat(8), true),
            hi: Endpoint::Finite(rat(27), true),
        };
        let out = contract_power(&cur, &q, 3).expect("non-empty");
        assert_eq!(out.lo, Endpoint::Finite(rat(2), true));
        assert_eq!(out.hi, Endpoint::Finite(rat(3), true));
    }

    #[test]
    fn rational_matrix_inverse() {
        // [[2, 0], [1, -1]]^-1 = [[1/2, 0], [1/2, -1]]
        let a = vec![vec![rat(2), rat(0)], vec![rat(1), rat(-1)]];
        let inv = invert_rational_matrix(&a).expect("nonsingular");
        assert_eq!(inv[0], vec![ratfrac(1, 2), rat(0)]);
        assert_eq!(inv[1], vec![ratfrac(1, 2), rat(-1)]);
        // Singular matrix.
        let s = vec![vec![rat(1), rat(2)], vec![rat(2), rat(4)]];
        assert!(invert_rational_matrix(&s).is_none());
    }

    /// End-to-end regression for the triangle-by-three-distances system at
    /// the theory level: the SAT witness is irrational (y3 = 3*sqrt(55)/4),
    /// so the verdict must come from the Krawczyk existence certificate. Also
    /// guards the endpoint-denominator rounding: without
    /// `round_interval_outward` this system exhibits exponential bignum
    /// growth through the k=1 projections and takes minutes instead of
    /// milliseconds.
    #[test]
    fn icp_triangle_three_distances_certifies_sat() {
        use ay_core::term::TermStore;
        use ay_core::Sort;
        let mut terms = TermStore::new();
        let x2 = terms.mk_var("x2", Sort::Real);
        let x3 = terms.mk_var("x3", Sort::Real);
        let y3 = terms.mk_var("y3", Sort::Real);
        let c100 = terms.mk_rational(rat(100));
        let c64 = terms.mk_rational(rat(64));
        let c49 = terms.mk_rational(rat(49));
        let c0 = terms.mk_rational(rat(0));
        let x2sq = terms.mk_mul(vec![x2, x2]);
        let x3sq = terms.mk_mul(vec![x3, x3]);
        let y3sq = terms.mk_mul(vec![y3, y3]);
        let a1 = terms.mk_eq(x2sq, c100);
        let s2 = terms.mk_add(vec![x3sq, y3sq]);
        let a2 = terms.mk_eq(s2, c64);
        let d = terms.mk_sub(vec![x3, x2]);
        let dsq = terms.mk_mul(vec![d, d]);
        let s3 = terms.mk_add(vec![dsq, y3sq]);
        let a3 = terms.mk_eq(s3, c49);
        let a4 = terms.mk_gt(y3, c0);
        let mut solver = NraSolver::new(&terms);
        use ay_core::TheorySolver;
        solver.assert_literal(a1, true);
        solver.assert_literal(a2, true);
        solver.assert_literal(a3, true);
        solver.assert_literal(a4, true);
        let res = solver.try_icp_branch_and_prune();
        let UniResult::SatAlgebraic(witnesses) = res else {
            panic!(
                "triangle 10/8/7 must be certified SAT via the Krawczyk existence \
                 certificate (its witnesses are irrational)"
            );
        };
        // The full witness assignment must be carried: x2 and x3 as exact
        // rationals, y3 as the exact algebraic root with y3^2 = 495/16
        // (y3 = 3*sqrt(55)/4).
        let val = witnesses
            .iter()
            .find_map(|(v, w)| match (v, w) {
                (v, UniWitness::Algebraic(a)) if *v == y3 => Some(a.clone()),
                _ => None,
            })
            .expect("y3 must carry an exact algebraic witness");
        match val.try_mul(&val).expect("same algebraic point") {
            crate::algebraic::RealScalar::Rational(sq) => {
                assert_eq!(
                    sq,
                    BigRational::new(BigInt::from(495), BigInt::from(16)),
                    "y3^2 must be exactly 495/16"
                );
            }
            crate::algebraic::RealScalar::Algebraic(_) => {
                panic!("y3^2 must reduce to the exact rational 495/16")
            }
        }
    }

    #[test]
    fn matching_finds_pin_complement() {
        // Two equations over {a, b, c}: eq0 ~ {a, b}, eq1 ~ {b}. A maximum
        // matching must match eq1 -> b, eq0 -> a, leaving c as the pin.
        let a = TermId(1);
        let b = TermId(2);
        let c = TermId(3);
        let eqs = vec![vec![a, b], vec![b]];
        let vars = vec![a, b, c];
        let matched = match_eqs_to_vars(&eqs, &vars).expect("matchable");
        assert!(matched.contains(&a));
        assert!(matched.contains(&b));
        assert!(!matched.contains(&c));
    }
}
