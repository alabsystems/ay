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
    collect_variable_bounds, constraint_is_infeasible, decide_single_variable, eval_poly_interval,
    intersect_intervals, isolate_roots, negate_endpoint_to_hi, negate_endpoint_to_lo,
    rational_sign, scale_interval, square_free_part, sturm_count, sturm_sequence, Endpoint,
    Interval, LinExpr, MultiAtom, MultiConstraint, MultiPoly, Rel, RootMarker, SingleVarResult,
    UniConstraint, UniPoly, UniResult, UniWitness,
};
use crate::NraSolver;

/// Maximum number of distinct variables the procedure attempts (sketch-scale).
///
/// MEASURED NEGATIVE, do not raise this again without new evidence. The
/// fix-sketch for the QF_NRA fast-decline families proposed raising it past the
/// family sizes (zankl 2..884 declared variables, median 57; UltimateAutomizer
/// 37..718, median 167) so the half-bounded matrix-interpretation systems would
/// reach a DECIDER instead of the relaxation. It was built and A/B'd:
/// `MAX_ICP_VARS = 64` plus a separate `MAX_ICP_TREE_VARS = 12` guarding the
/// expensive box tree, so the newly admitted systems paid only for root
/// contraction, `try_certify_box` and the small-integer ladder.
///
/// Interleaved same-day A/B, one release build per side, 96 instances of
/// 20200911-Pine / UltimateAutomizer / zankl at a 20 s cap:
///
///   * 0 conversions. Answers identical on all 96 (91 unknown, 3 sat, 2 unsat).
///   * Wall time 712.4 s -> 735.3 s, i.e. +3.2% for nothing.
///   * Soundness sweep over all 154 declared-status zankl + UltimateAutomizer
///     instances and a 387-instance stride sample of meti-tarski / LassoRanker
///     / Economics-Mulligan / Pine: 0 verdicts contradicting `:status`.
///
/// So the widening is SOUND but useless on this pool: those systems have no
/// bounded infeasibility for root contraction to refute, and their witnesses
/// are heterogeneous small rationals that a uniform ladder rung never hits.
/// See the development design notes for the companion negative on the grounding
/// lane's cover pins.
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

/// Total pinned (pin-variable, pin-value) attempts per call. Sized so a
/// typical pinned system exhausts its pin-variable choices against the whole
/// [`PIN_VALUE_LADDER`] rather than truncating the ladder after the first few
/// pin sets (12 truncated a 4-variable system to one ladder rung).
const MAX_PIN_ATTEMPTS: usize = 96;

/// Budget of boxes when variables had to be CLAMPED to the large initial box.
///
/// Such trees cannot prove UNSAT, so this budget only ever buys a SAT witness.
/// It was 64 on the theory that "only the first few boxes plausibly yield a
/// rational candidate" — measured false: the clamp is `2^20`, so the widest
/// dimension needs ~20 levels of DFS bisection before boxes reach unit width,
/// and 64 boxes cannot get there. Raising it to 1024 converted 11 of the 69
/// meti-tarski rational-witness misses for ~9% more wall time on that pool.
const CLAMPED_MAX_BOXES: usize = 1024;

/// Largest system [`NraSolver::dyadic_grid_search`] attempts. The grid is a
/// PRODUCT over coordinates, so past a handful of variables a node budget buys
/// only a prefix of the first variable's alphabet; the shape that phase is for
/// (meti-tarski Skolem constants) is 3-5 variables.
const GRID_MAX_VARS: usize = 6;

/// Finest dyadic grid level: denominators up to `2^GRID_MAX_LEVEL`.
const GRID_MAX_LEVEL: usize = 3;

/// Magnitude cap on grid values: `|k / 2^level| <= 4`. Raising it to 8 adds no
/// coverage on the measured witness pool (0 extra of 161) and doubles the
/// alphabet, so it stays at 4.
const GRID_ABS_CAP: usize = 4;

/// Contracted nodes [`NraSolver::dyadic_grid_search`] may expand in ONE call,
/// summed over all grid levels. One node costs one box clone plus one
/// `contract_box` — the same unit as a main-tree box, so this is sized against
/// [`MAX_BOXES`].
const GRID_MAX_NODES: usize = 20000;

/// Exact last-coordinate decisions [`NraSolver::dyadic_grid_search`] may spend
/// in its SECOND pass, per call.
///
/// One of these is a full univariate decision — square-free decomposition plus
/// Sturm root isolation over every residual constraint — so it costs orders of
/// magnitude more than the `contract_box` a grid node costs, and it must not be
/// allowed to consume a deadline the way an unbounded sweep would.
const GRID_EXACT_SOLVES: usize = 256;

/// Consecutive `Empty` exact decisions that switch pass 2 off for the rest of
/// the call.
///
/// WHY, MEASURED. `Empty` means the residual univariate system is PROVABLY
/// infeasible over that prefix's box — the exact solve did real work and proved
/// there is no witness there. A long run of them says the grid's whole surviving
/// prefix set is dead, and no later prefix in the same sweep is likely to differ.
/// The two ends of the observed distribution, both at `-T:60`, serial:
///
///   * `meti-tarski/polypaver/bench-sqrt-3d/polypaver-bench-sqrt-3d-chunk-0437`
///     — the cost case. Traced with `--nra-diag`: 110 exact decisions entered,
///     **every one of the 109 that completed returned `Empty`**, no witness, and
///     the pass ran until the deadline — `sat` in 51.0 s on `bee086d0a` became
///     `unknown` at the 60 s cap. The run is unbroken from the very first
///     decision, so any small cap ends it. With this cut the same file makes 8
///     decisions and is `sat` in 52.2-54.1 s, i.e. back to baseline.
///   * `meti-tarski/atan/problem/2/weak/atan-problem-2-weak-chunk-0135` and its
///     sibling `-0189` — the conversion cases. The witness
///     `skoS = root-obj(64x^2-1105, 2)` arrives on the **first** exact decision
///     of the file; the streak counter never leaves zero. Both conversions
///     observed in this lane behave the same way.
///
/// So the useful signal is entirely in the first few decisions and the cost is
/// entirely in the tail. Eight is a deliberately loose cut at a distribution
/// whose two modes are "1" and "never": it is 8x the observed conversion depth,
/// and it caps the cost case at ~7% of what it spent. This bound is measured on
/// this lane's pools only — it is not a claim about prefix sets in general.
const GRID_EXACT_EMPTY_STREAK: usize = 8;

/// What ONE exact last-coordinate decision costs in pass-2 node units.
///
/// The node budget exists to bound wall time, so it must be charged in units
/// proportional to wall time. A grid node is one `contract_box`; an exact
/// decision is a square-free decomposition plus Sturm root isolation over the
/// whole residual system, empirically two orders of magnitude dearer. Charging
/// it as one node let a boolean-heavy file — where the grid is re-entered on
/// every theory call — pay pass 2 over and over.
const GRID_EXACT_NODE_COST: usize = 64;

/// Pass-2 nodes available to ONE `check()`, drawn from
/// [`crate::NraSolver::grid_exact_budget`] rather than from pass 1's counter.
///
/// SEPARATE ON PURPOSE. Pass 2 re-sweeps the same tree pass 1 just swept, so
/// when both debit one counter the re-sweep bills pass 1's interior work twice
/// and every exact decision bills 64 more. That deficit is invisible on the call
/// that spends it — pass 2 only runs when pass 1 already failed — and surfaces
/// on a LATER theory call, whose pass 1 finds the shared budget gone. Splitting
/// the counters makes pass 1's node accounting bit-for-bit what it is on
/// `bee086d0a`, so the exact machinery cannot cost a file the grid already wins.
const GRID_EXACT_MAX_NODES: usize = 20000;

/// Pass-2 nodes available to one `NraSolver` instance, across every `check()`.
/// The same caveat as [`crate::NraSolver::grid_budget`] applies: the DPLL(T)
/// pipeline builds a fresh `NraSolver` per refinement, so this bounds an
/// instance, not a solve.
pub(crate) const GRID_EXACT_SOLVE_NODES: usize = 400_000;

/// Grid nodes available to the WHOLE solve, across every `check()`. Bounds the
/// boolean-heavy case, where the per-call cap alone would be paid once per
/// theory call. See [`crate::NraSolver::grid_budget`].
pub(crate) const GRID_SOLVE_NODES: usize = 400_000;

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

/// A "nice" rational inside an interval that may be UNBOUNDED on one or both
/// sides.
///
/// [`nice_point_in`] returns `None` the moment an endpoint is infinite, so
/// every SAT-candidate path built on it silently does NOTHING on the shape
/// that dominates meti-tarski: a Skolem constant with a one-sided bound
/// (`skoT > 0`, interval `(0, +inf)`). This replaces each infinite side with a
/// finite surrogate two units from the finite side (or `[-1, 1]` when both
/// sides are infinite) so the simplest-rational descent yields a SMALL value
/// -- `0`, `+/-1`, `+/-1/2` -- which is what these witnesses actually are.
/// The result is re-checked against the ORIGINAL interval, so nothing outside
/// it is ever proposed.
///
/// Sound by construction: this only proposes a candidate. Every rational
/// candidate is re-verified by exact substitution into EVERY asserted atom
/// (`verify_model`) before `sat` is claimed, so a bad proposal costs time and
/// can never cost correctness.
fn nice_point_in_open(iv: &Interval) -> Option<BigRational> {
    if matches!(iv.lo, Endpoint::Finite(..)) && matches!(iv.hi, Endpoint::Finite(..)) {
        return nice_point_in(iv);
    }
    let two = BigRational::from_integer(BigInt::from(2));
    let one = BigRational::one();
    let surrogate = match (&iv.lo, &iv.hi) {
        (Endpoint::Finite(l, inc), Endpoint::PosInf) => Interval {
            lo: Endpoint::Finite(l.clone(), *inc),
            hi: Endpoint::Finite(l + &two, true),
        },
        (Endpoint::NegInf, Endpoint::Finite(h, inc)) => Interval {
            lo: Endpoint::Finite(h - &two, true),
            hi: Endpoint::Finite(h.clone(), *inc),
        },
        (Endpoint::NegInf, Endpoint::PosInf) => Interval {
            lo: Endpoint::Finite(-(&one), true),
            hi: Endpoint::Finite(one, true),
        },
        _ => return None,
    };
    nice_point_in(&surrogate).filter(|p| interval_contains(iv, p))
}

/// Candidate values [`NraSolver::grid_dfs`] wants per coordinate before it will
/// accept a node's list as adequate.
///
/// MEASURED, and this constant exists only because of the measurement. Probing
/// the MV QF_NRA residual with `--nra-grid-probe` (`-T:60`, serial, 21 misses
/// that have a rational z3 witness, at most 6 variables, and actually reach
/// [`NraSolver::dyadic_grid_search`]):
///
/// * the sweep is budget-starved in **0 of 21** — it spends a MEDIAN of **48**
///   of its 20 000 nodes and a maximum of 11 616, then stops because it has run
///   out of ALPHABET, not out of budget;
/// * on the 9 files where the witness both satisfies a call's constraints and
///   lies in that call's box, the candidate list at the very first coordinate
///   is **2 entries long** and the witness value is in none of them.
///
/// Two entries is `{simplest rational, midpoint}`: on a contracted interval the
/// fixed alphabet `{k/2^L : |k/2^L| <= 4, L <= 3}` contributes **nothing at
/// all**, because the interval no longer straddles any of those values. The
/// "dyadic grid" is not a grid on this pool — it is two points per coordinate,
/// and a product of 2s is what the 20 000-node budget is being spent on.
///
/// So the coordinate is given a real branching factor at ITS OWN scale
/// ([`interval_scale_points`]), and 5 is chosen against the budget that was
/// measured free: five candidates over six variables is 15 625 nodes, still
/// inside [`GRID_MAX_NODES`], and over the three variables that dominate this
/// pool it is 125.
///
/// DO NOT RAISE THIS TO BUY RESIDUAL FILES. Measured ALONE at 9 and 13, T=300,
/// jobs 4, on the 35 MV QF_NRA residual files that reach
/// [`NraSolver::dyadic_grid_search`] with a known rational z3 witness:
/// **13 sat / 22 unknown at all three of 5, 9 and 13** — +0 files, -0 files —
/// for +6.3% wall at 9 and +15.0% at 13.
///
/// It is not that the widening fails to bite. It bites: at 9, five of the
/// `meti-tarski/sqrt/1mcosq/7` files move `MAX_PREFIX 0/3 -> 1/3` with the
/// witness's first coordinate offered at index 7 of 9 (chunks 0170, 0172, 0190,
/// 0153, 0187; chunk-0164 instead flips to out-of-box). The failure simply MOVES
/// TO THE NEXT COORDINATE, because these witnesses are z3's dyadic
/// approximations of transcendental constants at `2^-24` (pi), `2^-30` (pi/2)
/// and `2^-42`, and [`interval_scale_points`] takes the COARSEST scale holding
/// `want+1` points inside an interval ~`1e-7` wide.
///
/// **AVAILABILITY IS NON-MONOTONE IN THIS CONSTANT — do not reason geometrically
/// about it.** An earlier revision of this comment claimed the three witnesses
/// need `want` = 7, 95 and 393 215. Re-deriving `interval_scale_points` exactly
/// (it reproduces the probe's offered lists value-for-value) gives:
///
/// | witness | true min `want` | implied `GRID_MIN_BRANCH` |
/// |---|---|---|
/// | pi @ `2^-24` | **2** | **4** — *lower than the current 5* |
/// | pi/2 @ `2^-30` | **53** | 55 — `55^3` = 166k nodes, still 8x over the cap |
/// | `2^-42` | none | unreachable at ANY `want` (below) |
///
/// The chosen scale `k` JUMPS with `want`, so a value offered at branch 4 can be
/// absent at 5 and present again at 9. Measured on a real binary,
/// `sqrt-1mcosq-7-chunk-0170`: branch 4 offers `[d0:3/4, d1:-1/4]` (witness
/// offered, prefix advances), branch 5 offers `[d0:-1/5]`, branch 9 offers
/// `[d0:7/9]`. Tabulating a finite "min want" for the `2^-42` witness was also
/// wrong on its own terms — `6908435304717` is odd, so with
/// [`GRID_SCALE_MAX_BITS`] = 40 no multiple of `2^-40` equals it at any `want`.
///
/// The verdict survives the correction, on a WIDER basis than it was first
/// measured: branch **4** was tested too, serially at T=300 on the same 35-file
/// pool, and gives 13 sat / 22 unknown / 590.8s — identical to base. Lead 6
/// closes at 4, 5, 9 and 13.
///
/// Width is not the lever, and neither is the alphabet: at the nodes where the
/// witness is in-box and unoffered, the count of `dyadic_grid(GRID_MAX_LEVEL)`
/// values inside the interval is **0 in 9 of 10** measured records. See
/// the development design notes, lead 6.
const GRID_MIN_BRANCH: usize = 5;

/// Finest dyadic scale [`interval_scale_points`] will descend to, as a power of
/// two. Past this the interval is narrower than `2^-40 / GRID_MIN_BRANCH` and
/// the two points already in the list — the simplest rational in the interval
/// and its midpoint — describe it better than any subdivision would, at a
/// fraction of the arithmetic width.
const GRID_SCALE_MAX_BITS: usize = 40;

/// Number of distinct pin VALUES tried per pin-variable set (the ladder in
/// [`pin_candidate`]).
const PIN_VALUE_LADDER: usize = 8;

/// Up to `want` dyadic points spread across the INTERIOR of `iv`, at the
/// coarsest dyadic spacing that fits that many of them inside.
///
/// This is the reach that [`dyadic_grid`] does not have. `dyadic_grid` is a
/// fixed alphabet in absolute terms — it can only name values of magnitude at
/// most 4 with denominator at most 8 — so once contraction has narrowed a
/// coordinate to, say, `[1.5703, 1.5709]`, not one of its 65 values is inside
/// and it contributes nothing. These points are defined RELATIVE to the
/// interval, so they exist wherever the interval does and however narrow it is,
/// down to [`GRID_SCALE_MAX_BITS`].
///
/// Dyadic rather than evenly spaced on purpose: `lo + i*(hi-lo)/(want+1)`
/// inherits the denominators of both endpoints and multiplies them, and every
/// downstream exact substitution then pays for that width. A multiple of
/// `2^-k` has a denominator bounded by `2^GRID_SCALE_MAX_BITS` whatever the
/// endpoints look like.
///
/// SOUNDNESS. Nothing here decides anything. These are PROPOSALS handed to the
/// same [`NraSolver::verify_model`] gate every other grid candidate passes
/// through, inside a phase that cannot return `Unsat`. A useless point costs
/// one `contract_box` and cannot produce a verdict.
fn interval_scale_points(iv: &Interval, want: usize) -> Vec<BigRational> {
    let (Endpoint::Finite(lo, _), Endpoint::Finite(hi, _)) = (&iv.lo, &iv.hi) else {
        return Vec::new(); // unbounded: no scale to work at
    };
    if want == 0 || hi <= lo {
        return Vec::new();
    }
    let width = hi - lo;
    // Coarsest `k` with `2^-k <= width / (want+1)`, i.e. `2^k >= (want+1)/width`.
    let need = BigRational::from_integer(BigInt::from(want as u64 + 1)) / &width;
    let mut k = 0usize;
    let mut pow = BigRational::one();
    let two = BigRational::from_integer(BigInt::from(2));
    while pow < need {
        if k == GRID_SCALE_MAX_BITS {
            return Vec::new(); // narrower than this scale can describe
        }
        pow *= &two;
        k += 1;
    }
    // Multiples of `2^-k` strictly between the endpoints. By construction there
    // are at least `want` of them, so the count is bounded by `2*want + 2`.
    let m_lo = (lo * &pow).floor().to_integer() + BigInt::one();
    let m_hi = (hi * &pow).ceil().to_integer() - BigInt::one();
    if m_hi < m_lo {
        return Vec::new();
    }
    let den = BigInt::one() << k;

    // COST: index arithmetic, NOT materialisation. The obvious loop —
    // `while m <= m_hi { push(m/den) }` — is LINEAR IN INTERVAL WIDTH on the
    // `k == 0` branch, and `k == 0` is taken for every finite interval of width
    // >= want+1. The comment above ("bounded by 2*want + 2") follows from the
    // minimality of `k` only when `k >= 1`; at `k == 0` nothing bounds the
    // count, because no smaller scale was rejected.
    //
    // MEASURED on the materialising version: width 10 -> 84us, 1e6 -> 217ms,
    // 1e8 -> 26.5s, **1e9 -> 347 SECONDS in a single call** — one DFS node alone
    // blows a 300s competition cap. It is reachable on ordinary input: it needs
    // only a post-contraction interval that is wide and holds at most a couple
    // of the fixed alphabet's 65 values, e.g. `[10, 1e9]`.
    //
    // It was LATENT rather than active on this corpus — an instrumented scan of
    // 1,276 files found the `k == 0` branch live (25 of 1,076 calls) but always
    // at span 2, max span 8 anywhere. Nothing in the code kept it cheap; only
    // the corpus's incidental interval widths did. This form is flat in width
    // (width 1e9: 347s -> 5.2us) and returns the same values.
    let count = (&m_hi - &m_lo) + BigInt::one();
    let want_big = BigInt::from(want as u64);
    let pick = |m: &BigInt| BigRational::new(m.clone(), den.clone());

    if count <= want_big {
        // Few enough to take them all; the endpoint filter still applies.
        let mut all = Vec::new();
        let mut m = m_lo.clone();
        while m <= m_hi {
            let q = pick(&m);
            if interval_contains(iv, &q) {
                all.push(q);
            }
            m += BigInt::one();
        }
        return all;
    }

    // More multiples than asked for: walk STRAIGHT to the `want` indices that
    // the spread would have selected, so the cost is O(want) rather than
    // O(width). Indices match the previous `all[(i * (n - 1)) / (want - 1)]`
    // exactly when every multiple lies inside `iv` (the common case, since
    // `m_lo`/`m_hi` are already the strictly-interior bounds).
    let n_minus_1 = &count - BigInt::one();
    let divisor = BigInt::from((want.saturating_sub(1)).max(1) as u64);
    let mut out: Vec<BigRational> = Vec::with_capacity(want);
    for i in 0..want {
        let idx = (BigInt::from(i as u64) * &n_minus_1) / &divisor;
        let q = pick(&(&m_lo + idx));
        if interval_contains(iv, &q) && !out.contains(&q) {
            out.push(q);
        }
    }
    out
}

/// The `k`-th candidate pin value inside `iv`, `None` when that rung does not
/// land in the interval.
///
/// The three-rung ladder this replaces -- simplest-rational, midpoint,
/// lower-half-simplest -- is strongly CORRELATED: all three descend to the same
/// small-denominator neighbourhood, and on the meti-tarski shape all three
/// collapse to the single value `0`. A Skolem constant asserted `(not (<= skoT
/// 0))` yields the SOUND interval `[0, +inf)` (a strict bound relaxed to a
/// closed one is a legal over-approximation), whose simplest rational is `0` --
/// exactly the value the strict atom forbids. Every attempt then fails on the
/// same point and the whole pinned search does no work.
///
/// So the ladder adds the values these witnesses are actually made of: the
/// small integers `1`, `-1`, `2`, `1/2` and the two endpoint neighbourhoods.
/// Sound: a pin value is only a PROPOSAL. `sat` is claimed solely through
/// `verify_model`, which substitutes exactly into every asserted atom, so a
/// wrong rung wastes time and can never produce a wrong verdict.
fn pin_candidate(iv: &Interval, k: usize) -> Option<BigRational> {
    let unit = |x: BigRational| interval_contains(iv, &x).then_some(x);
    match k {
        0 => nice_point_in_open(iv),
        1 => unit(BigRational::one()),
        2 => unit(-BigRational::one()),
        3 => interval_midpoint(iv).filter(|m| interval_contains(iv, m)),
        4 => lower_half_point(iv),
        5 => unit(BigRational::from_integer(BigInt::from(2))),
        6 => unit(BigRational::new(BigInt::one(), BigInt::from(2))),
        // Just inside the finite lower (else upper) endpoint: the witness of a
        // strict bound often sits against it.
        _ => match (&iv.lo, &iv.hi) {
            (Endpoint::Finite(l, _), _) => unit(l + BigRational::one())
                .or_else(|| unit(l + BigRational::new(BigInt::one(), BigInt::from(1024)))),
            (_, Endpoint::Finite(h, _)) => unit(h - BigRational::one())
                .or_else(|| unit(h - BigRational::new(BigInt::one(), BigInt::from(1024)))),
            _ => None,
        },
    }
}

/// Sweep the [`pin_candidate`] ladder as whole candidate VECTORS over `bx`,
/// returning the first that `verify_model` accepts against every asserted atom.
/// Used where a single cheap shot is worth taking -- the unclamped root box and
/// the high-dimensional pure-inequality give-up -- not inside the box tree,
/// where it would multiply the per-box cost.
fn ladder_vector(vars: &[TermId], bx: &VarBox, k: usize) -> Option<Vec<(TermId, BigRational)>> {
    let mut model = Vec::with_capacity(vars.len());
    for &v in vars {
        model.push((v, pin_candidate(bx.get(&v)?, k)?));
    }
    Some(model)
}

// ============================================================================
// The box: per-variable intervals.
// ============================================================================

type VarBox = crate::HashMap<TermId, Interval>;

/// Immutable inputs shared by every node of one dyadic-grid DFS.
struct GridSearch<'a> {
    constraints: &'a [MultiConstraint],
    vars: &'a [TermId],
    order: &'a [TermId],
    grid: &'a [BigRational],
    /// Exact last-coordinate solving state for this pass. Pass 1 carries
    /// [`ExactState::disabled`] and is therefore bit-for-bit the cheap sweep;
    /// pass 2 carries a budgeted [`ExactState::with`].
    exact: &'a ExactState,
}

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

/// DIAGNOSTIC ONLY (`--nra-diag`): is the trace enabled?
fn diag_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().nra_diag)
}

macro_rules! diag {
    ($($a:tt)*) => { if diag_on() { eprintln!($($a)*); } };
}

/// DIAGNOSTIC ONLY (`--nra-grid-probe`, meaningful only alongside
/// `--nra-witness`): is the grid-enumeration probe enabled?
fn grid_probe_on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().nra_grid_probe)
}

/// DIAGNOSTIC ONLY (`--nra-grid-probe`): what [`NraSolver::grid_dfs`] did
/// with a KNOWN witness, for one [`NraSolver::dyadic_grid_search`] call.
///
/// The one question this exists to answer, which nothing outside the solver can:
/// **at the moment the sweep gave up, how many of the witness's coordinates had
/// it fixed correctly?** `max_prefix` is that number. A `max_prefix` near
/// `order.len()` says the traversal is in the right region and needs a tie-break;
/// a `max_prefix` of 0-1 says it is exploring somewhere else entirely.
///
/// It also separates the three ways a correct prefix can die, which have
/// completely different fixes:
///
/// * `absent` — the witness's value for `order[depth]` was not in that node's
///   candidate list at all (outside the contracted interval, or off the
///   alphabet). No ordering change can help; this is reach, not order.
/// * `refuted` — the correct child was built and `contract_box` refuted it.
///   That would be a soundness signal, not an ordering one.
/// * neither — the correct value WAS a candidate and was simply never taken
///   before the budget ran out. This is the pure ordering failure.
///
/// `cand_idx` records, per depth on an all-correct prefix, where the witness
/// value sat in the candidate list and how long that list was: the position it
/// would have to be promoted to.
///
/// Nothing here is read by any decision. It is written only through
/// [`Self::probe_pick`] and friends, all of which return immediately when the
/// thread-local slot is empty, and the slot is only ever filled when the env
/// variable is set.
#[derive(Default)]
struct GridProbe {
    /// Witness value for each position of `order`.
    wit: Vec<BigRational>,
    /// Variable names in `order` position, for the report.
    names: Vec<String>,
    /// `correct[d]` — is the value currently pinned at depth `d` the witness's?
    correct: std::cell::RefCell<Vec<bool>>,
    /// Contracted nodes expanded, all levels and both passes.
    nodes: std::cell::Cell<usize>,
    /// Deepest node reached at all.
    max_depth: std::cell::Cell<usize>,
    /// Deepest ALL-CORRECT prefix reached. The number this probe is for.
    max_prefix: std::cell::Cell<usize>,
    /// Grid level currently sweeping, and nodes spent per level.
    level: std::cell::Cell<usize>,
    per_level: std::cell::RefCell<Vec<usize>>,
    /// Deepest all-correct prefix reached WITHIN the current level sweep.
    ///
    /// Reported separately from `max_prefix` because the two answer different
    /// questions. Every level restarts the walk with a strictly larger
    /// alphabet, so a value absent at level 0 (integers only) may be present at
    /// level 3 — scoring "the witness value was not a candidate" across all
    /// levels at once would report every non-integer witness as unreachable.
    /// `lvl_*` therefore describe the LAST level swept, which is the one with
    /// the full alphabet.
    lvl_prefix: std::cell::Cell<usize>,
    /// Deepest all-correct prefix whose next witness value was not a candidate.
    absent_at: std::cell::Cell<isize>,
    /// Deepest all-correct prefix whose correct child `contract_box` refuted.
    refuted_at: std::cell::Cell<isize>,
    /// `(depth, index of witness value in cands, cands.len(), witness value is
    /// still inside this coordinate's contracted interval)` per all-correct
    /// prefix, deepest observation per depth.
    ///
    /// The fourth field is what separates the two causes of an ABSENT witness
    /// value, which need opposite fixes. `true` — the value is IN the box and
    /// the candidate generator simply never offered it: a WIDTH problem, fixed
    /// by generating more per coordinate. `false` — contraction under this
    /// prefix already pushed the value out of the interval, so no generator
    /// working inside the interval could ever propose it: only a different
    /// prefix, or re-offering on backtrack, can reach it.
    cand_idx: std::cell::RefCell<Vec<(usize, isize, usize, bool)>>,
    /// Did the sweep stop because `budget` hit zero?
    starved: std::cell::Cell<bool>,
    /// Deepest all-correct prefix at which the witness value was IN the
    /// interval and still not offered, rendered: the value, the interval, the
    /// candidates that were offered instead, and how many of the FULL pass-1
    /// alphabet (`dyadic_grid(GRID_MAX_LEVEL)`) lie inside that interval.
    ///
    /// That last count is the one that decides between the two width remedies:
    /// if it is 0 the fixed alphabet has nothing to contribute at this node
    /// however early it is offered, and only interval-relative generation can
    /// reach the value.
    absent_detail: std::cell::RefCell<String>,
}

thread_local! {
    /// DIAGNOSTIC ONLY: the probe for the innermost active
    /// [`NraSolver::dyadic_grid_search`], or `None`.
    static GRID_PROBE: std::cell::RefCell<Option<GridProbe>> =
        const { std::cell::RefCell::new(None) };
}

/// DIAGNOSTIC ONLY: run `f` against the active probe, if there is one.
fn probe<R>(f: impl FnOnce(&GridProbe) -> R) -> Option<R> {
    if !grid_probe_on() {
        return None;
    }
    GRID_PROBE.with(|p| p.borrow().as_ref().map(f))
}

impl GridProbe {
    /// Is the prefix `order[0..depth]` pinned entirely to witness values?
    fn prefix_ok(&self, depth: usize) -> bool {
        self.correct.borrow()[..depth].iter().all(|b| *b)
    }

    /// A new level sweep is starting: the alphabet just grew, so the
    /// per-level findings from the coarser sweep no longer describe what is
    /// reachable. Clear them; `max_prefix` and `nodes` are cumulative and stay.
    fn level_reset(&self, level: usize) {
        self.level.set(level);
        self.lvl_prefix.set(0);
        self.absent_at.set(-1);
        self.refuted_at.set(-1);
        self.cand_idx.borrow_mut().clear();
        self.absent_detail.borrow_mut().clear();
        self.correct
            .borrow_mut()
            .iter_mut()
            .for_each(|b| *b = false);
    }

    /// About to walk `cands` at `depth`. On the witness path, record where the
    /// witness's value sits in that list — or that it is not there at all.
    fn note_cands(&self, depth: usize, cands: &[BigRational], iv: &Interval) -> bool {
        if !self.prefix_ok(depth) {
            return false;
        }
        let idx = cands.iter().position(|c| *c == self.wit[depth]);
        let in_iv = interval_contains(iv, &self.wit[depth]);
        let mut ci = self.cand_idx.borrow_mut();
        let entry = (
            depth,
            idx.map(|i| i as isize).unwrap_or(-1),
            cands.len(),
            in_iv,
        );
        match ci.iter_mut().find(|(d, _, _, _)| *d == depth) {
            Some(slot) => *slot = entry,
            None => ci.push(entry),
        }
        if idx.is_none() && (depth as isize) > self.absent_at.get() {
            self.absent_at.set(depth as isize);
        }
        if idx.is_none() && in_iv {
            let full = dyadic_grid(GRID_MAX_LEVEL);
            let in_alpha = full.iter().filter(|g| interval_contains(iv, g)).count();
            *self.absent_detail.borrow_mut() = format!(
                "d{depth} wit={} iv=[{:?},{:?}] full_alphabet_in_iv={in_alpha} offered={:?}",
                self.wit[depth],
                iv.lo,
                iv.hi,
                cands.iter().map(|c| c.to_string()).collect::<Vec<_>>()
            );
        }
        true
    }

    /// Contraction had ALREADY collapsed `order[depth]` to `p`, so the sweep
    /// makes no choice here. Recording it is what keeps the prefix accounting
    /// honest: without this, a collapsed coordinate reads as "wrong" and every
    /// deeper node is scored off the witness path even when it is on it. Costs
    /// no node — nothing was expanded.
    fn pin(&self, depth: usize, p: &BigRational) {
        let ok = self.prefix_ok(depth) && *p == self.wit[depth];
        self.correct.borrow_mut()[depth] = ok;
        for d in depth + 1..self.wit.len() {
            self.correct.borrow_mut()[d] = false;
        }
        if ok {
            if depth + 1 > self.max_prefix.get() {
                self.max_prefix.set(depth + 1);
            }
            if depth + 1 > self.lvl_prefix.get() {
                self.lvl_prefix.set(depth + 1);
            }
        }
        if !ok && self.prefix_ok(depth) {
            // The collapse itself put the coordinate off the witness. Record it
            // in the same slot `note_cands` would use, with a marker length of
            // 0 meaning "no choice existed here".
            let mut ci = self.cand_idx.borrow_mut();
            match ci.iter_mut().find(|(d, _, _, _)| *d == depth) {
                Some(slot) => *slot = (depth, -2, 0, false),
                None => ci.push((depth, -2, 0, false)),
            }
            if (depth as isize) > self.absent_at.get() {
                self.absent_at.set(depth as isize);
            }
        }
    }

    /// A node is being expanded at `depth` with value `c`.
    fn pick(&self, depth: usize, c: &BigRational) {
        self.nodes.set(self.nodes.get() + 1);
        let lvl = self.level.get();
        let mut per = self.per_level.borrow_mut();
        if lvl < per.len() {
            per[lvl] += 1;
        }
        drop(per);
        if depth + 1 > self.max_depth.get() {
            self.max_depth.set(depth + 1);
        }
        let ok = self.prefix_ok(depth) && *c == self.wit[depth];
        self.correct.borrow_mut()[depth] = ok;
        // Deeper slots describe a prefix that no longer exists.
        for d in depth + 1..self.wit.len() {
            self.correct.borrow_mut()[d] = false;
        }
        if ok {
            if depth + 1 > self.max_prefix.get() {
                self.max_prefix.set(depth + 1);
            }
            if depth + 1 > self.lvl_prefix.get() {
                self.lvl_prefix.set(depth + 1);
            }
        }
    }

    /// `contract_box` refuted the node just picked at `depth`.
    fn note_refuted(&self, depth: usize) {
        if self.correct.borrow()[depth]
            && self.prefix_ok(depth)
            && (depth as isize) > self.refuted_at.get()
        {
            self.refuted_at.set(depth as isize);
        }
    }
}

/// DIAGNOSTIC ONLY (`--nra-witness`): an externally supplied rational
/// point, given as `name=p/q` items separated by commas or whitespace.
///
/// Consulted by [`NraSolver::diag_witness_report`] and by nothing else: it can
/// never influence a verdict, a box, or a candidate. It exists to answer one
/// question that cannot be answered from outside the solver — for a file AY
/// leaves `unknown`, does a KNOWN solution survive the root contraction of the
/// theory calls AY actually makes?
fn diag_witness() -> &'static [(String, BigRational)] {
    static W: std::sync::OnceLock<Vec<(String, BigRational)>> = std::sync::OnceLock::new();
    W.get_or_init(|| {
        let Some(raw) = ay_core::misc_cli_flags().nra_witness.clone() else {
            return Vec::new();
        };
        let mut out = Vec::new();
        for item in raw.split([',', ' ', '\t', '\n']).filter(|t| !t.is_empty()) {
            let Some((name, val)) = item.split_once('=') else {
                continue;
            };
            let val = val.trim();
            let parsed = match val.split_once('/') {
                Some((n, d)) => match (n.trim().parse::<BigInt>(), d.trim().parse::<BigInt>()) {
                    (Ok(n), Ok(d)) if !d.is_zero() => Some(BigRational::new(n, d)),
                    _ => None,
                },
                None => val.parse::<BigInt>().ok().map(BigRational::from_integer),
            };
            if let Some(q) = parsed {
                out.push((name.trim().to_string(), q));
            }
        }
        out
    })
    .as_slice()
}

/// Pass-2 state for [`NraSolver::dyadic_grid_search`], threaded through
/// [`NraSolver::grid_dfs`].
///
/// Pass 1 runs with [`ExactState::disabled`], whose `remaining` is zero, so the
/// exact branch in `grid_dfs` is dead code on that pass and pass 1 does exactly
/// the work it does without this feature.
struct ExactState {
    /// Is this the exact-solving pass? Pass 1 is `false` and behaves exactly as
    /// it does with this feature compiled out.
    pass2: bool,
    /// Exact decisions still permitted in this call.
    remaining: std::cell::Cell<usize>,
    /// Consecutive `Empty` decisions since the last non-`Empty` one. Reaching
    /// [`GRID_EXACT_EMPTY_STREAK`] zeroes `remaining`.
    empty_streak: std::cell::Cell<usize>,
}

impl ExactState {
    /// Pass 1: no exact decisions at all.
    fn disabled() -> Self {
        Self {
            pass2: false,
            remaining: std::cell::Cell::new(0),
            empty_streak: std::cell::Cell::new(0),
        }
    }

    /// Pass 2: up to `n` exact decisions, subject to the streak cut.
    fn with(n: usize) -> Self {
        Self {
            pass2: true,
            remaining: std::cell::Cell::new(n),
            empty_streak: std::cell::Cell::new(0),
        }
    }

    /// May another exact decision be made?
    fn available(&self) -> bool {
        self.remaining.get() > 0
    }

    /// Has pass 2 run out of exact decisions — by the streak cut or by its
    /// per-call count — and therefore have nothing left to contribute?
    ///
    /// Pass 2 exists ONLY to solve last coordinates. With no decisions left its
    /// tree walk would enumerate the very alphabet pass 1 has already
    /// enumerated, on a second budget, and find the same nothing. Stopping the
    /// sweep here is what makes the streak cut actually save the time it is
    /// supposed to save rather than merely stop the Sturm calls.
    fn spent(&self) -> bool {
        self.pass2 && !self.available()
    }

    /// Charge one decision and fold its outcome into the streak counter. A run
    /// of [`GRID_EXACT_EMPTY_STREAK`] `Empty`s disables the pass outright.
    ///
    /// `Declined` leaves the streak ALONE rather than resetting it. `Declined`
    /// is a bail that carries no information about feasibility (a pin that is not
    /// a point, a residual that is not univariate, a witness that failed
    /// re-verification), whereas `Empty` is a proof that the prefix is dead.
    /// Letting the uninformative outcome reset the counter would let an
    /// alternating `Empty, Declined, Empty, …` sequence run the expensive
    /// decision forever without the streak ever reaching the cut.
    ///
    /// Most `Empty`s arrive from `decide_single_variable` and cost a full Sturm
    /// decision; a few are the cheap constant-residual refutation. Both are
    /// counted, because the counter measures accumulated evidence that the prefix
    /// set is dead, not accumulated wall time — wall time is what
    /// [`GRID_EXACT_NODE_COST`] and the pass-2 node budget bound.
    fn charge(&self, outcome: &ExactOutcome) {
        self.remaining.set(self.remaining.get().saturating_sub(1));
        match outcome {
            ExactOutcome::Empty => {
                let s = self.empty_streak.get() + 1;
                self.empty_streak.set(s);
                if s >= GRID_EXACT_EMPTY_STREAK {
                    diag!("NRA-LAST streak-cut after={s}");
                    self.remaining.set(0);
                }
            }
            ExactOutcome::Declined => {}
            ExactOutcome::Model(_) => self.empty_streak.set(0),
        }
    }
}

/// What one exact last-coordinate decision established.
enum ExactOutcome {
    /// A full model, already re-verified against every parsed constraint.
    Model(UniResult),
    /// The residual univariate system is PROVABLY infeasible over this prefix's
    /// box. Evidence that the PREFIX is dead — never that the problem is, and
    /// never acted on as a refutation.
    Empty,
    /// Undecided, or declined before the decision was reached. No information.
    Declined,
}

impl NraSolver<'_> {
    /// DIAGNOSTIC ONLY: render a box as `name=[lo,hi]` pairs.
    fn diag_box(&self, vars: &[TermId], bx: &VarBox) -> String {
        let mut s = String::new();
        for &v in vars {
            let name = match self.terms.get(v) {
                ay_core::TermData::Var(n, _) => n.clone(),
                other => format!("{other:?}"),
            };
            let iv = bx.get(&v);
            let f = |e: &Endpoint| match e {
                Endpoint::Finite(q, _) => format!("{q}"),
                Endpoint::NegInf => "-inf".into(),
                Endpoint::PosInf => "+inf".into(),
            };
            match iv {
                Some(iv) => s.push_str(&format!("{name}=[{},{}] ", f(&iv.lo), f(&iv.hi))),
                None => s.push_str(&format!("{name}=<none> ")),
            }
        }
        s
    }

    /// DIAGNOSTIC ONLY (`--nra-witness`): report where the externally
    /// supplied rational point sits relative to THIS theory call's root box.
    ///
    /// Contraction is only obliged to preserve the solutions of the constraint
    /// set it is handed, and DPLL hands the theory one Boolean branch at a time.
    /// So the report always states three things together:
    ///
    /// * `sat_cons` — does the point satisfy THIS call's parsed constraints?
    /// * `pre_out`  — how many coordinates the INITIAL bounds already exclude;
    /// * `post_out` — how many the box excludes AFTER contraction.
    ///
    /// `sat_cons=y` with `post_out>0` (or `refuted=true`) is the ONLY reading
    /// that indicts contraction, and it would be a soundness bug: contraction
    /// may remove provably infeasible regions and nothing else. `sat_cons=n`
    /// says only that DPLL handed the theory a branch this point does not
    /// satisfy, which is ordinary and carries no information about the hull.
    fn diag_witness_report(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        pre: &VarBox,
        post: &VarBox,
        refuted: bool,
        all_parsed: bool,
    ) {
        let w = diag_witness();
        let mut model: Vec<(TermId, BigRational)> = Vec::new();
        let mut uncovered = 0usize;
        for &v in vars {
            let name = match self.terms.get(v) {
                ay_core::TermData::Var(n, _) => n.clone(),
                _ => String::new(),
            };
            match w.iter().find(|(k, _)| *k == name) {
                Some((_, q)) => model.push((v, q.clone())),
                None => uncovered += 1,
            }
        }
        // Printed on the witness gate alone, NOT behind `--nra-diag`: the full
        // trace is far too loud to run over a whole division, and this report
        // has to be collectable per file.
        if uncovered > 0 {
            eprintln!("NRA-WIT skip uncovered={uncovered}/{}", vars.len());
            return;
        }
        // Exact evaluation. On a DEGENERATE (point) box interval arithmetic is
        // exact, so `constraint_is_infeasible` here decides rather than bounds.
        let mut pbox: VarBox = VarBox::default();
        for (v, q) in &model {
            pbox.insert(*v, Interval::point(q.clone()));
        }
        let sat_cons = constraints
            .iter()
            .all(|c| match eval_poly_interval(&c.poly, &pbox) {
                Some(iv) => !constraint_is_infeasible(c.rel, &iv),
                None => false,
            });
        // The full atom-level gate, when every atom parsed into the fragment.
        let sat_atoms = all_parsed && self.verify_model(&model);
        let membership = |bx: &VarBox| -> (usize, String) {
            let mut n_out = 0usize;
            let mut detail = String::new();
            for (v, q) in &model {
                if bx.get(v).map(|iv| interval_contains(iv, q)) == Some(true) {
                    continue;
                }
                n_out += 1;
                detail.push_str(&format!("[{q} OUT OF {}] ", self.diag_box(&[*v], bx)));
            }
            (n_out, detail)
        };
        let (pre_out, pre_detail) = membership(pre);
        let (post_out, post_detail) = membership(post);
        eprintln!(
            "NRA-WIT vars={} cons={} sat_cons={} sat_atoms={} all_parsed={} refuted={} \
             pre_out={}/{} post_out={}/{} PRE {}POST {}",
            vars.len(),
            constraints.len(),
            u8::from(sat_cons),
            u8::from(sat_atoms),
            u8::from(all_parsed),
            u8::from(refuted),
            pre_out,
            model.len(),
            post_out,
            model.len(),
            pre_detail,
            post_detail
        );
    }

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
        diag!(
            "NRA-CALL asserted={} parsed_cons={} all_parsed={}",
            self.asserted.len(),
            constraints.len(),
            all_parsed
        );
        if constraints.is_empty() || constraints.len() > MAX_ICP_CONSTRAINTS {
            diag!("NRA-DIAG exit=CONSTRAINT_GATE cons={}", constraints.len());
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
        diag!(
            "NRA-DIAG entry vars={} cons={} all_parsed={}",
            vars.len(),
            constraints.len(),
            all_parsed
        );
        if vars.len() < 2 || vars.len() > MAX_ICP_VARS {
            diag!("NRA-DIAG exit=VAR_CAP vars={}", vars.len());
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
        // DIAGNOSTIC ONLY (`--nra-witness`): snapshot the pre-contraction hull
        // so the report below can attribute an excluded witness coordinate to
        // the INITIAL bounds or to CONTRACTION. The clone is paid only when the
        // env var is set; with it unset this is a null pointer check.
        let diag_pre = if diag_witness().is_empty() {
            None
        } else {
            Some(root.clone())
        };
        let refuted = matches!(
            contract_box(&constraints, &vars, &mut root),
            Contraction::Refuted
        );
        if let Some(pre) = &diag_pre {
            self.diag_witness_report(&constraints, &vars, pre, &root, refuted, all_parsed);
        }
        if refuted {
            return UniResult::Unsat;
        }
        let eq_count = constraints
            .iter()
            .filter(|c| matches!(c.rel, Rel::Eq))
            .count();
        diag!(
            "NRA-DIAG root eq={} vars={} box: {}",
            eq_count,
            vars.len(),
            self.diag_box(&vars, &root)
        );
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
        //
        //    The cutoff was 4, which is BELOW the dimension of most QF_NRA
        //    meti-tarski instances (3-5 Skolem constants), so the give-up was
        //    firing on ordinary small systems rather than on the dense
        //    high-dimensional pose clusters it was written for. 10 keeps the
        //    ASME shape out of the tree while letting the small systems use it;
        //    measured, this converted 1 of the 69 and cost no wall time.
        const PURE_INEQ_LOW_DIM: usize = 10;
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
            if all_parsed {
                for k in 0..PIN_VALUE_LADDER {
                    if let Some(model) = ladder_vector(&vars, &root, k) {
                        if self.verify_model(&model) {
                            return UniResult::Sat(model);
                        }
                    }
                }
            }
            diag!("NRA-DIAG exit=PURE_INEQ_HIGH_DIM vars={}", vars.len());
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
        //
        // Every system gets the same budget. Non-square systems used to get
        // `MAX_BOXES / 8`, on the argument that the pinned search above had
        // already taken their SAT side, leaving the tree useful to them only for
        // quick exhaustive refutations. That mis-sizes the penalty for this
        // division: UNDERDETERMINED is the NORMAL shape of meti-tarski, so the
        // divisor fired on the majority of QF_NRA rather than on a special case,
        // and the pinned search it leans on returns `None` outright when there is
        // no equality subsystem to match against.
        //
        // MEASURED TRADE, on the 310 MV QF_NRA misses at 300 s: removing the
        // divisor converts 4 more (23 -> 27) and costs exactly one previously
        // solved file, `polypaver/bench-sqrt-3d/...-chunk-0504`, which the
        // divisor solves in 231 s and the wider tree misses even at 600 s — the
        // budget it hands the tree is deadline the phase that actually answers
        // that instance no longer gets. Net +3, and the loss is an `unknown`,
        // never a wrong verdict. Restore the divisor to trade those 4 back for
        // that 1 if robustness is preferred to score.
        let budget = MAX_BOXES;
        let tree =
            self.branch_and_prune(&constraints, &vars, root.clone(), all_parsed, false, budget);
        // 8. LAST RESORT, SAT-only: dyadic grid search. Runs ONLY on the
        //    `Unknown` fallthrough, so it can neither change a verdict the tree
        //    reached nor widen the surface on which `Unsat` is claimed.
        diag!(
            "NRA-DIAG tree={} all_parsed={}",
            match &tree {
                UniResult::Sat(_) => "Sat",
                UniResult::SatAlgebraic(_) => "SatAlgebraic",
                UniResult::Unsat => "Unsat",
                UniResult::Unknown => "Unknown",
            },
            all_parsed
        );
        if all_parsed && matches!(tree, UniResult::Unknown) {
            if let Some(res) = self.dyadic_grid_search(&constraints, &vars, &root) {
                return res;
            }
        }
        tree
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
        // Sweep the small-integer ladder over the root box BEFORE the 2^20
        // clamp below. Once `(0, +inf)` becomes `(0, 2^20]` the simplest-
        // rational descent returns ~2^18 rather than the small integer these
        // witnesses actually are, and no bisection budget recovers it: reaching
        // width 1 from 2^20 costs 20 DFS levels. SAT only, gated by the same
        // exact `verify_model` as every other candidate.
        if all_parsed {
            for k in 0..PIN_VALUE_LADDER {
                if let Some(model) = ladder_vector(vars, &root, k) {
                    if self.verify_model(&model) {
                        return UniResult::Sat(model);
                    }
                }
            }
        }
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
                    match nice_point_in_open(iv) {
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
            // SOUNDNESS GATE for the ALGEBRAIC certificate — see
            // [`Self::asserted_fully_parsed`]. Rational results need no gate
            // here: every path that builds one already ran `verify_model`,
            // which walks `self.asserted` itself.
            if matches!(result, UniResult::SatAlgebraic(_)) && !self.asserted_fully_parsed() {
                return None;
            }
            return Some(result);
        }
        None
    }

    /// SOUNDNESS GATE for ALGEBRAIC witnesses: every asserted atom must lie in
    /// the parsed multivariate fragment.
    ///
    /// The `SatAlgebraic` witnesses built by [`Self::krawczyk_certify`] (and its
    /// bivariate helpers) are re-verified by exact Sturm sign determination
    /// against `constraints` — the PARSE of the asserted atoms, which by
    /// construction omits every atom `atom_to_multi` rejected — and nothing
    /// downstream re-validates them (`accept_algebraic_witnesses` in
    /// check_loop.rs only injects them into the model). So if ANY asserted atom
    /// failed to parse, the certificate says nothing about it and `sat` must
    /// not be claimed. The rational paths have no such gap: their
    /// `verify_model` iterates `self.asserted` and fails closed on any atom it
    /// cannot evaluate exactly.
    ///
    /// This is checked HERE, at the single choke point through which every ICP
    /// `SatAlgebraic` flows, rather than at each call site of
    /// [`Self::try_certify_box`]: a caller that omits its `all_parsed` guard
    /// then degrades to a sound `unknown` instead of an unsound `sat`. Cost is
    /// one re-parse of the atom list, paid only on the terminal step where a
    /// certificate is about to be returned.
    fn asserted_fully_parsed(&self) -> bool {
        self.asserted
            .iter()
            .all(|&(atom, value)| self.atom_to_multi(atom, value).is_some())
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
            // Pin-value assignments from the small-integer ladder.
            for attempt in 0..PIN_VALUE_LADDER {
                if attempts >= MAX_PIN_ATTEMPTS {
                    break;
                }
                attempts += 1;
                let mut bx = root.clone();
                let mut ok = true;
                for &v in &pin_vars {
                    let iv = root.get(&v)?;
                    let val = pin_candidate(iv, attempt);
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

    /// SAT-only DYADIC GRID SEARCH: assign each variable a SMALL DYADIC value
    /// INDEPENDENTLY, contracting after every assignment so an infeasible
    /// prefix is cut before its subtree is enumerated.
    ///
    /// WHY THIS SHAPE, MEASURED. Every candidate the ICP proposes today is
    /// DIAGONAL: [`ladder_vector`] and [`Self::pinned_sat_search`] both evaluate
    /// `pin_candidate(iv, k)` at ONE rung `k` for EVERY variable at once, so the
    /// vectors they can even name are `(v, v, …, v)` — a one-dimensional curve
    /// through the search space. On the 161 MV QF_NRA files that have a rational
    /// witness AY's own exact gate ACCEPTS, z3's witness is MIXED across
    /// coordinates in 158 — e.g. `(-1/2, -3/4, 1)`, `(0, 1, -1, 1)`,
    /// `(2, 1, 1/8, 1)`. The diagonal can never name any of them. It is not a
    /// budget problem and not a representation problem: the values are all
    /// individually on the existing ladder, only never in combination.
    /// Of the 85 such files small enough for this phase, 47 have EVERY witness
    /// coordinate on the `k/4, |k| ≤ 4` grid and 55 on `k/8`.
    ///
    /// Cost is controlled by ITERATIVE DEEPENING over grid resolution (integers,
    /// then halves, then quarters, then eighths) under a shared node budget, so
    /// the coarse grid — where most of these witnesses live — is always swept
    /// even when the fine grid cannot be afforded.
    ///
    /// SOUNDNESS. This only PROPOSES points. `sat` is claimed solely through
    /// [`crate::NraSolver::verify_model`], exact substitution into every asserted
    /// atom, and the phase returns `None` on failure. It never returns `Unsat`,
    /// never enlarges a box budget, and runs ONLY where the tree already returned
    /// `Unknown` — so the set of inputs on which an exhaustive refutation can be
    /// claimed is bit-for-bit unchanged.
    fn dyadic_grid_search(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        root: &VarBox,
    ) -> Option<UniResult> {
        if vars.len() > GRID_MAX_VARS {
            diag!("NRA-GRID declined vars={} > {}", vars.len(), GRID_MAX_VARS);
            return None;
        }
        diag!(
            "NRA-GRID enter vars={} budget={} box: {}",
            vars.len(),
            self.grid_budget.get(),
            self.diag_box(vars, root)
        );
        // Most-constrained-first: a narrow interval admits few grid values, so
        // ordering it early makes the tree bushy at the bottom, not the top.
        let mut order: Vec<TermId> = vars.to_vec();
        order.sort_by(|a, b| {
            let wa = root.get(a).and_then(interval_width);
            let wb = root.get(b).and_then(interval_width);
            match (wa, wb) {
                (Some(x), Some(y)) => x.cmp(&y),
                (Some(_), None) => std::cmp::Ordering::Less,
                (None, Some(_)) => std::cmp::Ordering::Greater,
                (None, None) => std::cmp::Ordering::Equal,
            }
        });
        // DIAGNOSTIC ONLY (`--nra-grid-probe`): arm the enumeration probe for
        // this call. `probe_install` is a no-op unless the env variable is set
        // AND `--nra-witness` names every variable of this call.
        let armed = self.probe_install(&order);
        let mut budget = GRID_MAX_NODES.min(self.grid_budget.get());
        let start = budget;
        let mut out = None;
        // PASS 1: the cheap sweep, bit-for-bit as on `bee086d0a`. `exact` is
        // disabled, so `grid_dfs` never enters [`Self::solve_last_coordinate`]
        // and `budget` is spent on exactly the nodes it was spent on before.
        let pass1 = ExactState::disabled();
        for level in 0..=GRID_MAX_LEVEL {
            probe(|p| p.level_reset(level));
            let grid = dyadic_grid(level);
            let search = GridSearch {
                constraints,
                vars,
                order: &order,
                grid,
                exact: &pass1,
            };
            out = self.grid_dfs(&search, 0, root.clone(), &mut budget);
            if out.is_some() || budget == 0 {
                break; // found, or no room for a finer grid
            }
        }
        self.grid_budget
            .set(self.grid_budget.get() - (start - budget));
        // PASS 2, ONLY on outright failure: re-sweep, SOLVING the last free
        // coordinate instead of drawing it from the alphabet.
        //
        // MEASURED WORTH, on `bee086d0a` vs this file, `-T:60`, jobs 2+2, every
        // model re-validated against z3 5.0.0.
        //   * MV QF_NRA 2026, all 936: **658 -> 659**, +1 and no loss. The
        //     conversion is `meti-tarski/atan/problem/2/weak/
        //     atan-problem-2-weak-chunk-0189`, re-checked SERIALLY 3/3: HEAD
        //     `unknown` at the 62 s cap every time, here `sat` in 5.2 s with a
        //     complete four-function model every time. Its witness is
        //     `skoS = root-obj(64x^2-1105, 2)` — sqrt(1105)/8 — produced through
        //     the algebraic branch of [`Self::solve_last_coordinate`] and
        //     z3-VALID. One file also flipped the other way in the parallel
        //     sweep (`meti-tarski/cbrt/3/weak/cbrt-problem-3-weak-chunk-0086`);
        //     serially it is a deadline coin-flip that behaves IDENTICALLY on
        //     both binaries (`sat` 2 of 3 runs either side), so it is noise, not
        //     a regression.
        //   * 360 QF_NRA files drawn independently OUTSIDE both the 2025 and
        //     2026 MV selections (0% contamination, verified): sat 70 -> 70,
        //     unsat 177 -> 177 — the identical sets, no flip in either
        //     direction — 70/70 models z3-VALID, total wall +1.4%.
        //   * 320 further out-of-pool files drawn from `meti-tarski/atan/
        //     problem/**`, the family the conversions live in (0% contamination,
        //     verified): **102 -> 104**, +2 and no loss, unsat 158 -> 158
        //     unchanged, 104/104 models z3-VALID, total wall -3.4%. The gains are
        //     `atan-problem-2-weak-chunk-0135` (`unknown` at the 62 s cap ->
        //     `sat` in 5.1 s) and `-0196` (`unknown` in 5.0 s -> `sat` in 5.1 s,
        //     i.e. a conversion that costs nothing at all — HEAD was not timing
        //     out there, it was giving up). Both 3/3 serially.
        //
        // So the capability generalizes, but WITHIN A FAMILY: all three known
        // conversions are `meti-tarski/atan/problem/*/weak` and all three run
        // through the algebraic branch on the SAME minimal polynomial shape.
        //
        // An earlier revision of this comment read "MEASURED WORTH ON MV QF_NRA
        // 2026: ZERO FILES ... Do not re-derive this." That was a real
        // measurement of an EARLIER, unbounded cut of this pass, generalized
        // into a claim about the mechanism. Both halves are now falsified: the
        // pass converts a file in the MV selection itself, and it converts
        // `atan-problem-2-weak-chunk-0135` out of pool through the same channel.
        //
        // WHAT IS ACTUALLY LIMITED, stated at the scope it was measured: the
        // conversion RATE is low and family-specific — 0 of 360 on a uniform
        // out-of-pool draw, 2 of 320 when the draw is aimed at the right family,
        // 1 of 936 on MV. Much of the residual is gated UPSTREAM of the geometry:
        // for 6 of the 22 residual files whose witness can be checked against the
        // boxes, z3's witness lies OUTSIDE every root box any theory call
        // constructs, i.e. in Boolean branches DPLL never hands to the theory.
        // No alphabet, budget, or last-coordinate work here can reach those.
        //
        // WHY A SECOND PASS RATHER THAN INLINE. Measured: solving the last
        // coordinate inline, at every prefix, costs more than it earns —
        // `20220314-Uncu/.../DDC_ProveIneq_ISSAC10_ex1e` and `_ex2c` are `sat`
        // in 12.5 s and 21 s from the alphabet and time out at 30 s once every
        // failing prefix first pays a Sturm-sequence univariate decision. The
        // exact solve must therefore never sit in front of a path that already
        // works. As a second pass it cannot: pass 1 is unchanged in work, order,
        // and result, so every file the grid solves today it still solves, at the
        // same cost, and the exact machinery is only ever paid for by files that
        // were `unknown` anyway.
        //
        // WHY ITS OWN BUDGET. Pass 1's spend is settled into `grid_budget` ABOVE,
        // and pass 2 draws from `grid_exact_budget` instead. When the two shared
        // one counter, pass 2's re-sweep billed pass 1's interior nodes a second
        // time and added 64 per exact decision, and the deficit landed on a LATER
        // theory call's pass 1 — `polypaver-bench-sqrt-3d-chunk-0437` burned
        // 19,278 of 20,000 nodes this way and went from `sat` at 51.0 s to
        // `unknown` at the 60 s cap.
        if out.is_none() {
            let mut ebudget = GRID_EXACT_MAX_NODES.min(self.grid_exact_budget.get());
            let estart = ebudget;
            let pass2 = ExactState::with(GRID_EXACT_SOLVES);
            for level in 0..=GRID_MAX_LEVEL {
                if ebudget < GRID_EXACT_NODE_COST || !pass2.available() {
                    break;
                }
                probe(|p| p.level_reset(GRID_MAX_LEVEL + 1 + level));
                let grid = dyadic_grid(level);
                let search = GridSearch {
                    constraints,
                    vars,
                    order: &order,
                    grid,
                    exact: &pass2,
                };
                out = self.grid_dfs(&search, 0, root.clone(), &mut ebudget);
                if out.is_some() {
                    break;
                }
            }
            self.grid_exact_budget
                .set(self.grid_exact_budget.get() - (estart - ebudget));
            diag!(
                "NRA-GRID pass2 found={} exact_nodes={} exact_left={}",
                out.is_some(),
                estart - ebudget,
                self.grid_exact_budget.get()
            );
        }
        diag!(
            "NRA-GRID exit found={} nodes_used={} budget_left={}",
            out.is_some(),
            start - budget,
            budget
        );
        if armed {
            self.probe_report(out.is_some(), start - budget, budget);
        }
        out
    }

    /// DIAGNOSTIC ONLY (`--nra-grid-probe`): arm [`GridProbe`] for this call.
    ///
    /// Returns `false`, having installed nothing, unless the probe is enabled
    /// and `--nra-witness` supplies a value for EVERY variable of this call —
    /// a partial witness cannot answer "how many coordinates were correct".
    fn probe_install(&self, order: &[TermId]) -> bool {
        if !grid_probe_on() {
            return false;
        }
        let w = diag_witness();
        let mut wit = Vec::with_capacity(order.len());
        let mut names = Vec::with_capacity(order.len());
        for &v in order {
            let name = match self.terms.get(v) {
                ay_core::TermData::Var(n, _) => n.clone(),
                _ => return false,
            };
            match w.iter().find(|(k, _)| *k == name) {
                Some((_, q)) => wit.push(q.clone()),
                None => return false,
            }
            names.push(name);
        }
        let p = GridProbe {
            wit,
            names,
            correct: std::cell::RefCell::new(vec![false; order.len()]),
            absent_at: std::cell::Cell::new(-1),
            refuted_at: std::cell::Cell::new(-1),
            per_level: std::cell::RefCell::new(vec![0; 2 * (GRID_MAX_LEVEL + 1) + 2]),
            ..GridProbe::default()
        };
        GRID_PROBE.with(|slot| *slot.borrow_mut() = Some(p));
        true
    }

    /// DIAGNOSTIC ONLY (`--nra-grid-probe`): print and disarm.
    fn probe_report(&self, found: bool, nodes_used: usize, budget_left: usize) {
        let line = probe(|p| {
            let per: Vec<String> = p
                .per_level
                .borrow()
                .iter()
                .enumerate()
                .filter(|(_, n)| **n > 0)
                .map(|(l, n)| {
                    if l > GRID_MAX_LEVEL {
                        format!("p2L{}:{n}", l - GRID_MAX_LEVEL - 1)
                    } else {
                        format!("L{l}:{n}")
                    }
                })
                .collect();
            let cands: Vec<String> = p
                .cand_idx
                .borrow()
                .iter()
                .map(|(d, i, n, inb)| format!("d{d}:{i}/{n}{}", if *inb { "I" } else { "X" }))
                .collect();
            format!(
                "NRA-GRIDPROBE found={found} nvars={} nodes={} budget_used={nodes_used} \
                 budget_left={budget_left} starved={} max_depth={} MAX_PREFIX={}/{} \
                 last_level={} LVL_PREFIX={} absent_at={} refuted_at={} \
                 per_level=[{}] cand_at_prefix=[{}] order={} ABSENT_DETAIL<<{}>>",
                p.wit.len(),
                p.nodes.get(),
                p.starved.get(),
                p.max_depth.get(),
                p.max_prefix.get(),
                p.wit.len(),
                p.level.get(),
                p.lvl_prefix.get(),
                p.absent_at.get(),
                p.refuted_at.get(),
                per.join(","),
                cands.join(","),
                p.names.join(">"),
                p.absent_detail.borrow()
            )
        });
        if let Some(l) = line {
            eprintln!("{l}");
        }
        GRID_PROBE.with(|slot| *slot.borrow_mut() = None);
    }

    /// Decide the LAST free coordinate `v` of a grid prefix EXACTLY.
    ///
    /// Every variable other than `v` is a point interval in `bx`, so
    /// substituting those points reduces each constraint to a univariate
    /// polynomial in `v`. `v`'s own box interval is added as up to two linear
    /// constraints so the answer stays inside the contracted region the prefix
    /// earned. [`decide_single_variable`] then decides that conjunction exactly.
    ///
    /// Returns [`ExactOutcome::Model`] carrying a FULL model —
    /// [`UniResult::Sat`] when the solved coordinate is rational,
    /// [`UniResult::SatAlgebraic`] when the feasible set for `v` contains no
    /// rational at all — already re-verified against every parsed constraint.
    ///
    /// [`ExactOutcome::Empty`] means this PREFIX is provably infeasible; it is
    /// reported so the caller can count the streak, and is never acted on as a
    /// refutation of anything larger. [`ExactOutcome::Declined`] carries no
    /// information at all. On either, the caller falls through to its ordinary
    /// enumeration.
    fn solve_last_coordinate(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        v: TermId,
        iv: &Interval,
        bx: &VarBox,
    ) -> ExactOutcome {
        // Points for every variable except `v`.
        let mut pins: Vec<(TermId, BigRational)> = Vec::with_capacity(vars.len());
        for &u in vars {
            if u == v {
                continue;
            }
            let Some(p) = bx.get(&u).and_then(interval_point) else {
                diag!("NRA-LAST bail=pin-not-point");
                return ExactOutcome::Declined;
            };
            pins.push((u, p.clone()));
        }
        let mut uni: Vec<UniConstraint> = Vec::with_capacity(constraints.len() + 2);
        // The residual system WITHOUT the box bounds: what an algebraic witness
        // must be re-verified against (the box bounds are a search narrowing,
        // the constraints are the specification).
        let mut resid: Vec<(UniPoly, Rel)> = Vec::with_capacity(constraints.len());
        for c in constraints {
            let mut p = c.poly.clone();
            for (u, val) in &pins {
                p = substitute_point(&p, *u, val);
            }
            // A constant residual is already settled by the prefix: if it is
            // violated the prefix is dead, otherwise it constrains nothing.
            let Some(poly) = p.to_unipoly() else {
                diag!(
                    "NRA-LAST bail=not-univariate vars={:?}",
                    p.variables().len()
                );
                return ExactOutcome::Declined;
            };
            if poly.degree() == Some(0) || poly.is_zero() {
                let k = poly
                    .coeffs()
                    .first()
                    .cloned()
                    .unwrap_or_else(BigRational::zero);
                if !c.rel.holds_for_sign(rational_sign(&k)) {
                    // The prefix ALONE violates this constraint: infeasible
                    // without needing the univariate decision at all.
                    return ExactOutcome::Empty;
                }
                continue;
            }
            resid.push((poly.clone(), c.rel));
            uni.push(UniConstraint { poly, rel: c.rel });
        }
        // Keep the answer inside `v`'s contracted interval. Closed bounds are a
        // sound narrowing here: the point is re-verified against the original
        // atoms regardless, and a strict original bound is still enforced by
        // the atom it came from.
        if let Endpoint::Finite(lo, _) = &iv.lo {
            // v - lo >= 0
            let mut p = UniPoly::x();
            p = p.sub(&UniPoly::constant(lo.clone()));
            uni.push(UniConstraint {
                poly: p,
                rel: Rel::Ge,
            });
        }
        if let Endpoint::Finite(hi, _) = &iv.hi {
            // hi - v >= 0
            let p = UniPoly::constant(hi.clone()).sub(&UniPoly::x());
            uni.push(UniConstraint {
                poly: p,
                rel: Rel::Ge,
            });
        }
        if uni.is_empty() {
            return ExactOutcome::Declined;
        }
        match decide_single_variable(&uni) {
            SingleVarResult::Witness(w) => {
                diag!("NRA-LAST witness={w}");
                let mut model: Vec<(TermId, BigRational)> = Vec::with_capacity(vars.len());
                for &u in vars {
                    if u == v {
                        model.push((u, w.clone()));
                    } else {
                        let Some(p) = bx.get(&u).and_then(interval_point) else {
                            return ExactOutcome::Declined;
                        };
                        model.push((u, p.clone()));
                    }
                }
                // Same exact gate as every other ICP candidate.
                if self.verify_model(&model) {
                    ExactOutcome::Model(UniResult::Sat(model))
                } else {
                    ExactOutcome::Declined
                }
            }
            // The feasible set for `v` under this prefix is NON-EMPTY but
            // contains no rational. That is precisely the shape the campaign
            // wrote off as needing "an algebraic sample point" — and here it
            // costs nothing extra: `decide_single_variable` has already
            // certified the feasible cell exactly and carries z3 `root-obj`
            // data for it. Emit it as a mixed rational/algebraic model.
            //
            // VERIFICATION is exact and total, not a weakening: every parsed
            // constraint is reduced to a univariate polynomial in `v` by the
            // same substitution used above, and its sign AT the algebraic point
            // is decided by Sturm sequences (`sign_of_poly`). Any constraint
            // whose sign cannot be decided, or that fails, declines. The caller
            // only reaches this phase with `all_parsed`, so "every parsed
            // constraint" is every asserted atom.
            SingleVarResult::IrrationalSat(alg) => {
                for (poly, rel) in &resid {
                    let Some(sign) = alg.sign_of_poly(poly) else {
                        return ExactOutcome::Declined;
                    };
                    if !rel.holds_for_sign(sign) {
                        return ExactOutcome::Declined;
                    }
                }
                diag!("NRA-LAST algebraic-witness");
                let mut witnesses: Vec<(TermId, UniWitness)> = Vec::with_capacity(vars.len());
                for &u in vars {
                    if u == v {
                        witnesses.push((u, UniWitness::Algebraic(alg.as_value())));
                    } else {
                        let Some(p) = bx.get(&u).and_then(interval_point) else {
                            return ExactOutcome::Declined;
                        };
                        witnesses.push((u, UniWitness::Rational(p.clone())));
                    }
                }
                ExactOutcome::Model(UniResult::SatAlgebraic(witnesses))
            }
            res => {
                let empty = matches!(res, SingleVarResult::Empty);
                diag!(
                    "NRA-LAST bail=decide pins={:?} n_uni={} kind={}",
                    pins.iter().map(|(_, q)| q.to_string()).collect::<Vec<_>>(),
                    uni.len(),
                    if empty { "Empty" } else { "Unknown" }
                );
                if empty {
                    ExactOutcome::Empty
                } else {
                    ExactOutcome::Declined
                }
            }
        }
    }

    /// One level of [`Self::dyadic_grid_search`]: pin `order[depth]`, contract,
    /// recurse. `budget` is decremented per contracted node and stops the sweep.
    fn grid_dfs(
        &self,
        search: &GridSearch<'_>,
        depth: usize,
        bx: VarBox,
        budget: &mut usize,
    ) -> Option<UniResult> {
        // Pass 2 with nothing left to spend has no work of its own remaining;
        // continuing would re-walk pass 1's tree on pass 2's budget.
        if search.exact.spent() {
            return None;
        }
        if depth == search.order.len() {
            // Every variable is a point interval; assemble and verify EXACTLY.
            let mut model = Vec::with_capacity(search.vars.len());
            for &v in search.vars {
                model.push((v, bx.get(&v).and_then(interval_point)?.clone()));
            }
            return self.verify_model(&model).then_some(UniResult::Sat(model));
        }
        let v = search.order[depth];
        let iv = bx.get(&v)?.clone();
        // Already collapsed by contraction: nothing to choose here.
        if let Some(p) = interval_point(&iv) {
            probe(|pr| pr.pin(depth, p));
            return self.grid_dfs(search, depth + 1, bx, budget);
        }
        // LAST FREE COORDINATE: SOLVE it, do not guess it.
        //
        // WHY, MEASURED. Once every other variable is a point, the residual
        // system in `v` is UNIVARIATE — exactly the fragment
        // [`decide_single_variable`] decides exactly, by square-free
        // decomposition and Sturm root isolation. The grid was instead picking
        // `v` from the same fixed alphabet as every other coordinate, so a
        // prefix that IS on the solution manifold still failed whenever the
        // matching last value was not a small dyadic.
        //
        // `meti-tarski/atan/vega/3/atan-vega-3-chunk-0544` is the whole story
        // in one file: 3 variables, z3's witness `(skoY 0, skoX -1/2,
        // skoZ 1/32)`. The grid REACHES the prefix `(0, -1/2)` at level 1 and
        // contraction does not refute it — assert those two pins into the
        // benchmark and AY answers `sat` with `skoZ = 1/52` immediately. But
        // `skoZ`'s contracted interval is unbounded above, so its midpoint does
        // not exist, its simplest rational is not feasible, and the alphabet
        // `{k/8, |k| <= 4}` contains no feasible point: the search had the
        // right prefix and threw it away. This is not a budget problem — that
        // file's whole four-level sweep spends 161 of 20000 nodes.
        //
        // SOUNDNESS. Unchanged, on both sides. A witness is a PROPOSAL: a
        // rational one passes through the same exact [`Self::verify_model`]
        // gate, an algebraic one through exact Sturm sign determination against
        // every parsed constraint. `Empty` and `Unknown` fall through rather
        // than pruning, so no branch is cut on this evidence and the phase still
        // cannot return `Unsat`.
        //
        // COST. Bounded three ways, because an unbounded run of these is what
        // made the first cut of this feature a net loss: [`ExactState`]'s
        // per-call decision count, its consecutive-`Empty` cut
        // ([`GRID_EXACT_EMPTY_STREAK`]), and the pass-2 node budget this charges
        // [`GRID_EXACT_NODE_COST`] against.
        if search.exact.pass2 && depth + 1 == search.order.len() {
            // Pass 1 already swept this node's alphabet and failed, so pass 2
            // either improves on it with an exact solve or has nothing to add.
            // Either way it must not re-enumerate.
            if !search.exact.available() || *budget < GRID_EXACT_NODE_COST {
                return None;
            }
            *budget -= GRID_EXACT_NODE_COST;
            diag!("NRA-LAST enter depth={depth}");
            let outcome = self.solve_last_coordinate(search.constraints, search.vars, v, &iv, &bx);
            search.exact.charge(&outcome);
            if let ExactOutcome::Model(m) = outcome {
                return Some(m);
            }
            return None;
        }
        // Candidates: the interval's own simplest rational and midpoint first
        // (these carry the tight numeric-constant intervals — `pi` bounded to
        // `26353589/8388608` and friends — that no fixed grid contains), then
        // the grid values that lie inside.
        let mut cands: Vec<BigRational> = Vec::with_capacity(search.grid.len() + 2);
        for c in [nice_point_in_open(&iv), interval_midpoint(&iv)]
            .into_iter()
            .flatten()
        {
            if interval_contains(&iv, &c) && !cands.contains(&c) {
                cands.push(c);
            }
        }
        for g in search.grid {
            if interval_contains(&iv, g) && !cands.contains(g) {
                cands.push(g.clone());
            }
        }
        // The fixed alphabet reached this coordinate barely or not at all.
        // Give it a branching factor at its own scale — see [`GRID_MIN_BRANCH`]
        // for the measurement that says this is where the sweep dies and that
        // the budget to pay for it is sitting unused.
        //
        // APPENDED, never interleaved: every candidate the sweep tries today it
        // still tries, at the same node, in the same order, before any of these.
        if cands.len() < GRID_MIN_BRANCH {
            for c in interval_scale_points(&iv, GRID_MIN_BRANCH - cands.len()) {
                if !cands.contains(&c) {
                    cands.push(c);
                }
            }
        }
        diag!(
            "NRA-CAND depth={depth} iv=[{:?},{:?}] cands={:?}",
            &iv.lo,
            &iv.hi,
            cands.iter().map(|q| q.to_string()).collect::<Vec<_>>()
        );
        // DIAGNOSTIC ONLY: on an all-correct prefix, where does the witness's
        // own value for this coordinate sit in the list we are about to walk?
        probe(|p| p.note_cands(depth, &cands, &iv));
        for c in cands {
            if *budget == 0 {
                probe(|p| p.starved.set(true));
                return None;
            }
            *budget -= 1;
            probe(|p| p.pick(depth, &c));
            let mut next = bx.clone();
            next.insert(v, Interval::point(c));
            if matches!(
                contract_box(search.constraints, search.vars, &mut next),
                Contraction::Refuted
            ) {
                probe(|p| p.note_refuted(depth));
                continue; // prefix PROVABLY infeasible — cut the whole subtree
            }
            if let Some(m) = self.grid_dfs(search, depth + 1, next, budget) {
                return Some(m);
            }
        }
        None
    }
}

/// Small dyadic values `k / 2^level` with `|k / 2^level| <= 4`, ordered by
/// magnitude (positive before negative), coarsest first and without repeats
/// across levels — the alphabet [`NraSolver::dyadic_grid_search`] draws from.
fn dyadic_grid(level: usize) -> &'static [BigRational] {
    static GRIDS: std::sync::OnceLock<Vec<Vec<BigRational>>> = std::sync::OnceLock::new();
    &GRIDS.get_or_init(|| {
        let mut out: Vec<Vec<BigRational>> = Vec::new();
        let mut acc: Vec<BigRational> = Vec::new();
        for level in 0..=GRID_MAX_LEVEL {
            let den = BigInt::one() << level;
            let cap = (GRID_ABS_CAP as i64) << level;
            let mut fresh: Vec<BigRational> = Vec::new();
            for k in -cap..=cap {
                let q = BigRational::new(BigInt::from(k), den.clone());
                if !acc.contains(&q) && !fresh.contains(&q) {
                    fresh.push(q);
                }
            }
            fresh.sort_by(|a, b| {
                let (aa, ba) = (a.abs(), b.abs());
                aa.cmp(&ba).then_with(|| b.cmp(a))
            });
            acc.extend(fresh);
            out.push(acc.clone());
        }
        out
    })[level.min(GRID_MAX_LEVEL)]
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

    /// [`interval_scale_points`] must produce points that are IN the interval,
    /// dyadic, distinct, spread, and bounded in denominator — and must decline
    /// rather than guess where there is no scale to work at.
    #[test]
    /// A WIDE interval must cost the same as a narrow one.
    ///
    /// Regression for the `k == 0` blow-up: the original implementation
    /// materialised every multiple of `2^-k` strictly inside the interval, which
    /// is linear in WIDTH, and `k == 0` is taken for every finite interval wider
    /// than `want + 1`. Measured on that version: width 1e9 took **347 seconds in
    /// a single call** — one DFS node alone over a 300s competition cap.
    ///
    /// It survived review because the only wide case tested was `[-3, 7]` (nine
    /// iterations). This asserts the real thing: a 1e9-wide interval returns
    /// promptly and still yields `want` in-interval values.
    #[test]
    fn interval_scale_points_is_flat_in_interval_width() {
        let iv = Interval {
            lo: Endpoint::Finite(rat(10), false),
            hi: Endpoint::Finite(rat(1_000_000_000), false),
        };
        let t0 = std::time::Instant::now();
        let pts = interval_scale_points(&iv, 5);
        let elapsed = t0.elapsed();
        assert!(
            elapsed < std::time::Duration::from_secs(1),
            "interval_scale_points took {elapsed:?} on a 1e9-wide interval — the \
             O(width) materialisation is back"
        );
        assert!(!pts.is_empty(), "should still produce candidates");
        assert!(pts.len() <= 5, "must not exceed `want`");
        for q in &pts {
            assert!(
                interval_contains(&iv, q),
                "candidate {q} outside the interval"
            );
        }
    }

    fn interval_scale_points_reach_where_the_fixed_alphabet_cannot() {
        let iv = |l: BigRational, h: BigRational| Interval {
            lo: Endpoint::Finite(l, false),
            hi: Endpoint::Finite(h, false),
        };
        // The shape the probe found: a contracted interval near pi/2 that
        // contains NO value of `dyadic_grid(3)` — every one of its 65 values is
        // a multiple of 1/8 with magnitude <= 4, and none lands in this window.
        let narrow = iv(ratfrac(15703, 10000), ratfrac(15709, 10000));
        assert!(
            dyadic_grid(GRID_MAX_LEVEL)
                .iter()
                .all(|g| !interval_contains(&narrow, g)),
            "the fixed alphabet is supposed to miss this interval entirely"
        );
        let pts = interval_scale_points(&narrow, GRID_MIN_BRANCH);
        assert_eq!(pts.len(), GRID_MIN_BRANCH);
        for p in &pts {
            assert!(interval_contains(&narrow, p), "{p} escaped the interval");
            let d = p.denom();
            assert!(
                d == &(BigInt::one() << (d.bits() as usize - 1)),
                "{p} is not dyadic — the denominator bound is the point"
            );
            assert!(p.denom().bits() as usize <= GRID_SCALE_MAX_BITS + 1);
        }
        for i in 1..pts.len() {
            assert!(pts[i - 1] != pts[i], "duplicate candidate {}", pts[i]);
        }
        // Spread, not clustered against the lower endpoint.
        assert!(pts.iter().max() > pts.iter().min());
        // A wide interval: still bounded, still inside, and small denominators.
        let wide = iv(rat(-3), rat(7));
        let w = interval_scale_points(&wide, GRID_MIN_BRANCH);
        assert_eq!(w.len(), GRID_MIN_BRANCH);
        assert!(w.iter().all(|p| interval_contains(&wide, p)));
        // Unbounded on either side: no scale exists, so no points, never a panic.
        assert!(interval_scale_points(
            &Interval {
                lo: Endpoint::Finite(rat(0), false),
                hi: Endpoint::PosInf
            },
            GRID_MIN_BRANCH
        )
        .is_empty());
        assert!(interval_scale_points(&Interval::whole(), GRID_MIN_BRANCH).is_empty());
        // Degenerate and empty requests decline.
        assert!(interval_scale_points(&iv(rat(1), rat(1)), GRID_MIN_BRANCH).is_empty());
        assert!(interval_scale_points(&wide, 0).is_empty());
        // Narrower than the scale cap: declines instead of building a
        // 2^GRID_SCALE_MAX_BITS-denominator candidate nobody can evaluate cheaply.
        let hair = iv(
            BigRational::new(BigInt::one(), BigInt::one() << 80u32),
            BigRational::new(BigInt::from(3), BigInt::one() << 80u32),
        );
        assert!(interval_scale_points(&hair, GRID_MIN_BRANCH).is_empty());
    }

    #[test]
    fn nice_point_in_open_handles_unbounded_sides() {
        // `(0, +inf)` — the meti-tarski Skolem shape. `nice_point_in` gives up.
        let half_open = Interval {
            lo: Endpoint::Finite(rat(0), false),
            hi: Endpoint::PosInf,
        };
        assert_eq!(nice_point_in(&half_open), None);
        assert_eq!(nice_point_in_open(&half_open), Some(rat(1)));
        // `[0, +inf)` — the SOUND relaxation of the same strict bound. The
        // simplest rational IS 0 here, which is why the ladder must offer more.
        let half_closed = Interval {
            lo: Endpoint::Finite(rat(0), true),
            hi: Endpoint::PosInf,
        };
        assert_eq!(nice_point_in_open(&half_closed), Some(rat(0)));
        assert_eq!(pin_candidate(&half_closed, 1), Some(rat(1)));
        assert_eq!(pin_candidate(&half_closed, 2), None); // -1 is outside

        // `(-inf, hi]` mirrors, and the doubly-unbounded interval yields 0.
        let below = Interval {
            lo: Endpoint::NegInf,
            hi: Endpoint::Finite(rat(-5), false),
        };
        assert_eq!(nice_point_in_open(&below), Some(rat(-6)));
        let whole = Interval::whole();
        assert_eq!(nice_point_in_open(&whole), Some(rat(0)));
        // Every proposal lands inside the interval it was asked about.
        for iv in [&half_open, &half_closed, &below, &whole] {
            for k in 0..PIN_VALUE_LADDER {
                if let Some(p) = pin_candidate(iv, k) {
                    assert!(interval_contains(iv, &p), "rung {k} escaped its interval");
                }
            }
        }
    }

    #[test]
    fn pin_ladder_is_not_degenerate_on_a_bounded_interval() {
        // The three-rung ladder collapsed to one value on intervals like this;
        // the replacement must offer several DISTINCT candidates.
        let iv = Interval {
            lo: Endpoint::Finite(rat(0), false),
            hi: Endpoint::Finite(ratfrac(151, 50), false),
        };
        let vals: std::collections::BTreeSet<_> = (0..PIN_VALUE_LADDER)
            .filter_map(|k| pin_candidate(&iv, k))
            .collect();
        assert!(vals.len() >= 4, "ladder collapsed to {vals:?}");
        assert!(vals.contains(&rat(1)) && vals.contains(&rat(2)));
        for p in &vals {
            assert!(interval_contains(&iv, p));
        }
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

    /// An algebraic certificate over only the parsed constraint subset must
    /// not authorize SAT while any asserted atom lies outside that subset.
    #[test]
    fn icp_algebraic_certificate_refuses_unparsed_atoms() {
        use ay_core::term::TermStore;
        use ay_core::Sort;
        use ay_core::TheorySolver;
        let mut terms = TermStore::new();
        let x2 = terms.mk_var("x2", Sort::Real);
        let x3 = terms.mk_var("x3", Sort::Real);
        let y3 = terms.mk_var("y3", Sort::Real);
        let c100 = terms.mk_rational(rat(100));
        let c64 = terms.mk_rational(rat(64));
        let c49 = terms.mk_rational(rat(49));
        let c0 = terms.mk_rational(rat(0));
        let c1000 = terms.mk_rational(rat(1000));
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
        // This division is outside the parsed multivariate fragment and false
        // at the triangle witness (`10 / 5.56` is nowhere near `> 1000`).
        let quot = terms.mk_div(x2, y3);
        let a5 = terms.mk_gt(quot, c1000);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(a1, true);
        solver.assert_literal(a2, true);
        solver.assert_literal(a3, true);
        solver.assert_literal(a4, true);
        solver.assert_literal(a5, true);

        assert!(
            solver.atom_to_multi(a5, true).is_none(),
            "x2 / y3 > 1000 must remain outside the multivariate fragment"
        );
        assert!(
            !solver.asserted_fully_parsed(),
            "the gate must observe the unparsed asserted atom"
        );

        // Build exactly the parsed subset and deliberately emulate a caller
        // that incorrectly claims `all_parsed = true`. The choke-point guard,
        // not caller discipline, must keep the answer fail-closed.
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &solver.asserted {
            if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
                constraints.push(c);
            }
        }
        let mut vars: Vec<TermId> = Vec::new();
        for c in &constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars.sort_unstable_by_key(|t| t.0);
        let mut root: VarBox = collect_variable_bounds(&constraints);
        for &v in &vars {
            root.entry(v).or_insert_with(Interval::whole);
        }
        assert!(
            !matches!(
                contract_box(&constraints, &vars, &mut root),
                Contraction::Refuted
            ),
            "the parsed subset alone is satisfiable"
        );

        let result = solver.branch_and_prune(&constraints, &vars, root, true, false, MAX_BOXES);
        let got = match result {
            UniResult::Sat(_) => "Sat",
            UniResult::SatAlgebraic(_) => "SatAlgebraic",
            UniResult::Unsat => "Unsat",
            UniResult::Unknown => "Unknown",
        };
        assert_eq!(
            got, "Unknown",
            "an algebraic certificate must not ignore an unparsed asserted atom"
        );
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

    #[test]
    fn dyadic_grid_is_cumulative_and_capped() {
        // Level 0 is the integers in [-4, 4], zero first, positive before its
        // negation; each finer level ADDS only the new denominators.
        let l0 = dyadic_grid(0);
        assert_eq!(
            l0.iter().map(|q| q.to_string()).collect::<Vec<_>>(),
            ["0", "1", "-1", "2", "-2", "3", "-3", "4", "-4"]
        );
        for level in 0..GRID_MAX_LEVEL {
            let (a, b) = (dyadic_grid(level), dyadic_grid(level + 1));
            assert_eq!(
                &b[..a.len()],
                a,
                "level {level} must be a prefix of the next"
            );
            assert!(b.len() > a.len(), "level {level} must gain values");
        }
        let fine = dyadic_grid(GRID_MAX_LEVEL);
        let cap = BigRational::from_integer(BigInt::from(GRID_ABS_CAP as i64));
        assert!(
            fine.iter().all(|q| q.abs() <= cap),
            "values stay within the cap"
        );
        assert!(
            fine.iter().all(
                |q| (q * BigRational::from_integer(BigInt::one() << GRID_MAX_LEVEL)).is_integer()
            ),
            "every value is a dyadic with denominator dividing 2^GRID_MAX_LEVEL"
        );
        let mut seen = fine.to_vec();
        seen.sort();
        seen.dedup();
        assert_eq!(seen.len(), fine.len(), "no value repeats across levels");
    }

    #[test]
    fn dyadic_grid_search_finds_a_mixed_coordinate_witness() {
        // `x*y = 2 ∧ x - y > 0 ∧ y > 0` has the witness (2, 1) — MIXED across
        // coordinates, so no single rung of the diagonal `pin_candidate` ladder
        // can name it. The grid must, and the model must verify exactly.
        use ay_core::term::TermStore;
        use ay_core::Sort;
        use ay_core::TheorySolver;
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let c0 = terms.mk_rational(rat(0));
        let c2 = terms.mk_rational(rat(2));
        let xy = terms.mk_mul(vec![x, y]);
        let a1 = terms.mk_eq(xy, c2);
        let diff = terms.mk_sub(vec![x, y]);
        let a2 = terms.mk_gt(diff, c0);
        let a3 = terms.mk_gt(y, c0);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(a1, true);
        solver.assert_literal(a2, true);
        solver.assert_literal(a3, true);

        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &solver.asserted {
            if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
                constraints.push(c);
            }
        }
        let mut vars: Vec<TermId> = Vec::new();
        for c in &constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars.sort_unstable_by_key(|t| t.0);
        let mut root: VarBox = collect_variable_bounds(&constraints);
        for &v in &vars {
            root.entry(v).or_insert_with(Interval::whole);
        }
        assert!(!matches!(
            contract_box(&constraints, &vars, &mut root),
            Contraction::Refuted
        ));
        let res = solver
            .dyadic_grid_search(&constraints, &vars, &root)
            .expect("the grid must find a mixed-coordinate rational witness");
        let UniResult::Sat(model) = res else {
            panic!("this system has a RATIONAL witness; the grid must report it as such");
        };
        assert!(
            solver.verify_model(&model),
            "the witness must pass the exact substitution gate"
        );
        assert_eq!(model.len(), 2);
    }

    /// Build the (constraints, vars, contracted-root) triple the grid takes,
    /// exactly as `try_icp_branch_and_prune` does.
    fn grid_inputs(solver: &NraSolver<'_>) -> (Vec<MultiConstraint>, Vec<TermId>, VarBox) {
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &solver.asserted {
            if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
                constraints.push(c);
            }
        }
        let mut vars: Vec<TermId> = Vec::new();
        for c in &constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars.sort_unstable_by_key(|t| t.0);
        let mut root: VarBox = collect_variable_bounds(&constraints);
        for &v in &vars {
            root.entry(v).or_insert_with(Interval::whole);
        }
        assert!(!matches!(
            contract_box(&constraints, &vars, &mut root),
            Contraction::Refuted
        ));
        (constraints, vars, root)
    }

    /// The grid's SECOND pass must SOLVE the last free coordinate, not guess it.
    ///
    /// `x*y = 1 ∧ x - 100 > 0 ∧ y > 0` forces `y = 1/x` with `x > 100`, so
    /// EVERY witness has `|y| < 1/100`. The grid alphabet is `{k/8, |k| <= 4}`,
    /// whose smallest nonzero magnitude is `1/8`: no combination of alphabet
    /// values can name a witness, and neither can any finer level of the same
    /// bounded grid without an exponential blowup. Solving the residual
    /// univariate system in the last coordinate names one immediately.
    #[test]
    fn grid_solves_a_last_coordinate_the_alphabet_cannot_name() {
        use ay_core::term::TermStore;
        use ay_core::Sort;
        use ay_core::TheorySolver;
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let c0 = terms.mk_rational(rat(0));
        let c1 = terms.mk_rational(rat(1));
        let c100 = terms.mk_rational(rat(100));
        let xy = terms.mk_mul(vec![x, y]);
        let a1 = terms.mk_eq(xy, c1);
        let xm = terms.mk_sub(vec![x, c100]);
        let a2 = terms.mk_gt(xm, c0);
        let a3 = terms.mk_gt(y, c0);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(a1, true);
        solver.assert_literal(a2, true);
        solver.assert_literal(a3, true);
        let (constraints, vars, root) = grid_inputs(&solver);
        let res = solver
            .dyadic_grid_search(&constraints, &vars, &root)
            .expect("the exact last-coordinate pass must find a witness");
        let UniResult::Sat(model) = res else {
            panic!("both coordinates are rational here");
        };
        assert!(solver.verify_model(&model), "exact substitution gate");
        let yv = model
            .iter()
            .find(|(v, _)| *v == y)
            .map(|(_, q)| q.clone())
            .expect("y valued");
        assert!(
            yv > BigRational::zero() && yv < BigRational::new(BigInt::one(), BigInt::from(100)),
            "y must be a genuine off-alphabet value in (0, 1/100), got {yv}"
        );
    }

    /// When the last coordinate's feasible set contains NO rational, the grid
    /// may report the exact algebraic point rather than declining. The rational
    /// coordinates stay rational; only the solved one is algebraic.
    #[test]
    fn grid_reports_an_algebraic_last_coordinate() {
        use ay_core::term::TermStore;
        use ay_core::Sort;
        use ay_core::TheorySolver;
        // `x = 1 ∧ y*y = 2*x ∧ y > 0` ⇒ y = sqrt(2), which is irrational, so
        // no rational assignment satisfies the system at all.
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let c0 = terms.mk_rational(rat(0));
        let c1 = terms.mk_rational(rat(1));
        let c2 = terms.mk_rational(rat(2));
        let a1 = terms.mk_eq(x, c1);
        let yy = terms.mk_mul(vec![y, y]);
        let twox = terms.mk_mul(vec![c2, x]);
        let a2 = terms.mk_eq(yy, twox);
        let a3 = terms.mk_gt(y, c0);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(a1, true);
        solver.assert_literal(a2, true);
        solver.assert_literal(a3, true);
        let (constraints, vars, root) = grid_inputs(&solver);
        let Some(UniResult::SatAlgebraic(witnesses)) =
            solver.dyadic_grid_search(&constraints, &vars, &root)
        else {
            panic!("the only witness is irrational; the grid must say SatAlgebraic");
        };
        let val = witnesses
            .iter()
            .find_map(|(v, w)| match w {
                UniWitness::Algebraic(a) if *v == y => Some(a.clone()),
                _ => None,
            })
            .expect("y must carry the exact algebraic witness");
        match val.try_mul(&val).expect("same algebraic point") {
            crate::algebraic::RealScalar::Rational(sq) => {
                assert_eq!(sq, BigRational::from_integer(BigInt::from(2)), "y^2 == 2");
            }
            other => panic!("y^2 must reduce to the rational 2, got {other:?}"),
        }
    }

    #[test]
    fn dyadic_grid_search_declines_without_a_witness_and_never_refutes() {
        // `x*x + y*y = -1` has no real solution. The grid must return `None`
        // (it has no `Unsat` to return) and must not spend beyond its budget.
        use ay_core::term::TermStore;
        use ay_core::Sort;
        use ay_core::TheorySolver;
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let cm1 = terms.mk_rational(rat(-1));
        let xx = terms.mk_mul(vec![x, x]);
        let yy = terms.mk_mul(vec![y, y]);
        let sum = terms.mk_add(vec![xx, yy]);
        let a1 = terms.mk_eq(sum, cm1);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(a1, true);
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &solver.asserted {
            if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
                constraints.push(c);
            }
        }
        let vars: Vec<TermId> = vec![x, y];
        let mut root: VarBox = VarBox::default();
        for &v in &vars {
            root.insert(v, Interval::whole());
        }
        let before = solver.grid_budget.get();
        assert!(solver
            .dyadic_grid_search(&constraints, &vars, &root)
            .is_none());
        assert!(
            solver.grid_budget.get() < before,
            "the sweep must charge its solve-wide budget"
        );
        assert!(before - solver.grid_budget.get() <= GRID_MAX_NODES);
    }

    /// Pass 2 must NOT be billed to pass 1's counter.
    ///
    /// `x*x + y*y = -1` is infeasible, so pass 1 sweeps every level, fails, and
    /// pass 2 then re-sweeps and also fails — the exact shape that used to
    /// double-charge `grid_budget` and starve a later `check()`. Pass 1's spend
    /// must be bounded by its own per-call cap and the exact work must appear on
    /// `grid_exact_budget` instead.
    #[test]
    fn the_exact_pass_is_billed_to_its_own_budget_not_the_grid_budget() {
        use ay_core::term::TermStore;
        use ay_core::Sort;
        use ay_core::TheorySolver;
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let cm1 = terms.mk_rational(rat(-1));
        let xx = terms.mk_mul(vec![x, x]);
        let yy = terms.mk_mul(vec![y, y]);
        let sum = terms.mk_add(vec![xx, yy]);
        let a1 = terms.mk_eq(sum, cm1);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(a1, true);
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &solver.asserted {
            if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
                constraints.push(c);
            }
        }
        let vars: Vec<TermId> = vec![x, y];
        let mut root: VarBox = VarBox::default();
        for &v in &vars {
            root.insert(v, Interval::whole());
        }
        let g_before = solver.grid_budget.get();
        let e_before = solver.grid_exact_budget.get();
        assert!(solver
            .dyadic_grid_search(&constraints, &vars, &root)
            .is_none());
        let g_spent = g_before - solver.grid_budget.get();
        let e_spent = e_before - solver.grid_exact_budget.get();
        assert!(
            g_spent <= GRID_MAX_NODES,
            "pass 1 may never exceed its own per-call cap, spent {g_spent}"
        );
        assert!(
            e_spent <= GRID_EXACT_MAX_NODES,
            "pass 2 may never exceed its own per-call cap, spent {e_spent}"
        );
        // The two counters are genuinely independent: draining pass 2's budget
        // must leave pass 1 with a full allowance on the next call.
        solver.grid_exact_budget.set(0);
        let g2_before = solver.grid_budget.get();
        assert!(solver
            .dyadic_grid_search(&constraints, &vars, &root)
            .is_none());
        assert!(
            g2_before - solver.grid_budget.get() > 0,
            "pass 1 must still run when the exact budget is exhausted"
        );
    }

    /// A long run of `Empty` exact decisions must switch the pass off rather
    /// than pay for every surviving prefix.
    #[test]
    fn consecutive_empty_exact_decisions_disable_the_pass() {
        let st = ExactState::with(GRID_EXACT_SOLVES);
        for _ in 0..GRID_EXACT_EMPTY_STREAK - 1 {
            assert!(st.available(), "the cut must not fire early");
            st.charge(&ExactOutcome::Empty);
        }
        assert!(st.available());
        st.charge(&ExactOutcome::Empty);
        assert!(
            !st.available(),
            "GRID_EXACT_EMPTY_STREAK consecutive Empties must disable the pass"
        );
    }

    /// `Declined` is a bail BEFORE the expensive decision, so it must not reset
    /// the streak — otherwise an alternating `Empty, Declined, …` run pays the
    /// Sturm decision forever and the cut never fires.
    #[test]
    fn a_cheap_decline_does_not_reset_the_empty_streak() {
        let st = ExactState::with(GRID_EXACT_SOLVES);
        for _ in 0..GRID_EXACT_EMPTY_STREAK {
            st.charge(&ExactOutcome::Empty);
            if st.available() {
                st.charge(&ExactOutcome::Declined);
            }
        }
        assert!(
            !st.available(),
            "interleaved cheap declines must not keep an Empty run alive"
        );
    }

    /// Pass 1 must be able to run an unbounded number of decisions-free sweeps:
    /// `ExactState::disabled` is what makes pass 1 bit-for-bit unchanged.
    ///
    /// It must ALSO never be treated as spent, or the guard that stops pass 2
    /// would stop pass 1 — which is the whole search.
    #[test]
    fn pass_one_never_makes_an_exact_decision_and_is_never_spent() {
        let st = ExactState::disabled();
        assert!(
            !st.available(),
            "pass 1 must never enter the exact last-coordinate solve"
        );
        assert!(
            !st.spent(),
            "pass 1 has no exact budget to spend and must never be cut short"
        );
    }

    /// The streak cut must STOP pass 2, not merely stop its Sturm calls.
    ///
    /// Once the decisions are gone, pass 2's tree walk can only re-enumerate the
    /// alphabet pass 1 already enumerated — on a second budget, for the same
    /// nothing. `spent()` is what `grid_dfs` checks to unwind immediately.
    #[test]
    fn the_streak_cut_stops_pass_two_outright() {
        let st = ExactState::with(GRID_EXACT_SOLVES);
        assert!(!st.spent(), "pass 2 starts with work to do");
        for _ in 0..GRID_EXACT_EMPTY_STREAK {
            st.charge(&ExactOutcome::Empty);
        }
        assert!(
            st.spent(),
            "after the streak cut pass 2 must unwind rather than re-sweep"
        );
    }

    #[test]
    fn dyadic_grid_search_declines_above_the_variable_cap() {
        use ay_core::term::TermStore;
        use ay_core::Sort;
        use ay_core::TheorySolver;
        let mut terms = TermStore::new();
        let vs: Vec<TermId> = (0..=GRID_MAX_VARS)
            .map(|i| terms.mk_var(format!("v{i}"), Sort::Real))
            .collect();
        let c1 = terms.mk_rational(rat(1));
        let prod = terms.mk_mul(vs.clone());
        let a1 = terms.mk_eq(prod, c1);
        let mut solver = NraSolver::new(&terms);
        solver.assert_literal(a1, true);
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &solver.asserted {
            if let Some(MultiAtom::Constraint(c)) = solver.atom_to_multi(atom, value) {
                constraints.push(c);
            }
        }
        let mut root: VarBox = VarBox::default();
        for &v in &vs {
            root.insert(v, Interval::whole());
        }
        let before = solver.grid_budget.get();
        assert!(
            solver
                .dyadic_grid_search(&constraints, &vs, &root)
                .is_none(),
            "{}+ variables must be declined outright",
            GRID_MAX_VARS + 1
        );
        assert_eq!(
            solver.grid_budget.get(),
            before,
            "a declined call must cost nothing"
        );
    }
}
