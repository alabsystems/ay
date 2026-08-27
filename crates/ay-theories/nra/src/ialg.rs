// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interval sets whose endpoints are REAL ALGEBRAIC numbers — z3's
//! `src/nlsat/nlsat_interval_set.{cpp,h}`.
//!
//! # What could and could not be read, MEASURED TWICE
//!
//! ```text
//!   $ ls reference/z3/5.0.0/                              -> bin include
//!   $ find reference/z3/5.0.0 -name '*nlsat*'             -> (nothing)
//!   $ find reference/z3/5.0.0 -name '*.cpp' | wc -l       -> 0
//!   $ find reference/z3/5.0.0/include -type f | wc -l     -> 14
//! ```
//!
//! The distribution on this machine is a **binary** distribution: `bin/` and
//! `include/` only. `nlsat_interval_set.cpp` is not present in any form, so
//! **no line count is claimed for it and nothing here is a transcription**.
//! What is ported is the algorithm and the documented semantics: a union of
//! disjoint intervals over real algebraic endpoints, each carrying the literal
//! that justifies it, closed under intersection, complement and subtraction,
//! with a sample-point selection that prefers the simplest value available.
//!
//! # What `feasible_set.rs` already does, and what this adds
//!
//! `crates/ay-theories/nonlinear-common/src/feasible_set.rs` is 1,061 lines
//! (414 of code, 647 of tests) and is **WIRED** into the live solve path —
//! 40 references outside its own file, including `nra/src/nlsat.rs` and
//! `nia/src/nlsat.rs`. It is NOT duplicated here and NOT touched. It provides,
//! over `BigRational` endpoints: `empty`, `full`, `singleton`, `from_interval`,
//! `is_empty`, `is_singleton`, `contains_point`, `union`, `intersection`,
//! `pick_value`, `num_intervals`, `classify`.
//!
//! Four things it does not have, which are exactly what an MCSAT search over
//! nonlinear constraints needs and what this module is:
//!
//!   1. **Algebraic endpoints.** `Endpoint::Finite(BigRational)` cannot name
//!      `sqrt(2)`. Root-isolating a projection polynomial produces endpoints
//!      that are irrational in general, so the wired structure can only
//!      represent the cells whose boundaries happen to be rational.
//!   2. **Justifications.** `Interval` carries `lo/lo_strict/hi/hi_strict` and
//!      nothing else. There is no literal on any interval and no way to answer
//!      "which literals made this set empty", which is the conflict clause.
//!   3. **Complement / subtract.** Absent. `feasible_set.rs` has `union` and
//!      `intersection` only; its own test named
//!      `test_feasible_set_complement_like_gap_contains` builds the gap by
//!      hand as a union of two half-lines. Removing a refuted cell is the
//!      operation MCSAT performs on every conflict.
//!   4. **A simplicity ladder in `pick`.** `Interval::pick_value` (`:182`)
//!      returns the arithmetic MIDPOINT `(a + b) / 2`. On `[1/3, 7/3]` that is
//!      `4/3`, when `1` and `2` are both available; iterated, the denominator
//!      doubles every step forever. This module picks the simplest value the
//!      interval admits, which is what keeps later sign evaluations cheap.
//!
//! They would eventually merge by generalising `Endpoint::Finite` over a trait
//! implemented by both `BigRational` and [`Anum`], with the justification field
//! defaulted to empty for the linear callers. That change edits wired code and
//! is deliberately not made here.
//!
//! # NEVER FAIL OPEN
//!
//! Every predicate in this module is decided exactly or not at all. The
//! ordering of two endpoints comes from [`Anum::cmp_anum`], which returns
//! `Option<Ordering>`; **every** such `None` is propagated with `?` and aborts
//! the whole operation. There is no `unwrap_or(Ordering::Equal)` anywhere, and
//! there cannot be: Rust's `slice::sort_by` demands an infallible comparator,
//! so this module sorts with an explicit insertion sort that propagates the
//! refusal instead (see [`IntervalSet::normalize`]). Reaching for `sort_by`
//! with a guessed tie-break is precisely the `check_monomial_consistency`
//! shape — a predicate that could not be decided answered in the permissive
//! direction — and it is structurally excluded here.
//!
//! The consequence is the module's central invariant:
//!
//! > **An [`IntervalSet`] cannot be constructed unless every one of its
//! > endpoint comparisons succeeded.**
//!
//! so [`IntervalSet::is_empty`] is exact by construction rather than by a
//! best-effort test. Nobody can ask emptiness of a set whose ordering was
//! never established, because no such value exists.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_integer::Integer as _;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::anum::Anum;
use crate::mpbq::{self, Bq, BqInterval};

// ============================================================================
// Declared ceilings — every loop in this module is bounded by one of these or
// by a quantity derived from its input. See the module test `ialg_bounds`.
// ============================================================================

/// Largest number of disjoint intervals one set may hold.
///
/// Normalisation sorts with a **fallible** comparator, so it cannot use
/// `sort_by`; the insertion sort it uses instead is `O(n^2)` comparisons. At
/// this ceiling that is at most `256 * 255 / 2 = 32,640` calls to
/// [`Anum::cmp_anum`]. A feasible set produced by root-isolating a degree-`d`
/// polynomial has at most `2d + 1` cells, so 256 covers degree 127 — far past
/// the degree 16 at which the sign-evaluation layer underneath is still usable
/// (measured: 584 us at degree 16, 215 ms at degree 64).
pub(crate) const MAX_INTERVALS: usize = 256;

/// Largest number of literals one interval's justification may carry.
pub(crate) const MAX_JUST: usize = 256;

/// Precision ladder for bracketing an algebraic endpoint by dyadics.
///
/// Doubling rather than incrementing: ten entries reach `2^-256`, which is
/// past the point where the separation machinery underneath declines anyway
/// (`anum::MAX_SEPARATION_BITS` is 8,192, but a root pair that close costs more
/// than the whole search). Exhausting the ladder is a **decline**, never a spin.
const BRACKET_KS: [u32; 10] = [0, 1, 2, 4, 8, 16, 32, 64, 128, 256];

/// Integers probed either side of the first candidate in the `Integer` rung.
const INT_PROBES: i64 = 8;

/// Largest denominator the `Simple` rung will offer.
pub(crate) const MAX_SIMPLE_DEN: i64 = 16;

// ============================================================================
// Justifications
// ============================================================================

/// The literals that put an interval into a set.
///
/// A signed literal id; `0` is not a literal and is rejected. Kept sorted and
/// deduplicated so equality is structural and merging is a linear scan.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Just {
    lits: Vec<i32>,
}

impl Just {
    /// The empty justification (a set that no literal is responsible for, such
    /// as the initial `full`).
    pub(crate) fn none() -> Self {
        Self { lits: Vec::new() }
    }

    /// A single literal. `None` for `0`, which is not a literal.
    pub(crate) fn of(lit: i32) -> Option<Self> {
        if lit == 0 {
            return None;
        }
        Some(Self { lits: vec![lit] })
    }

    /// The literals, ascending.
    pub(crate) fn lits(&self) -> &[i32] {
        &self.lits
    }

    /// How many literals.
    pub(crate) fn len(&self) -> usize {
        self.lits.len()
    }

    /// The union of two justifications: an interval that survives an
    /// intersection is justified by BOTH sides, and a conflict clause needs
    /// all of them.
    ///
    /// `None` past [`MAX_JUST`] — a decline, so a justification can never grow
    /// without bound behind the caller's back.
    pub(crate) fn merge(&self, other: &Self) -> Option<Self> {
        let mut lits = Vec::with_capacity(self.lits.len() + other.lits.len());
        lits.extend_from_slice(&self.lits);
        lits.extend_from_slice(&other.lits);
        // `i32` has a total order: no fallible comparator here, so the
        // library sort is safe. This is the only sort in the module that is.
        lits.sort_unstable();
        lits.dedup();
        if lits.len() > MAX_JUST {
            return None;
        }
        Some(Self { lits })
    }
}

// ============================================================================
// Endpoints
// ============================================================================

/// One end of an interval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AEnd {
    /// `-inf`. Only ever a lower bound, and always open.
    NegInf,
    /// A real algebraic value.
    Fin(Anum),
    /// `+inf`. Only ever an upper bound, and always open.
    PosInf,
}

impl AEnd {
    /// Exact order of two endpoint VALUES, ignoring strictness.
    ///
    /// `None` means the comparison could not be decided. It is never a guess,
    /// and every caller propagates it.
    pub(crate) fn cmp_value(&self, other: &Self) -> Option<Ordering> {
        match (self, other) {
            (Self::NegInf, Self::NegInf) | (Self::PosInf, Self::PosInf) => Some(Ordering::Equal),
            (Self::NegInf, _) | (_, Self::PosInf) => Some(Ordering::Less),
            (_, Self::NegInf) | (Self::PosInf, _) => Some(Ordering::Greater),
            (Self::Fin(a), Self::Fin(b)) => a.cmp_anum(b),
        }
    }

    /// Is this a finite value?
    pub(crate) fn is_finite(&self) -> bool {
        matches!(self, Self::Fin(_))
    }

    /// The value, when finite.
    pub(crate) fn value(&self) -> Option<&Anum> {
        match self {
            Self::Fin(a) => Some(a),
            _ => None,
        }
    }
}

/// Compare two endpoints as POSITIONS on the line, strictness included.
///
/// An open lower bound sits an infinitesimal above its value, an open upper
/// bound an infinitesimal below it. Encoding that as a tie-break `delta` makes
/// emptiness, overlap and adjacency one comparison each instead of a nest of
/// special cases — and, unlike the nest, it cannot silently omit a branch.
///
/// `delta` is `+1` for an open LOWER bound, `-1` for an open UPPER bound, `0`
/// for a closed bound of either kind.
fn cmp_pos(a: &AEnd, da: i8, b: &AEnd, db: i8) -> Option<Ordering> {
    match a.cmp_value(b)? {
        Ordering::Equal => Some(da.cmp(&db)),
        ord => Some(ord),
    }
}

/// The `delta` of an interval's lower bound.
fn lo_delta(open: bool) -> i8 {
    i8::from(open)
}

/// The `delta` of an interval's upper bound.
fn hi_delta(open: bool) -> i8 {
    -i8::from(open)
}

// ============================================================================
// Intervals
// ============================================================================

/// One interval, with the literals that justify it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AInterval {
    lo: AEnd,
    lo_open: bool,
    hi: AEnd,
    hi_open: bool,
    just: Just,
}

/// A conclusive interval-bound comparison.
///
/// Outer `None` means comparison failed; an inner `None` proves emptiness. The
/// wrapper preserves all three outcomes without a bespoke enum or allocation.
#[derive(Clone, Debug, PartialEq, Eq)]
#[must_use]
pub(crate) struct DecidedInterval(Option<AInterval>);

impl DecidedInterval {
    /// Compare bounds, preserving inconclusive, empty, and non-empty outcomes.
    ///
    /// `None` also refuses a malformed closed infinite endpoint.
    pub(crate) fn from_bounds(
        lo: AEnd,
        lo_open: bool,
        hi: AEnd,
        hi_open: bool,
        just: Just,
    ) -> Option<Self> {
        if (!lo.is_finite() && !lo_open) || (!hi.is_finite() && !hi_open) {
            return None;
        }
        let iv = AInterval {
            lo,
            lo_open,
            hi,
            hi_open,
            just,
        };
        if iv.is_proved_empty()? {
            return Some(Self(None));
        }
        Some(Self(Some(iv)))
    }

    /// Consume the decision, yielding the interval unless it was proved empty.
    pub(crate) fn into_interval(self) -> Option<AInterval> {
        self.0
    }
}

impl AInterval {
    /// The whole line, justified by `just`.
    pub(crate) fn full(just: Just) -> Self {
        Self {
            lo: AEnd::NegInf,
            lo_open: true,
            hi: AEnd::PosInf,
            hi_open: true,
            just,
        }
    }

    /// Lower endpoint.
    pub(crate) fn lo(&self) -> &AEnd {
        &self.lo
    }

    /// Is the lower endpoint open?
    pub(crate) fn lo_open(&self) -> bool {
        self.lo_open
    }

    /// Upper endpoint.
    pub(crate) fn hi(&self) -> &AEnd {
        &self.hi
    }

    /// Is the upper endpoint open?
    pub(crate) fn hi_open(&self) -> bool {
        self.hi_open
    }

    /// The literals responsible for this interval.
    pub(crate) fn just(&self) -> &Just {
        &self.just
    }

    /// Is this interval empty? `None` when the endpoints cannot be ordered.
    ///
    /// **Fail-closed note.** The permissive answer here is `true`: an interval
    /// wrongly called empty shrinks the feasible set, and a feasible set
    /// wrongly called empty is a CONFLICT that does not exist, which is
    /// unsoundness. So this never guesses `true`; an undecided comparison
    /// returns `None` and the interval is not built at all.
    fn is_proved_empty(&self) -> Option<bool> {
        Some(
            cmp_pos(
                &self.lo,
                lo_delta(self.lo_open),
                &self.hi,
                hi_delta(self.hi_open),
            )? == Ordering::Greater,
        )
    }

    /// Is this a closed single point `[a, a]`? `None` when undecided.
    pub(crate) fn as_singleton(&self) -> Option<Option<&Anum>> {
        if self.lo_open || self.hi_open {
            return Some(None);
        }
        let (AEnd::Fin(a), AEnd::Fin(b)) = (&self.lo, &self.hi) else {
            return Some(None);
        };
        if a.cmp_anum(b)? == Ordering::Equal {
            Some(Some(a))
        } else {
            Some(None)
        }
    }

    /// Does this interval contain `v`? `None` when undecided.
    pub(crate) fn contains(&self, v: &Anum) -> Option<bool> {
        let lo_ok = match &self.lo {
            AEnd::NegInf => true,
            AEnd::PosInf => false,
            AEnd::Fin(a) => {
                let o = v.cmp_anum(a)?;
                if self.lo_open {
                    o == Ordering::Greater
                } else {
                    o != Ordering::Less
                }
            }
        };
        if !lo_ok {
            return Some(false);
        }
        Some(match &self.hi {
            AEnd::NegInf => false,
            AEnd::PosInf => true,
            AEnd::Fin(b) => {
                let o = v.cmp_anum(b)?;
                if self.hi_open {
                    o == Ordering::Less
                } else {
                    o != Ordering::Greater
                }
            }
        })
    }

    /// Intersect, unioning the justifications.
    ///
    /// The surviving cell is justified by both sides — that union is what a
    /// conflict clause is built from, and dropping either half would produce a
    /// clause that does not entail the conflict.
    /// `None` is inconclusive; a decided disjoint pair has no interval.
    pub(crate) fn intersect(&self, other: &Self) -> Option<DecidedInterval> {
        let (lo, lo_open) = match cmp_pos(
            &self.lo,
            lo_delta(self.lo_open),
            &other.lo,
            lo_delta(other.lo_open),
        )? {
            Ordering::Less => (other.lo.clone(), other.lo_open),
            _ => (self.lo.clone(), self.lo_open),
        };
        let (hi, hi_open) = match cmp_pos(
            &self.hi,
            hi_delta(self.hi_open),
            &other.hi,
            hi_delta(other.hi_open),
        )? {
            Ordering::Greater => (other.hi.clone(), other.hi_open),
            _ => (self.hi.clone(), self.hi_open),
        };
        DecidedInterval::from_bounds(lo, lo_open, hi, hi_open, self.just.merge(&other.just)?)
    }

    /// Is there a real number strictly between `self` and `later`, given
    /// `self.lo <= later.lo`? `None` when undecided.
    ///
    /// This is the adjacency test the union depends on. `[1,2]` and `(2,3]`
    /// have no gap — every real above `2` up to `3` is in the second and `2`
    /// itself is in the first — so they merge. `(1,2)` and `(2,3)` DO have a
    /// gap, namely the single point `2`.
    fn gap_before(&self, later: &Self) -> Option<bool> {
        Some(match self.hi.cmp_value(&later.lo)? {
            Ordering::Greater => false,
            Ordering::Less => true,
            Ordering::Equal => self.hi_open && later.lo_open,
        })
    }

    /// Merge two intervals already known to have no gap, taking the widest
    /// bounds and unioning the justifications.
    fn merge_with(&self, other: &Self) -> Option<Self> {
        let (lo, lo_open) = match cmp_pos(
            &self.lo,
            lo_delta(self.lo_open),
            &other.lo,
            lo_delta(other.lo_open),
        )? {
            Ordering::Greater => (other.lo.clone(), other.lo_open),
            _ => (self.lo.clone(), self.lo_open),
        };
        let (hi, hi_open) = match cmp_pos(
            &self.hi,
            hi_delta(self.hi_open),
            &other.hi,
            hi_delta(other.hi_open),
        )? {
            Ordering::Less => (other.hi.clone(), other.hi_open),
            _ => (self.hi.clone(), self.hi_open),
        };
        Some(Self {
            lo,
            lo_open,
            hi,
            hi_open,
            just: self.just.merge(&other.just)?,
        })
    }
}

// ============================================================================
// Dyadic witnesses around an algebraic endpoint
// ============================================================================

/// The smallest dyadic `m / 2^k` STRICTLY greater than the rational `r`.
///
/// `m / 2^k > n / d` iff `m > n * 2^k / d` iff `m >= floor(n * 2^k / d) + 1`.
fn dyadic_above_rational(r: &BigRational, k: u32) -> Option<Bq> {
    if k > mpbq::MAX_SELECT_K {
        return None;
    }
    let scaled = r.numer() << k;
    Some(Bq::new(scaled.div_floor(r.denom()) + BigInt::one(), k))
}

/// The largest dyadic `m / 2^k` STRICTLY less than the rational `r`.
fn dyadic_below_rational(r: &BigRational, k: u32) -> Option<Bq> {
    if k > mpbq::MAX_SELECT_K {
        return None;
    }
    let scaled = r.numer() << k;
    let (q, rem) = scaled.div_rem(r.denom());
    let ceil = if rem.is_zero() || rem.is_negative() {
        q
    } else {
        q + BigInt::one()
    };
    Some(Bq::new(ceil - BigInt::one(), k))
}

/// A dyadic STRICTLY above `a`, tightened to about `2^-k`.
///
/// For an algebraic `a` the isolating interval's upper endpoint already is one
/// (`a < iv.hi` by the isolation invariant); refining first makes it tight.
fn witness_above(a: &Anum, k: u32) -> Option<Bq> {
    match a {
        Anum::Rational(r) => dyadic_above_rational(r, k),
        Anum::Alg(_) => match a.refine(&Bq::inv_two_pow(k))? {
            Anum::Rational(r) => dyadic_above_rational(&r, k),
            Anum::Alg(c) => Some(c.interval().hi().clone()),
        },
    }
}

/// A dyadic STRICTLY below `a`, tightened to about `2^-k`.
fn witness_below(a: &Anum, k: u32) -> Option<Bq> {
    match a {
        Anum::Rational(r) => dyadic_below_rational(r, k),
        Anum::Alg(_) => match a.refine(&Bq::inv_two_pow(k))? {
            Anum::Rational(r) => dyadic_below_rational(&r, k),
            Anum::Alg(c) => Some(c.interval().lo().clone()),
        },
    }
}

/// A dyadic interval `(L, H)` lying ENTIRELY inside `iv`, or `None`.
///
/// # Liveness
///
/// The scan walks [`BRACKET_KS`], ten fixed precisions ending at `2^-256`, and
/// at each one asks for one refinement per finite endpoint. `Anum::refine` is
/// itself bounded (`mpbq::refine_step_bound`, capped at `MAX_REFINE_STEPS`), so
/// the total work is bounded by a constant times the endpoint-refinement bound.
/// Running out of precisions **returns `None`**; it never widens the ladder,
/// and no interval — not even a genuine singleton, which has no interior at
/// all — can make it spin.
fn inner_dyadic(iv: &AInterval) -> Option<BqInterval> {
    for &k in &BRACKET_KS {
        let l = match &iv.lo {
            AEnd::NegInf => None,
            AEnd::PosInf => return None,
            AEnd::Fin(a) => Some(witness_above(a, k)?),
        };
        let h = match &iv.hi {
            AEnd::PosInf => None,
            AEnd::NegInf => return None,
            AEnd::Fin(b) => Some(witness_below(b, k)?),
        };
        let (l, h) = match (l, h) {
            (Some(l), Some(h)) => (l, h),
            // Unbounded below: any dyadic one unit under `h` is still inside.
            (None, Some(h)) => (h.sub(&Bq::one()), h),
            // Unbounded above: likewise one unit over `l`.
            (Some(l), None) => {
                let h = l.add(&Bq::one());
                (l, h)
            }
            (None, None) => (Bq::from_int(-BigInt::one()), Bq::one()),
        };
        if l.cmp_bq(&h) == Ordering::Less {
            if let Some(b) = BqInterval::new(l, h) {
                return Some(b);
            }
        }
    }
    None
}

// ============================================================================
// The simplicity ladder
// ============================================================================

/// How simple a picked value is. Strictly ordered, simplest first.
///
/// # Not a stored flag
///
/// This is **derived** by [`classify_value`]. `pick` does not record which
/// branch produced its answer and there is no field to read it off, because a
/// stored tag is the third blind-spot pattern: it can be hardwired and nothing
/// downstream diverges. The oracle re-derives the rung and, separately, checks
/// that no simpler rung was available.
///
/// # What it measures: the REPRESENTATION, not the abstract value
///
/// An [`Anum`] that is `Alg(cell)` classifies as [`Rung::Algebraic`] even when
/// its value happens to be rational. MEASURED at seed 20260806 over 12,000
/// cases: for the `interleaved` shape, whose polynomial is `(x-1)(x-3)(x-5)`
/// and whose roots are the integers 1, 3 and 5, `is_rational()` is **false**
/// for all of them — `from_poly_interval` does not collapse a rational root
/// when the square-free defining polynomial has degree above one, and
/// `(x-1)(x-3)(x-5)` is square-free.
///
/// That is the right metric anyway, and deliberately so. The cost this ladder
/// exists to control is the cost of the NEXT sign evaluation, and
/// `sign_of_poly` at a root of a degree-3 cell does degree-3 work whether or
/// not the value is an integer. What would be wrong is to report `Integer`
/// for such a cell: the caller would expect a cheap sample point and get an
/// expensive one. `pick`'s three simplest rungs all construct
/// `Anum::rational` directly, so a value they return is genuinely cheap.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Rung {
    /// An integer.
    Integer,
    /// A rational with denominator at most [`MAX_SIMPLE_DEN`].
    Simple,
    /// A dyadic `a / 2^k` that is not already [`Rung::Simple`].
    Dyadic,
    /// Any other exact rational.
    Rational,
    /// A genuine algebraic number: defining degree above one.
    Algebraic,
}

/// The rung a value sits on, derived from the value and nothing else.
pub(crate) fn classify_value(v: &Anum) -> Rung {
    let Some(r) = v.to_rational() else {
        return Rung::Algebraic;
    };
    if r.is_integer() {
        return Rung::Integer;
    }
    let d = r.denom();
    if d <= &BigInt::from(MAX_SIMPLE_DEN) {
        return Rung::Simple;
    }
    // A positive denominator is a power of two iff `d & (d - 1) == 0`.
    if (d & (d - BigInt::one())).is_zero() {
        return Rung::Dyadic;
    }
    Rung::Rational
}

// ============================================================================
// The set
// ============================================================================

/// A union of disjoint, ascending intervals with real algebraic endpoints.
///
/// # Invariant
///
/// The intervals are non-empty, ascending by lower position, and separated by
/// a gap containing at least one real number. Every operation that could break
/// that either re-establishes it or **declines**, so the invariant holds of
/// every value of this type that exists.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct IntervalSet {
    ivs: Vec<AInterval>,
}

impl IntervalSet {
    /// The empty set — the CONFLICT signal.
    pub(crate) fn empty() -> Self {
        Self { ivs: Vec::new() }
    }

    /// The whole line.
    pub(crate) fn full(just: Just) -> Self {
        Self {
            ivs: vec![AInterval::full(just)],
        }
    }

    /// Is the set empty?
    ///
    /// Exact **by construction**, not by a best-effort test: the constructors
    /// all return `Option` and refuse to produce a set whose interval ordering
    /// could not be established, so a set that exists has already had every
    /// comparison decided. There is no path by which an undecided emptiness
    /// question reaches a caller as `true`.
    pub(crate) fn is_empty(&self) -> bool {
        self.ivs.is_empty()
    }

    /// How many disjoint intervals.
    pub(crate) fn len(&self) -> usize {
        self.ivs.len()
    }

    /// The intervals, ascending.
    pub(crate) fn intervals(&self) -> &[AInterval] {
        &self.ivs
    }

    /// Exact SET equality: do these two denote the same points?
    ///
    /// # Why the derived `PartialEq` is not this
    ///
    /// `#[derive(PartialEq)]` on this type is STRUCTURAL, and structural
    /// equality is strictly finer than set equality for two independent
    /// reasons:
    ///
    ///   * **The same real number has many representations.** `sqrt(10)` as a
    ///     root of `x^2 - 10` and as a root of `(x^2-5)(x^2-10)` are `Eq`-
    ///     different `Anum`s that `cmp_anum` calls `Equal`. `intersect` keeps
    ///     `self`'s endpoint when the two are equal, so `a n b` and `b n a`
    ///     denote the same set through different endpoint objects.
    ///   * **Justifications accumulate.** Complementing twice unions the
    ///     literals of neighbouring gaps back onto the original interval, which
    ///     is correct and monotone, and leaves the point set alone.
    ///
    /// MEASURED: the oracle reported all three of `ialg-intersect` case 37
    /// ("not commutative"), `ialg-complement` case 38 ("double complement is
    /// not the identity") and `ialg-sign-cells` case 40 ("complement of Lt is
    /// not Ge") at seed 20260806 with 41 checks, on the FIRST run after the
    /// checks were added — every one of them a structural comparison standing
    /// in for a semantic one, and every one on the `irrational` / `rational`
    /// shapes where a shared factor makes two representations of one root
    /// meet. The point-set legs, which ask z3 directly, passed throughout.
    ///
    /// Both sets are normalised, and a normalised set is the unique maximal
    /// decomposition of its point set, so comparing them cell by cell is exact.
    /// `None` when an endpoint comparison could not be decided.
    pub(crate) fn same_set_as(&self, other: &Self) -> Option<bool> {
        if self.ivs.len() != other.ivs.len() {
            return Some(false);
        }
        for (a, b) in self.ivs.iter().zip(other.ivs.iter()) {
            if a.lo_open != b.lo_open || a.hi_open != b.hi_open {
                return Some(false);
            }
            if a.lo.cmp_value(&b.lo)? != Ordering::Equal
                || a.hi.cmp_value(&b.hi)? != Ordering::Equal
            {
                return Some(false);
            }
        }
        Some(true)
    }

    /// The union of every interval's justification — the conflict clause when
    /// this set is empty is built from the justifications that emptied it, so
    /// the caller needs them aggregated.
    pub(crate) fn justification(&self) -> Option<Just> {
        let mut j = Just::none();
        for iv in &self.ivs {
            j = j.merge(&iv.just)?;
        }
        Some(j)
    }

    /// Does the set contain `v`? `None` when undecided.
    pub(crate) fn contains(&self, v: &Anum) -> Option<bool> {
        for iv in &self.ivs {
            if iv.contains(v)? {
                return Some(true);
            }
        }
        Some(false)
    }

    /// Build from arbitrary intervals: drop the empty, sort, merge.
    ///
    /// # Why an explicit insertion sort
    ///
    /// The comparator is fallible. `slice::sort_by` requires
    /// `FnMut(&T, &T) -> Ordering` — a TOTAL order — so using it would mean
    /// converting an undecided comparison into some default, which is exactly
    /// the fail-open shape this module exists to avoid. Insertion sort with `?`
    /// keeps the refusal.
    ///
    /// # Liveness
    ///
    /// `n <= MAX_INTERVALS` is checked before any comparison. The sort makes at
    /// most `n(n-1)/2` comparisons and the merge scan exactly `n - 1`; both
    /// loops are `for` loops over fixed ranges with no early re-entry.
    pub(crate) fn normalize(raw: Vec<AInterval>) -> Option<Self> {
        if raw.len() > MAX_INTERVALS {
            return None;
        }
        // Drop intervals that are provably empty; refuse the undecided.
        let mut ivs: Vec<AInterval> = Vec::with_capacity(raw.len());
        for iv in raw {
            if !iv.is_proved_empty()? {
                ivs.push(iv);
            }
        }
        if ivs.is_empty() {
            return Some(Self::empty());
        }

        // Insertion sort by lower POSITION, fallible throughout.
        for i in 1..ivs.len() {
            let mut j = i;
            while j > 0 {
                let ord = cmp_pos(
                    &ivs[j - 1].lo,
                    lo_delta(ivs[j - 1].lo_open),
                    &ivs[j].lo,
                    lo_delta(ivs[j].lo_open),
                )?;
                if ord != Ordering::Greater {
                    break;
                }
                ivs.swap(j - 1, j);
                j -= 1;
            }
        }

        // Merge everything without a gap between it and the running interval.
        let mut out: Vec<AInterval> = Vec::with_capacity(ivs.len());
        for iv in ivs {
            match out.last() {
                Some(last) if !last.gap_before(&iv)? => {
                    let merged = last.merge_with(&iv)?;
                    let n = out.len();
                    out[n - 1] = merged;
                }
                _ => out.push(iv),
            }
        }
        Some(Self { ivs: out })
    }

    /// Check the invariant on an already-ordered list, then wrap it.
    ///
    /// Used where the algorithm is supposed to produce an ordered, disjoint
    /// result — intersection, complement — so that a bug in that reasoning
    /// surfaces as a **decline** here rather than as a silently malformed set.
    /// This guard is reachable: `ialg_intersect_guard_fires` fires it.
    fn from_ordered(ivs: Vec<AInterval>) -> Option<Self> {
        if ivs.len() > MAX_INTERVALS {
            return None;
        }
        for i in 0..ivs.len() {
            if ivs[i].is_proved_empty()? {
                return None;
            }
            if i > 0 && !ivs[i - 1].gap_before(&ivs[i])? {
                return None;
            }
        }
        Some(Self { ivs })
    }

    /// Union.
    pub(crate) fn union(&self, other: &Self) -> Option<Self> {
        let mut all = Vec::with_capacity(self.ivs.len() + other.ivs.len());
        all.extend(self.ivs.iter().cloned());
        all.extend(other.ivs.iter().cloned());
        Self::normalize(all)
    }

    /// Intersection, keeping justifications.
    ///
    /// # Liveness
    ///
    /// The two-pointer scan advances `i` or `j` (or both) on every iteration
    /// and neither ever decreases, so it runs at most `len(a) + len(b)`
    /// iterations. That count is asserted rather than assumed: exceeding it
    /// returns `None`.
    pub(crate) fn intersect(&self, other: &Self) -> Option<Self> {
        if self.is_empty() || other.is_empty() {
            return Some(Self::empty());
        }
        let limit = self.ivs.len() + other.ivs.len();
        let mut out = Vec::new();
        let (mut i, mut j, mut steps) = (0usize, 0usize, 0usize);
        while i < self.ivs.len() && j < other.ivs.len() {
            steps += 1;
            if steps > limit {
                return None;
            }
            let a = &self.ivs[i];
            let b = &other.ivs[j];
            if let Some(x) = a.intersect(b)?.into_interval() {
                if out.len() >= MAX_INTERVALS {
                    return None;
                }
                out.push(x);
            }
            match cmp_pos(&a.hi, hi_delta(a.hi_open), &b.hi, hi_delta(b.hi_open))? {
                Ordering::Less => i += 1,
                Ordering::Greater => j += 1,
                Ordering::Equal => {
                    i += 1;
                    j += 1;
                }
            }
        }
        Self::from_ordered(out)
    }

    /// Complement — how a refuted cell is removed.
    ///
    /// Each gap is justified by the intervals that bound it: those are exactly
    /// the literals that exclude the gap's neighbours, so they are what a
    /// caller must cite when it later refutes the gap too.
    ///
    /// # Liveness
    ///
    /// One pass over `n` intervals producing at most `n + 1` gaps.
    pub(crate) fn complement(&self) -> Option<Self> {
        if self.ivs.is_empty() {
            return Some(Self::full(Just::none()));
        }
        let mut out: Vec<AInterval> = Vec::with_capacity(self.ivs.len() + 1);
        let first = &self.ivs[0];
        if first.lo.is_finite() {
            out.push(AInterval {
                lo: AEnd::NegInf,
                lo_open: true,
                hi: first.lo.clone(),
                hi_open: !first.lo_open,
                just: first.just.clone(),
            });
        }
        for w in self.ivs.windows(2) {
            out.push(AInterval {
                lo: w[0].hi.clone(),
                lo_open: !w[0].hi_open,
                hi: w[1].lo.clone(),
                hi_open: !w[1].lo_open,
                just: w[0].just.merge(&w[1].just)?,
            });
        }
        let last = self.ivs.last()?;
        if last.hi.is_finite() {
            out.push(AInterval {
                lo: last.hi.clone(),
                lo_open: !last.hi_open,
                hi: AEnd::PosInf,
                hi_open: true,
                just: last.just.clone(),
            });
        }
        Self::from_ordered(out)
    }

    /// `self \ other`.
    pub(crate) fn subtract(&self, other: &Self) -> Option<Self> {
        self.intersect(&other.complement()?)
    }

    // --------------------------------------------------------------------
    // Priority 3: pick a value, preferring a SIMPLE one
    // --------------------------------------------------------------------

    /// A value in the set, as simple as this ladder can find.
    ///
    /// Rungs are tried in order: integer, then a rational of denominator at
    /// most [`MAX_SIMPLE_DEN`], then the minimal-exponent dyadic
    /// ([`mpbq::select_small`]), then an algebraic value read off a closed
    /// endpoint. Every candidate is **verified** with [`IntervalSet::contains`]
    /// before it is returned, so a wrong candidate is a decline and never a
    /// wrong answer — the rungs are heuristics, but the result never is.
    ///
    /// # Liveness
    ///
    /// At most `MAX_INTERVALS` intervals; within one interval,
    /// `1 + 2*INT_PROBES` integer probes, `MAX_SIMPLE_DEN - 1` denominators,
    /// one `select_small`, and three endpoint reads — all constants. Each
    /// verification is a bounded number of `cmp_anum` calls.
    pub(crate) fn pick(&self) -> Option<Anum> {
        for iv in &self.ivs {
            if let Some(v) = self.pick_in(iv)? {
                return Some(v);
            }
        }
        None
    }

    /// [`IntervalSet::pick`] restricted to one interval; `Ok(None)` means this
    /// interval offered nothing and the next should be tried.
    fn pick_in(&self, iv: &AInterval) -> Option<Option<Anum>> {
        let bracket = inner_dyadic(iv);

        // Rung 1: an integer.
        //
        // `select_int` answers about the BRACKET, which lies strictly inside
        // `iv`, so it can decline while `iv` itself holds an integer near an
        // endpoint — `(1/3, 7/3)` brackets to `(1, 2)`, which holds no integer
        // at all, while the interval holds both `1` and `2`. So the bracket
        // only seeds the probe; it never gates it. (Caught by
        // `ialg_pick_prefers_an_integer` against an earlier version that
        // gated on `select_int` and returned `1/2` for that interval.)
        if let Some(b) = &bracket {
            let base = mpbq::select_int(b.lo(), b.hi()).unwrap_or_else(|| b.lo().floor());
            let mut cands: Vec<BigInt> = (-INT_PROBES..=INT_PROBES)
                .map(|step| base.clone() + BigInt::from(step))
                .collect();
            // Closest to zero first, positive before negative on a tie: the
            // same simplicity tie-break `mpbq::select_int` uses. `BigInt` has a
            // total order, so this sort has no fallible comparator.
            cands.sort_by(|x, y| x.magnitude().cmp(y.magnitude()).then_with(|| y.cmp(x)));
            for n in cands {
                let cand = Anum::rational(BigRational::from_integer(n));
                if self.contains(&cand)? {
                    return Some(Some(cand));
                }
            }
        }

        // Rung 2: a rational with a small denominator.
        if let Some(b) = &bracket {
            for d in 2..=MAX_SIMPLE_DEN {
                let den = BigInt::from(d);
                // Smallest numerator with `n/d` above the bracket's floor.
                let lo_scaled = b.lo().to_rational() * BigRational::from_integer(den.clone());
                let n0 = lo_scaled.numer().div_floor(lo_scaled.denom()) + BigInt::one();
                for step in 0..=INT_PROBES {
                    let cand = Anum::rational(BigRational::new(
                        n0.clone() + BigInt::from(step),
                        den.clone(),
                    ));
                    if classify_value(&cand) == Rung::Simple && self.contains(&cand)? {
                        return Some(Some(cand));
                    }
                }
            }
        }

        // Rung 3: the minimal-exponent dyadic.
        if let Some(b) = &bracket {
            if let Some(sel) = mpbq::select_small(b) {
                let cand = Anum::rational(sel.value.to_rational());
                if self.contains(&cand)? {
                    return Some(Some(cand));
                }
            }
        }

        // Rung 4/5: an algebraic value read off a closed endpoint.
        if let Some(a) = iv.as_singleton()? {
            return Some(Some(a.clone()));
        }
        if !iv.lo_open {
            if let Some(a) = iv.lo.value() {
                if self.contains(a)? {
                    return Some(Some(a.clone()));
                }
            }
        }
        if !iv.hi_open {
            if let Some(a) = iv.hi.value() {
                if self.contains(a)? {
                    return Some(Some(a.clone()));
                }
            }
        }
        Some(None)
    }
}

// ============================================================================
// Priority 1: construct from a sign condition
// ============================================================================

/// The sign condition a cell must satisfy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SignCond {
    /// `p < 0`.
    Lt,
    /// `p <= 0`.
    Le,
    /// `p = 0`.
    Eq,
    /// `p != 0`.
    Ne,
    /// `p >= 0`.
    Ge,
    /// `p > 0`.
    Gt,
}

impl SignCond {
    /// Does sign `s` (one of `-1`, `0`, `1`) satisfy this condition?
    pub(crate) fn accepts(self, s: i32) -> bool {
        match self {
            Self::Lt => s < 0,
            Self::Le => s <= 0,
            Self::Eq => s == 0,
            Self::Ne => s != 0,
            Self::Ge => s >= 0,
            Self::Gt => s > 0,
        }
    }
}

/// The feasible set of `p `cond` 0`, given `p`'s real roots in ASCENDING order.
///
/// This is the cell decomposition nlsat builds after root-isolating a
/// projection polynomial: the roots cut the line into `2m + 1` cells — `m`
/// closed points and `m + 1` open gaps — `p` has a constant sign on each open
/// cell, and the cells whose sign satisfies `cond` are kept and merged.
///
/// Root ISOLATION is not repeated here. It already exists, is already
/// oracle-covered (`roots`, `mv-isolate-roots`), and taking the root list as an
/// argument makes this a pure function that the oracle can drive on z3's own
/// root list rather than only through a consumer.
///
/// # NEVER FAIL OPEN — the `check_monomial_consistency` shape, avoided
///
/// The sign of `p` on an open cell is read at a sample point. If that sample
/// cannot be produced, or its sign cannot be evaluated, the tempting moves are
/// to skip the cell (too small — a feasible set wrongly emptied is a conflict
/// that does not exist) or to keep it (too large, and silently imprecise).
/// **Neither is taken: the whole construction returns `None`.** The defect
/// injected for the oracle demonstration is exactly this — `?` replaced by
/// "assume the condition holds" — and it is what the campaign's worst bug was.
///
/// # Liveness
///
/// One pass over `2m + 1` cells for `m = roots.len()`, refused above
/// [`MAX_INTERVALS`] before any work. The ascending-order precondition is
/// **verified**, not assumed: an out-of-order or duplicated root is a refusal.
pub(crate) fn from_sign_condition(
    p: &[BigInt],
    roots: &[Anum],
    cond: SignCond,
    just: Just,
) -> Option<IntervalSet> {
    if p.iter().all(Zero::is_zero) {
        // The zero polynomial has sign 0 everywhere. No root list describes it.
        return Some(if cond.accepts(0) {
            IntervalSet::full(just)
        } else {
            IntervalSet::empty()
        });
    }
    if roots.len().checked_mul(2)?.checked_add(1)? > MAX_INTERVALS {
        return None;
    }
    // Verify the precondition rather than trusting it — BOTH halves.
    //
    // The weak half: the list ascends.
    for w in roots.windows(2) {
        if w[0].cmp_anum(&w[1])? != Ordering::Less {
            return None;
        }
    }

    // The list must contain exactly the real roots. Ordering alone is unsound:
    // dropping -1 from x^2 - 1 made `Lt` appear empty instead of `(-1, 1)`, a
    // nonexistent conflict and potentially wrong UNSAT; padding also passed.
    // Sampling cannot detect this unless it lands exactly on a missed root.
    // Count roots once with the existing Sturm machinery and require equality.
    {
        let zp = crate::upoly::ZPoly::from_coeffs(p.to_vec());
        // `normalize_defining` is the same square-free/primitive/positive-lc
        // normalization `Anum::new` runs before building a Sturm chain.
        let sf = crate::anum::normalize_defining(&zp)?;
        let chain = crate::anum::sturm_chain(&sf)?;
        let b = crate::anum::cauchy_bound_z(&sf)?;
        let lo = Bq::from_int(-(b.clone() + BigInt::one()));
        let hi = Bq::from_int(b + BigInt::one());
        // `sturm_count_in` counts distinct real roots in `(lo, hi]`; the bound
        // strictly encloses every root, so this is the total count.
        let n = crate::anum::sturm_count_in(&chain, &lo, &hi)?;
        if n != roots.len() {
            return None;
        }
    }

    // A dyadic strictly outside every root, from the Cauchy bound.
    let bound = crate::anum::cauchy_bound_z(&crate::upoly::ZPoly::from_coeffs(p.to_vec()))?;
    let outside = Bq::from_int(bound + BigInt::one());

    let mut cells: Vec<AInterval> = Vec::with_capacity(2 * roots.len() + 1);

    for i in 0..=roots.len() {
        // The open cell before root `i` (or after the last root).
        let lo = match i {
            0 => AEnd::NegInf,
            _ => AEnd::Fin(roots[i - 1].clone()),
        };
        let hi = if i == roots.len() {
            AEnd::PosInf
        } else {
            AEnd::Fin(roots[i].clone())
        };
        let sample = open_cell_sample(&lo, &hi, &outside)?;
        // FAIL CLOSED: an unevaluable sign aborts the construction.
        let s = mpbq::poly_sign_at(p, &sample)?;
        if s == 0 {
            // The sample must not be a root; if it is, the cell decomposition
            // this was handed is wrong. Refuse rather than paper over it.
            return None;
        }
        if cond.accepts(s) {
            if let Some(iv) =
                DecidedInterval::from_bounds(lo, true, hi, true, just.clone())?.into_interval()
            {
                cells.push(iv);
            }
        }
        // The closed point cell at root `i`, where the sign is exactly 0.
        if i < roots.len() && cond.accepts(0) {
            let r = AEnd::Fin(roots[i].clone());
            if let Some(iv) =
                DecidedInterval::from_bounds(r.clone(), false, r, false, just.clone())?
                    .into_interval()
            {
                cells.push(iv);
            }
        }
    }
    IntervalSet::normalize(cells)
}

/// A dyadic strictly inside the open cell `(lo, hi)`, using `outside` as the
/// witness beyond the last root in either direction.
fn open_cell_sample(lo: &AEnd, hi: &AEnd, outside: &Bq) -> Option<Bq> {
    let iv = AInterval {
        lo: lo.clone(),
        lo_open: true,
        hi: hi.clone(),
        hi_open: true,
        just: Just::none(),
    };
    match (lo, hi) {
        (AEnd::NegInf, AEnd::PosInf) => Some(Bq::zero()),
        (AEnd::NegInf, _) => {
            // Below every root: `-(B + 1)` is outside the Cauchy bound.
            Some(outside.neg())
        }
        (_, AEnd::PosInf) => Some(outside.clone()),
        _ => inner_dyadic(&iv).and_then(|b| b.midpoint()),
    }
}

#[cfg(test)]
#[path = "ialg_tests.rs"]
mod ialg_tests;
