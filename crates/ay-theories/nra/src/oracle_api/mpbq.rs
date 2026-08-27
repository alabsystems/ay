// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// `mpbq` — binary rationals (dyadics) and the interval machinery on them
// ============================================================================

/// A binary rational `a / 2^k`, in canonical form (`k == 0` or `a` odd).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct OBq(mpbq::Bq);

impl OBq {
    /// The exact value `a / 2^k`, normalized.
    #[must_use]
    pub fn new(a: BigInt, k: u32) -> Self {
        Self(mpbq::Bq::new(a, k))
    }

    /// The integer `n`.
    #[must_use]
    pub fn from_int(n: BigInt) -> Self {
        Self(mpbq::Bq::from_int(n))
    }

    /// Zero.
    #[must_use]
    pub fn zero() -> Self {
        Self(mpbq::Bq::zero())
    }

    /// `2^(-k)`.
    #[must_use]
    pub fn inv_two_pow(k: u32) -> Self {
        Self(mpbq::Bq::inv_two_pow(k))
    }

    /// The canonical numerator.
    #[must_use]
    pub fn numerator(&self) -> BigInt {
        self.0.numerator().clone()
    }

    /// The canonical denominator exponent.
    #[must_use]
    pub fn k(&self) -> u32 {
        self.0.k()
    }

    /// Bit length of the canonical numerator.
    #[must_use]
    pub fn numerator_bits(&self) -> u64 {
        self.0.numerator_bits()
    }

    /// `-1`, `0` or `1`.
    #[must_use]
    pub fn sign(&self) -> i32 {
        self.0.sign()
    }

    /// Whether the value is an integer.
    #[must_use]
    pub fn is_int(&self) -> bool {
        self.0.is_int()
    }

    /// Negation.
    #[must_use]
    pub fn neg(&self) -> Self {
        Self(self.0.neg())
    }

    /// Absolute value.
    #[must_use]
    pub fn abs(&self) -> Self {
        Self(self.0.abs())
    }

    /// Exact addition.
    #[must_use]
    pub fn add(&self, other: &Self) -> Self {
        Self(self.0.add(&other.0))
    }

    /// Exact subtraction.
    #[must_use]
    pub fn sub(&self, other: &Self) -> Self {
        Self(self.0.sub(&other.0))
    }

    /// Exact multiplication.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Option<Self> {
        self.0.mul(&other.0).map(Self)
    }

    /// `self * 2^e`.
    #[must_use]
    pub fn mul_two_pow(&self, e: u32) -> Self {
        Self(self.0.mul_two_pow(e))
    }

    /// `self / 2^e`.
    #[must_use]
    pub fn div_two_pow(&self, e: u32) -> Option<Self> {
        self.0.div_two_pow(e).map(Self)
    }

    /// Exact comparison.
    #[must_use]
    pub fn cmp_bq(&self, other: &Self) -> Ordering {
        self.0.cmp_bq(&other.0)
    }

    /// `floor(self)`.
    #[must_use]
    pub fn floor(&self) -> BigInt {
        self.0.floor()
    }

    /// `ceil(self)`.
    #[must_use]
    pub fn ceil(&self) -> BigInt {
        self.0.ceil()
    }

    /// `floor(self * 2^target)`.
    #[must_use]
    pub fn floor_at(&self, target: u32) -> BigInt {
        self.0.floor_at(target)
    }

    /// `ceil(self * 2^target)`.
    #[must_use]
    pub fn ceil_at(&self, target: u32) -> BigInt {
        self.0.ceil_at(target)
    }

    /// The exact rational this dyadic denotes.
    #[must_use]
    pub fn to_rational(&self) -> BigRational {
        self.0.to_rational()
    }

    /// The dyadic equal to `r`, or `None` when `r` is not exactly representable.
    #[must_use]
    pub fn from_rational(r: &BigRational) -> Option<Self> {
        mpbq::Bq::from_rational(r).map(Self)
    }

    /// Whether `r` is exactly representable as a dyadic.
    #[must_use]
    pub fn is_representable(r: &BigRational) -> bool {
        mpbq::Bq::is_representable(r)
    }
}

/// A non-empty open interval with dyadic endpoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OBqInterval(mpbq::BqInterval);

impl OBqInterval {
    /// Build `(lo, hi)`, or `None` when `lo >= hi`.
    #[must_use]
    pub fn new(lo: &OBq, hi: &OBq) -> Option<Self> {
        mpbq::BqInterval::new(lo.0.clone(), hi.0.clone()).map(Self)
    }

    /// Lower endpoint.
    #[must_use]
    pub fn lo(&self) -> OBq {
        OBq(self.0.lo().clone())
    }

    /// Upper endpoint.
    #[must_use]
    pub fn hi(&self) -> OBq {
        OBq(self.0.hi().clone())
    }

    /// `hi - lo`.
    #[must_use]
    pub fn width(&self) -> OBq {
        OBq(self.0.width())
    }

    /// The exact midpoint.
    #[must_use]
    pub fn midpoint(&self) -> Option<OBq> {
        self.0.midpoint().map(OBq)
    }

    /// Split at the midpoint: `(left, mid, right)`.
    #[must_use]
    pub fn bisect(&self) -> Option<(Self, OBq, Self)> {
        self.0.bisect().map(|(l, m, r)| (Self(l), OBq(m), Self(r)))
    }

    /// `lo < x < hi`.
    #[must_use]
    pub fn contains_open(&self, x: &OBq) -> bool {
        self.0.contains_open(&x.0)
    }

    /// The two open intervals share no point.
    #[must_use]
    pub fn disjoint(&self, other: &Self) -> bool {
        self.0.disjoint(&other.0)
    }

    /// The larger of the two endpoint precisions.
    #[must_use]
    pub fn max_k(&self) -> u32 {
        self.0.max_k()
    }
}

/// Exact sign of an integer polynomial (low-to-high) at a dyadic point.
#[must_use]
pub fn obq_poly_sign_at(p: &[BigInt], x: &OBq) -> Option<i32> {
    mpbq::poly_sign_at(p, &x.0)
}

/// Exact value of an integer polynomial at a dyadic point.
#[must_use]
pub fn obq_poly_eval_at(p: &[BigInt], x: &OBq) -> Option<OBq> {
    mpbq::poly_eval_at(p, &x.0).map(OBq)
}

/// The derived liveness bound for [`obq_refine_to_width`].
#[must_use]
pub fn obq_refine_step_bound(width: &OBq, target: &OBq) -> Option<u32> {
    mpbq::refine_step_bound(&width.0, &target.0)
}

/// What one refinement produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ORefined {
    /// The root is exactly this dyadic.
    Exact(OBq),
    /// A narrower isolating interval.
    Narrowed(OBqInterval),
}

/// The refinement's own account: steps taken, the derived bound, and the
/// precision of the answer (derived from the answer, not stored by the loop).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ORefineTrace {
    /// Bisections actually performed.
    pub steps: u32,
    /// The derived upper bound on `steps`.
    pub bound: u32,
    /// `max_k` of the returned interval.
    pub end_max_k: u32,
}

/// Narrow an isolating interval until its width is at most `target`.
#[must_use]
pub fn obq_refine_to_width(
    p: &[BigInt],
    iv: &OBqInterval,
    target: &OBq,
) -> Option<(ORefined, ORefineTrace)> {
    let (r, t) = mpbq::refine_to_width(p, &iv.0, &target.0)?;
    let r = match r {
        mpbq::Refined::Exact(v) => ORefined::Exact(OBq(v)),
        mpbq::Refined::Narrowed(iv) => ORefined::Narrowed(OBqInterval(iv)),
    };
    Some((
        r,
        ORefineTrace {
            steps: t.steps,
            bound: t.bound,
            end_max_k: t.end_max_k,
        },
    ))
}

/// How two isolated roots compare once separated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OSeparation {
    /// Disjoint intervals; this is the exact order.
    Ordered(Ordering),
    /// The budget ran out with the intervals still overlapping.
    Inconclusive,
}

/// Refine two isolating intervals in lockstep until they are disjoint.
#[must_use]
pub fn obq_refine_until_separated(
    p: &[BigInt],
    a: &OBqInterval,
    q: &[BigInt],
    b: &OBqInterval,
    max_rounds: u32,
) -> Option<(OSeparation, OBqInterval, OBqInterval, u32)> {
    let (s, ia, ib, n) = mpbq::refine_until_separated(p, &a.0, q, &b.0, max_rounds)?;
    let s = match s {
        mpbq::Separation::Ordered(o) => OSeparation::Ordered(o),
        mpbq::Separation::Inconclusive => OSeparation::Inconclusive,
    };
    Some((s, OBqInterval(ia), OBqInterval(ib), n))
}

/// An integer strictly inside `(lo, hi)`, closest to zero.
#[must_use]
pub fn obq_select_int(lo: &OBq, hi: &OBq) -> Option<BigInt> {
    mpbq::select_int(&lo.0, &hi.0)
}

/// The simplest dyadic strictly inside the interval, with its derived ceiling.
#[must_use]
pub fn obq_select_small(iv: &OBqInterval) -> Option<(OBq, u32)> {
    mpbq::select_small(&iv.0).map(|s| (OBq(s.value), s.k_ceiling))
}

/// The candidate numerator at precision `k`, or `None` when the scaled interval
/// contains no integer strictly inside.
///
/// This is the NEGATIVE half of `select_small`'s minimality certificate: for an
/// answer at exponent `k > 0`, this must be `None` at `k - 1`.
#[must_use]
pub fn obq_candidate_at(iv: &OBqInterval, k: u32) -> Option<BigInt> {
    mpbq::candidate_at(&iv.0, k)
}

/// A simple dyadic strictly inside the interval that is not a root of `p`.
#[must_use]
pub fn obq_select_non_root(p: &[BigInt], iv: &OBqInterval) -> Option<OBq> {
    mpbq::select_non_root(p, &iv.0).map(OBq)
}

/// The smallest `2^-k`-grid interval containing `(lo, hi)`.
#[must_use]
pub fn obq_enclose_rational(lo: &BigRational, hi: &BigRational, k: u32) -> Option<OBqInterval> {
    mpbq::enclose_rational(lo, hi, k).map(OBqInterval)
}
