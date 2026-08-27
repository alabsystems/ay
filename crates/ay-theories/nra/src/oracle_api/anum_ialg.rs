// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ============================================================================
// `anum` — real algebraic numbers over dyadic isolating intervals
// ============================================================================

/// What a sign or comparison call did, for the oracle to pin the counters from.
///
/// `sep_bits` and `bound` are pure functions of the inputs and the oracle
/// recomputes both; `steps_*` are real counters pinned by the exact halving
/// identity; `equal_by_certificate` is pinned by `steps == 0`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OAnumTrace {
    /// Derived root-separation exponent, when refinement was needed.
    pub sep_bits: Option<u32>,
    /// Bisections on the first operand.
    pub steps_a: u32,
    /// Bisections on the second operand.
    pub steps_b: u32,
    /// Derived liveness bound.
    pub bound: u32,
    /// Answered by the gcd/Sturm equality certificate, with no refinement.
    pub equal_by_certificate: bool,
}

impl From<anum::AnumTrace> for OAnumTrace {
    fn from(t: anum::AnumTrace) -> Self {
        Self {
            sep_bits: t.sep_bits,
            steps_a: t.steps_a,
            steps_b: t.steps_b,
            bound: t.bound,
            equal_by_certificate: t.equal_by_certificate,
        }
    }
}

/// A real algebraic number over a DYADIC isolating interval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ODyadicAnum(anum::Anum);

impl ODyadicAnum {
    /// The unique root of `coeffs` inside `iv`, or `None` when `iv` does not
    /// isolate exactly one real root. This refusal is the check's whole point.
    #[must_use]
    pub fn from_poly_interval(coeffs: &[BigInt], iv: &OBqInterval) -> Option<Self> {
        anum::Anum::from_poly_interval(coeffs, &iv.0).map(Self)
    }

    /// The exact rational `r` as an algebraic number.
    #[must_use]
    pub fn rational(r: BigRational) -> Self {
        Self(anum::Anum::rational(r))
    }

    /// Is this the rational case?
    #[must_use]
    pub fn is_rational(&self) -> bool {
        self.0.is_rational()
    }

    /// The exact rational value, when there is one.
    #[must_use]
    pub fn to_rational(&self) -> Option<BigRational> {
        self.0.to_rational().cloned()
    }

    /// Degree of the defining polynomial (`1` for a rational).
    #[must_use]
    pub fn degree(&self) -> usize {
        self.0.degree()
    }

    /// The defining polynomial, low-to-high, for the algebraic case.
    #[must_use]
    pub fn poly_coeffs(&self) -> Option<Vec<BigInt>> {
        self.0.cell().map(|c| c.poly_coeffs().to_vec())
    }

    /// The dyadic isolating interval, for the algebraic case.
    #[must_use]
    pub fn interval(&self) -> Option<OBqInterval> {
        self.0.cell().map(|c| OBqInterval(c.interval().clone()))
    }

    /// The 1-based index among the ascending real roots of the defining
    /// polynomial. DERIVED on every call; never a stored field.
    #[must_use]
    pub fn root_index(&self) -> Option<usize> {
        self.0.cell().and_then(anum::AlgCell::root_index)
    }

    /// Narrow the isolating interval to at most `target`, preserving the
    /// invariant.
    #[must_use]
    pub fn refine(&self, target: &OBq) -> Option<Self> {
        self.0.refine(&target.0).map(Self)
    }

    /// Exact sign of the integer polynomial `q` at this number.
    #[must_use]
    pub fn sign_of_poly(&self, q: &[BigInt]) -> Option<i32> {
        self.0.sign_of_poly(q)
    }

    /// [`ODyadicAnum::sign_of_poly`] with the trace.
    #[must_use]
    pub fn sign_of_poly_traced(&self, q: &[BigInt]) -> Option<(i32, OAnumTrace)> {
        self.0.sign_of_poly_traced(q).map(|(s, t)| (s, t.into()))
    }

    /// Exact comparison.
    #[must_use]
    pub fn cmp_anum(&self, other: &Self) -> Option<Ordering> {
        self.0.cmp_anum(&other.0)
    }

    /// [`ODyadicAnum::cmp_anum`] with the trace.
    #[must_use]
    pub fn cmp_anum_traced(&self, other: &Self) -> Option<(Ordering, OAnumTrace)> {
        self.0.cmp_anum_traced(&other.0).map(|(o, t)| (o, t.into()))
    }

    /// Exact sum.
    #[must_use]
    pub fn add(&self, other: &Self) -> Option<Self> {
        self.0.add(&other.0).map(Self)
    }

    /// Exact product.
    #[must_use]
    pub fn mul(&self, other: &Self) -> Option<Self> {
        self.0.mul(&other.0).map(Self)
    }

    /// Exact negation.
    #[must_use]
    pub fn neg(&self) -> Option<Self> {
        self.0.neg().map(Self)
    }
}

/// The DERIVED root-separation exponent `B`: any two distinct real roots of the
/// square-free integer polynomial `coeffs` differ by more than `2^-B`.
///
/// Exposed as a **pure function**, deliberately. The campaign's fifth blind-spot
/// pattern is a pure function only ever tested through its consumer, where a
/// wrong branch can be structurally unreachable; this is the entry point the
/// oracle calls directly, on arbitrary inputs, and validates against z3's own
/// root list BEFORE any consumer runs.
#[must_use]
pub fn anum_root_separation_exponent(coeffs: &[BigInt]) -> Option<u32> {
    anum::root_separation_exponent(&upoly::ZPoly::from_coeffs(coeffs.to_vec()))
}

/// Distinct real roots of `coeffs` strictly inside `(lo, hi)`, by the
/// fraction-free Sturm chain over `Z`. `None` when an endpoint is a root — the
/// guard, exposed so it can be fired on purpose.
#[must_use]
pub fn anum_sturm_count_in(coeffs: &[BigInt], lo: &OBq, hi: &OBq) -> Option<usize> {
    let p = upoly::ZPoly::from_coeffs(coeffs.to_vec());
    let chain = anum::sturm_chain(&p)?;
    anum::sturm_count_in(&chain, &lo.0, &hi.0)
}

/// The square-free radical of `coeffs`, primitive with positive leading
/// coefficient: the defining-polynomial normal form.
#[must_use]
pub fn anum_normalize_defining(coeffs: &[BigInt]) -> Option<Vec<BigInt>> {
    anum::normalize_defining(&upoly::ZPoly::from_coeffs(coeffs.to_vec()))
        .map(|p| p.coeffs().to_vec())
}

/// The Cauchy bound: every real root of `coeffs` lies strictly inside `(-b, b)`.
#[must_use]
pub fn anum_cauchy_bound(coeffs: &[BigInt]) -> Option<BigInt> {
    anum::cauchy_bound_z(&upoly::ZPoly::from_coeffs(coeffs.to_vec()))
}

/// The ceiling on the derived separation exponent, above which the module
/// declines rather than spends.
#[must_use]
pub fn anum_max_separation_bits() -> u32 {
    anum::MAX_SEPARATION_BITS
}

/// Which path an arithmetic operation will take, and whether it can legitimately
/// decline. DIAGNOSTIC ONLY: `add` / `mul` answer identically whether or not this
/// is called.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OAnumOpDiag {
    /// No resultant is built: two rationals, or a zero operand.
    ClosedForm,
    /// The degree-preserving affine path for a dyadic rational operand.
    Affine,
    /// The resultant path, with the derived separation exponent.
    Resultant(u32),
    /// Above the declared ceiling: the ONLY legitimate decline.
    OverCeiling,
    /// Degenerate operand; the resultant cannot be built.
    Degenerate,
}

/// See [`OAnumOpDiag`]. `is_add` selects `+` over `*`.
#[must_use]
pub fn anum_binop_diag(a: &ODyadicAnum, b: &ODyadicAnum, is_add: bool) -> OAnumOpDiag {
    match anum::binop_diag(&a.0, &b.0, is_add) {
        anum::OpDiag::ClosedForm => OAnumOpDiag::ClosedForm,
        anum::OpDiag::Affine => OAnumOpDiag::Affine,
        anum::OpDiag::Resultant(b) => OAnumOpDiag::Resultant(b),
        anum::OpDiag::OverCeiling => OAnumOpDiag::OverCeiling,
        anum::OpDiag::Degenerate => OAnumOpDiag::Degenerate,
    }
}

// ============================================================================
// Interval sets over real algebraic endpoints (`crate::ialg`)
// ============================================================================

/// How simple a picked value is; see `ialg::Rung`. Ordered simplest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum OIRung {
    /// An integer.
    Integer,
    /// A rational with denominator at most [`oialg_max_simple_den`].
    Simple,
    /// A dyadic that is not already `Simple`.
    Dyadic,
    /// Any other exact rational.
    Rational,
    /// A genuine algebraic number.
    Algebraic,
}

impl From<ialg::Rung> for OIRung {
    fn from(r: ialg::Rung) -> Self {
        match r {
            ialg::Rung::Integer => Self::Integer,
            ialg::Rung::Simple => Self::Simple,
            ialg::Rung::Dyadic => Self::Dyadic,
            ialg::Rung::Rational => Self::Rational,
            ialg::Rung::Algebraic => Self::Algebraic,
        }
    }
}

/// The rung a value sits on, DERIVED — never a stored tag.
///
/// Exposed as a pure function on purpose: it is the metric the `pick` ladder is
/// judged by, and if `pick` returned a stored tag instead, the oracle would be
/// reading the answer off the very thing it is checking.
///
/// It classifies the REPRESENTATION, not the abstract value: a cell whose root
/// happens to be rational still classifies `Algebraic`, because the sign
/// evaluation it will cost is the cell's. See `ialg::Rung` for the measurement.
#[must_use]
pub fn oialg_classify_value(v: &ODyadicAnum) -> OIRung {
    ialg::classify_value(&v.0).into()
}

/// The sign condition a cell must satisfy.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OISignCond {
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

impl OISignCond {
    fn inner(self) -> ialg::SignCond {
        match self {
            Self::Lt => ialg::SignCond::Lt,
            Self::Le => ialg::SignCond::Le,
            Self::Eq => ialg::SignCond::Eq,
            Self::Ne => ialg::SignCond::Ne,
            Self::Ge => ialg::SignCond::Ge,
            Self::Gt => ialg::SignCond::Gt,
        }
    }

    /// Does sign `s` satisfy this condition? The predicate itself, so the
    /// oracle can judge the cells without reimplementing it.
    #[must_use]
    pub fn accepts(self, s: i32) -> bool {
        self.inner().accepts(s)
    }
}

/// One interval of an [`OIAlgSet`], flattened for inspection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OIAlgInterval {
    /// Lower endpoint, `None` for `-inf`.
    pub lo: Option<ODyadicAnum>,
    /// Is the lower endpoint open?
    pub lo_open: bool,
    /// Upper endpoint, `None` for `+inf`.
    pub hi: Option<ODyadicAnum>,
    /// Is the upper endpoint open?
    pub hi_open: bool,
    /// The literals justifying this interval, ascending.
    pub lits: Vec<i32>,
}

/// A union of disjoint intervals with real algebraic endpoints.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OIAlgSet(ialg::IntervalSet);

impl OIAlgSet {
    /// The empty set — the conflict signal.
    #[must_use]
    pub fn empty() -> Self {
        Self(ialg::IntervalSet::empty())
    }

    /// The whole line, justified by `lits`.
    #[must_use]
    pub fn full(lits: &[i32]) -> Option<Self> {
        Some(Self(ialg::IntervalSet::full(just_of(lits)?)))
    }

    /// Build from flattened intervals, normalising (sort, merge, drop empty).
    ///
    /// `None` when any endpoint comparison could not be decided, when an
    /// infinite endpoint is marked closed, or when a ceiling is exceeded.
    #[must_use]
    pub fn from_parts(parts: &[OIAlgInterval]) -> Option<Self> {
        let mut ivs = Vec::with_capacity(parts.len());
        for p in parts {
            let lo = match &p.lo {
                Some(a) => ialg::AEnd::Fin(a.0.clone()),
                None => ialg::AEnd::NegInf,
            };
            let hi = match &p.hi {
                Some(a) => ialg::AEnd::Fin(a.0.clone()),
                None => ialg::AEnd::PosInf,
            };
            if let Some(interval) =
                ialg::DecidedInterval::from_bounds(lo, p.lo_open, hi, p.hi_open, just_of(&p.lits)?)?
                    .into_interval()
            {
                ivs.push(interval);
            }
        }
        ialg::IntervalSet::normalize(ivs).map(Self)
    }

    /// Is the set empty? Exact by construction — see the `ialg` header.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// How many disjoint intervals.
    #[must_use]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// The intervals, ascending.
    #[must_use]
    pub fn intervals(&self) -> Vec<OIAlgInterval> {
        self.0
            .intervals()
            .iter()
            .map(|iv| OIAlgInterval {
                lo: iv.lo().value().cloned().map(ODyadicAnum),
                lo_open: iv.lo_open(),
                hi: iv.hi().value().cloned().map(ODyadicAnum),
                hi_open: iv.hi_open(),
                lits: iv.just().lits().to_vec(),
            })
            .collect()
    }

    /// Every literal responsible for the set.
    #[must_use]
    pub fn justification(&self) -> Option<Vec<i32>> {
        self.0.justification().map(|j| j.lits().to_vec())
    }

    /// Exact SET equality — same points, regardless of how the endpoints are
    /// represented or which literals justify them.
    ///
    /// The derived `PartialEq` on this type is STRUCTURAL and is NOT set
    /// equality; see `ialg::IntervalSet::same_set_as` for the two measured ways
    /// they come apart.
    #[must_use]
    pub fn same_set_as(&self, other: &Self) -> Option<bool> {
        self.0.same_set_as(&other.0)
    }

    /// Does the set contain `v`? `None` when undecided — never a guess.
    #[must_use]
    pub fn contains(&self, v: &ODyadicAnum) -> Option<bool> {
        self.0.contains(&v.0)
    }

    /// Union.
    #[must_use]
    pub fn union(&self, other: &Self) -> Option<Self> {
        self.0.union(&other.0).map(Self)
    }

    /// Intersection, keeping justifications.
    #[must_use]
    pub fn intersect(&self, other: &Self) -> Option<Self> {
        self.0.intersect(&other.0).map(Self)
    }

    /// Complement.
    #[must_use]
    pub fn complement(&self) -> Option<Self> {
        self.0.complement().map(Self)
    }

    /// `self \ other`.
    #[must_use]
    pub fn subtract(&self, other: &Self) -> Option<Self> {
        self.0.subtract(&other.0).map(Self)
    }

    /// A value in the set, as simple as the ladder can find. Every returned
    /// value has been VERIFIED to lie in the set before being returned.
    #[must_use]
    pub fn pick(&self) -> Option<ODyadicAnum> {
        self.0.pick().map(ODyadicAnum)
    }
}

fn just_of(lits: &[i32]) -> Option<ialg::Just> {
    let mut j = ialg::Just::none();
    for &l in lits {
        j = j.merge(&ialg::Just::of(l)?)?;
    }
    Some(j)
}

/// The feasible set of `p cond 0` given `p`'s real roots in ASCENDING order.
///
/// Root isolation is NOT repeated here; the roots are an argument precisely so
/// the oracle can drive this on z3's own root list rather than only through a
/// consumer.
#[must_use]
pub fn oialg_from_sign_condition(
    p: &[BigInt],
    roots: &[ODyadicAnum],
    cond: OISignCond,
    lits: &[i32],
) -> Option<OIAlgSet> {
    let rs: Vec<anum::Anum> = roots.iter().map(|r| r.0.clone()).collect();
    ialg::from_sign_condition(p, &rs, cond.inner(), just_of(lits)?).map(OIAlgSet)
}

/// The declared ceiling on intervals per set.
#[must_use]
pub fn oialg_max_intervals() -> usize {
    ialg::MAX_INTERVALS
}

/// The largest denominator the `Simple` rung will offer.
#[must_use]
pub fn oialg_max_simple_den() -> i64 {
    ialg::MAX_SIMPLE_DEN
}

/// The declared ceiling on literals per justification.
#[must_use]
pub fn oialg_max_just() -> usize {
    ialg::MAX_JUST
}
