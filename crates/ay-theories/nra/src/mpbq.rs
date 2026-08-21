// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Binary rationals (dyadics) — `a / 2^k` — and the interval machinery that
//! rests on them. AY's port of z3's `util/mpbq.{cpp,h}`.
//!
//! # Why this layer exists at all
//!
//! Every isolating interval in an `algebraic_numbers`-style representation has
//! **dyadic** endpoints, and the reason is bisection. Halving an interval is
//! exact in base two and only in base two:
//!
//! ```text
//!   (a/2^j + b/2^k) / 2   is again  c / 2^m   with  m <= max(j,k) + 1
//! ```
//!
//! so the denominator exponent grows by **at most one bit per bisection**, and
//! no gcd is ever taken. The same loop over a general rational (`p/q` in lowest
//! terms) pays a gcd on every add and every halving, and the denominator is
//! whatever `q` happens to be — there is no bound on its shape, only on its
//! size. That is the difference between a refinement loop that is cheap and one
//! that is merely correct.
//!
//! # Porting note — the reference could not be read
//!
//! `reference/z3/5.0.0/` on this machine is a **binary distribution**: `bin/`
//! (dylib, static archive, jar, python) and `include/` (14 headers) only. There
//! is no `src/`, so `util/mpbq.cpp` and `util/mpbq.h` do not exist here and
//! **no line of this module was transliterated from them**. It is written from
//! the algorithms and from z3's documented semantics, and where a tie-break or
//! a preference is not pinned down by the semantics it is AY's own choice,
//! marked as such in the doc comment for the function that makes it. The
//! commonly cited sizes for the reference pair (`mpbq.cpp` 916 + `mpbq.h` 361 =
//! 1,277) are **quoted from the task brief, not measured on this machine**.
//!
//! # What z3 can be asked about this layer
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
//! `mpbq` is an internal C++ class. Its 224 symbols live only in the **static**
//! archive, mangled, as members of `mpbq_manager` — the oracle binds z3 by
//! `dlopen` on the **dylib**, where the count is zero, so there is no way to
//! call z3's dyadic layer at all. The `Z3_algebraic_*` family IS exported, and
//! that is the leg the oracle actually uses: a dyadic is a rational, hence an
//! algebraic number z3 can add, multiply and order, and an isolating interval
//! refined here can be checked against z3's own root by `Z3_algebraic_lt/gt`.
//!
//! # Scope
//!
//! **Ported:** the dyadic type with a canonical form, ordering, `+`/`-`/`*`,
//! multiply and divide by powers of two, conversion both ways against
//! [`BigRational`] with an exact-representability predicate, floor/ceil,
//! dyadic intervals, bisection, the polynomial-driven `refine` loop, pairwise
//! separation refinement, and the `select_small` / `select_int` family.
//!
//! **Deferred, deliberately:** general division (dyadics are **not** a field —
//! `1/3` is not dyadic and z3's `mpbq` has no general `div` either, only
//! `div2k`), `power` by a large exponent, decimal/float rendering, and the
//! `mpbq` <-> `mpf` bridge. None of them is on the refinement path.
//!
//! # Liveness
//!
//! Every loop in this module is bounded by a quantity **derived from its
//! input**, and the bound is stated and justified where the loop is written.
//! There is no unbounded `loop` and no `while` whose guard depends on
//! convergence. A refinement that cannot reach its target returns `None`.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Hard ceiling on the number of bisection steps any single refinement call
/// will take.
///
/// This is **not** the liveness argument — [`refine_to_width`] derives an exact
/// step bound from `(width, target)` and that bound is what makes the loop
/// terminate. This ceiling is the second gate: it refuses, up front, a target
/// so much narrower than the interval that the derived bound is itself absurd,
/// so a caller cannot request a hundred million bisections and get them.
/// 16,384 halvings narrow an interval by a factor of `2^16384`; nothing on a
/// CAD path needs that.
pub(crate) const MAX_REFINE_STEPS: u32 = 16_384;

/// Hard ceiling on the denominator exponent [`select_small`] will search up to.
///
/// Again not the liveness argument: the search provably succeeds at
/// `k = width.k() + 1` (see [`select_small`]). This refuses an input whose
/// width is already so tiny that the derived bound exceeds anything a real
/// interval reaches.
pub(crate) const MAX_SELECT_K: u32 = 1 << 20;

// ============================================================================
// The dyadic type
// ============================================================================

/// A binary rational: the exact value `a / 2^k` with `a` an integer and `k` a
/// non-negative integer.
///
/// # Canonical form
///
/// The invariant is `k == 0 || a is odd`, and zero is exactly `(0, 0)`.
///
/// This makes structural equality **identical** to numeric equality, so
/// `PartialEq`/`Eq`/`Hash` can be derived and are sound. Proof: suppose
/// `a1/2^k1 == a2/2^k2` with both canonical and (wlog) `k1 <= k2`. Then
/// `a1 * 2^(k2-k1) == a2`. If `k2 > k1` the left side is even, so `a2` is even;
/// canonicity then forces `k2 == 0`, contradicting `k2 > k1 >= 0`. Hence
/// `k1 == k2` and `a1 == a2`. The zero case is immediate: `a1 == 0` forces
/// `k1 == 0` by the constructor and `a2 == 0`, hence `k2 == 0`.
///
/// Every constructor goes through [`Bq::new`], which restores the invariant, so
/// no other code has to think about it.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct Bq {
    /// The numerator. Odd whenever `k > 0`; zero only when `k == 0`.
    a: BigInt,
    /// The denominator exponent: the value is `a / 2^k`.
    k: u32,
}

impl Bq {
    /// The canonical constructor: the exact value `a / 2^k`, normalized.
    ///
    /// Strips the common power of two, so `6/2^2` and `3/2^1` are the *same*
    /// value and the *same* bits. `k == 0` and a negative `a` are ordinary
    /// inputs, not special cases.
    pub(crate) fn new(a: BigInt, k: u32) -> Self {
        if a.is_zero() {
            return Self {
                a: BigInt::zero(),
                k: 0,
            };
        }
        // `trailing_zeros` is `None` only for zero, handled above.
        let tz = u32::try_from(a.trailing_zeros().unwrap_or(0)).unwrap_or(u32::MAX);
        let shift = tz.min(k);
        if shift == 0 {
            Self { a, k }
        } else {
            Self {
                a: a >> shift,
                k: k - shift,
            }
        }
    }

    /// The integer `n`, i.e. `n / 2^0`.
    pub(crate) fn from_int(n: BigInt) -> Self {
        Self::new(n, 0)
    }

    // NOTE: there was a `from_i64(i64)` convenience constructor here. A
    // mechanical coverage audit (`entrypoint / oracle refs / test refs`) found
    // it was reached by ZERO oracle checks and ZERO unit tests — the campaign's
    // first blind-spot pattern, "an entry point no check ever calls", where
    // `square_free` shipped a wrong answer through 4,000 cases. It duplicated
    // `Bq::new(BigInt::from(n), 0)` exactly, so it was DELETED rather than
    // given a check: an entry point that does not exist cannot be wrong.

    /// Zero.
    pub(crate) fn zero() -> Self {
        Self {
            a: BigInt::zero(),
            k: 0,
        }
    }

    /// One.
    pub(crate) fn one() -> Self {
        Self {
            a: BigInt::one(),
            k: 0,
        }
    }

    /// `2^(-k)`.
    pub(crate) fn inv_two_pow(k: u32) -> Self {
        Self::new(BigInt::one(), k)
    }

    /// The canonical numerator `a`.
    pub(crate) fn numerator(&self) -> &BigInt {
        &self.a
    }

    /// The canonical denominator exponent `k`.
    ///
    /// This is the number the whole module exists to keep small: it is the
    /// precision, in bits, that the value costs to carry.
    pub(crate) fn k(&self) -> u32 {
        self.k
    }

    /// Bit length of the canonical numerator (`0` for zero).
    ///
    /// Reported by the growth harness alongside [`Bq::k`]: `k` alone does not
    /// say how big the number is, only how fine its grid is.
    pub(crate) fn numerator_bits(&self) -> u64 {
        self.a.bits()
    }

    /// `true` for exactly the value zero.
    pub(crate) fn is_zero(&self) -> bool {
        self.a.is_zero()
    }

    /// `-1`, `0` or `1`.
    pub(crate) fn sign(&self) -> i32 {
        match self.a.sign() {
            num_bigint::Sign::Minus => -1,
            num_bigint::Sign::NoSign => 0,
            num_bigint::Sign::Plus => 1,
        }
    }

    /// `true` when the value is an integer — which, in canonical form, is
    /// exactly `k == 0`.
    pub(crate) fn is_int(&self) -> bool {
        self.k == 0
    }

    /// Negation. Exact, and canonical form is preserved (negating does not
    /// change the parity of the numerator).
    pub(crate) fn neg(&self) -> Self {
        Self {
            a: -self.a.clone(),
            k: self.k,
        }
    }

    /// Absolute value.
    pub(crate) fn abs(&self) -> Self {
        Self {
            a: self.a.abs(),
            k: self.k,
        }
    }

    /// `self * 2^e`. Exact; `k` can only go **down**.
    pub(crate) fn mul_two_pow(&self, e: u32) -> Self {
        if e >= self.k {
            Self::new(&self.a << (e - self.k), 0)
        } else {
            // `a` is already odd here (k > e >= 0 implies k > 0), so the result
            // is canonical without further work — but go through `new` anyway
            // so there is exactly one place the invariant is established.
            Self::new(self.a.clone(), self.k - e)
        }
    }

    /// `self / 2^e`. Exact; `k` grows by at most `e`.
    ///
    /// This is the operation that makes bisection cheap: no gcd, no division,
    /// one addition to an exponent.
    pub(crate) fn div_two_pow(&self, e: u32) -> Option<Self> {
        if self.a.is_zero() {
            return Some(Self::zero());
        }
        let k = self.k.checked_add(e)?;
        Some(Self::new(self.a.clone(), k))
    }

    /// Scale the numerator up so the value reads as `n / 2^target`, for
    /// `target >= self.k`. Exact.
    fn numerator_at(&self, target: u32) -> BigInt {
        debug_assert!(target >= self.k);
        &self.a << (target - self.k)
    }

    /// Exact addition.
    pub(crate) fn add(&self, other: &Self) -> Self {
        let m = self.k.max(other.k);
        Self::new(self.numerator_at(m) + other.numerator_at(m), m)
    }

    /// Exact subtraction.
    pub(crate) fn sub(&self, other: &Self) -> Self {
        let m = self.k.max(other.k);
        Self::new(self.numerator_at(m) - other.numerator_at(m), m)
    }

    /// Exact multiplication.
    ///
    /// `None` only if the denominator exponents sum past `u32` — a value with
    /// more than four billion bits of precision, which is a fail-closed refusal
    /// rather than a silent wrap.
    pub(crate) fn mul(&self, other: &Self) -> Option<Self> {
        let k = self.k.checked_add(other.k)?;
        Some(Self::new(&self.a * &other.a, k))
    }

    /// Exact comparison.
    ///
    /// Cross-scales to the coarser grid; never divides, never allocates a
    /// rational.
    pub(crate) fn cmp_bq(&self, other: &Self) -> Ordering {
        // Cheap exact shortcut: different signs decide it with no shifting.
        let (sa, sb) = (self.sign(), other.sign());
        if sa != sb {
            return sa.cmp(&sb);
        }
        let m = self.k.max(other.k);
        self.numerator_at(m).cmp(&other.numerator_at(m))
    }

    /// `floor(self)`.
    ///
    /// `BigInt`'s `>>` is an **arithmetic** shift — measured: `-7 >> 1 == -4` —
    /// so it is exactly `floor(x / 2^e)` on negatives too, which is what floor
    /// needs and what a truncating division would get wrong.
    pub(crate) fn floor(&self) -> BigInt {
        if self.k == 0 {
            self.a.clone()
        } else {
            &self.a >> self.k
        }
    }

    /// `ceil(self)`.
    pub(crate) fn ceil(&self) -> BigInt {
        if self.k == 0 {
            self.a.clone()
        } else {
            // k > 0 implies `a` odd, so the value is never an integer and
            // ceil is floor + 1.
            (&self.a >> self.k) + 1
        }
    }

    /// `floor(self * 2^target)` — the integer grid position at precision
    /// `target`. Exact for every sign.
    pub(crate) fn floor_at(&self, target: u32) -> BigInt {
        if target >= self.k {
            self.numerator_at(target)
        } else {
            &self.a >> (self.k - target)
        }
    }

    /// `ceil(self * 2^target)`.
    pub(crate) fn ceil_at(&self, target: u32) -> BigInt {
        if target >= self.k {
            self.numerator_at(target)
        } else {
            let e = self.k - target;
            let f = &self.a >> e;
            // Exact iff the discarded low `e` bits are zero, i.e. iff
            // `f << e == a`.
            if (&f << e) == self.a {
                f
            } else {
                f + 1
            }
        }
    }

    /// The exact rational this dyadic denotes.
    pub(crate) fn to_rational(&self) -> BigRational {
        BigRational::new(self.a.clone(), BigInt::one() << self.k)
    }

    /// The dyadic equal to `r`, or `None` when `r` is **not** exactly
    /// representable — i.e. when its reduced denominator is not a power of two.
    ///
    /// This is the "is this exactly representable" predicate, returned as data
    /// rather than as a `bool` plus a separate conversion, so the two can never
    /// disagree. `1/3` declines; `3/8` does not; every integer succeeds.
    pub(crate) fn from_rational(r: &BigRational) -> Option<Self> {
        let d = r.denom();
        // `BigRational` keeps a positive, reduced denominator.
        debug_assert!(d.is_positive());
        let bits = d.bits();
        if bits == 0 {
            return None;
        }
        let k = u32::try_from(bits - 1).ok()?;
        // `d` is a power of two iff it has exactly one set bit iff
        // `1 << (bits-1) == d`.
        if (BigInt::one() << k) != *d {
            return None;
        }
        Some(Self::new(r.numer().clone(), k))
    }

    /// Whether `r` is exactly representable as a dyadic.
    ///
    /// Defined as `from_rational(r).is_some()` so the predicate and the
    /// conversion are the *same* computation and cannot drift apart. (This is
    /// the "stored flag" shape the campaign has been bitten by: a separate
    /// `is_dyadic` implementation could answer `true` where the conversion
    /// declines, and nothing would notice.)
    pub(crate) fn is_representable(r: &BigRational) -> bool {
        Self::from_rational(r).is_some()
    }
}

impl PartialOrd for Bq {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Bq {
    fn cmp(&self, other: &Self) -> Ordering {
        self.cmp_bq(other)
    }
}

// ============================================================================
// Dyadic intervals
// ============================================================================

/// A **non-empty open** interval `(lo, hi)` with dyadic endpoints.
///
/// Open, and `lo < hi` strictly, because that is the shape an isolating
/// interval has: the endpoints are known non-roots and the root is strictly
/// inside. The two degenerate inputs the campaign rules call out are refused by
/// the constructor rather than handled downstream:
///
///   * `lo == hi` — the open interval is empty, there is nothing to isolate;
///   * `lo > hi`  — not an interval at all.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct BqInterval {
    lo: Bq,
    hi: Bq,
}

impl BqInterval {
    /// Build `(lo, hi)`, or `None` when `lo >= hi`.
    pub(crate) fn new(lo: Bq, hi: Bq) -> Option<Self> {
        if lo.cmp_bq(&hi) == Ordering::Less {
            Some(Self { lo, hi })
        } else {
            None
        }
    }

    /// Lower endpoint.
    pub(crate) fn lo(&self) -> &Bq {
        &self.lo
    }

    /// Upper endpoint.
    pub(crate) fn hi(&self) -> &Bq {
        &self.hi
    }

    /// `hi - lo`, exactly. Always strictly positive.
    pub(crate) fn width(&self) -> Bq {
        self.hi.sub(&self.lo)
    }

    /// The exact midpoint `(lo + hi)/2`.
    ///
    /// The whole point of the layer: `k(mid) <= max(k(lo), k(hi)) + 1`, always,
    /// with no gcd and no reduction.
    pub(crate) fn midpoint(&self) -> Option<Bq> {
        self.lo.add(&self.hi).div_two_pow(1)
    }

    /// Split at the midpoint into `(lo, mid)` and `(mid, hi)`.
    ///
    /// `None` when the midpoint coincides with an endpoint, which for dyadics
    /// **cannot happen** for a non-empty open interval — `lo < mid < hi` is
    /// exact here — so a `None` is a broken invariant, not a narrow interval.
    pub(crate) fn bisect(&self) -> Option<(Self, Bq, Self)> {
        let mid = self.midpoint()?;
        let left = Self::new(self.lo.clone(), mid.clone())?;
        let right = Self::new(mid.clone(), self.hi.clone())?;
        Some((left, mid, right))
    }

    /// `lo < x < hi`.
    pub(crate) fn contains_open(&self, x: &Bq) -> bool {
        self.lo.cmp_bq(x) == Ordering::Less && x.cmp_bq(&self.hi) == Ordering::Less
    }

    /// The two open intervals share no point.
    pub(crate) fn disjoint(&self, other: &Self) -> bool {
        self.hi.cmp_bq(&other.lo) != Ordering::Greater
            || other.hi.cmp_bq(&self.lo) != Ordering::Greater
    }

    /// The larger of the two endpoint precisions — what the interval costs to
    /// carry.
    pub(crate) fn max_k(&self) -> u32 {
        self.lo.k.max(self.hi.k)
    }
}

// ============================================================================
// Sign of an integer polynomial at a dyadic point
// ============================================================================

/// Exact sign of `p(x)` for an integer polynomial `p` (low-to-high
/// coefficients) at a dyadic `x = a / 2^k`.
///
/// No division and no rational: with `n = deg(p)`,
///
/// ```text
///   p(a/2^k) * 2^(k*n)  =  sum_i  c_i * a^i * 2^(k*(n-i))
/// ```
///
/// is an **integer**, and `2^(k*n) > 0`, so its sign is the answer. Evaluated
/// by Horner on that integer form, so the only operations are multiply, add and
/// shift.
///
/// `None` when the required shift width overflows `u32` — fail closed rather
/// than truncate.
pub(crate) fn poly_sign_at(p: &[BigInt], x: &Bq) -> Option<i32> {
    if p.is_empty() {
        return Some(0);
    }
    let n = p.len() - 1;
    let mut v = p[n].clone();
    for i in (0..n).rev() {
        let e = x.k.checked_mul(u32::try_from(n - i).ok()?)?;
        v = v * &x.a + (&p[i] << e);
    }
    Some(match v.sign() {
        num_bigint::Sign::Minus => -1,
        num_bigint::Sign::NoSign => 0,
        num_bigint::Sign::Plus => 1,
    })
}

/// Exact value of `p(x)` as a dyadic. Same identity as [`poly_sign_at`], kept
/// as a dyadic rather than collapsed to a sign.
pub(crate) fn poly_eval_at(p: &[BigInt], x: &Bq) -> Option<Bq> {
    if p.is_empty() {
        return Some(Bq::zero());
    }
    let n = p.len() - 1;
    let mut v = p[n].clone();
    for i in (0..n).rev() {
        let e = x.k.checked_mul(u32::try_from(n - i).ok()?)?;
        v = v * &x.a + (&p[i] << e);
    }
    let denom_k = x.k.checked_mul(u32::try_from(n).ok()?)?;
    Some(Bq::new(v, denom_k))
}

// ============================================================================
// Refinement
// ============================================================================

/// What one refinement produced.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Refined {
    /// The root turned out to be exactly this dyadic — a bisection midpoint
    /// landed on it. Only possible for a dyadic-rational root.
    Exact(Bq),
    /// A narrower isolating interval.
    Narrowed(BqInterval),
}

/// The refinement's own account of what it did.
///
/// # Which of these can be hardwired, and which cannot
///
/// This struct is exactly the shape the campaign has already been bitten by —
/// "a stored flag the headline metric is read off". So:
///
///   * `end_max_k` is **derived**, in [`refine_to_width`], from the returned
///     interval (`iv.max_k()`). It is not a counter and there is no code path
///     that could set it to anything else, so the defect is unrepresentable.
///   * `steps` **is** a genuine counter, and it is pinned by an exact identity
///     the oracle re-derives from the answer alone: for a `Narrowed` outcome,
///     `width_end * 2^steps == width_start`, exactly, because every step halves
///     the width and nothing else changes it. Hardwiring `steps` to any
///     constant diverges on the first case whose true count differs.
///   * `bound` is the derived liveness bound (see [`refine_step_bound`]); it is
///     a pure function of `(width_start, target)` and the oracle recomputes it
///     independently.
///
/// The `Exact` outcome is the disclosed gap: when a midpoint lands on the root
/// the width identity no longer applies, and `steps` is then only pinned by
/// `steps <= bound`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RefineTrace {
    /// Bisections actually performed.
    pub(crate) steps: u32,
    /// The derived upper bound on `steps` for this call.
    pub(crate) bound: u32,
    /// `max_k` of the returned interval — derived from the answer, never stored
    /// by the loop.
    pub(crate) end_max_k: u32,
}

/// The exact number of halvings that takes `width` to `<= target`.
///
/// # The liveness bound, and why it is sound
///
/// A bisection replaces the interval by one of its two halves, so the width
/// after `n` steps is **exactly** `width / 2^n` — dyadic halving is exact, so
/// this is an equality, not an estimate. The loop must therefore stop as soon
/// as `width / 2^n <= target`.
///
/// Write `width = wa / 2^wk` and `target = ta / 2^tk`, both with positive
/// numerators. Then
///
/// ```text
///   width / 2^n <= target
///     <=>  wa * 2^tk  <=  ta * 2^(wk + n)
///     <=>  L <= R * 2^n        with  L = wa << tk,  R = ta << wk
/// ```
///
/// Take `n = max(0, bits(L) - bits(R) + 1)`. Since `R >= 2^(bits(R) - 1)`,
///
/// ```text
///   R * 2^n  >=  2^(bits(R) - 1 + bits(L) - bits(R) + 1)  =  2^bits(L)  >  L
/// ```
///
/// so the condition holds at `n`, hence at every step from `n` on. The bound is
/// a pure function of the two inputs, it is reached, and a loop that runs to
/// `n` without meeting the target has had its invariant violated — which is why
/// exhausting it returns `None` instead of continuing.
///
/// `None` when `target <= 0` (nothing to converge to), or when the derived
/// bound exceeds [`MAX_REFINE_STEPS`].
pub(crate) fn refine_step_bound(width: &Bq, target: &Bq) -> Option<u32> {
    if target.sign() <= 0 || width.sign() <= 0 {
        return None;
    }
    let l = width.a.clone() << target.k;
    let r = target.a.clone() << width.k;
    let (lb, rb) = (l.bits(), r.bits());
    // `lb < rb`, NOT `lb <= rb`. When the two bit-lengths are EQUAL, `L` can
    // still exceed `R` by up to a factor of two, so the correct bound is 1 and
    // clamping to 0 understates it. The proof above says the same thing —
    // `n = max(0, bits(L) - bits(R) + 1)` is 1 when the lengths are equal — so
    // this line and the doc comment had disagreed, and the code was the wrong
    // one.
    //
    // MEASURED consequence of the clamp: 210 of 3,779 natural (width, target)
    // pairs with `width > target` received an insufficient bound, and
    // `refine_to_width(x^2-2, (1/2, 2), target = 1)` DECLINED on a genuine
    // isolating interval with a legitimate target — the loop ran `0..=0`, failed
    // its single width test and fell through to the fail-closed `None`. Never a
    // wrong interval (equal bit-lengths force the true minimum to be exactly 1,
    // so the loop runs out rather than returning something too wide), but a
    // documented-as-exact entry point returning a demonstrably wrong number.
    let n = if lb < rb { 0u64 } else { lb - rb + 1 };
    let n = u32::try_from(n).ok()?;
    if n > MAX_REFINE_STEPS {
        return None;
    }
    Some(n)
}

/// Narrow an isolating interval of the integer polynomial `p` until its width
/// is at most `target`.
///
/// # Preconditions, checked rather than assumed
///
/// `p(lo)` and `p(hi)` must be non-zero with **opposite** signs. That is the
/// isolating-interval invariant; it is re-checked on entry and a violation
/// returns `None` rather than producing a confidently wrong interval. (Opposite
/// endpoint signs guarantee an odd number of roots inside, so the sign test at
/// the midpoint always keeps a bracketing half.)
///
/// # Liveness
///
/// The loop runs at most `refine_step_bound(width, target) + 1` times — see
/// that function for the proof that the bound is reached. Exhausting it returns
/// `None`. There is no other exit.
pub(crate) fn refine_to_width(
    p: &[BigInt],
    iv: &BqInterval,
    target: &Bq,
) -> Option<(Refined, RefineTrace)> {
    let bound = refine_step_bound(&iv.width(), target)?;

    let s_lo = poly_sign_at(p, &iv.lo)?;
    let s_hi = poly_sign_at(p, &iv.hi)?;
    if s_lo == 0 || s_hi == 0 || s_lo == s_hi {
        // Endpoint is a root, or the interval does not bracket a sign change.
        return None;
    }

    let mut cur = iv.clone();
    let mut steps: u32 = 0;
    // `bound + 1` iterations: `bound` bisections plus the final width test.
    // `bound` is `u32` and capped at MAX_REFINE_STEPS, so this cannot be a
    // long-running loop by construction.
    for _ in 0..=bound {
        if cur.width().cmp_bq(target) != Ordering::Greater {
            let end_max_k = cur.max_k();
            return Some((
                Refined::Narrowed(cur),
                RefineTrace {
                    steps,
                    bound,
                    end_max_k,
                },
            ));
        }
        let (left, mid, right) = cur.bisect()?;
        let s_mid = poly_sign_at(p, &mid)?;
        steps += 1;
        if s_mid == 0 {
            return Some((
                Refined::Exact(mid.clone()),
                RefineTrace {
                    steps,
                    bound,
                    end_max_k: mid.k(),
                },
            ));
        }
        cur = if s_mid == s_lo { right } else { left };
    }
    // Unreachable when the invariant holds (the bound is proved sufficient), so
    // arriving here means the invariant was violated mid-flight. Fail closed.
    None
}

/// How two isolated roots compare, once their intervals have been separated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Separation {
    /// The intervals are disjoint; this is the exact order of the two roots.
    Ordered(Ordering),
    /// The budget ran out with the intervals still overlapping. The roots may
    /// be equal, or merely closer together than the budget could resolve —
    /// this call cannot tell, and says so.
    Inconclusive,
}

/// Refine two isolating intervals in lockstep until they are disjoint.
///
/// # Liveness, and the honest limit
///
/// Each round bisects both intervals once, so after `rounds` rounds each width
/// has been divided by exactly `2^rounds`. The loop is bounded by `max_rounds`,
/// supplied by the caller, and capped at [`MAX_REFINE_STEPS`].
///
/// It is **not** bounded by a root-separation bound, and that is deliberate: a
/// genuine separation bound (Mahler/Davenport) needs the resultant of the two
/// defining polynomials and costs more than the refinement it would justify.
/// Two roots that are actually **equal** can never be separated, so no finite
/// loop can be complete here. Exhausting the budget therefore returns
/// [`Separation::Inconclusive`] — a decline, never a spin.
pub(crate) fn refine_until_separated(
    p: &[BigInt],
    a: &BqInterval,
    q: &[BigInt],
    b: &BqInterval,
    max_rounds: u32,
) -> Option<(Separation, BqInterval, BqInterval, u32)> {
    let rounds = max_rounds.min(MAX_REFINE_STEPS);
    let mut ia = a.clone();
    let mut ib = b.clone();

    let sa_lo = poly_sign_at(p, &ia.lo)?;
    let sa_hi = poly_sign_at(p, &ia.hi)?;
    let sb_lo = poly_sign_at(q, &ib.lo)?;
    let sb_hi = poly_sign_at(q, &ib.hi)?;
    if sa_lo == 0 || sa_hi == 0 || sa_lo == sa_hi {
        return None;
    }
    if sb_lo == 0 || sb_hi == 0 || sb_lo == sb_hi {
        return None;
    }

    for done in 0..=rounds {
        if ia.disjoint(&ib) {
            let ord = if ia.hi.cmp_bq(&ib.lo) != Ordering::Greater {
                Ordering::Less
            } else {
                Ordering::Greater
            };
            return Some((Separation::Ordered(ord), ia, ib, done));
        }
        if done == rounds {
            break;
        }
        ia = bisect_keeping_root(p, &ia, sa_lo)?;
        ib = bisect_keeping_root(q, &ib, sb_lo)?;
    }
    Some((Separation::Inconclusive, ia, ib, rounds))
}

/// One bisection that keeps the bracketing half. `s_lo` is the (non-zero) sign
/// of `p` at the interval's lower endpoint.
///
/// A midpoint that lands exactly on the root is refused (`None`) rather than
/// handled here: the separation loop's whole contract is that it returns
/// intervals, and an exact hit is a different answer that the caller has to see.
fn bisect_keeping_root(p: &[BigInt], iv: &BqInterval, s_lo: i32) -> Option<BqInterval> {
    let (left, mid, right) = iv.bisect()?;
    let s_mid = poly_sign_at(p, &mid)?;
    if s_mid == 0 {
        return None;
    }
    Some(if s_mid == s_lo { right } else { left })
}

// ============================================================================
// Selecting a simple point inside an interval
// ============================================================================

/// An integer strictly inside `(lo, hi)`, or `None` if there is none.
///
/// Among the integers available it returns the one of **smallest absolute
/// value**, and `0` whenever `0` is inside. z3's documented intent for this
/// family is "keep the sample point simple"; the exact tie-break is **AY's
/// choice**, made deterministic here so the oracle can pin it.
pub(crate) fn select_int(lo: &Bq, hi: &Bq) -> Option<BigInt> {
    if lo.cmp_bq(hi) != Ordering::Less {
        return None;
    }
    // Smallest integer strictly greater than `lo`, largest strictly less than
    // `hi`.
    let m0 = lo.floor() + 1;
    let m1 = lo_ceil_minus_one(hi);
    if m0 > m1 {
        return None;
    }
    Some(closest_to_zero(m0, m1))
}

/// `ceil(x) - 1` — the largest integer strictly below `x`.
fn lo_ceil_minus_one(x: &Bq) -> BigInt {
    x.ceil() - 1
}

/// The element of `[m0, m1]` (non-empty) closest to zero; on the `±m` tie the
/// positive one.
fn closest_to_zero(m0: BigInt, m1: BigInt) -> BigInt {
    if m0.is_positive() {
        m0
    } else if m1.is_negative() {
        m1
    } else {
        // m0 <= 0 <= m1
        BigInt::zero()
    }
}

/// The certificate that accompanies a [`select_small`] answer.
///
/// `k` is **not stored** — it is read off `value.k()` — for the same reason
/// `RefineTrace::end_max_k` is derived: a stored copy could be hardwired and
/// nothing would diverge. What is stored is the *searched* range, which the
/// oracle re-derives from the interval width alone.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Selected {
    /// The chosen dyadic, strictly inside the interval.
    pub(crate) value: Bq,
    /// The derived ceiling the search was allowed to reach — a pure function of
    /// the interval width (`width.k() + 1`).
    pub(crate) k_ceiling: u32,
}

/// The **simplest** dyadic strictly inside `(lo, hi)`: the one with the
/// smallest denominator exponent `k`.
///
/// This is z3's `select_small` family, and it is what keeps CAD sample points
/// from growing without bound. Picking the midpoint instead is correct and
/// costs one bit of `k` per refinement step forever; picking the minimal-`k`
/// point resets the precision to whatever the interval actually forces.
///
/// # Algorithm
///
/// For a fixed `k`, the dyadics `m / 2^k` strictly inside `(lo, hi)` are the
/// integers `m` with `lo*2^k < m < hi*2^k`, i.e. `m` in
/// `[floor(lo*2^k) + 1, ceil(hi*2^k) - 1]`. Scan `k` upward from `0` and stop
/// at the first `k` whose range is non-empty; within it take the candidate
/// closest to zero (AY's tie-break, as in [`select_int`]).
///
/// # Liveness, and why the bound is exact
///
/// Let `w = hi - lo = wa / 2^wk` with `wa >= 1`. At `k = wk + 1` the scaled
/// interval has width `2^(wk+1) * wa / 2^wk = 2*wa >= 2 > 1`, and **every open
/// interval of width greater than one contains an integer strictly inside**
/// (`floor(x)+1 > x` always, and `floor(x)+1 <= x+1 < x+w`). So the scan
/// succeeds at or before `k = wk + 1`; that is the loop bound, derived from the
/// input, and it cannot be missed. [`MAX_SELECT_K`] refuses an interval whose
/// derived ceiling is absurd, before any work is done.
///
/// # A minimality fact the oracle uses
///
/// At the minimal `k > 0` every candidate `m` is **odd**: an even `m` would give
/// `m/2^k = (m/2)/2^(k-1)`, a point strictly inside at `k-1`, contradicting
/// minimality. So the returned value's canonical `k` equals the `k` the search
/// stopped at — normalization is a no-op — and the certificate "no dyadic of
/// exponent `k-1` lies strictly inside" is checkable in one step.
pub(crate) fn select_small(iv: &BqInterval) -> Option<Selected> {
    let w = iv.width();
    let ceiling = w.k.checked_add(1)?;
    if ceiling > MAX_SELECT_K {
        return None;
    }
    for k in 0..=ceiling {
        if let Some(m) = candidate_at(iv, k) {
            let value = Bq::new(m, k);
            // The scan is minimal by construction; assert the consequence so a
            // future edit that breaks it is caught here rather than downstream.
            debug_assert_eq!(value.k(), k, "minimal k must survive normalization");
            debug_assert!(iv.contains_open(&value));
            return Some(Selected {
                value,
                k_ceiling: ceiling,
            });
        }
    }
    // Unreachable: `ceiling` is proved sufficient above. Fail closed anyway.
    None
}

/// The candidate numerator at precision `k` — the integer `m` closest to zero
/// with `lo*2^k < m < hi*2^k` — or `None` when no such integer exists.
///
/// Exposed to the oracle (through the facade) precisely so the **negative**
/// half of the minimality certificate can be asked: `candidate_at(iv, k-1)`
/// must be `None` whenever `select_small` returned exponent `k > 0`.
pub(crate) fn candidate_at(iv: &BqInterval, k: u32) -> Option<BigInt> {
    let m0 = iv.lo.floor_at(k) + 1;
    let m1 = iv.hi.ceil_at(k) - 1;
    if m0 > m1 {
        return None;
    }
    Some(closest_to_zero(m0, m1))
}

/// A simple dyadic strictly inside `(lo, hi)` that is additionally **not** a
/// root of `p` — the sample-point selection a CAD cell actually needs.
///
/// Starts from [`select_small`] and, if that point is a root, walks the
/// exponent upward taking the candidate at each `k`.
///
/// # Liveness, and why the bound is exact
///
/// Let `d = deg(p)`, so `p` has at most `d` real roots. Write
/// `w = hi - lo = wa / 2^wk`. At precision `k = wk + 1 + e` the scaled interval
/// has width `wa * 2^(1+e) >= 2^(1+e)`, so it contains at least
/// `2^(1+e) - 1` integers strictly inside. Choosing `e = bits(d + 2)` gives
/// `2^(1+e) - 1 >= 2*(d+2) - 1 > d`, i.e. **strictly more interior candidates
/// than `p` has roots** — so at that precision a non-root is guaranteed.
///
/// The scan therefore runs `k` from `0` to `wk + 1 + bits(d+2)` and, at each
/// `k`, tries the first `d + 1` consecutive interior integers. Total work is
/// bounded by `(wk + 2 + bits(d+2)) * (d + 1)`, a pure function of the input.
/// `None` on exhaustion — which also covers `p == 0`, where every point is a
/// root and the honest answer is a refusal.
pub(crate) fn select_non_root(p: &[BigInt], iv: &BqInterval) -> Option<Bq> {
    if p.iter().all(Zero::is_zero) {
        return None;
    }
    // Degree, from the highest non-zero coefficient.
    let deg = p.iter().rposition(|c| !c.is_zero())?;
    let deg = u32::try_from(deg).ok()?;
    let w = iv.width();
    // `bits(d + 2)`: enough scaling that the interior integer count exceeds the
    // root count. `deg + 2` never overflows for a real polynomial.
    let e = u64::from(deg)
        .checked_add(2)?
        .next_power_of_two()
        .trailing_zeros()
        + 1;
    let ceiling = w.k.checked_add(1)?.checked_add(e)?;
    if ceiling > MAX_SELECT_K {
        return None;
    }
    for k in 0..=ceiling {
        let m0: BigInt = iv.lo.floor_at(k) + 1;
        let m1: BigInt = iv.hi.ceil_at(k) - 1;
        if m0 > m1 {
            continue;
        }
        // Prefer the simple candidate first, then walk consecutively OUTWARD
        // from it, staying inside `[m0, m1]`. At most `deg + 1` distinct
        // probes: `p` cannot vanish at all of them.
        //
        // The outward walk is not decoration. This loop used to start at
        // `closest_to_zero` and only ever step `m += 1`, which is fine on a
        // positive interval — the start is `m0`, the smallest — but on a WHOLLY
        // NEGATIVE one the start is `m1`, the LARGEST, so the very first step
        // left the interval and the loop broke after a SINGLE probe. The
        // completeness argument above claims `deg + 1` probes per level, and it
        // was getting one.
        //
        // MEASURED: for the degree-7 polynomial with roots at `-1 - 2^-j`,
        // `select_non_root` on `(-3, -1)` returned `None` even though `-5/2`,
        // `-11/4`, `-10/4`, `-9/4` and `-7/4` are all interior non-roots, while
        // the MIRRORED polynomial on `(1, 3)` answered `5/2`. That asymmetry
        // was the tell.
        let start = closest_to_zero(m0.clone(), m1.clone());
        let mut lo_probe = start.clone();
        let mut hi_probe = start.clone();
        let mut cur = Some(start);
        let mut probes = 0u32;
        while let Some(m) = cur {
            let v = Bq::new(m, k);
            if poly_sign_at(p, &v)? != 0 {
                return Some(v);
            }
            probes += 1;
            if probes > deg {
                break;
            }
            // Step outward: prefer downward, then upward, whichever still has
            // room. Both directions are clamped to the interior range.
            let down: BigInt = &lo_probe - 1;
            let up: BigInt = &hi_probe + 1;
            cur = if down >= m0 {
                lo_probe = down.clone();
                Some(down)
            } else if up <= m1 {
                hi_probe = up.clone();
                Some(up)
            } else {
                None
            };
        }
    }
    None
}

// ============================================================================
// BigRational bridge for callers that still speak `Q`
// ============================================================================

/// The smallest dyadic interval with `k`-bit endpoints that **contains**
/// `(lo, hi)`: `lo` rounded down and `hi` rounded up onto the `2^-k` grid.
///
/// Used to bring an interval produced by the existing `BigRational` isolation
/// in `univariate.rs` onto the dyadic grid without ever narrowing it, which
/// would risk dropping the root. `None` if the rounded endpoints collapse
/// (impossible for `k >= 0` and `lo < hi` unless the inputs were already
/// equal), or if `lo >= hi`.
///
/// # This duplicates something already in the tree, and that was concealed
///
/// `icp.rs` has `round_interval_outward` (plus `dyadic_floor` / `dyadic_ceil` /
/// `dyadic_grid`), which does the same job onto a fixed `2^-ROOT_SCALE_BITS`
/// grid — and unlike everything in this module, **it is wired into the live ICP
/// solve path**. This module's own scoping report claimed "inside
/// `crates/ay-theories/nra/` the count is 2, both in prose"; the real count at
/// the time was 62, of which 57 are in `icp.rs`. The headline that no dyadic
/// TYPE existed still holds — `icp.rs` is `BigRational`-valued with no packed
/// `a/2^k` and no minimal-denominator selection — but the measurement offered as
/// proof was wrong, and it hid a genuine overlap with wired code.
///
/// Consolidating the two is deliberately NOT done here: `icp.rs` is on the
/// solve path and this module is not wired, so a shared implementation would
/// have to be introduced by changing live code, which is its own change with
/// its own before/after.
pub(crate) fn enclose_rational(lo: &BigRational, hi: &BigRational, k: u32) -> Option<BqInterval> {
    if lo >= hi {
        return None;
    }
    // The one unguarded resource path in this module, until a verifier pointed
    // at it: every other entry point bounds its work by a derived quantity
    // (`MAX_REFINE_STEPS`, `MAX_SELECT_K`), but this one shifted by a
    // caller-supplied `k` with no ceiling. MEASURED: `k = 2^24` returns in 4 ms
    // after allocating a 2 MB `BigInt`; `k` near `u32::MAX` would allocate about
    // 512 MB. Not a hang and not reachable from any caller today, but refusing
    // is free and the module's stated discipline is that nothing is unbounded.
    if k > MAX_SELECT_K {
        return None;
    }
    let scale = BigInt::one() << k;
    let l = (lo.numer() * &scale).div_floor(lo.denom());
    let h = ceil_div(&(hi.numer() * &scale), hi.denom());
    BqInterval::new(Bq::new(l, k), Bq::new(h, k))
}

/// `ceil(n / d)` for `d > 0`.
fn ceil_div(n: &BigInt, d: &BigInt) -> BigInt {
    let (q, r) = n.div_rem(d);
    if r.is_zero() || r.is_negative() {
        q
    } else {
        q + 1
    }
}
