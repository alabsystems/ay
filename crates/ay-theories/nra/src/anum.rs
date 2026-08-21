// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Real algebraic numbers over **dyadic** isolating intervals — the `anum`
//! layer of z3's `algebraic_numbers`, rebuilt on this crate's ported slices.
//!
//! # What this is, and what it is not
//!
//! Reference: z3's `src/math/polynomial/algebraic_numbers.{cpp,h}`. **MEASURED
//! TWICE: `reference/z3/5.0.0/` on this machine is a BINARY distribution
//! (`bin/` + `include/` only) — there is no `src/`.**
//!
//! ```text
//!   $ ls reference/z3/5.0.0/                          -> bin  include
//!   $ find reference/z3/5.0.0 -name 'algebraic*'      -> (nothing)
//! ```
//!
//! So this is a port from the *algorithms* and from z3's documented API
//! semantics, not a transcription. No line count is claimed for a file that
//! cannot be read here. What CAN be read is the exported surface —
//! `nm -gU reference/z3/5.0.0/bin/libz3.dylib | grep -c Z3_algebraic` is 21 —
//! and that is a real differential surface, which the oracle uses.
//!
//! # The representation
//!
//! An [`Anum`] is either
//!
//!   * an exact **rational** (z3's `anum` carries an `mpq` for this case), or
//!   * an [`AlgCell`]: a **square-free**, primitive, positive-leading-coefficient
//!     integer polynomial together with an **open dyadic** isolating interval
//!     `(lo, hi)` containing exactly one of its real roots, with both endpoints
//!     known non-roots.
//!
//! The dyadic endpoints are the point of the exercise. A bisection midpoint of
//! two dyadics is a dyadic whose precision grows by exactly one bit and needs no
//! gcd; the same bisection over `BigRational` reduces a fraction every step. The
//! residual MV QF_NRA witnesses this campaign is chasing — `52707179/2^24`,
//! `1686629713/2^30`, `6908435304717/2^42` — are literally dyadics, and past
//! `2^-40` no enumeration reaches them (see
//! the development design notes).
//!
//! # Every constructor refuses rather than trusts
//!
//! [`AlgCell::new`] recomputes a fraction-free **Sturm chain over `Z`** and
//! refuses any interval whose root count is not exactly one, or whose endpoints
//! are roots. A caller cannot assert an isolating interval into existence.
//!
//! # Liveness: every loop's bound, and why it is sound
//!
//! This module has exactly **three** loops that can run more than a fixed
//! number of times, and none of them is bounded by a guess:
//!
//!   1. [`sturm_chain`]'s remainder loop. Bound: `deg(p) + 1` iterations, and
//!      every iteration is *checked* to strictly decrease the degree
//!      (`next.degree() >= bd` fails closed). Falling out of the loop without
//!      reaching a constant returns `None`.
//!   2. [`mpbq::refine_to_width`], called from comparison, sign and arithmetic.
//!      Its bound is `mpbq::refine_step_bound(width, target)`, a pure function
//!      of the two widths with a proof in that module.
//!   3. The bisection inside [`mpbq::refine_to_width`] is the only bisection
//!      here; **this module performs no halving of its own.**
//!   4. The [`SEPARATION_RUNGS`] escalation ladder in [`AlgCell::cmp_cell`] and
//!      [`AlgCell::sign_of_poly_traced`]. Bound: `SEPARATION_RUNGS.len() + 2`
//!      iterations, a compile-time constant, because every rung is clamped to
//!      the proved separation exponent and the iteration after the clamped rung
//!      exits unconditionally. Each iteration performs at most one
//!      [`mpbq::refine_to_width`] per side, itself bounded by (2). The ladder
//!      therefore adds a **fixed** number of iterations, not an open-ended
//!      search, and it never refines past the precision the separation bound
//!      proves sufficient.
//!
//! The dangerous case the campaign named — comparing two **equal** algebraic
//! numbers, which no amount of refinement can separate — is decided **before
//! any refinement happens**, by a gcd/Sturm certificate
//! ([`AlgCell::cmp_cell`]). Equal inputs perform **zero** bisections. Unequal
//! inputs are refined toward a target width derived from
//! [`root_separation_exponent`] — a Mahler/Davenport separation bound — so the
//! number of bisections is a *derived* quantity, not a budget that guesses.
//!
//! # Why the refinement is reached by a ladder, MEASURED
//!
//! The separation bound is *proved* sufficient but exponentially conservative,
//! and obeying it literally was where nearly all the time went.
//! `anum_profile_cmp_phases` (load 8.66) split one `cmp_anum` on two distinct
//! algebraic numbers into its phases:
//!
//! ```text
//!   pair                      gcd  cert  radical  sep-bound  refine  TOTAL
//!   3+sqrt2 vs 6+sqrt3        4us   0us     21us        0us    57us   75us
//!   deg8: 2^(1/8) vs 7^(1/8)  2us   0us     19us        0us   363us  398us
//! ```
//!
//! The exponent itself cost **0 us** — it is integer bit lengths. The
//! REFINEMENT it mandated was 76-95% of the call: 42 to 232 bisections, where
//! the number that actually made the two isolating intervals disjoint was
//! **0 to 3**. So the two named suspects were half right: the bound was never
//! expensive to compute, only to obey.
//!
//! The ladder refines in geometrically growing steps and stops at the first rung
//! that admits an exact decision. It is free in the worst case: each rung
//! continues from the previous rung's interval, and dyadic halving is exact, so
//! the cumulative bisection count to reach `2^-k` equals the count one direct
//! call to `2^-k` would make.
//!
//! # What `algebraic.rs` already does, measured
//!
//! `crates/ay-theories/nra/src/algebraic.rs` (1,385 lines) already ships
//! `RealAlgebraic` with `BigRational` intervals: `sign_of_poly` (`:268`),
//! `cmp_number` (`:319`), and cross-point `add`/`mul` via **Sylvester
//! determinants plus Lagrange interpolation** (`sylvester_det_fixed` `:1061`,
//! `lagrange_interpolate` `:1115`). This module deliberately does **not**
//! duplicate that. What it adds, and only that:
//!
//!   * dyadic (`a/2^k`) intervals instead of `BigRational` ones;
//!   * a fraction-free Sturm chain over `Z` evaluated by integer shifts
//!     ([`mpbq::poly_sign_at`]) instead of a `BigRational` remainder chain;
//!   * **derived** liveness bounds from a root-separation bound, replacing
//!     `algebraic.rs`'s `MAX_REFINE_STEPS = 4096` magic constant (`:50`), which
//!     is a guess: it is neither necessary nor sufficient for any particular
//!     input;
//!   * resultants by the **fraction-free subresultant PRS**
//!     ([`crate::subresultant::resultant`]) instead of `mn + 1` Sylvester
//!     determinant evaluations followed by Lagrange interpolation.
//!
//! # Deferred, deliberately
//!
//!   * **Minimality of the defining polynomial.** z3 factors over `Z` (Hensel
//!     lifting) and keeps an irreducible factor, so a rational root always
//!     collapses to the rational case. `upoly` ships factoring over `Z_p` only,
//!     so this module collapses to a rational exactly when the square-free
//!     defining polynomial has degree 1. A rational root hiding inside a
//!     higher-degree square-free polynomial stays in algebraic form. That is
//!     **sound but not canonical**: comparison still answers `Equal` correctly
//!     through the gcd certificate, and the oracle checks exactly that.
//!   * **Division, reciprocal, root extraction.** `algebraic.rs` has `recip`
//!     (`:379`) already; nothing here would be new.
//!   * **`root-obj` printing.** `algebraic.rs::to_smtlib` (`:415`) does it.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::mpbq::{self, Bq, BqInterval, Refined};
// NOTE: `ExactRing` is deliberately NOT imported. It is implemented for
// `BigInt`, so bringing it into scope makes every `BigInt::zero()`,
// `BigInt::one()` and `x.is_zero()` in this file ambiguous between it and
// `num_traits`. The two resultant builders accumulate `(Mono, BigInt)` term
// vectors and hand them to `MPolyZ::from_terms`, which needs no trait method.
use crate::subresultant::{self, MPolyZ, Mono, RPoly};
use crate::upoly::ZPoly;

/// Hard ceiling on the DERIVED separation exponent this module will act on.
///
/// This is **not** the liveness argument — [`root_separation_exponent`] returns
/// an exponent that is *proved* sufficient, and that exponent is what bounds the
/// refinement. This ceiling refuses, up front, an input whose proved bound is so
/// large that acting on it would burn unbounded time: a degree-40 polynomial
/// with 200-bit coefficients has a Mahler bound near 2^-8500, and honestly
/// declining beats spending minutes to answer.
///
/// A `None` from this ceiling is a **decline**, which the oracle counts
/// separately from a divergence and separately from a match.
pub(crate) const MAX_SEPARATION_BITS: u32 = 8_192;

/// Hard ceiling on `deg(p) * deg(q)` — the degree of the resultant an ADDITION
/// is about to build.
///
/// # Why this is separate from [`MAX_SEPARATION_BITS`], MEASURED
///
/// The separation ceiling is checked on the resultant, so it can only refuse
/// AFTER the resultant has been computed. That is too late: measured by
/// `ay-nra-oracle anum-growth --cases 20000` (load average 10.57), an addition
/// at base degree 9 whose resultant would have degree 729 spent **446.6
/// seconds** building it and then declined on the separation ceiling anyway.
/// Not a hang — it returned — but seven and a half minutes to say `None` is
/// indistinguishable from one at any human time scale.
///
/// 256 admits every addition the sweep completed (the largest was degree 64 in
/// 2.5 s) and refuses the 343 that cost 8.6 s and the 729 that cost 446 s —
/// both of which were going to decline anyway.
pub(crate) const MAX_ADD_RESULTANT_DEGREE: usize = 256;

/// The same ceiling for MULTIPLICATION, which is measurably cheaper at equal
/// degree and therefore gets four times the budget.
///
/// `q(z - y)` expands to a DENSE bivariate with `O(n^2)` terms; `y^n q(z/y)` is
/// the same coefficients rearranged, `n + 1` terms, sparse. At the identical raw
/// resultant degree of 729 the same sweep measured
///
/// ```text
///   mul  ->  19.9 s, succeeded, radical degree 81
///   add  -> 446.6 s, declined
/// ```
///
/// a 22x difference from the operand shape alone. A single ceiling either
/// refuses the 19.9 s success or admits the 446 s failure; two ceilings do
/// neither.
pub(crate) const MAX_MUL_RESULTANT_DEGREE: usize = 1_024;

/// The `MPolyZ` variable index used for the outer variable of a resultant.
const OUTER: subresultant::MVar = 0;

// ============================================================================
// Fraction-free Sturm chains over Z, evaluated at dyadic points
// ============================================================================

/// The Sturm chain of a square-free integer polynomial, over `Z`.
///
/// `S_0 = p`, `S_1 = pp(p')`, `S_{k+1} = -prem(S_{k-1}, S_k)` reduced to its
/// primitive part and corrected for the **sign** of the pseudo-division's
/// `lc(S_k)^d` factor. Only positive rescalings are applied after that
/// correction, so the sign sequence — the only thing Sturm's theorem reads — is
/// unchanged, while the coefficients stay as small as a primitive part allows.
///
/// This is what makes the chain usable at all: a plain Euclidean chain over `Q`
/// (what `univariate::sturm_sequence` builds) grows coefficient denominators
/// multiplicatively.
///
/// # Liveness
///
/// The loop runs at most `deg(p) + 1` times, and each iteration is **checked**
/// to strictly decrease the degree of the last element. Since degrees are
/// non-negative and start at `deg(p) - 1`, a correct run reaches a constant
/// well inside the bound; exhausting it means the invariant broke, and the
/// function returns `None` rather than continuing with a truncated chain.
///
/// `None` for degree < 1, a vanishing derivative, or any non-exact division.
pub(crate) fn sturm_chain(p: &ZPoly) -> Option<Vec<ZPoly>> {
    let d = p.degree()?;
    if d < 1 {
        return None;
    }
    let dp = p.derivative();
    if dp.is_zero() {
        return None;
    }
    let mut chain = vec![p.clone(), dp.primitive_part()?];
    let mut finished = false;
    for _ in 0..=d {
        let n = chain.len();
        let bd = chain[n - 1].degree()?;
        if bd == 0 {
            finished = true;
            break;
        }
        let pd = chain[n - 2].pseudo_div(&chain[n - 1])?;
        if pd.r.is_zero() {
            // `p` square-free makes this unreachable (the chain ends at a
            // non-zero constant), but a non-square-free input would land here
            // and must not be silently accepted.
            finished = true;
            break;
        }
        // `lc(b)^pd.d * a = q*b + r`, so the true remainder is `r` divided by
        // `lc(b)^pd.d`, whose SIGN is `sign(lc(b))^pd.d`. Sturm wants
        // `-rem(a, b)` up to a POSITIVE multiple.
        let mut next = pd.r.neg();
        if chain[n - 1].lc()?.is_negative() && pd.d % 2 == 1 {
            next = next.neg();
        }
        // `content()` is non-negative, so the primitive part keeps the sign.
        let next = next.primitive_part()?;
        if next.degree()? >= bd {
            return None;
        }
        chain.push(next);
    }
    if !finished {
        return None;
    }
    Some(chain)
}

/// Number of sign changes in the chain at a dyadic point, zeros skipped.
pub(crate) fn sturm_sign_changes(chain: &[ZPoly], x: &Bq) -> Option<usize> {
    let mut changes = 0usize;
    let mut last = 0i32;
    for q in chain {
        let s = mpbq::poly_sign_at(q.coeffs(), x)?;
        if s == 0 {
            continue;
        }
        if last != 0 && s != last {
            changes += 1;
        }
        last = s;
    }
    Some(changes)
}

/// Number of distinct real roots of `chain[0]` in the open interval `(lo, hi)`.
///
/// # The endpoint guard, and why it is not decoration
///
/// Sturm's theorem counts roots in `(lo, hi]` and is stated for endpoints that
/// are **not** roots; with a root endpoint the two readings differ by one and
/// the answer is silently off. This refuses (`None`) instead. Callers in this
/// module all arrange non-root endpoints by an argument, so a `None` here means
/// a broken invariant — but the check is what makes that true rather than
/// hoped.
pub(crate) fn sturm_count_in(chain: &[ZPoly], lo: &Bq, hi: &Bq) -> Option<usize> {
    let p = chain.first()?;
    if lo.cmp_bq(hi) != Ordering::Less {
        return None;
    }
    if mpbq::poly_sign_at(p.coeffs(), lo)? == 0 || mpbq::poly_sign_at(p.coeffs(), hi)? == 0 {
        return None;
    }
    let vlo = sturm_sign_changes(chain, lo)?;
    let vhi = sturm_sign_changes(chain, hi)?;
    vlo.checked_sub(vhi)
}

// ============================================================================
// The root separation bound — the liveness argument
// ============================================================================

/// Bit length of a `u64` (`0` for zero).
fn bit_len(v: u64) -> u64 {
    64 - u64::from(v.leading_zeros())
}

/// An exponent `B` such that **any two distinct real roots** of the square-free
/// integer polynomial `p` differ by strictly more than `2^-B`.
///
/// # The bound
///
/// Mahler's separation bound: for square-free `p` of degree `n >= 2`,
///
/// ```text
///   sep(p)  >  sqrt(3) * n^(-(n+2)/2) * M(p)^(1-n)
/// ```
///
/// with `M(p)` the Mahler measure, and `M(p) <= ||p||_2 <= sqrt(n+1) * H` where
/// `H = max |c_i|`. Taking `log2` and dropping `log2(sqrt 3) > 0`:
///
/// ```text
///   -log2 sep  <  ((n+2)/2) log2 n  +  (n-1) (log2 H + (1/2) log2(n+1))
/// ```
///
/// Every term on the right is replaced by an integer over-estimate — `log2 n` by
/// `bits(n)`, `log2 H` by `bits(H)`, and each halving dropped — so
///
/// ```text
///   B = (n+2)*bits(n) + (n-1)*(bits(H) + bits(n+1)) + 2
/// ```
///
/// satisfies `2^-B < sep(p)`. **No floating point anywhere**: the derivation is
/// on paper and the computation is integer bit lengths.
///
/// Degree `< 2` returns `0`: such a polynomial has at most one real root, so
/// there is no pair to separate and any bound is vacuously true.
///
/// `None` when the derived exponent exceeds [`MAX_SEPARATION_BITS`] — a
/// decline, never a silent truncation.
pub(crate) fn root_separation_exponent(p: &ZPoly) -> Option<u32> {
    let n = p.degree()?;
    if n < 2 {
        return Some(0);
    }
    let hbits = p.coeffs().iter().map(BigInt::bits).max()?.max(1);
    let nu = u64::try_from(n).ok()?;
    let nbits = bit_len(nu);
    let n1bits = bit_len(nu + 1);
    let b = (nu + 2)
        .checked_mul(nbits)?
        .checked_add((nu - 1).checked_mul(hbits.checked_add(n1bits)?)?)?
        .checked_add(2)?;
    let b = u32::try_from(b).ok()?;
    if b > MAX_SEPARATION_BITS {
        return None;
    }
    Some(b)
}

/// The separation exponent for the pair `(a, b)`, both **square-free**, whose
/// gcd is `g`.
///
/// # Why this is not just `root_separation_exponent(normalize_defining(a*b))`
///
/// MEASURED (`anum_profile_cmp_phases`, load 16.54): of the 70 us one
/// `cmp_anum` spent on `3+sqrt2` vs `6+sqrt3`, the square-free radical of the
/// PRODUCT was 17 us — 24% — and the exponent itself was **0 us**. The Yun
/// decomposition is the expensive half of "compute the separation bound", and
/// it is unnecessary in the common case:
///
///   * `a` and `b` are each square-free (every [`AlgCell`] normalizes, and
///     `sign_of_poly` takes a radical);
///   * when `deg(g) == 0` they are coprime, and a product of coprime square-free
///     polynomials is square-free.
///
/// So `a * b` is **already** in the form Mahler's bound is stated for, and
/// taking the radical is a no-op that costs a full Yun run. Primitivity is not
/// needed either: [`root_separation_exponent`] reads `H = max |c_i|`, and
/// scaling a polynomial by a positive integer multiplies its Mahler measure by
/// that integer, which — since the exponent `1 - n` is negative — only makes the
/// derived `B` LARGER. A larger `B` is a weaker, still-sound separation bound.
/// Roots are unchanged by the scaling, so nothing else moves.
///
/// When `deg(g) >= 1` the product genuinely has repeated roots and the radical
/// is taken, exactly as before.
fn separation_exponent_for_pair(a: &ZPoly, b: &ZPoly, g: &ZPoly) -> Option<u32> {
    let prod = a.mul(b);
    if g.degree()? == 0 {
        return root_separation_exponent(&prod);
    }
    root_separation_exponent(&normalize_defining(&prod)?)
}

/// The escalation ladder for the separation search, in bits of precision.
///
/// # Why a ladder, MEASURED
///
/// The Mahler/Davenport exponent is *proved* sufficient but is exponentially
/// conservative. `anum_profile_cmp_phases` (load 16.54) measured, over seven
/// representative pairs, a derived exponent of 38-227 bits driving 42-232
/// bisections — while the number of bisections that actually made the two
/// isolating intervals disjoint was **0, 0, 0, 0, 1, 2, 3**. The refinement was
/// 76-95% of the whole call, so the bound was not expensive to COMPUTE; it was
/// expensive to OBEY.
///
/// This ladder is not a liveness bound and not a budget. It is a fixed,
/// 15-entry escalation schedule — the same shape as `ialg::BRACKET_KS` — and
/// every rung is **clamped to the proved exponent**, so the last rung actually
/// attempted is always the one today's code would have gone to directly. The
/// guarantee is therefore unchanged; only the order of work changed.
///
/// The extra work in the worst case is 15 interval comparisons, because
/// bisection is monotone: refining from the previous rung's interval rather
/// than from the original means the cumulative number of bisections to reach
/// `2^-k` is *exactly* the number a single direct call would make. Halving is
/// exact, so the width after `n` halvings is exactly `w / 2^n` regardless of how
/// the halvings were grouped.
const SEPARATION_RUNGS: [u32; 15] = [
    0, 1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192,
];

/// A strict upper bound on `|root|` for every real root of `p`: the Cauchy
/// bound `1 + max|c_i| / |lc|`, rounded up to an integer.
pub(crate) fn cauchy_bound_z(p: &ZPoly) -> Option<BigInt> {
    let lc = p.lc()?.abs();
    if lc.is_zero() {
        return None;
    }
    let hmax = p.coeffs().iter().map(BigInt::abs).max()?;
    Some(hmax.div_ceil(&lc) + BigInt::one())
}

// ============================================================================
// Normalization
// ============================================================================

/// The square-free radical of `p`, primitive with a positive leading
/// coefficient: exactly the defining-polynomial normal form.
///
/// Uses [`ZPoly::square_free_decomposition`] (Yun over `Z`, from the `upoly`
/// slice) and multiplies the distinct factors back together. The factors are
/// pairwise coprime and individually square-free, so the product is square-free
/// and has precisely the distinct roots of `p`.
///
/// `None` for the zero polynomial and for a non-zero constant (neither defines
/// an algebraic number).
pub(crate) fn normalize_defining(p: &ZPoly) -> Option<ZPoly> {
    let decomp = p.square_free_decomposition()?;
    let mut rad = ZPoly::one();
    for (f, _) in &decomp.factors {
        rad = rad.mul(f);
    }
    if rad.degree()? < 1 {
        return None;
    }
    let (_, pp) = rad.split_content()?;
    Some(pp)
}

/// Divide out the largest power of `x`, leaving a polynomial with a non-zero
/// constant term and exactly the non-zero roots of `p`.
fn strip_zero_roots(p: &ZPoly) -> Option<ZPoly> {
    let c = p.coeffs();
    let k = c.iter().position(|x| !x.is_zero())?;
    Some(ZPoly::from_coeffs(c[k..].to_vec()))
}

// ============================================================================
// The cell
// ============================================================================

/// A real algebraic number in the non-rational representation: a square-free
/// integer polynomial plus a dyadic isolating interval.
///
/// The Sturm chain is cached because every operation needs it and recomputing it
/// per call dominates; it is **derived from `p` alone** and never set
/// independently, so it cannot drift.
#[derive(Clone, Debug)]
pub(crate) struct AlgCell {
    /// Square-free, primitive, positive leading coefficient, degree >= 1.
    p: ZPoly,
    /// Open dyadic interval containing exactly one root of `p`; neither
    /// endpoint is a root.
    iv: BqInterval,
    /// Sturm chain of `p`, derived in the constructor.
    chain: Vec<ZPoly>,
}

impl PartialEq for AlgCell {
    fn eq(&self, other: &Self) -> bool {
        // Structural, NOT numeric. Two cells that denote the same number can
        // have different intervals; `Anum::cmp_anum` is the numeric test and
        // nothing here may be mistaken for it.
        self.p == other.p && self.iv == other.iv
    }
}

impl Eq for AlgCell {}

impl AlgCell {
    /// Build from an arbitrary integer polynomial and a dyadic interval.
    ///
    /// The polynomial is normalized (square-free radical, primitive, positive
    /// leading coefficient) and the interval is then **verified**: exactly one
    /// root strictly inside, neither endpoint a root. Anything else is `None`.
    pub(crate) fn new(p: &ZPoly, iv: &BqInterval) -> Option<Self> {
        Self::from_normalized(normalize_defining(p)?, iv.clone())
    }

    /// Same verification, for a polynomial already in normal form.
    fn from_normalized(p: ZPoly, iv: BqInterval) -> Option<Self> {
        let chain = sturm_chain(&p)?;
        // Endpoint-is-a-root is refused here rather than inside `sturm_count_in`
        // so the two failure modes stay distinguishable to a reader.
        if mpbq::poly_sign_at(p.coeffs(), iv.lo())? == 0
            || mpbq::poly_sign_at(p.coeffs(), iv.hi())? == 0
        {
            return None;
        }
        if sturm_count_in(&chain, iv.lo(), iv.hi())? != 1 {
            return None;
        }
        Some(Self { p, iv, chain })
    }

    /// The defining polynomial's integer coefficients, low-to-high.
    pub(crate) fn poly_coeffs(&self) -> &[BigInt] {
        self.p.coeffs()
    }

    /// The current dyadic isolating interval.
    pub(crate) fn interval(&self) -> &BqInterval {
        &self.iv
    }

    /// Degree of the defining polynomial.
    pub(crate) fn degree(&self) -> usize {
        self.p.degree().unwrap_or(0)
    }

    /// The 1-based index of this root among the ascending real roots of the
    /// defining polynomial.
    ///
    /// **DERIVED on every call** from `(p, iv)` by a Sturm count below `lo`, and
    /// deliberately not a stored field. The campaign's third blind-spot pattern
    /// is "a stored flag the headline metric is read off, hardwireable with no
    /// divergence"; storing an index here would be exactly that shape, so the
    /// defect is made unrepresentable instead of merely tested for.
    pub(crate) fn root_index(&self) -> Option<usize> {
        let b = cauchy_bound_z(&self.p)?;
        let below = Bq::from_int(-(b + BigInt::one()));
        Some(sturm_count_in(&self.chain, &below, self.iv.lo())? + 1)
    }

    /// Narrow the isolating interval to width at most `target`, preserving the
    /// invariant. An exact hit collapses to the rational.
    ///
    /// Liveness: `mpbq::refine_to_width` derives its own step bound from
    /// `(width, target)`; there is no loop here.
    pub(crate) fn refine(&self, target: &Bq) -> Option<Anum> {
        let (r, _) = mpbq::refine_to_width(self.p.coeffs(), &self.iv, target)?;
        match r {
            Refined::Exact(m) => Some(Anum::Rational(m.to_rational())),
            Refined::Narrowed(iv) => {
                // Re-verified, not assumed: the narrowed interval goes back
                // through the same constructor every caller uses.
                Some(Anum::Alg(Self::from_normalized(self.p.clone(), iv)?))
            }
        }
    }

    /// Collapse to the rational case when the defining polynomial is linear.
    fn collapse(self) -> Anum {
        if self.p.degree() == Some(1) {
            let c = self.p.coeffs();
            return Anum::Rational(BigRational::new(-c[0].clone(), c[1].clone()));
        }
        Anum::Alg(self)
    }
}

/// What a sign / comparison call actually did.
///
/// # Which of these can be hardwired
///
/// `bound` and `sep_bits` are **pure functions of the inputs** — the oracle
/// recomputes both independently through the facade. `steps` is a real counter
/// but is pinned by the exact identity `width_end * 2^steps == width_start`,
/// which the oracle re-derives from the answer alone. `equal_by_certificate` is
/// pinned by `steps == 0`: the certificate path performs no bisection, so
/// claiming it falsely is observable.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub(crate) struct AnumTrace {
    /// The derived separation exponent that bounded the refinement, when one
    /// was needed.
    pub(crate) sep_bits: Option<u32>,
    /// Bisections performed on the first operand.
    pub(crate) steps_a: u32,
    /// Bisections performed on the second operand (0 for unary calls).
    pub(crate) steps_b: u32,
    /// The derived liveness bound each of those step counts respects.
    pub(crate) bound: u32,
    /// The answer came from the gcd/Sturm equality certificate, with **no**
    /// refinement at all.
    pub(crate) equal_by_certificate: bool,
}

// ============================================================================
// The number
// ============================================================================

/// An exact real algebraic number.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Anum {
    /// An exact rational. z3's `anum` carries an `mpq` in the same position.
    Rational(BigRational),
    /// A root of a square-free integer polynomial, pinned by a dyadic interval.
    Alg(AlgCell),
}

impl Anum {
    /// The exact rational `r`.
    pub(crate) fn rational(r: BigRational) -> Self {
        Self::Rational(r)
    }

    /// The unique root of `coeffs` inside the dyadic interval `iv`.
    ///
    /// Returns `None` unless `iv` genuinely isolates exactly one real root —
    /// the refusal every caller relies on.
    pub(crate) fn from_poly_interval(coeffs: &[BigInt], iv: &BqInterval) -> Option<Self> {
        let cell = AlgCell::new(&ZPoly::from_coeffs(coeffs.to_vec()), iv)?;
        Some(cell.collapse())
    }

    /// Is this the rational case?
    pub(crate) fn is_rational(&self) -> bool {
        matches!(self, Self::Rational(_))
    }

    /// The exact rational value, when there is one.
    pub(crate) fn to_rational(&self) -> Option<&BigRational> {
        match self {
            Self::Rational(r) => Some(r),
            Self::Alg(_) => None,
        }
    }

    /// Degree of the defining polynomial (`1` for a rational).
    pub(crate) fn degree(&self) -> usize {
        match self {
            Self::Rational(_) => 1,
            Self::Alg(c) => c.degree(),
        }
    }

    /// The cell, for the algebraic case.
    pub(crate) fn cell(&self) -> Option<&AlgCell> {
        match self {
            Self::Rational(_) => None,
            Self::Alg(c) => Some(c),
        }
    }

    /// Narrow the isolating interval (a no-op for the rational case).
    pub(crate) fn refine(&self, target: &Bq) -> Option<Self> {
        match self {
            Self::Rational(_) => Some(self.clone()),
            Self::Alg(c) => c.refine(target),
        }
    }

    /// Promote to a cell: the rational `n/d` becomes the unique root of
    /// `d*x - n` in `(floor(n/d) - 1, floor(n/d) + 2)`.
    ///
    /// A degree-1 polynomial has exactly one real root, so any interval strictly
    /// containing it isolates it; the constructor verifies that anyway.
    fn as_cell(&self) -> Option<AlgCell> {
        match self {
            Self::Alg(c) => Some(c.clone()),
            Self::Rational(r) => {
                let p = ZPoly::from_coeffs(vec![-r.numer().clone(), r.denom().clone()]);
                let f = r.numer().div_floor(r.denom());
                let iv = BqInterval::new(
                    Bq::from_int(&f - BigInt::one()),
                    Bq::from_int(&f + BigInt::from(2)),
                )?;
                AlgCell::new(&p, &iv)
            }
        }
    }

    // ------------------------------------------------------------------
    // Priority 3: exact sign of a polynomial at this point
    // ------------------------------------------------------------------

    /// Exact sign of the integer polynomial `q` at this number: `-1`, `0`, `1`.
    pub(crate) fn sign_of_poly(&self, q: &[BigInt]) -> Option<i32> {
        self.sign_of_poly_traced(q).map(|(s, _)| s)
    }

    /// [`Anum::sign_of_poly`], with the trace the oracle pins the counters from.
    ///
    /// # How zero is decided, and why it is not a tolerance
    ///
    /// `q(alpha) == 0` **iff** `gcd(p, radical(q))` has a root in the isolating
    /// interval. Forward: `alpha` is then a common root, so its minimal
    /// polynomial divides both and hence the gcd. Backward: a root of the gcd in
    /// the interval is a root of `p` there, and the interval isolates exactly
    /// one, so it *is* `alpha`. Both directions are exact; nothing is ever
    /// inferred from smallness.
    ///
    /// # Liveness
    ///
    /// Once zero is excluded, `alpha` is provably not a root of `q`. Both
    /// `alpha` and every real root of `q` are roots of `r = radical(p * rad q)`,
    /// so they are at least `sep(r)` apart. Refining to width `<= 2^-(B+1)`
    /// with `2^-B < sep(r)` puts the entire closed interval within `sep(r)/2` of
    /// `alpha`, so it contains no root of `q`, so `q` is sign-constant on it and
    /// the midpoint's sign is the answer. The number of bisections is
    /// `refine_step_bound(width, 2^-(B+1))` — derived, not budgeted.
    pub(crate) fn sign_of_poly_traced(&self, q: &[BigInt]) -> Option<(i32, AnumTrace)> {
        let qz = ZPoly::from_coeffs(q.to_vec());
        match self {
            Self::Rational(r) => Some((rational_poly_sign(&qz, r)?, AnumTrace::default())),
            Self::Alg(c) => c.sign_of_poly_traced(&qz),
        }
    }

    // ------------------------------------------------------------------
    // Priority 2: exact comparison
    // ------------------------------------------------------------------

    /// Exact comparison. Total on this representation — it never returns
    /// "inconclusive"; a `None` is a decline (a derived bound over the ceiling,
    /// or a broken invariant), never a guess.
    pub(crate) fn cmp_anum(&self, other: &Self) -> Option<Ordering> {
        self.cmp_anum_traced(other).map(|(o, _)| o)
    }

    /// [`Anum::cmp_anum`], with the trace.
    ///
    /// Equality is decided **first**, by certificate, so two equal numbers do
    /// **zero** bisections. That is the whole liveness story for this function:
    /// the case that cannot terminate by refinement never enters refinement.
    pub(crate) fn cmp_anum_traced(&self, other: &Self) -> Option<(Ordering, AnumTrace)> {
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Some((a.cmp(b), AnumTrace::default())),
            (Self::Rational(r), Self::Alg(c)) => {
                let (o, t) = c.cmp_rational_traced(r)?;
                Some((o.reverse(), t))
            }
            (Self::Alg(c), Self::Rational(r)) => c.cmp_rational_traced(r),
            (Self::Alg(a), Self::Alg(b)) => a.cmp_cell(b),
        }
    }

    // ------------------------------------------------------------------
    // Priority 4: arithmetic through the subresultant PRS
    // ------------------------------------------------------------------

    /// Exact sum.
    ///
    /// A **dyadic** rational operand takes the direct affine path
    /// ([`affine_shift`]), which preserves the degree; a non-dyadic rational and
    /// a genuine algebraic operand go through the resultant, which squares it.
    pub(crate) fn add(&self, other: &Self) -> Option<Self> {
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Some(Self::Rational(a + b)),
            (Self::Rational(r), Self::Alg(c)) | (Self::Alg(c), Self::Rational(r)) => {
                match Bq::from_rational(r) {
                    Some(m) => affine_shift(c, &m),
                    None => binop_cells(&self.as_cell()?, &other.as_cell()?, Op::Add),
                }
            }
            (Self::Alg(_), Self::Alg(_)) => {
                binop_cells(&self.as_cell()?, &other.as_cell()?, Op::Add)
            }
        }
    }

    /// Exact product. Same dyadic fast path as [`Anum::add`].
    pub(crate) fn mul(&self, other: &Self) -> Option<Self> {
        if self.is_zero_value() || other.is_zero_value() {
            return Some(Self::Rational(BigRational::zero()));
        }
        match (self, other) {
            (Self::Rational(a), Self::Rational(b)) => Some(Self::Rational(a * b)),
            (Self::Rational(r), Self::Alg(c)) | (Self::Alg(c), Self::Rational(r)) => {
                match Bq::from_rational(r) {
                    Some(m) => affine_scale(c, &m),
                    None => binop_cells(&self.as_cell()?, &other.as_cell()?, Op::Mul),
                }
            }
            (Self::Alg(_), Self::Alg(_)) => {
                binop_cells(&self.as_cell()?, &other.as_cell()?, Op::Mul)
            }
        }
    }

    /// Exact negation.
    pub(crate) fn neg(&self) -> Option<Self> {
        match self {
            Self::Rational(r) => Some(Self::Rational(-r)),
            Self::Alg(c) => {
                // Roots of `p(-x)` are the negations of `p`'s roots; the
                // interval reflects exactly (dyadics are closed under negation).
                let coeffs: Vec<BigInt> =
                    c.p.coeffs()
                        .iter()
                        .enumerate()
                        .map(|(i, v)| if i % 2 == 1 { -v.clone() } else { v.clone() })
                        .collect();
                let iv = BqInterval::new(c.iv.hi().neg(), c.iv.lo().neg())?;
                Some(AlgCell::new(&ZPoly::from_coeffs(coeffs), &iv)?.collapse())
            }
        }
    }

    /// Is this number exactly zero? Exact, and cheap: zero is a root of `p` iff
    /// `p(0) == 0`, and it is *this* root iff it lies in the isolating interval.
    fn is_zero_value(&self) -> bool {
        match self {
            Self::Rational(r) => r.is_zero(),
            Self::Alg(c) => {
                c.p.coeffs().first().is_some_and(Zero::is_zero) && c.iv.contains_open(&Bq::zero())
            }
        }
    }
}

/// Exact sign of an integer polynomial at a rational `n/d` with `d > 0`.
///
/// `sign(sum c_i (n/d)^i) == sign(sum c_i n^i d^(m-i))` because `d^m > 0`, so
/// this is an integer computation with no division.
fn rational_poly_sign(q: &ZPoly, r: &BigRational) -> Option<i32> {
    let Some(m) = q.degree() else {
        return Some(0);
    };
    let (n, d) = (r.numer(), r.denom());
    // Horner on the homogenized form: `((c_m * n + c_{m-1} * d) * n + ...)`,
    // which after `m` steps is exactly `sum_i c_i n^i d^(m-i)`.
    let mut total = q.coeffs()[m].clone();
    for i in (0..m).rev() {
        total = total * n + &q.coeffs()[i] * d.pow(u32::try_from(m - i).ok()?);
    }
    Some(match total.sign() {
        num_bigint::Sign::Minus => -1,
        num_bigint::Sign::NoSign => 0,
        num_bigint::Sign::Plus => 1,
    })
}

impl AlgCell {
    /// Exact sign of `q` at this root. See [`Anum::sign_of_poly_traced`].
    fn sign_of_poly_traced(&self, q: &ZPoly) -> Option<(i32, AnumTrace)> {
        if q.is_zero() {
            return Some((0, AnumTrace::default()));
        }
        if q.degree()? == 0 {
            let s = match q.coeffs()[0].sign() {
                num_bigint::Sign::Minus => -1,
                num_bigint::Sign::NoSign => 0,
                num_bigint::Sign::Plus => 1,
            };
            return Some((s, AnumTrace::default()));
        }
        let qs = normalize_defining(q)?;
        // Zero certificate.
        let g = self.p.gcd(&qs)?;
        if g.degree()? >= 1 {
            let gchain = sturm_chain(&g)?;
            // `g` divides `p`, and `p` is non-zero at both endpoints, so `g` is
            // too: the count cannot fail for an endpoint reason.
            if sturm_count_in(&gchain, self.iv.lo(), self.iv.hi())? >= 1 {
                return Some((
                    0,
                    AnumTrace {
                        equal_by_certificate: true,
                        ..AnumTrace::default()
                    },
                ));
            }
        }
        // Proved non-zero. Derive the bound, then climb the ladder toward it.
        //
        // The stopping test at each rung is a SECOND certificate, not a
        // tolerance: if `qs` — which has exactly the real roots of `q` — has no
        // root in the closed refined interval, then `q` is sign-constant there,
        // and `alpha` is inside it, so the sign at the interval's lower endpoint
        // IS the sign at `alpha`. `sturm_count_in` refuses when an endpoint is a
        // root, which is precisely the case where that reasoning would not hold,
        // so a refusal escalates instead of deciding.
        let b = separation_exponent_for_pair(&self.p, &qs, &g)?;
        let final_bits = b.checked_add(1)?;
        let final_target = Bq::inv_two_pow(final_bits);
        let bound = mpbq::refine_step_bound(&self.iv.width(), &final_target)?;
        let qchain = sturm_chain(&qs)?;

        let mut iv = self.iv.clone();
        let mut steps = 0u32;
        let mut rung = 0usize;
        let mut attempted_final = false;
        loop {
            // ONE decision rule for every rung, including the last.
            //
            // # Why there is no separate "we reached the proved bound" arm
            //
            // An earlier draft of this function kept the original rule at the
            // final rung — refine to `2^-(B+1)`, take the midpoint's sign — and
            // used the Sturm certificate only on the cheap rungs. That is a
            // second decision rule reachable only when the ladder fails, and it
            // was MEASURED UNREACHABLE: negating the sign that arm returns
            // produced **0 divergences** in `fuzz --seed 20260806 --cases 3000`
            // and `--seed 4242`, i.e. the oracle could no longer catch a defect
            // in it. A rule nothing can reach is a rule nothing tests.
            //
            // It is also unnecessary. At width `<= 2^-(B+1)` the separation
            // bound already PROVES that the closed interval holds no root of
            // `q`: `alpha` and every root of `q` are roots of `p * qs`, whose
            // distinct roots are more than `2^-B` apart, and the whole interval
            // lies within `2^-(B+1)` of `alpha`. So this same certificate is
            // guaranteed to succeed at the final rung whenever the bound is
            // sound — the midpoint rule was answering a question the Sturm count
            // answers too, only without checking.
            //
            // The certificate: `q` has no root in `[lo, hi]`, so `q` is
            // sign-constant there, and `alpha` is inside, so the endpoint's sign
            // IS `alpha`'s. `sturm_count_in` refuses outright when an endpoint
            // is a root — precisely the case where that reasoning would not
            // hold — so a refusal escalates rather than decides.
            //
            // MEASURED, and the reason this is `== 0` and not `<= 1`: relaxing
            // it to `<= 1` — on the plausible-sounding but wrong reasoning that
            // "alpha is not a root of q, so a single root of q in here cannot be
            // alpha" — makes `cmp_anum` return the WRONG ORDER. The root of
            // `x^3 - 2x - 7` compares Less to `9/4` when it is Greater. Caught
            // by `ay-nra-oracle fuzz --seed 20260806 --cases 3000` as 5
            // divergences, the first at **case 122**. The reasoning fails
            // because the single root of `q` can sit between `lo` and `alpha`,
            // which flips the sign at the endpoint.
            if sturm_count_in(&qchain, iv.lo(), iv.hi()) == Some(0) {
                let s = mpbq::poly_sign_at(q.coeffs(), iv.lo())?;
                if s != 0 {
                    return Some((
                        s,
                        AnumTrace {
                            sep_bits: Some(b),
                            steps_a: steps,
                            steps_b: 0,
                            bound,
                            equal_by_certificate: false,
                        },
                    ));
                }
            }
            if attempted_final {
                // The certificate failed at the precision the separation bound
                // proves sufficient: unreachable when the bound is sound, so
                // reaching here means the invariant broke. FAIL CLOSED — never
                // guess a sign. This is the same shape as `cmp_cell`'s final
                // arm and as the `else` arm this function's predecessor had.
                return None;
            }
            let k = SEPARATION_RUNGS
                .get(rung)
                .copied()
                .unwrap_or(final_bits)
                .min(final_bits);
            rung += 1;
            if k >= final_bits {
                attempted_final = true;
            }
            let target = Bq::inv_two_pow(k);
            let (refined, tr) = mpbq::refine_to_width(self.p.coeffs(), &iv, &target)?;
            steps += tr.steps;
            match refined {
                // A bisection landed on the root: `alpha` is exactly this
                // dyadic, so evaluate there and stop.
                Refined::Exact(m) => {
                    let s = mpbq::poly_sign_at(q.coeffs(), &m)?;
                    return Some((
                        s,
                        AnumTrace {
                            sep_bits: Some(b),
                            steps_a: steps,
                            steps_b: 0,
                            bound,
                            equal_by_certificate: false,
                        },
                    ));
                }
                Refined::Narrowed(v) => iv = v,
            }
        }
    }

    /// Compare this root against a rational: the sign of `d*x - n` at the root.
    fn cmp_rational_traced(&self, r: &BigRational) -> Option<(Ordering, AnumTrace)> {
        let q = ZPoly::from_coeffs(vec![-r.numer().clone(), r.denom().clone()]);
        let (s, t) = self.sign_of_poly_traced(&q)?;
        Some((s.cmp(&0), t))
    }

    /// Compare two algebraic cells.
    ///
    /// # Equality, decided by an argument
    ///
    /// `g = gcd(p1, p2)`. If `g` has a real root in `I1 ∩ I2`, that root is a
    /// root of `p1` in `I1` — which isolates exactly one — so it is `alpha`;
    /// symmetrically it is `beta`; hence `alpha == beta`. If it has none, the
    /// two are **provably distinct**, and only then does refinement start.
    ///
    /// The endpoints of `I1 ∩ I2` are endpoints of `I1` or of `I2`, and `g`
    /// divides both defining polynomials, so `g` is non-zero at both: the Sturm
    /// count's endpoint guard cannot spuriously refuse here.
    ///
    /// # Liveness
    ///
    /// `alpha != beta` and both are roots of `r = radical(p1 * p2)`, so they are
    /// more than `2^-B` apart for `B = root_separation_exponent(r)`. Refining
    /// each interval to width `<= 2^-(B+2)` puts each inside a ball of radius
    /// `sep/4` around its root, and two such balls around points `>= sep` apart
    /// are disjoint. That is still exactly the argument; what changed is that
    /// the refinement is reached by the [`SEPARATION_RUNGS`] ladder, whose last
    /// rung is clamped to `B + 2`. The ladder loop runs at most
    /// `SEPARATION_RUNGS.len() + 2` times, each iteration performing one
    /// `mpbq::refine_to_width` per side that is itself bounded by its own
    /// derived step bound. Exhausting the ladder without a decision is the same
    /// fail-closed `None` the direct version returned.
    ///
    /// # Why the ladder is free in the worst case
    ///
    /// Each rung refines from the PREVIOUS rung's interval, and dyadic halving
    /// is exact: the width after `n` halvings is exactly `w / 2^n`. So the
    /// cumulative bisection count to reach `2^-k` through the ladder equals the
    /// count a single direct call to `2^-k` would make. The ladder adds interval
    /// comparisons, not bisections.
    fn cmp_cell(&self, other: &Self) -> Option<(Ordering, AnumTrace)> {
        let g = self.p.gcd(&other.p)?;
        if g.degree()? >= 1 {
            let lo = if self.iv.lo().cmp_bq(other.iv.lo()) == Ordering::Greater {
                self.iv.lo().clone()
            } else {
                other.iv.lo().clone()
            };
            let hi = if self.iv.hi().cmp_bq(other.iv.hi()) == Ordering::Less {
                self.iv.hi().clone()
            } else {
                other.iv.hi().clone()
            };
            if lo.cmp_bq(&hi) == Ordering::Less {
                let gchain = sturm_chain(&g)?;
                if sturm_count_in(&gchain, &lo, &hi)? >= 1 {
                    return Some((
                        Ordering::Equal,
                        AnumTrace {
                            equal_by_certificate: true,
                            ..AnumTrace::default()
                        },
                    ));
                }
            }
        }
        // Proved distinct.
        let b = separation_exponent_for_pair(&self.p, &other.p, &g)?;
        let final_bits = b.checked_add(2)?;
        let final_target = Bq::inv_two_pow(final_bits);
        // The declared liveness bound, computed from the ORIGINAL widths and the
        // FINAL target — the identical quantity the direct version reported, so
        // the oracle's `steps <= bound` assertion is unchanged in strength. It
        // upper-bounds the ladder's cumulative steps because
        // `refine_step_bound(w, 2^-k)` is non-decreasing in `k` and the ladder's
        // cumulative count to precision `k` equals the direct count to `k`.
        let bound = mpbq::refine_step_bound(&self.iv.width(), &final_target)?
            .max(mpbq::refine_step_bound(&other.iv.width(), &final_target)?);

        let mut ia = self.iv.clone();
        let mut ib = other.iv.clone();
        let (mut steps_a, mut steps_b) = (0u32, 0u32);
        let mut rung = 0usize;
        let mut attempted_final = false;
        loop {
            let trace = AnumTrace {
                sep_bits: Some(b),
                steps_a,
                steps_b,
                bound,
                equal_by_certificate: false,
            };
            // Disjoint intervals ARE the order. This test is exact and costs two
            // dyadic comparisons; it is the whole point of the ladder.
            if ia.hi().cmp_bq(ib.lo()) != Ordering::Greater {
                return Some((Ordering::Less, trace));
            }
            if ib.hi().cmp_bq(ia.lo()) != Ordering::Greater {
                return Some((Ordering::Greater, trace));
            }
            if attempted_final {
                // Refined to the precision the separation bound PROVES
                // sufficient and still overlapping: unreachable when the bound
                // is sound. Fail closed rather than pick an order.
                return None;
            }
            let k = SEPARATION_RUNGS
                .get(rung)
                .copied()
                .unwrap_or(final_bits)
                .min(final_bits);
            rung += 1;
            if k >= final_bits {
                attempted_final = true;
            }
            let target = Bq::inv_two_pow(k);
            let (ra, ta) = mpbq::refine_to_width(self.p.coeffs(), &ia, &target)?;
            steps_a += ta.steps;
            // A bisection that lands on the root proves it dyadic; fall back to
            // the rational comparison, which is one non-recursive call.
            let ia_next = match ra {
                Refined::Exact(m) => {
                    let trace = AnumTrace {
                        sep_bits: Some(b),
                        steps_a,
                        steps_b,
                        bound,
                        equal_by_certificate: false,
                    };
                    let (o, _) = other.cmp_rational_traced(&m.to_rational())?;
                    return Some((o.reverse(), trace));
                }
                Refined::Narrowed(v) => v,
            };
            let (rb, tb) = mpbq::refine_to_width(other.p.coeffs(), &ib, &target)?;
            steps_b += tb.steps;
            let ib_next = match rb {
                Refined::Exact(m) => {
                    let trace = AnumTrace {
                        sep_bits: Some(b),
                        steps_a,
                        steps_b,
                        bound,
                        equal_by_certificate: false,
                    };
                    let (o, _) = self.cmp_rational_traced(&m.to_rational())?;
                    return Some((o, trace));
                }
                Refined::Narrowed(v) => v,
            };
            ia = ia_next;
            ib = ib_next;
        }
    }
}

// ============================================================================
// Arithmetic: resultants through the fraction-free subresultant PRS
// ============================================================================

/// `deg(a) * deg(b)` is above the ceiling for `op`, so the resultant must be
/// refused before it is built. A missing degree (the zero polynomial) counts as
/// over: it is degenerate either way.
fn resultant_degree_over_ceiling(a: &ZPoly, b: &ZPoly, op: Op) -> bool {
    let ceiling = match op {
        Op::Add => MAX_ADD_RESULTANT_DEGREE,
        Op::Mul => MAX_MUL_RESULTANT_DEGREE,
    };
    match (a.degree(), b.degree()) {
        (Some(m), Some(n)) => m.checked_mul(n).is_none_or(|d| d > ceiling),
        _ => true,
    }
}

/// Which binary operation a resultant construction is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Op {
    Add,
    Mul,
}

/// `C(n, k)` as a `BigInt`, for the small `n` a polynomial degree provides.
fn binomial(n: usize, k: usize) -> BigInt {
    let mut acc = BigInt::one();
    for i in 0..k {
        acc = acc * BigInt::from(n - i) / BigInt::from(i + 1);
    }
    acc
}

/// Read an [`MPolyZ`] back as a univariate `ZPoly` in [`OUTER`].
///
/// `None` if any monomial mentions another variable — which would mean the
/// resultant did not eliminate what it was supposed to.
fn mpoly_to_zpoly(m: &MPolyZ) -> Option<ZPoly> {
    let mut coeffs: Vec<BigInt> = Vec::new();
    for (mono, c) in m.terms() {
        let e = match mono.pairs() {
            [] => 0usize,
            [(v, e)] if *v == OUTER => usize::try_from(*e).ok()?,
            _ => return None,
        };
        if coeffs.len() <= e {
            coeffs.resize(e + 1, BigInt::zero());
        }
        coeffs[e] += c;
    }
    Some(ZPoly::from_coeffs(coeffs))
}

/// `Res_y(p(y), q(z - y))` as a polynomial in `z`.
///
/// Every root is `a + b` for a root `a` of `p` and a root `b` of `q`. The second
/// argument's leading coefficient in `y` is `(-1)^n * lc(q)`, a non-zero
/// **constant**, so no degree collapse can make the subresultant chain compute
/// the resultant of a different pair.
fn sum_resultant(p: &ZPoly, q: &ZPoly) -> Option<ZPoly> {
    let f: RPoly<MPolyZ> = RPoly::from_coeffs(
        p.coeffs()
            .iter()
            .map(|c| MPolyZ::constant(c.clone()))
            .collect(),
    );
    let n = q.degree()?;
    let mut acc: Vec<Vec<(Mono, BigInt)>> = vec![Vec::new(); n + 1];
    for j in 0..=n {
        let cj = &q.coeffs()[j];
        if cj.is_zero() {
            continue;
        }
        for i in 0..=j {
            let mut coef = cj * binomial(j, i);
            if i % 2 == 1 {
                coef = -coef;
            }
            acc[i].push((Mono::var_pow(OUTER, u32::try_from(j - i).ok()?), coef));
        }
    }
    let g = RPoly::from_coeffs(acc.into_iter().map(MPolyZ::from_terms).collect());
    mpoly_to_zpoly(&subresultant::resultant(&f, &g)?)
}

/// `Res_y(p(y), y^n q(z / y))` as a polynomial in `z`, for `q(0) != 0`.
///
/// Every root is `a * b`. The second argument's leading coefficient in `y` is
/// `q(0)`, non-zero by the precondition, so again no degree collapse.
fn product_resultant(p: &ZPoly, q: &ZPoly) -> Option<ZPoly> {
    let f: RPoly<MPolyZ> = RPoly::from_coeffs(
        p.coeffs()
            .iter()
            .map(|c| MPolyZ::constant(c.clone()))
            .collect(),
    );
    let n = q.degree()?;
    if q.coeffs()[0].is_zero() {
        return None;
    }
    let mut gc: Vec<MPolyZ> = vec![MPolyZ::zero(); n + 1];
    for i in 0..=n {
        let cj = &q.coeffs()[n - i];
        if cj.is_zero() {
            continue;
        }
        gc[i] = MPolyZ::term(Mono::var_pow(OUTER, u32::try_from(n - i).ok()?), cj.clone());
    }
    let g = RPoly::from_coeffs(gc);
    mpoly_to_zpoly(&subresultant::resultant(&f, &g)?)
}

/// `alpha + m` for a DYADIC `m`, without a resultant.
///
/// `p(x - m)` scaled by `2^(k*d)` has integer coefficients, and the interval
/// translates to `(lo + m, hi + m)` — still dyadic, because dyadics are closed
/// under addition. Degree is preserved (a resultant would square it), and the
/// constructor re-verifies the isolating property.
///
/// This exists because the recursive alternative **did not terminate**: routing
/// an exact-dyadic operand back through [`Anum::mul`] re-entered
/// [`binop_cells`], which refined to the same exact dyadic, forever. Measured as
/// a stack overflow in `multiplying_by_a_rational_goes_through_the_same_resultant_path`
/// before this function existed. A hang is strictly worse than a decline.
fn affine_shift(c: &AlgCell, m: &Bq) -> Option<Anum> {
    let d = c.p.degree()?;
    let (a, k) = (m.numerator().clone(), m.k());
    let two_k = BigInt::one() << k;
    let mut out = vec![BigInt::zero(); d + 1];
    for j in 0..=d {
        let cj = &c.p.coeffs()[j];
        if cj.is_zero() {
            continue;
        }
        for i in 0..=j {
            // c_j * C(j,i) * (2^k)^i * (-a)^(j-i) * (2^k)^(d-j)
            let e = u32::try_from(j - i).ok()?;
            let term = cj
                * binomial(j, i)
                * two_k.pow(u32::try_from(i).ok()?)
                * (-a.clone()).pow(e)
                * two_k.pow(u32::try_from(d - j).ok()?);
            out[i] += term;
        }
    }
    let iv = BqInterval::new(c.iv.lo().add(m), c.iv.hi().add(m))?;
    Some(AlgCell::new(&ZPoly::from_coeffs(out), &iv)?.collapse())
}

/// `alpha * m` for a NON-ZERO DYADIC `m`, without a resultant.
///
/// `p(x/m)` scaled by `a^d` has integer coefficients (coefficient of `x^i` is
/// `c_i * 2^(k*i) * a^(d-i)`), and the interval scales to `(lo*m, hi*m)`,
/// swapped when `m < 0`. Same reason for existing as [`affine_shift`].
fn affine_scale(c: &AlgCell, m: &Bq) -> Option<Anum> {
    if m.is_zero() {
        return Some(Anum::Rational(BigRational::zero()));
    }
    let d = c.p.degree()?;
    let (a, k) = (m.numerator().clone(), m.k());
    let two_k = BigInt::one() << k;
    let mut out = vec![BigInt::zero(); d + 1];
    for i in 0..=d {
        // `(2^k)^i == 2^(k*i)`, exactly the factor in the doc comment.
        out[i] = &c.p.coeffs()[i]
            * two_k.pow(u32::try_from(i).ok()?)
            * a.pow(u32::try_from(d - i).ok()?);
    }
    let lo = c.iv.lo().mul(m)?;
    let hi = c.iv.hi().mul(m)?;
    let iv = if m.sign() > 0 {
        BqInterval::new(lo, hi)?
    } else {
        BqInterval::new(hi, lo)?
    };
    Some(AlgCell::new(&ZPoly::from_coeffs(out), &iv)?.collapse())
}

/// An exponent `e` with `|x| < 2^e` for every endpoint of `iv`.
fn magnitude_exponent(iv: &BqInterval) -> u32 {
    let one = |x: &Bq| -> u32 {
        let bits = u32::try_from(x.numerator_bits()).unwrap_or(u32::MAX);
        bits.saturating_sub(x.k())
    };
    one(iv.lo()).max(one(iv.hi()))
}

/// The dyadic interval enclosing `{x * y : x in a, y in b}`.
fn interval_product(a: &BqInterval, b: &BqInterval) -> Option<BqInterval> {
    let corners = [
        a.lo().mul(b.lo())?,
        a.lo().mul(b.hi())?,
        a.hi().mul(b.lo())?,
        a.hi().mul(b.hi())?,
    ];
    let mut lo = corners[0].clone();
    let mut hi = corners[0].clone();
    for c in &corners[1..] {
        if c.cmp_bq(&lo) == Ordering::Less {
            lo = c.clone();
        }
        if c.cmp_bq(&hi) == Ordering::Greater {
            hi = c.clone();
        }
    }
    BqInterval::new(lo, hi)
}

/// Which path an arithmetic operation will take, and whether it can legitimately
/// decline.
///
/// # This is DIAGNOSTIC ONLY
///
/// [`Anum::add`] and [`Anum::mul`] compute exactly the same answer whether or not
/// this is called; nothing in this module consults it. It exists so a caller —
/// in practice the differential oracle — can tell a **legitimate** decline (the
/// declared [`MAX_SEPARATION_BITS`] ceiling, or a degenerate operand) from a
/// decline that means the construction failed.
///
/// # Why it had to exist, MEASURED
///
/// A sign-parity defect injected into [`sum_resultant`] turns the sum resultant
/// into the DIFFERENCE resultant. The enclosure of `alpha + beta` then contains
/// no root of the wrong polynomial, so [`AlgCell::from_normalized`] refuses and
/// the operation returns `None`. That is a **decline**, and a decline is not a
/// divergence: the defect scored 0 divergences and 47 declines out of 111
/// `anum-arith` cases at seed 20260805, against a baseline of 0 declines. With
/// this diagnosis the oracle asserts, before it reads the answer, that a
/// non-ceiling case must succeed — and the same defect becomes a divergence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OpDiag {
    /// No resultant is built: two rationals, or a zero operand.
    ClosedForm,
    /// A dyadic rational operand takes the degree-preserving affine path.
    Affine,
    /// The resultant path, with the derived separation exponent it will use.
    Resultant(u32),
    /// The derived exponent is above the ceiling: the ONLY legitimate decline.
    OverCeiling,
    /// The resultant could not be built (degenerate operand).
    Degenerate,
}

/// Which path `a + b` (`is_add`) or `a * b` will take. See [`OpDiag`].
pub(crate) fn binop_diag(a: &Anum, b: &Anum, is_add: bool) -> OpDiag {
    if a.is_zero_value() || b.is_zero_value() {
        return OpDiag::ClosedForm;
    }
    match (a, b) {
        (Anum::Rational(_), Anum::Rational(_)) => OpDiag::ClosedForm,
        (Anum::Rational(r), Anum::Alg(_)) | (Anum::Alg(_), Anum::Rational(r)) => {
            if Bq::from_rational(r).is_some() {
                OpDiag::Affine
            } else {
                diag_resultant(a, b, is_add)
            }
        }
        (Anum::Alg(_), Anum::Alg(_)) => diag_resultant(a, b, is_add),
    }
}

fn diag_resultant(a: &Anum, b: &Anum, is_add: bool) -> OpDiag {
    let (Some(ca), Some(cb)) = (a.as_cell(), b.as_cell()) else {
        return OpDiag::Degenerate;
    };
    let op = if is_add { Op::Add } else { Op::Mul };
    let pair = match op {
        Op::Add => Some((ca.p.clone(), cb.p.clone())),
        Op::Mul => strip_zero_roots(&ca.p).zip(strip_zero_roots(&cb.p)),
    };
    let Some((pa, pb)) = pair else {
        return OpDiag::Degenerate;
    };
    if resultant_degree_over_ceiling(&pa, &pb, op) {
        return OpDiag::OverCeiling;
    }
    let r = match op {
        Op::Add => sum_resultant(&pa, &pb),
        Op::Mul => product_resultant(&pa, &pb),
    };
    let Some(res) = r.as_ref().and_then(normalize_defining) else {
        return OpDiag::Degenerate;
    };
    match root_separation_exponent(&res) {
        Some(bits) => OpDiag::Resultant(bits),
        None => OpDiag::OverCeiling,
    }
}

/// `alpha op beta`, exactly.
///
/// # Shape
///
/// 1. Build a defining polynomial for the result as a resultant, using
///    [`crate::subresultant::resultant`] over `RPoly<MPolyZ>` — the fraction-free
///    subresultant PRS. `algebraic.rs` does the same job with `deg(p)*deg(q) + 1`
///    Sylvester determinant evaluations plus a Lagrange interpolation; this is
///    one chain.
/// 2. Take its square-free radical and derive `B = root_separation_exponent`.
/// 3. Refine **each operand once** to a width small enough that the interval
///    enclosure of the result is narrower than `sep/4`.
/// 4. Hand the enclosure to [`AlgCell::from_normalized`], which **verifies**
///    that it isolates exactly one root. There is no outer retry loop: the
///    target width is derived so that one pass suffices, and a verification
///    failure is a fail-closed `None`, not a reason to loop again.
fn binop_cells(a: &AlgCell, b: &AlgCell, op: Op) -> Option<Anum> {
    let (pa, pb) = match op {
        Op::Add => (a.p.clone(), b.p.clone()),
        // Sound because the caller has already returned for a zero operand: the
        // represented roots are non-zero, and dividing out `x^k` removes only
        // the root zero.
        Op::Mul => (strip_zero_roots(&a.p)?, strip_zero_roots(&b.p)?),
    };
    // Refused BEFORE the resultant is built: see `MAX_RESULTANT_DEGREE`.
    if resultant_degree_over_ceiling(&pa, &pb, op) {
        return None;
    }
    let r = match op {
        Op::Add => sum_resultant(&pa, &pb)?,
        Op::Mul => product_resultant(&pa, &pb)?,
    };
    if r.is_zero() {
        return None;
    }
    let res = normalize_defining(&r)?;
    let bsep = root_separation_exponent(&res)?;
    // Add: enclosure width is `wa + wb <= 2w`, so `w <= 2^-(B+3)` gives
    // `<= 2^-(B+2)`.
    // Mul: for `|x|, |y| < 2^e`, `|xy - x'y'| <= 2^e (wa + wb) <= 2^(e+1) w`, so
    // the enclosure width is at most `2^(e+2) w`, and `w <= 2^-(B+e+4)` gives
    // `<= 2^-(B+2)`.
    let extra = match op {
        Op::Add => 3u32,
        Op::Mul => magnitude_exponent(&a.iv)
            .max(magnitude_exponent(&b.iv))
            .checked_add(4)?,
    };
    let target = Bq::inv_two_pow(bsep.checked_add(extra)?);
    let (ra, _) = mpbq::refine_to_width(a.p.coeffs(), &a.iv, &target)?;
    let (rb, _) = mpbq::refine_to_width(b.p.coeffs(), &b.iv, &target)?;
    // An exact hit means that operand is a dyadic rational after all. Recurse
    // once through `Anum`, which is not a loop: the rational/rational and
    // rational/algebraic cases below never hit this branch again.
    // An exact hit means that operand is a DYADIC rational after all. Finish
    // with the direct affine construction on the OTHER operand — never by
    // re-entering this function, which is what made the first version of this
    // code recurse without bound.
    let (ia, ib) = match (ra, rb) {
        (Refined::Exact(m), _) => {
            return match op {
                Op::Add => affine_shift(b, &m),
                Op::Mul => affine_scale(b, &m),
            }
        }
        (_, Refined::Exact(m)) => {
            return match op {
                Op::Add => affine_shift(a, &m),
                Op::Mul => affine_scale(a, &m),
            }
        }
        (Refined::Narrowed(ia), Refined::Narrowed(ib)) => (ia, ib),
    };
    let enc = match op {
        Op::Add => BqInterval::new(ia.lo().add(ib.lo()), ia.hi().add(ib.hi()))?,
        Op::Mul => interval_product(&ia, &ib)?,
    };
    Some(AlgCell::from_normalized(res, enc)?.collapse())
}

#[cfg(test)]
#[path = "anum_tests.rs"]
mod tests;
