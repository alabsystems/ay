// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3-compatible Real Closed Field (RCF) C API — REAL over the exact
//! rational + real-algebraic engine (`ay_nra`), plus EXACT SYMBOLIC support for
//! the transcendental (π, e) and infinitesimal extensions.
//!
//! Z3's `z3_rcf.h` exposes an ordered real-closed field with rational,
//! algebraic, transcendental (π, e) and infinitesimal extensions. Each element
//! is an opaque `Z3_rcf_num`:
//!
//! * **REAL (rational/algebraic)** — a handle boxing an exact [`RealScalar`]
//!   (arena-owned, freed at `Z3_del_context`). Constructors, field arithmetic,
//!   ordering/equality, classification and introspection all read the exact
//!   `ay_nra` engine. Equality/sign is GCD-certified, orderings by exact
//!   interval separation — NEVER numeric proximity.
//!
//! * **REAL (transcendental)** — `mk_pi`/`mk_e` allocate the SYMBOLIC linear
//!   form `a + b·t` (`t ∈ {π, e}`, exact rational `a`, `b ≠ 0`). Arithmetic
//!   closed under the form (add/sub/neg, rational scaling) is exact symbolic
//!   coefficient arithmetic; anything beyond it (t·t, 1/(a+b·t), π+e) is an
//!   honest `Z3_EXCEPTION`. Comparisons against rationals/algebraics/same-kind
//!   forms are decided by refining a RIGOROUS rational enclosure of t
//!   ([`super::rcf_series`]) until it separates — this always terminates
//!   because `a + b·t` (b ≠ 0, rational a, b) is transcendental (Lindemann),
//!   hence never equal to any rational or algebraic number; the same-kind
//!   equal case reduces to exact coefficient equality. π-vs-e comparisons
//!   refine both enclosures and fail closed on the (mathematically unresolved)
//!   equality frontier.
//!
//! * **REAL (infinitesimal)** — `mk_infinitesimal` allocates a fresh positive
//!   infinitesimal ε (per-context tower index). Values are EXACT
//!   rational-coefficient finite Laurent series `Σ qₖ·εᵏ` (k ∈ ℤ, so `1/ε` is
//!   representable and correct). Add/sub/neg/mul are exact polynomial
//!   arithmetic; `inv` is exact for monomials `q·εᵏ` and an honest error
//!   otherwise (`1/(1+ε)` is an infinite series — truncating it would
//!   fabricate equalities). The order is the non-Archimedean lexicographic
//!   order of ℚ((ε)): the sign of a series is the sign of its LOWEST-exponent
//!   nonzero coefficient (ε infinitesimal ⇒ smaller exponents dominate), which
//!   makes every comparison exact and total on the represented values. Mixing
//!   two DIFFERENT infinitesimal generators, or ε with π/e in arithmetic, is
//!   an honest `Z3_EXCEPTION` (single-generator series only, documented).
//!
//! **Soundness invariants:** every engine `None` (refinement cap /
//! unrepresentable) maps to `Z3_EXCEPTION` and a null/false/0 sentinel — never a
//! default that reads as a real comparison; a zero/equal answer is only ever a
//! GCD certificate (algebraic) or exact coefficient identity (symbolic forms);
//! every unsupported mixed operation raises `Z3_EXCEPTION`, never a guess;
//! decimal strings for irrational values carry a trailing `?` and are
//! display-only (never fed to a comparison).

use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::ffi::{c_int, c_uint};
use std::ptr;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use ay_nra::{rcf_api, RealScalar};

use super::rcf_series::{self, TransKind};
use super::{
    cache_string, cache_symbol, ffi_guard_const_ptr, ffi_guard_int, ffi_guard_ptr, ffi_guard_uint,
    ffi_guard_void, Z3Context, Z3_context, Z3_string, Z3_symbol, MAX_FFI_ALGEBRAIC_EXPONENT,
    MAX_FFI_DECIMAL_PRECISION, MAX_FFI_REFINEMENT_PRECISION, Z3_EXCEPTION, Z3_OK,
};

/// An exact Real Closed Field numeral.
///
/// Canonical-form invariants (enforced by [`mk_trans`] / [`mk_inf`], so the
/// variant IS the classification):
/// * `Transcendental` always has `b ≠ 0` (a degenerate form collapses to
///   `Real`), so every `Transcendental` value is provably transcendental.
/// * `Infinitesimal` has no zero coefficients and at least one term with
///   exponent ≠ 0 (a constant series collapses to `Real`), so every
///   `Infinitesimal` value genuinely depends on ε.
pub enum RcfNum {
    /// An exact rational or real-algebraic scalar.
    Real(RealScalar),
    /// The symbolic linear form `a + b·t` over one transcendental `t ∈ {π, e}`
    /// with exact rational coefficients and `b ≠ 0`.
    Transcendental {
        /// Which transcendental extends ℚ.
        kind: TransKind,
        /// Constant coefficient.
        a: BigRational,
        /// Coefficient of `t` (never zero).
        b: BigRational,
    },
    /// An exact finite Laurent series `Σ qₖ·εᵏ` (map: exponent → nonzero
    /// rational coefficient) in the context's `index`-th infinitesimal.
    Infinitesimal {
        /// Tower index of the generator (per-context, ≥ 3; π = 1, e = 2).
        index: c_uint,
        /// Exponent → coefficient, no zero coefficients, not all-constant.
        series: BTreeMap<i64, BigRational>,
    },
}

/// Canonicalizing constructor for the transcendental linear form: `b == 0`
/// collapses to an exact rational.
fn mk_trans(kind: TransKind, a: BigRational, b: BigRational) -> RcfNum {
    if b.is_zero() {
        RcfNum::Real(RealScalar::Rational(a))
    } else {
        RcfNum::Transcendental { kind, a, b }
    }
}

/// Canonicalizing constructor for an ε-series: drops zero coefficients and
/// collapses a constant series to an exact rational.
fn mk_inf(index: c_uint, mut series: BTreeMap<i64, BigRational>) -> RcfNum {
    series.retain(|_, coeff| !coeff.is_zero());
    let non_constant = series.keys().any(|&e| e != 0);
    if !non_constant {
        let a0 = series.remove(&0).unwrap_or_else(BigRational::zero);
        return RcfNum::Real(RealScalar::Rational(a0));
    }
    RcfNum::Infinitesimal { index, series }
}

/// Opaque handle for a Real Closed Field numeral: a raw pointer to an
/// arena-owned [`RcfNum`]. Freed once, at `Z3_del_context` (so `Z3_rcf_del` is a
/// bookkeeping no-op). Producers never hand back a fabricated value: an
/// uncomputable request yields null + `Z3_EXCEPTION`.
pub type Z3_rcf_num = *mut RcfNum;

// ============================================================================
// Handle / engine plumbing
// ============================================================================

/// Allocate an RCF numeral in the context arena and return its raw handle.
fn alloc_num(ctx: &mut Z3Context, n: RcfNum) -> Z3_rcf_num {
    let handle = Box::into_raw(Box::new(n));
    ctx.rcf_num_cache.push(handle);
    handle
}

/// Allocate an exact rational/algebraic scalar in the context arena.
fn alloc_rcf(ctx: &mut Z3Context, s: RealScalar) -> Z3_rcf_num {
    alloc_num(ctx, RcfNum::Real(s))
}

/// Record an unsupported / uncomputable result: `Z3_EXCEPTION` + a message.
fn fail(ctx: &mut Z3Context, msg: String) {
    ctx.last_error = Z3_EXCEPTION;
    ctx.error_msg = Some(msg);
}

/// Canonicalize an engine result and box it as a handle; `None` (refinement cap
/// / unrepresentable) → `Z3_EXCEPTION` + null (never a fabricated value).
fn produce(ctx: &mut Z3Context, r: Option<RealScalar>, who: &str) -> Z3_rcf_num {
    match r.and_then(|s| rcf_api::canonicalize(&s)) {
        Some(s) => {
            ctx.last_error = Z3_OK;
            alloc_rcf(ctx, s)
        }
        None => {
            fail(
                ctx,
                format!(
                    "{who}: result not exactly computable (engine refinement cap) — fail-closed"
                ),
            );
            ptr::null_mut()
        }
    }
}

/// Box a symbolic-arithmetic result as a handle; an `Err` (unsupported mixed
/// operation / refinement cap) → `Z3_EXCEPTION` + null, never a guess.
fn produce_num(ctx: &mut Z3Context, r: Result<RcfNum, String>, who: &str) -> Z3_rcf_num {
    match r {
        Ok(RcfNum::Real(s)) => produce(ctx, Some(s), who),
        Ok(n) => {
            ctx.last_error = Z3_OK;
            alloc_num(ctx, n)
        }
        Err(msg) => {
            fail(ctx, format!("{who}: {msg}"));
            ptr::null_mut()
        }
    }
}

/// Borrow the numeral behind an RCF handle; `None` for a null handle.
///
/// # Safety
/// `a`, when non-null, must be a live handle from this context's arena.
unsafe fn rcf_ref<'a>(a: Z3_rcf_num) -> Option<&'a RcfNum> {
    // SAFETY: caller guarantees `a` is null or a live arena handle.
    unsafe { a.as_ref() }
}

/// Borrow the RATIONAL/ALGEBRAIC scalar behind a handle for the entry points
/// whose contract only covers that class (defining-polynomial introspection,
/// numerator/denominator, Thom conditions, `mk_roots` coefficients). A
/// transcendental/infinitesimal operand → honest `Z3_EXCEPTION` + `None`
/// (those values have no defining polynomial over ℚ); a null handle → the
/// usual null-operand error.
fn expect_real<'a>(
    ctx: &mut Z3Context,
    n: Option<&'a RcfNum>,
    who: &str,
) -> Option<&'a RealScalar> {
    match n {
        Some(RcfNum::Real(s)) => Some(s),
        Some(_) => {
            fail(
                ctx,
                format!("{who}: unsupported for a transcendental/infinitesimal operand (no defining polynomial over Q)"),
            );
            None
        }
        None => {
            fail(ctx, format!("{who}: null operand"));
            None
        }
    }
}

// ============================================================================
// Exact symbolic arithmetic / comparison over the extended numeral kinds.
//
// Every function is total-or-`Err`: an `Err` is an UNSUPPORTED (or capped)
// case that the FFI maps to `Z3_EXCEPTION` — never a fabricated value. All
// coefficient arithmetic is exact `BigRational`; enclosure refinement is used
// ONLY to decide strict orderings between provably-distinct values.
// ============================================================================

/// The exact rational value of a `Real` numeral, when it is rational
/// (canonicalizes an algebraic that collapses, e.g. √4). `None` for genuine
/// irrationals and non-`Real` kinds.
fn rational_of(n: &RcfNum) -> Option<BigRational> {
    match n {
        RcfNum::Real(s) => rcf_api::as_rational(s).map(|(num, den)| BigRational::new(num, den)),
        _ => None,
    }
}

/// Exact `x + y` over all numeral kinds; `Err` on an unsupported mix.
fn num_add(x: &RcfNum, y: &RcfNum) -> Result<RcfNum, String> {
    match (x, y) {
        (RcfNum::Real(a), RcfNum::Real(b)) => a
            .add(b)
            .map(RcfNum::Real)
            .ok_or_else(|| "not exactly computable (engine refinement cap) — fail-closed".into()),
        (RcfNum::Transcendental { kind, a, b }, other)
        | (other, RcfNum::Transcendental { kind, a, b }) => match other {
            RcfNum::Real(_) => match rational_of(other) {
                Some(q) => Ok(mk_trans(*kind, a + q, b.clone())),
                None => Err(format!(
                    "algebraic + {} arithmetic is outside the supported linear form",
                    kind.name()
                )),
            },
            RcfNum::Transcendental {
                kind: k2,
                a: a2,
                b: b2,
            } => {
                if kind == k2 {
                    Ok(mk_trans(*kind, a + a2, b + b2))
                } else {
                    Err("mixed transcendentals (pi and e) are unsupported".into())
                }
            }
            RcfNum::Infinitesimal { .. } => {
                Err("transcendental + infinitesimal arithmetic is unsupported".into())
            }
        },
        (RcfNum::Infinitesimal { index, series }, other)
        | (other, RcfNum::Infinitesimal { index, series }) => match other {
            RcfNum::Real(_) => match rational_of(other) {
                Some(q) => {
                    let mut s = series.clone();
                    let a0 = s.remove(&0).unwrap_or_else(BigRational::zero) + q;
                    if !a0.is_zero() {
                        s.insert(0, a0);
                    }
                    Ok(mk_inf(*index, s))
                }
                None => Err(
                    "algebraic + infinitesimal arithmetic is unsupported (rational \
                             coefficients only)"
                        .into(),
                ),
            },
            RcfNum::Infinitesimal {
                index: i2,
                series: s2,
            } => {
                if index == i2 {
                    let mut s = series.clone();
                    for (e, coeff) in s2 {
                        let entry = s.entry(*e).or_insert_with(BigRational::zero);
                        *entry += coeff;
                    }
                    Ok(mk_inf(*index, s))
                } else {
                    Err(
                        "mixing two different infinitesimals is unsupported (single-generator \
                         series only)"
                            .into(),
                    )
                }
            }
            // (Trans, Inf) combinations were already matched above.
            RcfNum::Transcendental { .. } => {
                Err("transcendental + infinitesimal arithmetic is unsupported".into())
            }
        },
    }
}

/// Exact `-x` (total: every kind negates coefficient-wise).
fn num_neg(x: &RcfNum) -> RcfNum {
    match x {
        RcfNum::Real(s) => RcfNum::Real(s.neg()),
        RcfNum::Transcendental { kind, a, b } => RcfNum::Transcendental {
            kind: *kind,
            a: -a.clone(),
            b: -b.clone(),
        },
        RcfNum::Infinitesimal { index, series } => RcfNum::Infinitesimal {
            index: *index,
            series: series.iter().map(|(&e, c)| (e, -c.clone())).collect(),
        },
    }
}

/// Exact `x · y`; `Err` when the product leaves the supported forms
/// (`t·t` would be quadratic in the transcendental; ε-series multiply exactly
/// by convolution).
fn num_mul(x: &RcfNum, y: &RcfNum) -> Result<RcfNum, String> {
    match (x, y) {
        (RcfNum::Real(a), RcfNum::Real(b)) => a
            .mul(b)
            .map(RcfNum::Real)
            .ok_or_else(|| "not exactly computable (engine refinement cap) — fail-closed".into()),
        (RcfNum::Transcendental { kind, a, b }, other)
        | (other, RcfNum::Transcendental { kind, a, b }) => match other {
            RcfNum::Real(_) => match rational_of(other) {
                Some(q) => Ok(mk_trans(*kind, a * &q, b * &q)),
                None => Err(format!(
                    "algebraic × {} arithmetic is outside the supported linear form",
                    kind.name()
                )),
            },
            RcfNum::Transcendental { .. } => Err(
                "the product of two transcendental forms is quadratic in the extension — \
                 outside the supported linear form"
                    .into(),
            ),
            RcfNum::Infinitesimal { .. } => {
                Err("transcendental × infinitesimal arithmetic is unsupported".into())
            }
        },
        (RcfNum::Infinitesimal { index, series }, other)
        | (other, RcfNum::Infinitesimal { index, series }) => match other {
            RcfNum::Real(_) => match rational_of(other) {
                Some(q) => {
                    if q.is_zero() {
                        return Ok(RcfNum::Real(RealScalar::Rational(BigRational::zero())));
                    }
                    Ok(mk_inf(
                        *index,
                        series.iter().map(|(&e, c)| (e, c * &q)).collect(),
                    ))
                }
                None => Err(
                    "algebraic × infinitesimal arithmetic is unsupported (rational \
                             coefficients only)"
                        .into(),
                ),
            },
            RcfNum::Infinitesimal {
                index: i2,
                series: s2,
            } => {
                if index == i2 {
                    // Exact Laurent-polynomial convolution.
                    let mut acc: BTreeMap<i64, BigRational> = BTreeMap::new();
                    for (&e1, c1) in series {
                        for (&e2, c2) in s2 {
                            let entry = acc.entry(e1 + e2).or_insert_with(BigRational::zero);
                            *entry += c1 * c2;
                        }
                    }
                    Ok(mk_inf(*index, acc))
                } else {
                    Err(
                        "mixing two different infinitesimals is unsupported (single-generator \
                         series only)"
                            .into(),
                    )
                }
            }
            RcfNum::Transcendental { .. } => {
                Err("transcendental × infinitesimal arithmetic is unsupported".into())
            }
        },
    }
}

/// Exact `1/x`; `Err` for zero, an unsupported form (`1/(a+b·t)` is not a
/// linear form; `1/(non-monomial ε-series)` is an infinite Laurent series —
/// truncating either would FABRICATE equalities, so both fail closed).
fn num_inv(x: &RcfNum) -> Result<RcfNum, String> {
    match x {
        RcfNum::Real(s) => s
            .recip()
            .map(RcfNum::Real)
            .ok_or_else(|| "value is zero (no reciprocal), or engine refinement cap".into()),
        RcfNum::Transcendental { kind, .. } => Err(format!(
            "1/(a + b·{}) is outside the supported linear form",
            kind.name()
        )),
        RcfNum::Infinitesimal { index, series } => {
            if series.len() == 1 {
                // Exact: (q·ε^k)^{-1} = q^{-1}·ε^{-k}.
                let (&e, c) = series.iter().next().expect("len == 1");
                let mut out = BTreeMap::new();
                out.insert(-e, c.recip());
                Ok(mk_inf(*index, out))
            } else {
                Err(
                    "the reciprocal of a non-monomial ε-series is an infinite Laurent series — \
                     unsupported (truncation would fabricate equalities)"
                        .into(),
                )
            }
        }
    }
}

/// Sign of a canonical (nonzero-coefficient, non-constant) ε-series under the
/// lexicographic order of ℚ((ε)): ε is a POSITIVE infinitesimal, so the term
/// with the LOWEST exponent dominates and its coefficient's sign is the sign
/// of the whole series. Exact and total; `Ordering::Equal` only for the empty
/// (zero) series.
fn inf_series_sign(series: &BTreeMap<i64, BigRational>) -> Ordering {
    match series.iter().next() {
        Some((_, coeff)) => {
            if coeff.is_positive() {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        }
        None => Ordering::Equal,
    }
}

/// Enclosure-refinement iteration cap for transcendental sign decisions. The
/// enclosure width shrinks geometrically per doubling, so provably-distinct
/// values separate after very few rounds; the cap is a fail-closed defense.
const TRANS_REFINE_ROUNDS: usize = 48;

/// Exact ordering of the transcendental linear form `a + b·kind` (b ≠ 0)
/// against a rational/algebraic scalar, by refining the rigorous enclosure of
/// the transcendental until it separates. ALWAYS terminates for these operand
/// classes: `a + b·t` with rational `a, b ≠ 0` is transcendental (Lindemann),
/// hence never equal to any rational or algebraic number, so the shrinking
/// enclosure must eventually exclude `other`. `Err` only on the defensive cap
/// or an engine comparison cap — fail-closed, never a guess.
fn cmp_trans_vs_scalar(
    kind: TransKind,
    a: &BigRational,
    b: &BigRational,
    other: &RealScalar,
) -> Result<Ordering, String> {
    let mut terms = 8usize;
    for _ in 0..TRANS_REFINE_ROUNDS {
        let (lo_t, hi_t) = rcf_series::enclosure(kind, terms);
        // lo_v < a + b·t < hi_v (strict: the enclosure of t is strict).
        let (lo_v, hi_v) = if b.is_positive() {
            (a + b * lo_t, a + b * hi_t)
        } else {
            (a + b * hi_t, a + b * lo_t)
        };
        match other.cmp_exact(&RealScalar::Rational(lo_v)) {
            Some(Ordering::Less) | Some(Ordering::Equal) => return Ok(Ordering::Greater),
            Some(Ordering::Greater) => {}
            None => return Err("engine comparison cap — fail-closed".into()),
        }
        match other.cmp_exact(&RealScalar::Rational(hi_v)) {
            Some(Ordering::Greater) | Some(Ordering::Equal) => return Ok(Ordering::Less),
            Some(Ordering::Less) => {}
            None => return Err("engine comparison cap — fail-closed".into()),
        }
        terms = terms.saturating_mul(2);
    }
    Err("transcendental enclosure refinement cap — fail-closed".into())
}

/// Ordering of two DIFFERENT-kind transcendental forms by refining both
/// enclosures until they separate. Distinct values separate quickly (π vs e);
/// if the two values were actually equal (a question number theory has not
/// settled for general rational combinations of π and e), refinement would
/// never separate them and the cap yields an honest `Err` — never a guess.
fn cmp_trans_vs_trans(
    k1: TransKind,
    a1: &BigRational,
    b1: &BigRational,
    k2: TransKind,
    a2: &BigRational,
    b2: &BigRational,
) -> Result<Ordering, String> {
    let mut terms = 8usize;
    for _ in 0..TRANS_REFINE_ROUNDS {
        let (lo1_t, hi1_t) = rcf_series::enclosure(k1, terms);
        let (lo1, hi1) = if b1.is_positive() {
            (a1 + b1 * lo1_t, a1 + b1 * hi1_t)
        } else {
            (a1 + b1 * hi1_t, a1 + b1 * lo1_t)
        };
        let (lo2_t, hi2_t) = rcf_series::enclosure(k2, terms);
        let (lo2, hi2) = if b2.is_positive() {
            (a2 + b2 * lo2_t, a2 + b2 * hi2_t)
        } else {
            (a2 + b2 * hi2_t, a2 + b2 * lo2_t)
        };
        if hi1 < lo2 {
            return Ok(Ordering::Less);
        }
        if lo1 > hi2 {
            return Ok(Ordering::Greater);
        }
        terms = terms.saturating_mul(2);
    }
    Err(
        "mixed-transcendental comparison did not separate under refinement — fail-closed \
         (equality of rational pi/e combinations is not decidable here)"
            .into(),
    )
}

/// Exact total-or-`Err` ordering over all numeral kinds. Every `Ok` answer is
/// exact: coefficient identity / GCD certificates for equality, enclosure
/// separation or lexicographic ε-order for strict orderings.
fn num_cmp(x: &RcfNum, y: &RcfNum) -> Result<Ordering, String> {
    match (x, y) {
        (RcfNum::Real(a), RcfNum::Real(b)) => a
            .cmp_exact(b)
            .ok_or_else(|| "comparison not exactly computable — fail-closed".into()),
        (RcfNum::Transcendental { kind, a, b }, RcfNum::Real(r)) => {
            cmp_trans_vs_scalar(*kind, a, b, r)
        }
        (RcfNum::Real(r), RcfNum::Transcendental { kind, a, b }) => {
            cmp_trans_vs_scalar(*kind, a, b, r).map(Ordering::reverse)
        }
        (
            RcfNum::Transcendental {
                kind: k1,
                a: a1,
                b: b1,
            },
            RcfNum::Transcendental {
                kind: k2,
                a: a2,
                b: b2,
            },
        ) => {
            if k1 == k2 {
                // Difference (a1−a2) + (b1−b2)·t: coefficient identity decides
                // equality EXACTLY; a nonzero form is compared against 0.
                let da = a1 - a2;
                let db = b1 - b2;
                if db.is_zero() {
                    Ok(da.cmp(&BigRational::zero()))
                } else {
                    cmp_trans_vs_scalar(*k1, &da, &db, &RealScalar::Rational(BigRational::zero()))
                }
            } else {
                cmp_trans_vs_trans(*k1, a1, b1, *k2, a2, b2)
            }
        }
        (
            RcfNum::Infinitesimal {
                index: i1,
                series: s1,
            },
            RcfNum::Infinitesimal {
                index: i2,
                series: s2,
            },
        ) => {
            if i1 == i2 {
                // Exact lexicographic order on the difference series.
                let mut diff = s1.clone();
                for (e, coeff) in s2 {
                    let entry = diff.entry(*e).or_insert_with(BigRational::zero);
                    *entry -= coeff;
                }
                diff.retain(|_, c| !c.is_zero());
                Ok(inf_series_sign(&diff))
            } else {
                Err(
                    "comparing two different infinitesimals is unsupported (single-generator \
                     series only)"
                        .into(),
                )
            }
        }
        (RcfNum::Infinitesimal { series, .. }, RcfNum::Real(r)) => cmp_inf_vs_scalar(series, r),
        (RcfNum::Real(r), RcfNum::Infinitesimal { series, .. }) => {
            cmp_inf_vs_scalar(series, r).map(Ordering::reverse)
        }
        (RcfNum::Infinitesimal { series, .. }, RcfNum::Transcendental { kind, a, b }) => {
            cmp_inf_vs_trans(series, *kind, a, b)
        }
        (RcfNum::Transcendental { kind, a, b }, RcfNum::Infinitesimal { series, .. }) => {
            cmp_inf_vs_trans(series, *kind, a, b).map(Ordering::reverse)
        }
    }
}

/// Ordering of an ε-series against a rational/algebraic scalar. Exact: a
/// series with a negative exponent is infinite (its leading sign decides
/// against ANY real); otherwise the standard part `a₀` decides unless it
/// exactly equals the scalar, in which case the (nonzero) infinitesimal tail
/// decides.
fn cmp_inf_vs_scalar(
    series: &BTreeMap<i64, BigRational>,
    other: &RealScalar,
) -> Result<Ordering, String> {
    if let Some((&e, coeff)) = series.iter().next() {
        if e < 0 {
            // Infinite magnitude: the sign of the leading coefficient decides
            // against every (finite) real number.
            return Ok(if coeff.is_positive() {
                Ordering::Greater
            } else {
                Ordering::Less
            });
        }
    }
    let a0 = series.get(&0).cloned().unwrap_or_else(BigRational::zero);
    match RealScalar::Rational(a0).cmp_exact(other) {
        Some(Ordering::Equal) => {
            // Standard parts coincide exactly: the infinitesimal tail (nonzero
            // by the canonical-form invariant) decides.
            let tail: BTreeMap<i64, BigRational> = series
                .iter()
                .filter(|(&e, _)| e != 0)
                .map(|(&e, c)| (e, c.clone()))
                .collect();
            Ok(inf_series_sign(&tail))
        }
        Some(ord) => Ok(ord),
        None => Err("engine comparison cap — fail-closed".into()),
    }
}

/// Ordering of an ε-series against a transcendental linear form. Exact: an
/// infinite series decides by leading sign; otherwise the rational standard
/// part `a₀` is NEVER equal to the transcendental value, so
/// [`cmp_trans_vs_scalar`] decides (the infinitesimal tail cannot bridge a
/// nonzero real gap).
fn cmp_inf_vs_trans(
    series: &BTreeMap<i64, BigRational>,
    kind: TransKind,
    a: &BigRational,
    b: &BigRational,
) -> Result<Ordering, String> {
    if let Some((&e, coeff)) = series.iter().next() {
        if e < 0 {
            return Ok(if coeff.is_positive() {
                Ordering::Greater
            } else {
                Ordering::Less
            });
        }
    }
    let a0 = series.get(&0).cloned().unwrap_or_else(BigRational::zero);
    cmp_trans_vs_scalar(kind, a, b, &RealScalar::Rational(a0)).map(Ordering::reverse)
}

/// Parse a rational literal: integer `"n"`, fraction `"n/d"`, or decimal
/// `"[-]i.f"`. `None` on a malformed string or a zero denominator.
fn parse_rcf_rational(s: &str) -> Option<BigRational> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    if let Some((n, d)) = s.split_once('/') {
        let num: BigInt = n.trim().parse().ok()?;
        let den: BigInt = d.trim().parse().ok()?;
        if den.is_zero() {
            return None;
        }
        return Some(BigRational::new(num, den));
    }
    if let Some(dot) = s.find('.') {
        let (int_part, frac_with_dot) = s.split_at(dot);
        let frac = &frac_with_dot[1..];
        let neg = int_part.starts_with('-');
        let int_digits = int_part.trim_start_matches(['-', '+']);
        if !int_digits.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        if !frac.chars().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let combined = format!(
            "{}{}",
            if int_digits.is_empty() {
                "0"
            } else {
                int_digits
            },
            frac
        );
        let num: BigInt = combined.parse().ok()?;
        let den = BigInt::from(10).pow(frac.len() as u32);
        let val = BigRational::new(num, den);
        return Some(if neg { -val } else { val });
    }
    let n: BigInt = s.parse().ok()?;
    Some(BigRational::from_integer(n))
}

/// Format a rational `q` to exactly `prec` truncated decimal places.
fn format_rational_decimal(q: &BigRational, prec: u32) -> String {
    let neg = q.is_negative();
    let q = q.abs();
    let int_part = q.floor().to_integer();
    let mut frac = &q - BigRational::from_integer(int_part.clone());
    let ten = BigRational::from_integer(BigInt::from(10));
    let mut digits = String::with_capacity(prec as usize);
    for _ in 0..prec {
        frac *= &ten;
        let d = frac.floor().to_integer();
        digits.push_str(&d.to_string());
        frac -= BigRational::from_integer(d);
    }
    let sign = if neg && (!int_part.is_zero() || digits.chars().any(|c| c != '0')) {
        "-"
    } else {
        ""
    };
    if prec == 0 {
        format!("{sign}{int_part}")
    } else {
        format!("{sign}{int_part}.{digits}")
    }
}

// ============================================================================
// Lifetime
// ============================================================================

/// Delete an RCF numeral created using the RCF API.
///
/// The arena owns every `Z3_rcf_num` and frees it exactly once at
/// `Z3_del_context`, so this is a genuine bookkeeping no-op (no per-call free,
/// no double-free), matching AY's non-RC handle discipline. It sets no error.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a` is not dereferenced.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_del(c: Z3_context, a: Z3_rcf_num) {
    let _ = a;
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics. Nothing is
    // freed here — the arena frees `a` at context drop.
    unsafe {
        ffi_guard_void(c, |_ctx| {});
    }
}

// ============================================================================
// Constructors
// ============================================================================

/// Return an RCF rational parsed from the given string.
///
/// REAL: parses an integer / fraction / decimal literal to an exact
/// `BigRational`. Malformed input → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `val`, when non-null, a
/// valid C string.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_mk_rational(c: Z3_context, val: Z3_string) -> Z3_rcf_num {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics; `val` is read
    // as a C string only after a null-check.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if val.is_null() {
                fail(ctx, "Z3_rcf_mk_rational: null string".into());
                return ptr::null_mut();
            }
            let s = match std::ffi::CStr::from_ptr(val).to_str() {
                Ok(s) => s,
                Err(_) => {
                    fail(ctx, "Z3_rcf_mk_rational: non-UTF-8 string".into());
                    return ptr::null_mut();
                }
            };
            match parse_rcf_rational(s) {
                Some(r) => produce(ctx, Some(RealScalar::Rational(r)), "Z3_rcf_mk_rational"),
                None => {
                    fail(ctx, format!("Z3_rcf_mk_rational: malformed rational '{s}'"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Return an RCF small integer.
///
/// REAL: the exact rational `val/1`.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_mk_small_int(c: Z3_context, val: c_int) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_mk_rational.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let r = RealScalar::Rational(BigRational::from_integer(BigInt::from(val)));
            produce(ctx, Some(r), "Z3_rcf_mk_small_int")
        })
    }
}

/// Return π as an RCF transcendental.
///
/// REAL: allocates the exact SYMBOLIC element π (the linear form `0 + 1·π`).
/// Comparisons refine a rigorous Machin-formula enclosure; arithmetic is exact
/// on the linear form `a + b·π` and honestly errors beyond it. See the module
/// docs.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_mk_pi(c: Z3_context) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_mk_rational.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            produce_num(
                ctx,
                Ok(mk_trans(
                    TransKind::Pi,
                    BigRational::zero(),
                    BigRational::one(),
                )),
                "Z3_rcf_mk_pi",
            )
        })
    }
}

/// Return e (Euler's constant) as an RCF transcendental.
///
/// REAL: allocates the exact SYMBOLIC element e (the linear form `0 + 1·e`),
/// with a rigorous factorial-series enclosure for comparisons. See
/// [`Z3_rcf_mk_pi`].
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_mk_e(c: Z3_context) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_mk_rational.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            produce_num(
                ctx,
                Ok(mk_trans(
                    TransKind::E,
                    BigRational::zero(),
                    BigRational::one(),
                )),
                "Z3_rcf_mk_e",
            )
        })
    }
}

/// Next free infinitesimal tower index in this context: one past the largest
/// index of any live ε generator (indices start at 3; π = 1, e = 2).
fn next_infinitesimal_index(ctx: &Z3Context) -> c_uint {
    let mut next: c_uint = 3;
    for &h in &ctx.rcf_num_cache {
        if h.is_null() {
            continue;
        }
        // SAFETY: every non-null arena entry is a live `Box::into_raw` pointer
        // owned by this context (freed only at `Z3_del_context`); shared read,
        // single-threaded per context.
        if let RcfNum::Infinitesimal { index, .. } = unsafe { &*h } {
            next = next.max(index.saturating_add(1));
        }
    }
    next
}

/// Return a new infinitesimal smaller than every positive element of the field.
///
/// REAL: allocates the exact SYMBOLIC element ε (the series `1·ε¹`) with a
/// fresh per-context tower index. Values over ε are exact rational-coefficient
/// finite Laurent series ordered lexicographically (the non-Archimedean order
/// of ℚ((ε))): `0 < ε < q` for every positive rational `q`, and `1/ε` is
/// representable (and greater than every rational). Arithmetic mixing two
/// DIFFERENT infinitesimals is an honest `Z3_EXCEPTION`.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null).
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_mk_infinitesimal(c: Z3_context) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_mk_rational.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let index = next_infinitesimal_index(ctx);
            let mut series = BTreeMap::new();
            series.insert(1_i64, BigRational::one());
            produce_num(ctx, Ok(mk_inf(index, series)), "Z3_rcf_mk_infinitesimal")
        })
    }
}

/// Store in `roots` the real roots of `a[0] + a[1]*x + ... + a[n-1]*x^(n-1)`,
/// returning the number of roots.
///
/// REAL when every coefficient is rational: exact real-root isolation
/// ([`rcf_api::real_roots`]) yields the roots in ascending order. `roots` must
/// have room for `n` handles; only the first (returned count) are written.
///
/// DIVERGENCE: any algebraic (non-rational) coefficient, or an engine cap →
/// `Z3_EXCEPTION`, `roots` untouched, return `0` (never fabricated roots).
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null). When `n > 0`, `a` must
/// point to `n` valid handles and `roots` to `n` writable slots.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_mk_roots(
    c: Z3_context,
    n: c_uint,
    a: *const Z3_rcf_num,
    roots: *mut Z3_rcf_num,
) -> c_uint {
    let n_usize = n as usize;
    // Read the coefficient handles before entering the guard.
    let coeff_handles: Vec<Z3_rcf_num> = if n_usize == 0 || a.is_null() {
        Vec::new()
    } else {
        // SAFETY: caller guarantees `a` points to `n` valid handles.
        (0..n_usize).map(|i| unsafe { *a.add(i) }).collect()
    };
    // SAFETY: `ffi_guard_uint` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            if roots.is_null() && n_usize > 0 {
                fail(ctx, "Z3_rcf_mk_roots: null roots output".into());
                return 0;
            }
            // Read each coefficient as an exact rational (low-to-high).
            let mut coeffs: Vec<BigRational> = Vec::with_capacity(n_usize);
            for &h in &coeff_handles {
                let Some(s) = expect_real(ctx, rcf_ref(h), "Z3_rcf_mk_roots") else {
                    return 0;
                };
                match rcf_api::as_rational(s) {
                    Some((num, den)) => coeffs.push(BigRational::new(num, den)),
                    None => {
                        fail(
                            ctx,
                            "Z3_rcf_mk_roots: algebraic-coefficient polynomials are not supported (rational coefficients only)".into(),
                        );
                        return 0;
                    }
                }
            }
            let real_roots = match rcf_api::real_roots(&coeffs) {
                Some(r) => r,
                None => {
                    fail(
                        ctx,
                        "Z3_rcf_mk_roots: root isolation not exactly computable — fail-closed"
                            .into(),
                    );
                    return 0;
                }
            };
            let count = real_roots.len();
            for (i, root) in real_roots.into_iter().enumerate() {
                let handle = alloc_rcf(ctx, root);
                // SAFETY (covered by the enclosing `unsafe`): `roots` has room
                // for `n >= count` slots (caller contract); `i < count <= n`.
                *roots.add(i) = handle;
            }
            ctx.last_error = Z3_OK;
            count as c_uint
        })
    }
}

// ============================================================================
// Field arithmetic
// ============================================================================

/// Return `a + b`. REAL exact addition over every supported numeral kind
/// (engine arithmetic for rational/algebraic; exact symbolic coefficient
/// arithmetic for transcendental forms and ε-series). Unsupported mixes
/// (π + e, ε + π, algebraic + symbolic) or an engine cap → `Z3_EXCEPTION` +
/// null.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_add(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_mk_rational; `a`/`b` are live handles per contract.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(x), Some(y)) = (rcf_ref(a), rcf_ref(b)) else {
                fail(ctx, "Z3_rcf_add: null operand".into());
                return ptr::null_mut();
            };
            produce_num(ctx, num_add(x, y), "Z3_rcf_add")
        })
    }
}

/// Return `a - b`. REAL exact subtraction (see [`Z3_rcf_add`]); unsupported
/// mix or engine cap → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_sub(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_add.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(x), Some(y)) = (rcf_ref(a), rcf_ref(b)) else {
                fail(ctx, "Z3_rcf_sub: null operand".into());
                return ptr::null_mut();
            };
            produce_num(ctx, num_add(x, &num_neg(y)), "Z3_rcf_sub")
        })
    }
}

/// Return `a * b`. REAL exact multiplication (engine arithmetic; rational
/// scaling of a transcendental form; exact convolution of ε-series). A product
/// leaving the supported forms (π·π, π·ε, algebraic·symbolic) or an engine cap
/// → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_mul(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_add.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(x), Some(y)) = (rcf_ref(a), rcf_ref(b)) else {
                fail(ctx, "Z3_rcf_mul: null operand".into());
                return ptr::null_mut();
            };
            produce_num(ctx, num_mul(x, y), "Z3_rcf_mul")
        })
    }
}

/// Return `a / b`. REAL exact division (`a · b⁻¹`); a zero divisor, a divisor
/// with no representable reciprocal (see [`Z3_rcf_inv`]) or an engine cap →
/// `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_div(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_add.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let (Some(x), Some(y)) = (rcf_ref(a), rcf_ref(b)) else {
                fail(ctx, "Z3_rcf_div: null operand".into());
                return ptr::null_mut();
            };
            let r = num_inv(y).and_then(|inv| num_mul(x, &inv));
            produce_num(ctx, r, "Z3_rcf_div")
        })
    }
}

/// Return `-a`. REAL exact negation (total over every numeral kind).
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_neg(c: Z3_context, a: Z3_rcf_num) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_add.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(x) = rcf_ref(a) else {
                fail(ctx, "Z3_rcf_neg: null operand".into());
                return ptr::null_mut();
            };
            produce_num(ctx, Ok(num_neg(x)), "Z3_rcf_neg")
        })
    }
}

/// Return `1/a`. REAL exact reciprocal for rational/algebraic values and for
/// ε-monomials (`(q·εᵏ)⁻¹ = q⁻¹·ε⁻ᵏ`, exact in the Laurent representation).
/// Zero, `1/(a + b·t)` (not a linear form) and non-monomial ε-series (an
/// infinite Laurent series — truncation would fabricate equalities) →
/// `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_inv(c: Z3_context, a: Z3_rcf_num) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_add.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(x) = rcf_ref(a) else {
                fail(ctx, "Z3_rcf_inv: null operand".into());
                return ptr::null_mut();
            };
            produce_num(ctx, num_inv(x), "Z3_rcf_inv")
        })
    }
}

/// Return `a^k`. REAL exact power (`k == 0` → `1`, iterated exact
/// multiplication otherwise — so ε-series powers are exact, and `k ≥ 2` on a
/// transcendental form honestly errors like [`Z3_rcf_mul`]); engine cap →
/// `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` must be a valid `Z3_context` pointer (or null); `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_power(c: Z3_context, a: Z3_rcf_num, k: c_uint) -> Z3_rcf_num {
    // SAFETY: see Z3_rcf_add.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            if k > MAX_FFI_ALGEBRAIC_EXPONENT {
                fail(
                    ctx,
                    format!(
                        "Z3_rcf_power: exponent {k} exceeds the supported maximum {MAX_FFI_ALGEBRAIC_EXPONENT}"
                    ),
                );
                return ptr::null_mut();
            }
            let Some(x) = rcf_ref(a) else {
                fail(ctx, "Z3_rcf_power: null operand".into());
                return ptr::null_mut();
            };
            let mut acc = RcfNum::Real(RealScalar::Rational(BigRational::one()));
            for _ in 0..k {
                match num_mul(&acc, x) {
                    Ok(v) => acc = v,
                    Err(msg) => {
                        fail(ctx, format!("Z3_rcf_power: {msg}"));
                        return ptr::null_mut();
                    }
                }
            }
            produce_num(ctx, Ok(acc), "Z3_rcf_power")
        })
    }
}

// ============================================================================
// Ordering / equality predicates
// ============================================================================

/// Evaluate an exact comparison predicate over any two numeral kinds; an `Err`
/// (unsupported mix / refinement cap) → `Z3_EXCEPTION` + `false` (NEVER a
/// default that reads as a real ordering).
///
/// # Safety
/// `c` valid or null; `a`/`b` live handles.
unsafe fn rcf_cmp(
    c: Z3_context,
    a: Z3_rcf_num,
    b: Z3_rcf_num,
    who: &str,
    pred: impl FnOnce(Ordering) -> bool,
) -> bool {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let (Some(x), Some(y)) = (rcf_ref(a), rcf_ref(b)) else {
                fail(ctx, format!("{who}: null operand"));
                return 0;
            };
            match num_cmp(x, y) {
                Ok(ord) => {
                    ctx.last_error = Z3_OK;
                    c_int::from(pred(ord))
                }
                Err(msg) => {
                    fail(ctx, format!("{who}: {msg}"));
                    0
                }
            }
        }) != 0
    }
}

/// Return `true` if `a < b`. REAL exact ordering; cap → `Z3_EXCEPTION` + false.
///
/// # Safety
/// `c` valid or null; `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_lt(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_cmp.
    unsafe { rcf_cmp(c, a, b, "Z3_rcf_lt", |o| o == Ordering::Less) }
}

/// Return `true` if `a > b`. REAL exact ordering; cap → `Z3_EXCEPTION` + false.
///
/// # Safety
/// `c` valid or null; `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_gt(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_cmp.
    unsafe { rcf_cmp(c, a, b, "Z3_rcf_gt", |o| o == Ordering::Greater) }
}

/// Return `true` if `a <= b`. REAL exact ordering; cap → `Z3_EXCEPTION` + false.
///
/// # Safety
/// `c` valid or null; `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_le(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_cmp.
    unsafe { rcf_cmp(c, a, b, "Z3_rcf_le", |o| o != Ordering::Greater) }
}

/// Return `true` if `a >= b`. REAL exact ordering; cap → `Z3_EXCEPTION` + false.
///
/// # Safety
/// `c` valid or null; `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_ge(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_cmp.
    unsafe { rcf_cmp(c, a, b, "Z3_rcf_ge", |o| o != Ordering::Less) }
}

/// Return `true` if `a == b`. REAL GCD-certified equality; cap → `Z3_EXCEPTION`
/// + false.
///
/// # Safety
/// `c` valid or null; `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_eq(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_cmp.
    unsafe { rcf_cmp(c, a, b, "Z3_rcf_eq", |o| o == Ordering::Equal) }
}

/// Return `true` if `a != b`. REAL exact disequality; cap → `Z3_EXCEPTION` +
/// false.
///
/// # Safety
/// `c` valid or null; `a`/`b` live handles.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_neq(c: Z3_context, a: Z3_rcf_num, b: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_cmp.
    unsafe { rcf_cmp(c, a, b, "Z3_rcf_neq", |o| o != Ordering::Equal) }
}

// ============================================================================
// Stringification
// ============================================================================

/// Render a rational as `n` or `n/d`.
fn rational_string(q: &BigRational) -> String {
    if q.denom().is_one() {
        q.numer().to_string()
    } else {
        format!("{}/{}", q.numer(), q.denom())
    }
}

/// Exact symbolic rendering of a transcendental linear form `a + b·t`.
fn trans_string(kind: TransKind, a: &BigRational, b: &BigRational) -> String {
    let t = kind.name();
    let bt = if b.is_one() {
        t.to_string()
    } else {
        format!("(* {} {t})", rational_string(b))
    };
    if a.is_zero() {
        bt
    } else {
        format!("(+ {} {bt})", rational_string(a))
    }
}

/// Exact symbolic rendering of an ε-series (ascending exponents).
fn inf_string(index: c_uint, series: &BTreeMap<i64, BigRational>) -> String {
    let eps = format!("eps!{index}");
    let mut parts: Vec<String> = Vec::with_capacity(series.len());
    for (&e, coeff) in series {
        let base = match e {
            0 => rational_string(coeff),
            1 if coeff.is_one() => eps.clone(),
            1 => format!("(* {} {eps})", rational_string(coeff)),
            _ if e > 0 && coeff.is_one() => format!("(^ {eps} {e})"),
            _ if e > 0 => format!("(* {} (^ {eps} {e}))", rational_string(coeff)),
            _ => format!("(/ {} (^ {eps} {}))", rational_string(coeff), -e),
        };
        parts.push(base);
    }
    match parts.len() {
        1 => parts.pop().expect("len == 1"),
        _ => format!("(+ {})", parts.join(" ")),
    }
}

/// Convert the RCF numeral into a string.
///
/// REAL: a rational renders as `n` / `n/d`; an algebraic value renders in z3
/// `root-obj` syntax; a transcendental form renders symbolically (`pi`,
/// `(+ 1 pi)`, `(* 2 e)`); an ε-series renders symbolically over `eps!<idx>`.
/// Cap → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_num_to_string(
    c: Z3_context,
    a: Z3_rcf_num,
    compact: bool,
    html: bool,
) -> Z3_string {
    let _ = (compact, html);
    // SAFETY: `ffi_guard_const_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(n) = rcf_ref(a) else {
                fail(ctx, "Z3_rcf_num_to_string: null operand".into());
                return ptr::null();
            };
            let rendered = match n {
                RcfNum::Real(s) => match rcf_api::as_rational(s) {
                    Some((num, den)) => rational_string(&BigRational::new(num, den)),
                    None => match rcf_api::root_obj_string(s) {
                        Some(txt) => txt,
                        None => {
                            fail(
                                ctx,
                                "Z3_rcf_num_to_string: not exactly computable — fail-closed".into(),
                            );
                            return ptr::null();
                        }
                    },
                },
                RcfNum::Transcendental { kind, a, b } => trans_string(*kind, a, b),
                RcfNum::Infinitesimal { index, series } => inf_string(*index, series),
            };
            ctx.last_error = Z3_OK;
            cache_string(ctx, rendered)
        })
    }
}

/// Convert the RCF numeral into a truncated decimal string (`prec` places).
///
/// REAL: exact for a rational; an algebraic value refines its isolating
/// interval; a transcendental form refines its rigorous series enclosure until
/// the truncation stabilizes (terminates: the value is irrational, never on a
/// decimal-grid boundary); a finite ε-series truncates EXACTLY (an
/// infinitesimal tail crosses a grid boundary only when the standard part sits
/// exactly on one, which is decided by exact rational arithmetic). Every
/// irrational/non-standard value carries a trailing `?` (display-only
/// approximation, never fed to a comparison). An ε-series with a negative
/// exponent (infinite magnitude) or a cap → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_num_to_decimal_string(
    c: Z3_context,
    a: Z3_rcf_num,
    prec: c_uint,
) -> Z3_string {
    // SAFETY: `ffi_guard_const_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_const_ptr(c, |ctx| {
            let Some(n) = rcf_ref(a) else {
                fail(ctx, "Z3_rcf_num_to_decimal_string: null operand".into());
                return ptr::null();
            };
            let is_rational =
                matches!(n, RcfNum::Real(value) if rcf_api::as_rational(value).is_some());
            let max_precision = if is_rational {
                MAX_FFI_DECIMAL_PRECISION
            } else {
                MAX_FFI_REFINEMENT_PRECISION
            };
            if prec > max_precision {
                fail(
                    ctx,
                    format!(
                        "Z3_rcf_num_to_decimal_string: precision {prec} exceeds the supported maximum {max_precision}"
                    ),
                );
                return ptr::null();
            }
            match num_decimal_string(n, prec) {
                Ok(txt) => {
                    ctx.last_error = Z3_OK;
                    cache_string(ctx, txt)
                }
                Err(msg) => {
                    fail(ctx, format!("Z3_rcf_num_to_decimal_string: {msg}"));
                    ptr::null()
                }
            }
        })
    }
}

/// Decimal rendering over every numeral kind (see the entry point's docs).
fn num_decimal_string(n: &RcfNum, prec: c_uint) -> Result<String, String> {
    match n {
        RcfNum::Real(s) => {
            decimal_string(s, prec).ok_or_else(|| "not exactly computable — fail-closed".into())
        }
        RcfNum::Transcendental { kind, a, b } => trans_decimal_string(*kind, a, b, prec),
        RcfNum::Infinitesimal { series, .. } => inf_decimal_string(series, prec),
    }
}

/// Truncated decimal of `a + b·t` (`b ≠ 0`): refine the rigorous enclosure of
/// `t` until BOTH endpoint truncations agree — that common prefix is the exact
/// truncation of the (irrational) value, marked `?`. Terminates because an
/// irrational value never sits exactly on the truncation grid; the round cap
/// is fail-closed defense (display-only path).
fn trans_decimal_string(
    kind: TransKind,
    a: &BigRational,
    b: &BigRational,
    prec: c_uint,
) -> Result<String, String> {
    let mut terms = 8usize;
    for _ in 0..TRANS_REFINE_ROUNDS {
        let (lo_t, hi_t) = rcf_series::enclosure(kind, terms);
        let (lo_v, hi_v) = if b.is_positive() {
            (a + b * lo_t, a + b * hi_t)
        } else {
            (a + b * hi_t, a + b * lo_t)
        };
        let dl = format_rational_decimal(&lo_v, prec);
        if dl == format_rational_decimal(&hi_v, prec) {
            return Ok(format!("{dl}?"));
        }
        terms = terms.saturating_mul(2);
    }
    Err("decimal refinement cap — fail-closed".into())
}

/// EXACT truncated decimal of a finite ε-series `a₀ + h` (`h` = the nonzero
/// infinitesimal tail): `trunc(|a₀ + h|·10^p)` equals `trunc(|a₀|·10^p)`
/// except when `a₀·10^p` lands exactly on an integer and the tail pulls the
/// magnitude below it — all decided by exact rational arithmetic. A series
/// with a negative exponent has infinite magnitude → `Err`.
fn inf_decimal_string(series: &BTreeMap<i64, BigRational>, prec: c_uint) -> Result<String, String> {
    if series.keys().next().is_some_and(|&e| e < 0) {
        return Err(
            "the value has infinite magnitude (negative ε-exponent) — no decimal rendering".into(),
        );
    }
    let a0 = series.get(&0).cloned().unwrap_or_else(BigRational::zero);
    // Sign of the infinitesimal tail = sign of the lowest POSITIVE exponent's
    // coefficient (nonzero by the canonical-form invariant).
    let tail_sign_positive = series
        .iter()
        .find(|(&e, _)| e > 0)
        .map(|(_, c)| c.is_positive())
        .ok_or_else(|| "malformed ε-series (no non-constant term)".to_string())?;
    // Value sign: a₀ decides unless it is exactly zero.
    let value_negative = a0.is_negative() || (a0.is_zero() && !tail_sign_positive);
    // |value|·10^p = S ± tail·10^p with S = |a₀|·10^p and the tail's sign
    // flipped for negative values.
    let ten_p = BigRational::from_integer(BigInt::from(10).pow(prec));
    let s = a0.abs() * &ten_p;
    let mag_tail_positive = tail_sign_positive != value_negative;
    let floor_s = s.floor().to_integer();
    let digits_int = if s == BigRational::from_integer(floor_s.clone()) && !mag_tail_positive {
        // Exactly on the grid with a negative tail: the magnitude sits just
        // below the boundary. (Never negative: |value| > 0 keeps the floor
        // ≥ 0; a₀ = 0 with a negative tail was folded into `value_negative`.)
        &floor_s - BigInt::one()
    } else {
        floor_s
    };
    let digits_int = if digits_int.is_negative() {
        BigInt::zero() // defensive: |value| < 10^-p rounds to all zeros
    } else {
        digits_int
    };
    let text = digits_int.to_string();
    let p = prec as usize;
    let padded = if text.len() <= p {
        format!("{}{}", "0".repeat(p + 1 - text.len()), text)
    } else {
        text
    };
    let (int_part, frac_part) = padded.split_at(padded.len() - p);
    let all_zero = digits_int.is_zero();
    let sign = if value_negative && !all_zero { "-" } else { "" };
    Ok(if prec == 0 {
        format!("{sign}{int_part}?")
    } else {
        format!("{sign}{int_part}.{frac_part}?")
    })
}

/// Decimal rendering of a scalar to `prec` places (approximate + `?` for a
/// genuine algebraic, exact for a rational). `None` on a refinement cap.
fn decimal_string(s: &RealScalar, prec: c_uint) -> Option<String> {
    match rcf_api::canonicalize(s)? {
        RealScalar::Rational(r) => Some(format_rational_decimal(&r, prec)),
        RealScalar::Algebraic(v) => {
            let alpha = v.alpha();
            let (lo0, hi0) = alpha.interval();
            let (mut lo, mut hi) = (lo0.clone(), hi0.clone());
            let two = BigRational::from_integer(BigInt::from(2));
            // Refine until the lower and upper bounds truncate to the SAME
            // `prec`-digit decimal — that common prefix is then the exact
            // truncation of the (irrational) value. A `?` marks the value as an
            // approximation (display-only; never fed to a comparison).
            let cap = 4 * prec as usize + 256;
            for _ in 0..cap {
                let dl = format_rational_decimal(&lo, prec);
                if dl == format_rational_decimal(&hi, prec) {
                    return Some(format!("{dl}?"));
                }
                let mid = (&lo + &hi) / &two;
                match alpha.cmp_rational(&mid)? {
                    Ordering::Less => hi = mid,    // value < mid
                    Ordering::Greater => lo = mid, // value > mid
                    // An irrational never equals a rational midpoint, but stay
                    // fail-safe: the exact value is `mid`, truncate it.
                    Ordering::Equal => {
                        return Some(format!("{}?", format_rational_decimal(&mid, prec)))
                    }
                }
            }
            // Cap hit (display-only): return the lower bound's truncation.
            Some(format!("{}?", format_rational_decimal(&lo, prec)))
        }
    }
}

// ============================================================================
// Structural extraction / introspection
// ============================================================================

/// Extract the numerator `n` and denominator `d` such that `a = n/d`.
///
/// REAL: a rational yields `(num, den)`; a genuine algebraic yields `(a, 1)`
/// (its value is not a ratio of two rationals — z3's contract). A
/// transcendental/infinitesimal operand or a cap → `Z3_EXCEPTION` + cleared
/// outputs.
///
/// # Safety
/// `c` valid or null; `a` a live handle; `n`/`d`, when non-null, writable
/// `Z3_rcf_num` slots.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_get_numerator_denominator(
    c: Z3_context,
    a: Z3_rcf_num,
    n: *mut Z3_rcf_num,
    d: *mut Z3_rcf_num,
) {
    // SAFETY: `ffi_guard_void` null-checks `c` and catches panics; `n`/`d`
    // written only after a null-check.
    unsafe {
        ffi_guard_void(c, |ctx| {
            let clear = |ctx: &mut Z3Context, msg: String| {
                fail(ctx, msg);
                if !n.is_null() {
                    *n = ptr::null_mut();
                }
                if !d.is_null() {
                    *d = ptr::null_mut();
                }
            };
            let Some(s) = expect_real(ctx, rcf_ref(a), "Z3_rcf_get_numerator_denominator") else {
                let msg = ctx
                    .error_msg
                    .clone()
                    .unwrap_or_else(|| "Z3_rcf_get_numerator_denominator: invalid operand".into());
                clear(ctx, msg);
                return;
            };
            let (num_scalar, den_scalar) = match rcf_api::canonicalize(s) {
                Some(RealScalar::Rational(r)) => (
                    RealScalar::Rational(BigRational::from_integer(r.numer().clone())),
                    RealScalar::Rational(BigRational::from_integer(r.denom().clone())),
                ),
                Some(alg) => (alg, RealScalar::Rational(BigRational::one())),
                None => {
                    clear(
                        ctx,
                        "Z3_rcf_get_numerator_denominator: not exactly computable — fail-closed"
                            .into(),
                    );
                    return;
                }
            };
            let nh = alloc_rcf(ctx, num_scalar);
            let dh = alloc_rcf(ctx, den_scalar);
            if !n.is_null() {
                *n = nh;
            }
            if !d.is_null() {
                *d = dh;
            }
            ctx.last_error = Z3_OK;
        });
    }
}

/// Boolean classifier over any numeral kind; `Err` (cap) → `Z3_EXCEPTION` +
/// false.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
unsafe fn rcf_classify(
    c: Z3_context,
    a: Z3_rcf_num,
    who: &str,
    pred: impl FnOnce(&RcfNum) -> Option<bool>,
) -> bool {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some(n) = rcf_ref(a) else {
                fail(ctx, format!("{who}: null operand"));
                return 0;
            };
            match pred(n) {
                Some(b) => {
                    ctx.last_error = Z3_OK;
                    c_int::from(b)
                }
                None => {
                    fail(ctx, format!("{who}: not exactly computable — fail-closed"));
                    0
                }
            }
        }) != 0
    }
}

/// Return `true` if `a` represents a rational number. REAL exact
/// classification over every kind: transcendental forms (irrational by
/// Lindemann) and ε-series (not real numbers at all) are exactly `false`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_is_rational(c: Z3_context, a: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_classify.
    unsafe {
        rcf_classify(c, a, "Z3_rcf_is_rational", |n| match n {
            RcfNum::Real(s) => rcf_api::is_rational(s),
            RcfNum::Transcendental { .. } | RcfNum::Infinitesimal { .. } => Some(false),
        })
    }
}

/// Return `true` if `a` represents an (irrational) algebraic number. REAL exact
/// classification — rationals report `false` (they are the rational class, not
/// the algebraic-extension class, matching z3's mutually-exclusive taxonomy);
/// transcendental forms are provably NOT algebraic (`a + b·t` algebraic would
/// make `t` algebraic) and ε-series are non-Archimedean, so both are exactly
/// `false`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_is_algebraic(c: Z3_context, a: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_classify.
    unsafe {
        rcf_classify(c, a, "Z3_rcf_is_algebraic", |n| match n {
            RcfNum::Real(s) => rcf_api::is_rational(s).map(|r| !r),
            RcfNum::Transcendental { .. } | RcfNum::Infinitesimal { .. } => Some(false),
        })
    }
}

/// Return `true` if `a` represents an infinitesimal.
///
/// REAL exact classification: `true` exactly for values represented in an
/// infinitesimal extension (the canonical-form invariant guarantees such a
/// value genuinely depends on ε — this includes `1/ε`, which lives in the
/// extension while being infinite); rational/algebraic/transcendental values
/// are exactly `false`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_is_infinitesimal(c: Z3_context, a: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_classify.
    unsafe {
        rcf_classify(c, a, "Z3_rcf_is_infinitesimal", |n| {
            Some(matches!(n, RcfNum::Infinitesimal { .. }))
        })
    }
}

/// Return `true` if `a` represents a transcendental number.
///
/// REAL exact classification: `true` exactly for the symbolic linear forms
/// `a + b·t` with `b ≠ 0` (transcendental by Lindemann); rationals, algebraics
/// and ε-series are exactly `false`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_is_transcendental(c: Z3_context, a: Z3_rcf_num) -> bool {
    // SAFETY: see rcf_classify.
    unsafe {
        rcf_classify(c, a, "Z3_rcf_is_transcendental", |n| {
            Some(matches!(n, RcfNum::Transcendental { .. }))
        })
    }
}

/// Return the index of a field extension.
///
/// REAL for extension elements (z3's precondition: the operand is
/// transcendental or infinitesimal): AY's per-context tower numbering is
/// π = 1, e = 2, infinitesimals = 3, 4, ... in creation order (indices are
/// opaque ordinals in z3 too). A rational/algebraic operand violates the
/// precondition → honest `Z3_EXCEPTION` + `0`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_extension_index(c: Z3_context, a: Z3_rcf_num) -> c_uint {
    // SAFETY: `ffi_guard_uint` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| match rcf_ref(a) {
            Some(RcfNum::Transcendental { kind, .. }) => {
                ctx.last_error = Z3_OK;
                match kind {
                    TransKind::Pi => 1,
                    TransKind::E => 2,
                }
            }
            Some(RcfNum::Infinitesimal { index, .. }) => {
                ctx.last_error = Z3_OK;
                *index
            }
            Some(RcfNum::Real(_)) => {
                fail(
                    ctx,
                    "Z3_rcf_extension_index: the operand is rational/algebraic — not a \
                         transcendental/infinitesimal extension element (z3 precondition)"
                        .into(),
                );
                0
            }
            None => {
                fail(ctx, "Z3_rcf_extension_index: null operand".into());
                0
            }
        })
    }
}

/// Return the name of a transcendental.
///
/// REAL: `pi` / `e` for a transcendental form (the extension it lives in);
/// any other operand violates z3's precondition → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_transcendental_name(c: Z3_context, a: Z3_rcf_num) -> Z3_symbol {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| match rcf_ref(a) {
            Some(RcfNum::Transcendental { kind, .. }) => {
                ctx.last_error = Z3_OK;
                cache_symbol(ctx, kind.name().to_string())
            }
            Some(_) => {
                fail(
                    ctx,
                    "Z3_rcf_transcendental_name: the operand is not a transcendental (z3 \
                     precondition)"
                        .into(),
                );
                ptr::null_mut()
            }
            None => {
                fail(ctx, "Z3_rcf_transcendental_name: null operand".into());
                ptr::null_mut()
            }
        })
    }
}

/// Return the name of an infinitesimal.
///
/// REAL: `eps!<tower-index>` for an ε-series value; any other operand violates
/// z3's precondition → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_infinitesimal_name(c: Z3_context, a: Z3_rcf_num) -> Z3_symbol {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| match rcf_ref(a) {
            Some(RcfNum::Infinitesimal { index, .. }) => {
                ctx.last_error = Z3_OK;
                cache_symbol(ctx, format!("eps!{index}"))
            }
            Some(_) => {
                fail(
                    ctx,
                    "Z3_rcf_infinitesimal_name: the operand is not an infinitesimal (z3 \
                     precondition)"
                        .into(),
                );
                ptr::null_mut()
            }
            None => {
                fail(ctx, "Z3_rcf_infinitesimal_name: null operand".into());
                ptr::null_mut()
            }
        })
    }
}

/// Return the number of coefficients in the defining polynomial of `a`.
///
/// REAL: for a genuine algebraic value, the degree + 1 of its square-free
/// defining polynomial; for a rational, `2` (`den*x - num`). A transcendental/
/// infinitesimal operand has NO defining polynomial over ℚ → `Z3_EXCEPTION` +
/// `0` (also on a cap).
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_num_coefficients(c: Z3_context, a: Z3_rcf_num) -> c_uint {
    // SAFETY: `ffi_guard_uint` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(s) = expect_real(ctx, rcf_ref(a), "Z3_rcf_num_coefficients") else {
                return 0;
            };
            match rcf_api::defining_coeffs(s) {
                Some(coeffs) => {
                    ctx.last_error = Z3_OK;
                    coeffs.len() as c_uint
                }
                None => {
                    fail(
                        ctx,
                        "Z3_rcf_num_coefficients: not exactly computable — fail-closed".into(),
                    );
                    0
                }
            }
        })
    }
}

/// Extract the `i`-th coefficient of the defining polynomial (low-to-high) as an
/// RCF rational.
///
/// REAL; out-of-range `i` or cap → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_coefficient(c: Z3_context, a: Z3_rcf_num, i: c_uint) -> Z3_rcf_num {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(s) = expect_real(ctx, rcf_ref(a), "Z3_rcf_coefficient") else {
                return ptr::null_mut();
            };
            let coeffs = match rcf_api::defining_coeffs(s) {
                Some(v) => v,
                None => {
                    fail(
                        ctx,
                        "Z3_rcf_coefficient: not exactly computable — fail-closed".into(),
                    );
                    return ptr::null_mut();
                }
            };
            match coeffs.get(i as usize) {
                Some(coeff) => {
                    let scalar = RealScalar::Rational(BigRational::from_integer(coeff.clone()));
                    produce(ctx, Some(scalar), "Z3_rcf_coefficient")
                }
                None => {
                    fail(ctx, format!("Z3_rcf_coefficient: index {i} out of range"));
                    ptr::null_mut()
                }
            }
        })
    }
}

/// Extract the isolating interval of `a`.
///
/// REAL: a genuine algebraic value yields its open rational endpoints (both
/// finite, both open); a rational yields the degenerate closed point `[a, a]`;
/// a transcendental form yields a RIGOROUS open rational enclosure from its
/// series bounds. Returns `1` on success. An ε-series (no faithful Archimedean
/// interval) or a cap → `Z3_EXCEPTION`, cleared outputs, `0`.
///
/// # Safety
/// `c` valid or null; `a` a live handle; every non-null output points to a
/// writable location of its element type.
#[no_mangle]
#[allow(clippy::too_many_arguments)]
pub unsafe extern "C" fn Z3_rcf_interval(
    c: Z3_context,
    a: Z3_rcf_num,
    lower_is_inf: *mut bool,
    lower_is_open: *mut bool,
    lower: *mut Z3_rcf_num,
    upper_is_inf: *mut bool,
    upper_is_open: *mut bool,
    upper: *mut Z3_rcf_num,
) -> c_int {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics; every output
    // is written only after an explicit null-check.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let clear = |ctx: &mut Z3Context, msg: String| {
                fail(ctx, msg);
                for p in [lower_is_inf, lower_is_open, upper_is_inf, upper_is_open] {
                    if !p.is_null() {
                        *p = false;
                    }
                }
                if !lower.is_null() {
                    *lower = ptr::null_mut();
                }
                if !upper.is_null() {
                    *upper = ptr::null_mut();
                }
            };
            let Some(n) = rcf_ref(a) else {
                clear(ctx, "Z3_rcf_interval: null operand".into());
                return 0;
            };
            let (lo, hi, open) = match n {
                RcfNum::Real(s) => match rcf_api::canonicalize(s) {
                    Some(RealScalar::Rational(r)) => (r.clone(), r, false),
                    Some(_) => match rcf_api::interval(s) {
                        Some((lo, hi)) => (lo, hi, true),
                        None => {
                            clear(
                                ctx,
                                "Z3_rcf_interval: not exactly computable — fail-closed".into(),
                            );
                            return 0;
                        }
                    },
                    None => {
                        clear(
                            ctx,
                            "Z3_rcf_interval: not exactly computable — fail-closed".into(),
                        );
                        return 0;
                    }
                },
                RcfNum::Transcendental { kind, a: qa, b: qb } => {
                    // A rigorous (strict) enclosure of a + b·t; 64 series terms
                    // give far more than double-precision width.
                    let (lo_t, hi_t) = rcf_series::enclosure(*kind, 64);
                    if qb.is_positive() {
                        (qa + qb * lo_t, qa + qb * hi_t, true)
                    } else {
                        (qa + qb * hi_t, qa + qb * lo_t, true)
                    }
                }
                RcfNum::Infinitesimal { .. } => {
                    clear(
                        ctx,
                        "Z3_rcf_interval: an infinitesimal has no faithful Archimedean rational \
                         interval"
                            .into(),
                    );
                    return 0;
                }
            };
            if !lower_is_inf.is_null() {
                *lower_is_inf = false;
            }
            if !upper_is_inf.is_null() {
                *upper_is_inf = false;
            }
            if !lower_is_open.is_null() {
                *lower_is_open = open;
            }
            if !upper_is_open.is_null() {
                *upper_is_open = open;
            }
            let lo_h = alloc_rcf(ctx, RealScalar::Rational(lo));
            let hi_h = alloc_rcf(ctx, RealScalar::Rational(hi));
            if !lower.is_null() {
                *lower = lo_h;
            }
            if !upper.is_null() {
                *upper = hi_h;
            }
            ctx.last_error = Z3_OK;
            1
        })
    }
}

// ============================================================================
// Thom sign-condition family (root discriminator of the defining polynomial)
// ============================================================================

/// Return the number of Thom sign conditions of `a` (derivative-tower signs that
/// pin the root among the roots of its defining polynomial).
///
/// REAL: `deg(p) - 1` for a genuine algebraic value, `0` for a rational. Cap →
/// `Z3_EXCEPTION` + `0`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_num_sign_conditions(c: Z3_context, a: Z3_rcf_num) -> c_uint {
    // SAFETY: `ffi_guard_uint` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(s) = expect_real(ctx, rcf_ref(a), "Z3_rcf_num_sign_conditions") else {
                return 0;
            };
            match rcf_api::thom_sign_conditions(s) {
                Some(conds) => {
                    ctx.last_error = Z3_OK;
                    conds.len() as c_uint
                }
                None => {
                    fail(
                        ctx,
                        "Z3_rcf_num_sign_conditions: not exactly computable — fail-closed".into(),
                    );
                    0
                }
            }
        })
    }
}

/// Extract the sign (`-1`/`0`/`1`) of the `i`-th Thom sign condition.
///
/// REAL; out-of-range `i` or cap → `Z3_EXCEPTION` + `0`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_sign_condition_sign(
    c: Z3_context,
    a: Z3_rcf_num,
    i: c_uint,
) -> c_int {
    // SAFETY: `ffi_guard_int` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_int(c, 0, |ctx| {
            let Some(s) = expect_real(ctx, rcf_ref(a), "Z3_rcf_sign_condition_sign") else {
                return 0;
            };
            match rcf_api::thom_sign_conditions(s) {
                Some(conds) => match conds.get(i as usize) {
                    Some((_, sign)) => {
                        ctx.last_error = Z3_OK;
                        *sign
                    }
                    None => {
                        fail(
                            ctx,
                            format!("Z3_rcf_sign_condition_sign: index {i} out of range"),
                        );
                        0
                    }
                },
                None => {
                    fail(
                        ctx,
                        "Z3_rcf_sign_condition_sign: not exactly computable — fail-closed".into(),
                    );
                    0
                }
            }
        })
    }
}

/// Return the number of polynomial coefficients of the `i`-th Thom sign
/// condition.
///
/// REAL; out-of-range `i` or cap → `Z3_EXCEPTION` + `0`.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_num_sign_condition_coefficients(
    c: Z3_context,
    a: Z3_rcf_num,
    i: c_uint,
) -> c_uint {
    // SAFETY: `ffi_guard_uint` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_uint(c, 0, |ctx| {
            let Some(s) = expect_real(ctx, rcf_ref(a), "Z3_rcf_num_sign_condition_coefficients")
            else {
                return 0;
            };
            match rcf_api::thom_sign_conditions(s) {
                Some(conds) => {
                    match conds.get(i as usize) {
                        Some((coeffs, _)) => {
                            ctx.last_error = Z3_OK;
                            coeffs.len() as c_uint
                        }
                        None => {
                            fail(ctx, format!("Z3_rcf_num_sign_condition_coefficients: index {i} out of range"));
                            0
                        }
                    }
                }
                None => {
                    fail(ctx, "Z3_rcf_num_sign_condition_coefficients: not exactly computable — fail-closed".into());
                    0
                }
            }
        })
    }
}

/// Extract the `j`-th polynomial coefficient of the `i`-th Thom sign condition as
/// an RCF rational.
///
/// REAL; out-of-range indices or cap → `Z3_EXCEPTION` + null.
///
/// # Safety
/// `c` valid or null; `a` a live handle.
#[no_mangle]
pub unsafe extern "C" fn Z3_rcf_sign_condition_coefficient(
    c: Z3_context,
    a: Z3_rcf_num,
    i: c_uint,
    j: c_uint,
) -> Z3_rcf_num {
    // SAFETY: `ffi_guard_ptr` null-checks `c` and catches panics.
    unsafe {
        ffi_guard_ptr(c, |ctx| {
            let Some(s) = expect_real(ctx, rcf_ref(a), "Z3_rcf_sign_condition_coefficient") else {
                return ptr::null_mut();
            };
            let conds = match rcf_api::thom_sign_conditions(s) {
                Some(v) => v,
                None => {
                    fail(
                        ctx,
                        "Z3_rcf_sign_condition_coefficient: not exactly computable — fail-closed"
                            .into(),
                    );
                    return ptr::null_mut();
                }
            };
            match conds
                .get(i as usize)
                .and_then(|(coeffs, _)| coeffs.get(j as usize))
            {
                Some(coeff) => {
                    let scalar = RealScalar::Rational(BigRational::from_integer(coeff.clone()));
                    produce(ctx, Some(scalar), "Z3_rcf_sign_condition_coefficient")
                }
                None => {
                    fail(
                        ctx,
                        format!("Z3_rcf_sign_condition_coefficient: index ({i},{j}) out of range"),
                    );
                    ptr::null_mut()
                }
            }
        })
    }
}

#[cfg(test)]
#[path = "rcf_tests.rs"]
mod rcf_tests;

#[cfg(test)]
#[path = "rcf_ext_tests.rs"]
mod rcf_ext_tests;
