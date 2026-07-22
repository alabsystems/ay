// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Arithmetic operator implementations for [`Rational`].

use crate::rational::{gcd_u64, normalize_small, try_shrink, BigBacking, Rational};
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, ToPrimitive, Zero};
use std::borrow::Cow;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

// --- Helpers ----------------------------------------------------------------

/// Binary GCD for u128 (no allocation, no division).
/// #8782: Used by try_add/sub/mul_small to reduce i128 intermediates back to i64.
#[inline]
fn gcd_u128(mut a: u128, mut b: u128) -> u128 {
    if a == 0 {
        return b;
    }
    if b == 0 {
        return a;
    }
    let shift = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        b -= a;
        if b == 0 {
            return a << shift;
        }
    }
}

// --- Big-backing integer fast arms (#certora-bigint-fast) --------------------
//
// `num_rational`'s operators normalize EVERY result with `num_bigint`'s
// Stein-gcd, which has no special case for small operands: `gcd(x, 1)` on a
// 2^256-scale `x` runs ~bits(x) shift/subtract iterations on the bignum. On
// the Certora QF_UFLIA VCs (Ethereum bignum constants) that gcd churn was
// ~50% of ALL solver samples. These helpers construct results that are
// REDUCED BY CONSTRUCTION whenever either operand is an integer
// (denominator 1) — the overwhelmingly common case in the LIA lane — so no
// gcd runs at all; a division by a u64-sized value uses one Euclid step
// (bignum mod + u64 binary gcd) instead of Stein's.
//
// Soundness: every `new_raw` below carries a proof that (a) the denominator
// is positive and (b) numerator/denominator are coprime, given the inputs
// are normalized. Inputs ARE normalized: `Big` backings only ever come from
// `num_rational` ops, `from_integer`, or these helpers (audited: no external
// `Rational::Big(..)` construction), and the `Small -> BigBacking`
// conversion goes through `BigRational::new` which normalizes.

/// Borrow the [`BigBacking`] of a `Big` value; convert (normalized) for `Small`.
#[inline]
fn backing_of(r: &Rational) -> Cow<'_, BigBacking> {
    match r {
        Rational::Big(b) => Cow::Borrowed(&**b),
        small => Cow::Owned(small.to_rug()),
    }
}

/// `a ± b` without any gcd when either side is an integer.
///
/// With `b = n/d` reduced and integer `N`: `N ± n/d = (N·d ± n)/d`, and
/// `gcd(N·d ± n, d) = gcd(±n, d) = 1`, so the result is reduced by
/// construction. Returns `None` when neither side is an integer.
#[inline]
fn backing_add_sub_int_fast(a: &BigBacking, b: &BigBacking, sub: bool) -> Option<BigBacking> {
    if a.denom().is_one() {
        let scaled = a.numer() * b.denom();
        let numer = if sub {
            scaled - b.numer()
        } else {
            scaled + b.numer()
        };
        Some(BigBacking::new_raw(numer, b.denom().clone()))
    } else if b.denom().is_one() {
        let scaled = b.numer() * a.denom();
        let numer = if sub {
            a.numer() - scaled
        } else {
            a.numer() + scaled
        };
        Some(BigBacking::new_raw(numer, a.denom().clone()))
    } else {
        None
    }
}

/// `gcd(|a|, d)` for `d: u64 > 0` via ONE bignum mod + u64 binary gcd
/// (Euclid's first step), instead of Stein's O(bits) loop on the bignum.
#[inline]
fn gcd_big_u64(a: &BigInt, d: u64) -> u64 {
    if d == 1 {
        return 1;
    }
    let r = (a.magnitude() % BigUint::from(d)).to_u64().unwrap_or(0);
    // gcd_u64(0, d) = d, correct: d divides a exactly.
    gcd_u64(r, d)
}

/// `a * b` without Stein's gcd when at least one side is an integer.
///
/// int × int: product over 1 — reduced trivially. int `N` × reduced `n/d`
/// (d fits u64): with `g = gcd(N, d)` the result `((N/g)·n) / (d/g)` is
/// reduced because `gcd(N/g, d/g) = 1` and `gcd(n, d/g) | gcd(n, d) = 1`.
#[inline]
fn backing_mul_int_fast(a: &BigBacking, b: &BigBacking) -> Option<BigBacking> {
    let a_int = a.denom().is_one();
    let b_int = b.denom().is_one();
    if a_int && b_int {
        return Some(BigBacking::new_raw(a.numer() * b.numer(), BigInt::one()));
    }
    let (int_side, rat_side) = if a_int {
        (a, b)
    } else if b_int {
        (b, a)
    } else {
        return None;
    };
    let d = rat_side.denom().to_u64()?;
    let g = gcd_big_u64(int_side.numer(), d);
    let numer = if g == 1 {
        int_side.numer() * rat_side.numer()
    } else {
        (int_side.numer() / g) * rat_side.numer()
    };
    Some(BigBacking::new_raw(numer, BigInt::from(d / g)))
}

/// `a / b` via `a * (1/b)`. Inverting a reduced `n/d` swaps the (coprime)
/// pair and moves the sign to the numerator, so the inverse is reduced with
/// a positive denominator; the multiply then reuses the int fast arms.
/// Returns `None` (caller falls back) when the fast multiply doesn't apply.
#[inline]
fn backing_div_int_fast(a: &BigBacking, b: &BigBacking) -> Option<BigBacking> {
    let inv = match b.numer().sign() {
        Sign::Plus => BigBacking::new_raw(b.denom().clone(), b.numer().clone()),
        Sign::Minus => BigBacking::new_raw(-b.denom(), -b.numer()),
        Sign::NoSign => return None, // division by zero: caller's assert fires
    };
    backing_mul_int_fast(a, &inv)
}

/// Shared slow-path add/sub through the backing, with the int fast arms.
#[inline]
fn add_sub_via_backing(a: &Rational, b: &Rational, sub: bool) -> Rational {
    let x = backing_of(a);
    let y = backing_of(b);
    let r = backing_add_sub_int_fast(&x, &y, sub).unwrap_or_else(|| {
        if sub {
            &*x - &*y
        } else {
            &*x + &*y
        }
    });
    Rational::from_rug(r)
}

/// Shared slow-path mul through the backing, with the int fast arms.
#[inline]
fn mul_via_backing(a: &Rational, b: &Rational) -> Rational {
    let x = backing_of(a);
    let y = backing_of(b);
    let r = backing_mul_int_fast(&x, &y).unwrap_or_else(|| &*x * &*y);
    Rational::from_rug(r)
}

/// Shared slow-path div through the backing, with the int fast arms.
#[inline]
fn div_via_backing(a: &Rational, b: &Rational) -> Rational {
    let x = backing_of(a);
    let y = backing_of(b);
    let r = backing_div_int_fast(&x, &y).unwrap_or_else(|| &*x / &*y);
    Rational::from_rug(r)
}

// --- Monomorphic i64 operations (#8406) --------------------------------------

impl Rational {
    /// Scale a `Small(n, d)` coefficient by `(sn/sd)` using pure i128 arithmetic.
    ///
    /// Returns `Some(Rational::Small(rn, rd))` if the result fits in i64,
    /// `None` otherwise. Avoids all enum matching -- the caller must guarantee
    /// that `self` is `Small`. This is the inner-loop operation in
    /// `substitute_var_work_vec` when column-index pivoting is active.
    ///
    /// Hot path: called per-coefficient in pivot substitution (#8406).
    #[inline]
    pub fn scale_small_i64(&self, sn: i64, sd: i64) -> Option<Self> {
        if let Self::Small(cn, cd) = self {
            // Pre-reduce cross-GCD to minimize overflow risk
            let g1 = gcd_u64(cn.unsigned_abs(), sd.unsigned_abs());
            let g2 = gcd_u64(sn.unsigned_abs(), cd.unsigned_abs());
            let cnr = *cn / g1 as i64;
            let sdr = sd / g1 as i64;
            let snr = sn / g2 as i64;
            let cdr = *cd / g2 as i64;
            if let (Some(num), Some(den)) = (cnr.checked_mul(snr), cdr.checked_mul(sdr)) {
                if num == 0 {
                    return Some(Self::Small(0, 1));
                }
                let (num, den) = if den < 0 {
                    match (num.checked_neg(), den.checked_neg()) {
                        (Some(n), Some(d)) => (n, d),
                        _ => return None,
                    }
                } else {
                    (num, den)
                };
                let g = gcd_u64(num.unsigned_abs(), den.unsigned_abs());
                return Some(Self::Small(num / g as i64, den / g as i64));
            }
            // Widen to i128 for overflow
            let num128 = i128::from(cnr) * i128::from(snr);
            let den128 = i128::from(cdr) * i128::from(sdr);
            if den128 == 0 {
                return None;
            }
            let (num128, den128) = if den128 < 0 {
                (-num128, -den128)
            } else {
                (num128, den128)
            };
            if num128 == 0 {
                return Some(Self::Small(0, 1));
            }
            let g = gcd_u128(num128.unsigned_abs(), den128.unsigned_abs());
            let rn = num128 / g as i128;
            let rd = den128 / g as i128;
            if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
                return Some(Self::Small(n, d));
            }
        }
        None
    }

    /// Add two `Small` rationals using i128 arithmetic.
    ///
    /// Returns `Some(Rational::Small(rn, rd))` if both are `Small` and the
    /// result fits in i64, `None` otherwise.
    ///
    /// Avoids enum matching in the caller -- used by the monomorphic i64 path
    /// in `substitute_var_work_vec` (#8406).
    #[inline]
    pub fn add_small_i64(&self, other: &Self) -> Option<Self> {
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (self, other) {
            if *d1 == *d2 {
                let n = n1.checked_add(*n2)?;
                let (rn, rd) = normalize_small(n, *d1)?;
                return Some(Self::Small(rn, rd));
            }
            let dg = gcd_u64(d1.unsigned_abs(), d2.unsigned_abs());
            let d1g = d1 / dg as i64;
            let d2g = d2 / dg as i64;
            let num = i128::from(*n1) * i128::from(d2g) + i128::from(*n2) * i128::from(d1g);
            let den = i128::from(d1g) * i128::from(*d2);
            if den == 0 {
                return None;
            }
            let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs());
            let rn = num / g as i128;
            let rd = den / g as i128;
            let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
            if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
                return Some(Self::Small(n, d));
            }
        }
        None
    }
}

// --- Fused divide-add and negation (#8406) -----------------------------------

impl Rational {
    /// Fused `self / divisor + addend` in a single i128 pass.
    ///
    /// When all three operands are `Small(i64, i64)`, computes
    /// `(self / divisor) + addend` with a single GCD reduction instead of
    /// the two separate reductions that `&(&self / &divisor) + &addend`
    /// requires.
    ///
    /// Returns `None` if any operand is `Big` or if i128 arithmetic overflows.
    ///
    /// Hot path: called per-variable in implied bounds derivation (#8406),
    /// where `bound_val = rhs_base / eq_c + ib.value`.
    #[inline]
    pub fn div_add_small(&self, divisor: &Self, addend: &Self) -> Option<Self> {
        if let (Self::Small(rn, rd), Self::Small(dn, dd), Self::Small(an, ad)) =
            (self, divisor, addend)
        {
            if *dn == 0 {
                return None;
            }
            // self / divisor = (rn * dd) / (rd * dn)
            // result = (rn*dd) / (rd*dn) + an/ad
            //        = (rn*dd*ad + an*rd*dn) / (rd*dn*ad)
            //
            // Pre-reduce to minimize overflow:
            // g1 = gcd(|rn|, |dn|), g2 = gcd(|dd|, |rd|)
            let g1 = gcd_u64(rn.unsigned_abs(), dn.unsigned_abs());
            let g2 = gcd_u64(dd.unsigned_abs(), rd.unsigned_abs());
            let rn_r = i128::from(*rn / g1 as i64);
            let dn_r = i128::from(*dn / g1 as i64);
            let dd_r = i128::from(*dd / g2 as i64);
            let rd_r = i128::from(*rd / g2 as i64);
            let an128 = i128::from(*an);
            let ad128 = i128::from(*ad);

            // numerator = rn_r * dd_r * ad + an * rd_r * dn_r
            let term1 = rn_r.checked_mul(dd_r)?.checked_mul(ad128)?;
            let term2 = an128.checked_mul(rd_r)?.checked_mul(dn_r)?;
            let num = term1.checked_add(term2)?;
            // denominator = rd_r * dn_r * ad
            let den = rd_r.checked_mul(dn_r)?.checked_mul(ad128)?;

            if den == 0 {
                return None;
            }
            let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
            if num == 0 {
                return Some(Self::Small(0, 1));
            }
            let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs());
            let rn_out = num / g as i128;
            let rd_out = den / g as i128;
            if let (Ok(n), Ok(d)) = (i64::try_from(rn_out), i64::try_from(rd_out)) {
                return Some(Self::Small(n, d));
            }
        }
        None
    }

    /// O(1) negation for `Small` rationals, avoiding enum dispatch overhead.
    ///
    /// Returns `None` if `self` is `Big` or if the numerator is `i64::MIN`
    /// (which cannot be negated in i64).
    ///
    /// Hot path: called per-coefficient in implied bounds accumulation (#8406),
    /// where `eq_c = -coeff` is computed for every nonbasic variable.
    #[inline]
    pub fn neg_small(&self) -> Option<Self> {
        if let Self::Small(n, d) = self {
            if *n == 0 {
                return Some(Self::Small(0, 1));
            }
            n.checked_neg().map(|neg_n| Self::Small(neg_n, *d))
        } else {
            None
        }
    }
}

// --- Fused multiply-add -----------------------------------------------------

impl Rational {
    /// Fused multiply-add: `self += a * b`.
    ///
    /// When all three operands are `Small(i64, i64)`, computes `self + a * b`
    /// entirely in i128 arithmetic with a single GCD reduction, instead of the
    /// two separate reductions that `self += &(&a * &b)` would require.
    ///
    /// Returns the product `a * b` as a Rational for callers that also need it.
    #[inline]
    pub fn add_product(&mut self, a: &Self, b: &Self) -> Self {
        if let (Self::Small(sn, sd), Self::Small(an, ad), Self::Small(bn, bd)) = (&*self, a, b) {
            let g1 = gcd_u64(an.unsigned_abs(), bd.unsigned_abs());
            let g2 = gcd_u64(bn.unsigned_abs(), ad.unsigned_abs());
            let anr = *an / g1 as i64;
            let bdr = *bd / g1 as i64;
            let bnr = *bn / g2 as i64;
            let adr = *ad / g2 as i64;

            let prod_n = i128::from(anr) * i128::from(bnr);
            let prod_d = i128::from(adr) * i128::from(bdr);

            // #8373: Use checked multiplication to avoid i128 overflow.
            // When sd * prod_d overflows i128, fall back to BigRational.
            // In release mode, unchecked overflow wraps silently, producing
            // wrong arithmetic that causes false SAT on QF_LRA benchmarks.
            let Some(sum_d) = i128::from(*sd).checked_mul(prod_d) else {
                let product = a * b;
                *self += &product;
                return product;
            };
            if sum_d == 0 {
                let product = a * b;
                *self += &product;
                return product;
            }

            let term1 = i128::from(*sn).checked_mul(prod_d);
            let term2 = prod_n.checked_mul(i128::from(*sd));
            if let (Some(t1), Some(t2)) = (term1, term2) {
                if let Some(sum_n) = t1.checked_add(t2) {
                    let g = gcd_u128(sum_n.unsigned_abs(), sum_d.unsigned_abs());
                    let rn = sum_n / g as i128;
                    let rd = sum_d / g as i128;
                    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
                    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
                        *self = Self::Small(n, d);
                        let pg = gcd_u128(prod_n.unsigned_abs(), prod_d.unsigned_abs());
                        let pn = prod_n / pg as i128;
                        let pd = prod_d / pg as i128;
                        let (pn, pd) = if pd < 0 { (-pn, -pd) } else { (pn, pd) };
                        let product =
                            if let (Ok(pn64), Ok(pd64)) = (i64::try_from(pn), i64::try_from(pd)) {
                                Self::Small(pn64, pd64)
                            } else {
                                a * b
                            };
                        return product;
                    }
                }
            }
        }
        // #8003: Optimized fallback for Big accumulator. When self is already
        // Big (common in dense LP implied bounds after ~10 terms), add the
        // product in-place using the backend's in-place `BigRational` add.
        // #certora-bigint-fast: gcd-free arm when either side is an integer.
        if let Self::Big(ref mut acc) = self {
            let product = a * b;
            let p = backing_of(&product);
            if let Some(r) = backing_add_sub_int_fast(acc, &p, false) {
                **acc = r;
            } else {
                **acc += &*p;
            }
            return product;
        }
        // Fallback: self is Small but i128 overflowed — promote to Big.
        let product = a * b;
        *self += &product;
        product
    }

    /// Fused multiply-add: `self += a * b` without returning the product.
    ///
    /// Like `add_product` but skips computing and reducing the product return
    /// value, saving one GCD reduction in the i128 fast path. Use this when the
    /// caller only needs the accumulated result, not the individual product.
    ///
    /// Hot path: called per-term in `compute_expr_interval` (#8406).
    #[inline]
    pub fn mul_add_assign(&mut self, a: &Self, b: &Self) {
        if let (Self::Small(sn, sd), Self::Small(an, ad), Self::Small(bn, bd)) = (&*self, a, b) {
            let g1 = gcd_u64(an.unsigned_abs(), bd.unsigned_abs());
            let g2 = gcd_u64(bn.unsigned_abs(), ad.unsigned_abs());
            let anr = *an / g1 as i64;
            let bdr = *bd / g1 as i64;
            let bnr = *bn / g2 as i64;
            let adr = *ad / g2 as i64;

            let prod_n = i128::from(anr) * i128::from(bnr);
            let prod_d = i128::from(adr) * i128::from(bdr);

            let Some(sum_d) = i128::from(*sd).checked_mul(prod_d) else {
                *self += &(a * b);
                return;
            };
            if sum_d == 0 {
                *self += &(a * b);
                return;
            }

            let term1 = i128::from(*sn).checked_mul(prod_d);
            let term2 = prod_n.checked_mul(i128::from(*sd));
            if let (Some(t1), Some(t2)) = (term1, term2) {
                if let Some(sum_n) = t1.checked_add(t2) {
                    let g = gcd_u128(sum_n.unsigned_abs(), sum_d.unsigned_abs());
                    let rn = sum_n / g as i128;
                    let rd = sum_d / g as i128;
                    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
                    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
                        *self = Self::Small(n, d);
                        return;
                    }
                }
            }
        }
        // Big accumulator or i128 overflow fallback.
        // #certora-bigint-fast: gcd-free arm when either side is an integer.
        if let Self::Big(ref mut acc) = self {
            let product = a * b;
            let p = backing_of(&product);
            if let Some(r) = backing_add_sub_int_fast(acc, &p, false) {
                **acc = r;
            } else {
                **acc += &*p;
            }
            return;
        }
        // Small accumulator but i128 overflowed — promote to Big.
        *self += &(a * b);
    }
}

// --- Add --------------------------------------------------------------------

/// Try small addition: a/b + c/d via i128 with GCD reduction.
#[inline]
fn try_add_small(n1: i64, d1: i64, n2: i64, d2: i64) -> Option<Rational> {
    if d1 == d2 {
        let n = n1.checked_add(n2)?;
        return normalize_small(n, d1).map(|(n, d)| Rational::Small(n, d));
    }
    let dg = gcd_u64(d1.unsigned_abs(), d2.unsigned_abs());
    let d1g = d1 / dg as i64;
    let d2g = d2 / dg as i64;
    let num = i128::from(n1) * i128::from(d2g) + i128::from(n2) * i128::from(d1g);
    let den = i128::from(d1g) * i128::from(d2);
    if den == 0 {
        return None;
    }
    let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs());
    let rn = num / g as i128;
    let rd = den / g as i128;
    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
        Some(Rational::Small(n, d))
    } else {
        None
    }
}

impl Add for Rational {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self {
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_add_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        add_sub_via_backing(&self, &rhs, false)
    }
}

impl Add for &Rational {
    type Output = Rational;
    #[inline]
    fn add(self, rhs: &Rational) -> Rational {
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            if let Some(r) = try_add_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        add_sub_via_backing(self, rhs, false)
    }
}

impl AddAssign for Rational {
    #[inline]
    fn add_assign(&mut self, rhs: Self) {
        if rhs.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = rhs;
            return;
        }
        // #8003: In-place backend addition when self is already Big (owned rhs).
        // #certora-bigint-fast: gcd-free arm when either side is an integer.
        if let Self::Big(ref mut lhs) = self {
            let y = backing_of(&rhs);
            if let Some(r) = backing_add_sub_int_fast(lhs, &y, false) {
                **lhs = r;
            } else {
                **lhs += &*y;
            }
            if let Some(s) = try_shrink(lhs) {
                *self = s;
            }
            return;
        }
        *self = std::mem::take(self) + rhs;
    }
}

impl AddAssign<&Self> for Rational {
    #[inline]
    fn add_assign(&mut self, rhs: &Self) {
        if rhs.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = rhs.clone();
            return;
        }
        // #8003: In-place backend addition when self is already Big.
        // #certora-bigint-fast: gcd-free arm when either side is an integer.
        if let Self::Big(ref mut lhs) = self {
            let y = backing_of(rhs);
            if let Some(r) = backing_add_sub_int_fast(lhs, &y, false) {
                **lhs = r;
            } else {
                **lhs += &*y;
            }
            if let Some(s) = try_shrink(lhs) {
                *self = s;
            }
            return;
        }
        *self = &*self + rhs;
    }
}

// --- Sub --------------------------------------------------------------------

/// Try small subtraction via i128 with GCD reduction.
#[inline]
fn try_sub_small(n1: i64, d1: i64, n2: i64, d2: i64) -> Option<Rational> {
    if d1 == d2 {
        let n = n1.checked_sub(n2)?;
        return normalize_small(n, d1).map(|(n, d)| Rational::Small(n, d));
    }
    let dg = gcd_u64(d1.unsigned_abs(), d2.unsigned_abs());
    let d1g = d1 / dg as i64;
    let d2g = d2 / dg as i64;
    let num = i128::from(n1) * i128::from(d2g) - i128::from(n2) * i128::from(d1g);
    let den = i128::from(d1g) * i128::from(d2);
    if den == 0 {
        return None;
    }
    let g = gcd_u128(num.unsigned_abs(), den.unsigned_abs());
    let rn = num / g as i128;
    let rd = den / g as i128;
    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
        Some(Rational::Small(n, d))
    } else {
        None
    }
}

impl Sub for Rational {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self {
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_sub_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        self + (-rhs)
    }
}

impl Sub for &Rational {
    type Output = Rational;
    #[inline]
    fn sub(self, rhs: &Rational) -> Rational {
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            if let Some(r) = try_sub_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        add_sub_via_backing(self, rhs, true)
    }
}

impl SubAssign for Rational {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) {
        if rhs.is_zero() {
            return;
        }
        *self = std::mem::take(self) - rhs;
    }
}

impl SubAssign<&Self> for Rational {
    #[inline]
    fn sub_assign(&mut self, rhs: &Self) {
        if rhs.is_zero() {
            return;
        }
        *self = &*self - rhs;
    }
}

// --- Mul --------------------------------------------------------------------

/// Try small multiplication with pre-reduction and i128 fallback.
#[inline]
fn try_mul_small(n1: i64, d1: i64, n2: i64, d2: i64) -> Option<Rational> {
    let g1 = gcd_u64(n1.unsigned_abs(), d2.unsigned_abs());
    let g2 = gcd_u64(n2.unsigned_abs(), d1.unsigned_abs());
    let n1r = n1 / g1 as i64;
    let d2r = d2 / g1 as i64;
    let n2r = n2 / g2 as i64;
    let d1r = d1 / g2 as i64;
    if let (Some(num), Some(den)) = (n1r.checked_mul(n2r), d1r.checked_mul(d2r)) {
        return normalize_small(num, den).map(|(n, d)| Rational::Small(n, d));
    }
    let num128 = i128::from(n1r) * i128::from(n2r);
    let den128 = i128::from(d1r) * i128::from(d2r);
    if den128 == 0 {
        return None;
    }
    let g = gcd_u128(num128.unsigned_abs(), den128.unsigned_abs());
    let rn = num128 / g as i128;
    let rd = den128 / g as i128;
    let (rn, rd) = if rd < 0 { (-rn, -rd) } else { (rn, rd) };
    if let (Ok(n), Ok(d)) = (i64::try_from(rn), i64::try_from(rd)) {
        Some(Rational::Small(n, d))
    } else {
        None
    }
}

impl Mul for Rational {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self {
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_mul_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        mul_via_backing(&self, &rhs)
    }
}

impl Mul for &Rational {
    type Output = Rational;
    #[inline]
    fn mul(self, rhs: &Rational) -> Rational {
        if self.is_zero() || rhs.is_zero() {
            return Rational::zero();
        }
        if matches!(self, Rational::Small(1, 1)) {
            return rhs.clone();
        }
        if matches!(self, Rational::Small(-1, 1)) {
            return -rhs;
        }
        if matches!(rhs, Rational::Small(1, 1)) {
            return self.clone();
        }
        if matches!(rhs, Rational::Small(-1, 1)) {
            return -self;
        }
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            if let Some(r) = try_mul_small(*n1, *d1, *n2, *d2) {
                return r;
            }
        }
        mul_via_backing(self, rhs)
    }
}

impl Mul<&Self> for Rational {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: &Self) -> Self {
        (&self).mul(rhs)
    }
}

impl MulAssign for Rational {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) {
        *self = std::mem::take(self) * rhs;
    }
}

impl MulAssign<&Self> for Rational {
    #[inline]
    fn mul_assign(&mut self, rhs: &Self) {
        *self = &*self * rhs;
    }
}

// --- Div --------------------------------------------------------------------

impl Div for Rational {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self {
        assert!(!rhs.is_zero(), "Rational: division by zero");
        if let Self::Small(n2, 1) = &rhs {
            if *n2 == 1 {
                return self;
            }
            if *n2 == -1 {
                return -self;
            }
        }
        if let (Self::Small(n1, d1), Self::Small(n2, d2)) = (&self, &rhs) {
            if let Some(r) = try_mul_small(*n1, *d1, *d2, *n2) {
                return r;
            }
        }
        div_via_backing(&self, &rhs)
    }
}

impl Div for &Rational {
    type Output = Rational;
    #[inline]
    fn div(self, rhs: &Rational) -> Rational {
        assert!(!rhs.is_zero(), "Rational: division by zero");
        if let Rational::Small(n2, 1) = rhs {
            if *n2 == 1 {
                return self.clone();
            }
            if *n2 == -1 {
                return -self;
            }
        }
        if let (Rational::Small(n1, d1), Rational::Small(n2, d2)) = (self, rhs) {
            if let Some(r) = try_mul_small(*n1, *d1, *d2, *n2) {
                return r;
            }
        }
        div_via_backing(self, rhs)
    }
}

impl DivAssign for Rational {
    #[inline]
    fn div_assign(&mut self, rhs: Self) {
        *self = std::mem::take(self) / rhs;
    }
}

impl DivAssign<&Self> for Rational {
    #[inline]
    fn div_assign(&mut self, rhs: &Self) {
        *self = &*self / rhs;
    }
}

// --- Neg --------------------------------------------------------------------

impl Neg for Rational {
    type Output = Self;
    #[inline]
    fn neg(self) -> Self {
        match self {
            Self::Small(0, _) => Self::Small(0, 1),
            Self::Small(n, d) => {
                if let Some(neg_n) = n.checked_neg() {
                    Self::Small(neg_n, d)
                } else {
                    Self::from_rug(-self.to_rug())
                }
            }
            Self::Big(br) => Self::from_rug(-*br),
        }
    }
}

impl Neg for &Rational {
    type Output = Rational;
    #[inline]
    fn neg(self) -> Rational {
        match self {
            Rational::Small(0, _) => Rational::Small(0, 1),
            Rational::Small(n, d) => {
                if let Some(neg_n) = n.checked_neg() {
                    Rational::Small(neg_n, *d)
                } else {
                    Rational::from_rug(-self.to_rug())
                }
            }
            Rational::Big(br) => Rational::from_rug(-(**br).clone()),
        }
    }
}

// --- BigRational interop ----------------------------------------------------

use num_rational::BigRational;
use std::cmp::Ordering;

impl Rational {
    /// Multiply by a BigRational, returning Rational (shrinks result if possible).
    #[inline]
    pub fn mul_big_to_rational(&self, other: &BigRational) -> Self {
        Self::from_big(self.mul_bigrational(other))
    }
}

/// Cross-type multiply: `&BigRational * &Rational` -> `BigRational`.
impl Mul<&Rational> for &BigRational {
    type Output = BigRational;
    #[inline]
    fn mul(self, rhs: &Rational) -> BigRational {
        self * &rhs.to_big()
    }
}

/// Cross-type subtract: `Rational - &BigRational` -> `Rational`.
impl Sub<&BigRational> for Rational {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: &BigRational) -> Self {
        Self::from(self.to_big() - rhs)
    }
}

/// Cross-type add: `Rational + &BigRational` -> `Rational`.
impl Add<&BigRational> for Rational {
    type Output = Self;
    #[inline]
    fn add(self, rhs: &BigRational) -> Self {
        Self::from(self.to_big() + rhs)
    }
}

/// Cross-type subtract: `BigRational - &Rational` -> `BigRational`.
impl Sub<&Rational> for BigRational {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: &Rational) -> Self {
        self - &rhs.to_big()
    }
}

/// Cross-type subtract: `&BigRational - &Rational` -> `BigRational`.
impl Sub<&Rational> for &BigRational {
    type Output = BigRational;
    #[inline]
    fn sub(self, rhs: &Rational) -> BigRational {
        self - &rhs.to_big()
    }
}

/// Cross-type add: `BigRational + &Rational` -> `BigRational`.
impl Add<&Rational> for BigRational {
    type Output = Self;
    #[inline]
    fn add(self, rhs: &Rational) -> Self {
        self + &rhs.to_big()
    }
}

/// PartialEq with BigRational for comparison in compute_bound_propagations.
impl PartialEq<BigRational> for Rational {
    #[inline]
    fn eq(&self, other: &BigRational) -> bool {
        match self {
            Self::Small(n, d) => {
                if let (Ok(p), Ok(q)) = (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    i128::from(*n) * i128::from(q) == i128::from(p) * i128::from(*d)
                } else {
                    self.to_big() == *other
                }
            }
            Self::Big(br) => **br == *other,
        }
    }
}

/// PartialOrd with BigRational for comparison in compute_bound_propagations.
impl PartialOrd<BigRational> for Rational {
    #[inline]
    fn partial_cmp(&self, other: &BigRational) -> Option<Ordering> {
        match self {
            Self::Small(n, d) => {
                if let (Ok(p), Ok(q)) = (i64::try_from(other.numer()), i64::try_from(other.denom()))
                {
                    let lhs = i128::from(*n) * i128::from(q);
                    let rhs = i128::from(p) * i128::from(*d);
                    Some(lhs.cmp(&rhs))
                } else {
                    Some(self.to_big().cmp(other))
                }
            }
            Self::Big(br) => Some((**br).cmp(other)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_product_matches_separate_ops() {
        let cases: Vec<(Rational, Rational, Rational)> = vec![
            (
                Rational::from(10i64),
                Rational::from(3i64),
                Rational::from(7i64),
            ),
            (
                Rational::new(1, 3),
                Rational::new(2, 5),
                Rational::new(7, 11),
            ),
            (
                Rational::from(100i64),
                Rational::new(-3, 7),
                Rational::new(50, 3),
            ),
            (
                Rational::zero(),
                Rational::new(999, 1000),
                Rational::new(1001, 1000),
            ),
            (
                Rational::from(i64::MAX / 2),
                Rational::from(2i64),
                Rational::from(i64::MAX / 4),
            ),
            (
                Rational::from(1_000_000_000i64),
                Rational::from(3_000_000_000i64),
                Rational::from(4_000_000_000i64),
            ),
        ];

        for (acc_init, a, b) in &cases {
            let mut acc_fused = acc_init.clone();
            let product_fused = acc_fused.add_product(a, b);

            let product_separate = a * b;
            let mut acc_separate = acc_init.clone();
            acc_separate += &product_separate;

            assert_eq!(
                acc_fused, acc_separate,
                "add_product mismatch for acc={acc_init:?}, a={a:?}, b={b:?}: \
                 fused={acc_fused:?} vs separate={acc_separate:?}"
            );
            assert_eq!(
                product_fused, product_separate,
                "product mismatch for a={a:?}, b={b:?}: \
                 fused={product_fused:?} vs separate={product_separate:?}"
            );
        }
    }

    #[test]
    fn test_add_product_accumulation() {
        let coeffs: Vec<Rational> = (1..=20).map(|i| Rational::new(i, i + 1)).collect();
        let bounds: Vec<Rational> = (1..=20).map(|i| Rational::new(i * 3, i * 2 + 1)).collect();

        let mut total_fused = Rational::zero();
        let mut total_separate = Rational::zero();

        for (c, b) in coeffs.iter().zip(bounds.iter()) {
            total_fused.add_product(c, b);

            let product = c * b;
            total_separate += &product;
        }

        assert_eq!(
            total_fused, total_separate,
            "Accumulated totals differ: fused={total_fused:?} vs separate={total_separate:?}"
        );
        assert!(
            total_fused.is_small(),
            "Expected Small representation, got Big"
        );
    }

    // --- Monomorphic i64 fast path tests (#8406) ---

    #[test]
    fn test_scale_small_i64_basic() {
        let r = Rational::new(3, 7);
        // (3/7) * (5/2) = 15/14
        let scaled = r.scale_small_i64(5, 2).expect("should succeed");
        assert_eq!(scaled, Rational::new(15, 14));
    }

    #[test]
    fn test_scale_small_i64_one() {
        let r = Rational::new(42, 13);
        let scaled = r.scale_small_i64(1, 1).expect("should succeed");
        assert_eq!(scaled, Rational::new(42, 13));
    }

    #[test]
    fn test_scale_small_i64_neg_one() {
        let r = Rational::new(3, 4);
        let scaled = r.scale_small_i64(-1, 1).expect("should succeed");
        assert_eq!(scaled, Rational::new(-3, 4));
    }

    #[test]
    fn test_scale_small_i64_zero_coeff() {
        let r = Rational::new(3, 4);
        let scaled = r.scale_small_i64(0, 1).expect("should succeed");
        assert_eq!(scaled, Rational::zero());
    }

    #[test]
    fn test_scale_small_i64_negative_denom_scale() {
        // (3/4) * (-5/-2) = (3/4) * (5/2) = 15/8
        let r = Rational::new(3, 4);
        let scaled = r.scale_small_i64(-5, -2);
        // scale_small_i64 does not require pre-normalized input, but
        // the caller should pass a valid (n, d) pair. Let's test
        // that the reduction handles the negative denominator.
        // (-5/-2) is not normalized, but the code should handle it.
        // Actually, the GCD approach works on unsigned_abs, so sign
        // is handled by the product sign. Let's verify.
        if let Some(s) = scaled {
            // The result should be 15/8 or equivalent
            assert_eq!(s, Rational::new(15, 8));
        }
    }

    #[test]
    fn test_scale_small_i64_matches_generic_mul() {
        let cases = vec![
            (Rational::new(1, 3), 2, 5),
            (Rational::new(-7, 11), 3, 13),
            (Rational::new(100, 1), -3, 7),
            (Rational::new(1, 1000), 999, 1),
            (Rational::from(0i64), 42, 1),
            (Rational::from(i64::MAX / 100), 50, 1),
        ];
        for (r, sn, sd) in &cases {
            let scale = Rational::new(*sn, *sd);
            let generic = r * &scale;
            if let Some(fast) = r.scale_small_i64(*sn, *sd) {
                assert_eq!(
                    fast, generic,
                    "scale_small_i64 mismatch for r={r:?}, scale={sn}/{sd}: fast={fast:?} vs generic={generic:?}"
                );
            }
            // If scale_small_i64 returns None, the generic path handles it — that's fine.
        }
    }

    #[test]
    fn test_add_small_i64_basic() {
        let a = Rational::new(1, 3);
        let b = Rational::new(1, 6);
        let sum = a.add_small_i64(&b).expect("should succeed");
        assert_eq!(sum, Rational::new(1, 2));
    }

    #[test]
    fn test_add_small_i64_same_denom() {
        let a = Rational::new(3, 7);
        let b = Rational::new(4, 7);
        let sum = a.add_small_i64(&b).expect("should succeed");
        assert_eq!(sum, Rational::new(1, 1));
    }

    #[test]
    fn test_add_small_i64_cancellation() {
        let a = Rational::new(5, 3);
        let b = Rational::new(-5, 3);
        let sum = a.add_small_i64(&b).expect("should succeed");
        assert_eq!(sum, Rational::zero());
    }

    #[test]
    fn test_add_small_i64_matches_generic_add() {
        let cases = vec![
            (Rational::new(1, 3), Rational::new(2, 5)),
            (Rational::new(-7, 11), Rational::new(3, 13)),
            (Rational::from(100i64), Rational::from(-50i64)),
            (Rational::new(1, 1000), Rational::new(999, 1000)),
            (Rational::from(0i64), Rational::from(42i64)),
        ];
        for (a, b) in &cases {
            let generic = a + b;
            if let Some(fast) = a.add_small_i64(b) {
                assert_eq!(
                    fast, generic,
                    "add_small_i64 mismatch for a={a:?}, b={b:?}: fast={fast:?} vs generic={generic:?}"
                );
            }
        }
    }

    #[test]
    fn test_add_small_i64_big_returns_none() {
        // Create a Big variant
        let big = Rational::from(i64::MAX) * Rational::from(2i64);
        let small = Rational::from(1i64);
        // add_small_i64 should return None when one operand is Big
        assert!(big.add_small_i64(&small).is_none());
    }

    #[test]
    fn test_scale_small_i64_big_returns_none() {
        let big = Rational::from(i64::MAX) * Rational::from(2i64);
        assert!(big.scale_small_i64(1, 1).is_none());
    }

    #[test]
    fn test_mul_add_assign_matches_add_product() {
        let cases: Vec<(Rational, Rational, Rational)> = vec![
            (
                Rational::from(10i64),
                Rational::from(3i64),
                Rational::from(7i64),
            ),
            (
                Rational::new(1, 3),
                Rational::new(2, 5),
                Rational::new(7, 11),
            ),
            (
                Rational::from(100i64),
                Rational::new(-3, 7),
                Rational::new(50, 3),
            ),
            (
                Rational::zero(),
                Rational::new(999, 1000),
                Rational::new(1001, 1000),
            ),
            (
                Rational::from(i64::MAX / 2),
                Rational::from(2i64),
                Rational::from(i64::MAX / 4),
            ),
            (
                Rational::from(1_000_000_000i64),
                Rational::from(3_000_000_000i64),
                Rational::from(4_000_000_000i64),
            ),
        ];

        for (acc_init, a, b) in &cases {
            let mut acc_fused = acc_init.clone();
            acc_fused.mul_add_assign(a, b);

            let mut acc_separate = acc_init.clone();
            acc_separate += &(a * b);

            assert_eq!(
                acc_fused, acc_separate,
                "mul_add_assign mismatch for acc={acc_init:?}, a={a:?}, b={b:?}: fused={acc_fused:?} vs separate={acc_separate:?}"
            );
        }
    }

    #[test]
    fn test_mul_add_assign_accumulation() {
        // Test accumulating many terms like compute_expr_interval does.
        let coeffs: Vec<Rational> = (1..=20).map(|i| Rational::new(i, i + 1)).collect();
        let bounds: Vec<Rational> = (1..=20).map(|i| Rational::new(i * 3, i * 2 + 1)).collect();

        let mut total_fused = Rational::zero();
        let mut total_separate = Rational::zero();

        for (c, b) in coeffs.iter().zip(bounds.iter()) {
            total_fused.mul_add_assign(c, b);

            let product = c * b;
            total_separate += &product;
        }

        assert_eq!(
            total_fused, total_separate,
            "Accumulated totals differ: fused={total_fused:?} vs separate={total_separate:?}"
        );
    }

    // --- div_add_small tests (#8406) ---

    #[test]
    fn test_div_add_small_basic() {
        // (6/1) / (3/1) + (1/1) = 2 + 1 = 3
        let a = Rational::from(6i64);
        let b = Rational::from(3i64);
        let c = Rational::from(1i64);
        let result = a.div_add_small(&b, &c).expect("should succeed");
        assert_eq!(result, Rational::from(3i64));
    }

    #[test]
    fn test_div_add_small_fractions() {
        // (1/3) / (2/5) + (7/11) = (5/6) + (7/11) = (55 + 42)/66 = 97/66
        let a = Rational::new(1, 3);
        let b = Rational::new(2, 5);
        let c = Rational::new(7, 11);
        let result = a.div_add_small(&b, &c).expect("should succeed");
        let expected = &(&a / &b) + &c;
        assert_eq!(
            result, expected,
            "div_add_small mismatch: got {result:?}, expected {expected:?}"
        );
    }

    #[test]
    fn test_div_add_small_negative() {
        // (-3/7) / (-5/2) + (1/4) = (6/35) + (1/4) = (24 + 35)/140 = 59/140
        let a = Rational::new(-3, 7);
        let b = Rational::new(-5, 2);
        let c = Rational::new(1, 4);
        let result = a.div_add_small(&b, &c).expect("should succeed");
        let expected = &(&a / &b) + &c;
        assert_eq!(result, expected);
    }

    #[test]
    fn test_div_add_small_zero_addend() {
        // (10/3) / (5/1) + 0 = 2/3
        let a = Rational::new(10, 3);
        let b = Rational::from(5i64);
        let c = Rational::zero();
        let result = a.div_add_small(&b, &c).expect("should succeed");
        assert_eq!(result, Rational::new(2, 3));
    }

    #[test]
    fn test_div_add_small_zero_numerator() {
        // 0 / (5/1) + (3/4) = 0 + 3/4 = 3/4
        let a = Rational::zero();
        let b = Rational::from(5i64);
        let c = Rational::new(3, 4);
        let result = a.div_add_small(&b, &c).expect("should succeed");
        assert_eq!(result, Rational::new(3, 4));
    }

    #[test]
    fn test_div_add_small_matches_generic() {
        let cases = vec![
            (
                Rational::new(1, 3),
                Rational::new(2, 5),
                Rational::new(7, 11),
            ),
            (
                Rational::from(100i64),
                Rational::new(-3, 7),
                Rational::new(50, 3),
            ),
            (
                Rational::new(-42, 13),
                Rational::new(7, 3),
                Rational::new(-1, 6),
            ),
            (
                Rational::from(0i64),
                Rational::from(42i64),
                Rational::new(3, 4),
            ),
            (
                Rational::new(999, 1000),
                Rational::new(1001, 1000),
                Rational::new(1, 2),
            ),
            (
                Rational::from(i64::MAX / 100),
                Rational::from(50i64),
                Rational::from(1i64),
            ),
        ];
        for (a, b, c) in &cases {
            let generic = &(a / b) + c;
            if let Some(fast) = a.div_add_small(b, c) {
                assert_eq!(
                    fast, generic,
                    "div_add_small mismatch for a={a:?}, b={b:?}, c={c:?}: fast={fast:?} vs generic={generic:?}"
                );
            }
        }
    }

    #[test]
    fn test_div_add_small_big_returns_none() {
        let big = Rational::from(i64::MAX) * Rational::from(2i64);
        let small = Rational::from(1i64);
        assert!(big.div_add_small(&small, &small).is_none());
    }

    #[test]
    fn test_div_add_small_zero_divisor_returns_none() {
        let a = Rational::from(5i64);
        let zero = Rational::zero();
        let c = Rational::from(1i64);
        assert!(a.div_add_small(&zero, &c).is_none());
    }

    // --- neg_small tests (#8406) ---

    #[test]
    fn test_neg_small_positive() {
        let r = Rational::new(3, 7);
        let result = r.neg_small().expect("should succeed");
        assert_eq!(result, Rational::new(-3, 7));
    }

    #[test]
    fn test_neg_small_negative() {
        let r = Rational::new(-5, 3);
        let result = r.neg_small().expect("should succeed");
        assert_eq!(result, Rational::new(5, 3));
    }

    #[test]
    fn test_neg_small_zero() {
        let r = Rational::zero();
        let result = r.neg_small().expect("should succeed");
        assert_eq!(result, Rational::zero());
    }

    #[test]
    fn test_neg_small_matches_generic_neg() {
        let cases = vec![
            Rational::new(1, 3),
            Rational::new(-7, 11),
            Rational::from(100i64),
            Rational::from(-100i64),
            Rational::zero(),
            Rational::new(i64::MAX / 2, 1),
        ];
        for r in &cases {
            let generic = -r;
            if let Some(fast) = r.neg_small() {
                assert_eq!(
                    fast, generic,
                    "neg_small mismatch for r={r:?}: fast={fast:?} vs generic={generic:?}"
                );
            }
        }
    }

    #[test]
    fn test_neg_small_big_returns_none() {
        let big = Rational::from(i64::MAX) * Rational::from(2i64);
        assert!(big.neg_small().is_none());
    }

    #[test]
    fn test_neg_small_min_returns_none() {
        // i64::MIN cannot be negated to i64
        let r = Rational::Small(i64::MIN, 1);
        assert!(r.neg_small().is_none());
    }
}
