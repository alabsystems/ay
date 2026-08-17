// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict semantic validation for `TheoryLemmaKind::FpGroundEval`.
//!
//! An `FpGroundEval` lemma claims: "this clause is TRUE under every
//! interpretation, and an EXACT IEEE-754 evaluation of the clause itself
//! demonstrates it." Two ingredients make that decidable for the shapes AY's
//! FP lane actually produces:
//!
//! 1. **Clause-carried bindings.** A literal `(not (= v g))` whose `v` is a
//!    variable and whose `g` is GROUND licenses replacing `v` by `g` in every
//!    literal. The argument is local to this clause: any valuation that
//!    FALSIFIES the clause makes every literal false, hence makes `(= v g)`
//!    TRUE, so `v` and `g` denote the same value there and congruence
//!    preserves each literal's truth value under the replacement. Therefore
//!    the substituted clause is falsifiable exactly when the original is, and
//!    proving the substituted clause valid proves the original valid.
//! 2. **Exhaustive residual enumeration.** Whatever variables survive the
//!    substitution are enumerated over their COMPLETE finite domains (`Bool`,
//!    `(_ BitVec w)`, `(_ FloatingPoint eb sb)`) within a fixed total BIT
//!    budget. If every assignment satisfies some literal the clause is valid;
//!    if any assignment falsifies all of them the lemma is REJECTED.
//!
//! ## Why this exists next to [`super::fp_bounded`]
//!
//! `validate_fp_classification` deliberately excludes ALL FP arithmetic: it has
//! no correctly-rounded evaluator, so `fp.add`, `fp.mul`, `fp.fma`, `fp.sqrt`
//! and the `to_fp` conversions fail closed there. That left AY computing the
//! right answer on ground FP queries such as
//! `(not (fp.eq (fp.add RNE +zero +zero) +zero))` and then publishing `unknown`,
//! because the one-literal refutation carried a `Generic`/trust kind that
//! strict certification (correctly) refuses.
//!
//! This module supplies the missing kernel: correctly-rounded IEEE-754
//! arithmetic in EXACT integer/rational arithmetic — never `f64`, so there is
//! no double rounding — for `fp.add`, `fp.sub`, `fp.mul`, `fp.div`, `fp.fma`,
//! `fp.sqrt`, and the `to_fp` / `to_fp_unsigned` conversions, under all five
//! SMT-LIB rounding modes.
//!
//! ## Fail-closed boundary
//!
//! Every partial function returns `None` — never a guess — when a term uses an
//! operator this kernel does not implement, mentions a variable it cannot
//! enumerate, exceeds a format bound, or exhausts the work budget. `None`
//! propagates to a REJECTED lemma, never to an accepted one. In particular
//! `fp.rem`, `fp.roundToIntegral`, `fp.min`, `fp.max`, `fp.to_ubv`,
//! `fp.to_sbv`, and `fp.to_ieee_bv` are NOT implemented here and fail closed
//! (`fp.to_ubv`/`fp.to_sbv` are additionally UNDER-SPECIFIED out of range, so a
//! proof checker must never evaluate them at all).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::ProofCheckError;

/// Total enumerated bits across every residual variable in one clause.
///
/// 16 bits = 65_536 assignments, which covers a single `Float16`, a handful of
/// `Bool`s, or a narrow bitvector. The checker is a validator, not a second
/// bit-blaster: a clause needing more fails closed.
const MAX_ENUMERATION_BITS: u32 = 16;

/// Work budget for one clause validation, in evaluated term nodes summed over
/// every enumerated assignment. Exhaustion fails closed.
pub(crate) const FP_GROUND_WORK_LIMIT: usize = 4_000_000;

/// Recursion depth bound for the evaluator and the structural walks.
const MAX_DEPTH: usize = 512;

/// Largest exponent width this kernel decodes. `Float64` has `eb = 11`; the
/// bound keeps `1 << eb` and the bias inside `u64`.
const MAX_EB: u32 = 20;

/// Largest significand width this kernel decodes (hidden bit included).
/// `Float64` has `sb = 53`, so the stored significand fits `u64`.
const MAX_SB: u32 = 64;

/// Largest bitvector width this kernel will decode or enumerate.
const MAX_BV_WIDTH: u32 = 256;

/// Cap on the precision of exact rationals reaching the rounding kernel, as a
/// bit count on numerator and denominator. A proof payload cannot make the
/// checker allocate unbounded precision.
const MAX_RATIONAL_BITS: u64 = 1 << 16;

// ===========================================================================
// Rounding modes
// ===========================================================================

/// The five SMT-LIB `RoundingMode` values.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Rm {
    /// `roundNearestTiesToEven`
    Rne,
    /// `roundNearestTiesToAway`
    Rna,
    /// `roundTowardPositive`
    Rtp,
    /// `roundTowardNegative`
    Rtn,
    /// `roundTowardZero`
    Rtz,
}

impl Rm {
    fn from_name(name: &str) -> Option<Self> {
        Some(match name {
            "RNE" | "roundNearestTiesToEven" => Self::Rne,
            "RNA" | "roundNearestTiesToAway" => Self::Rna,
            "RTP" | "roundTowardPositive" => Self::Rtp,
            "RTN" | "roundTowardNegative" => Self::Rtn,
            "RTZ" | "roundTowardZero" => Self::Rtz,
            _ => return None,
        })
    }
}

// ===========================================================================
// Exact IEEE 754 values
// ===========================================================================

/// A concrete IEEE 754 value, stored as its decoded fields.
///
/// Deliberately independent of [`super::fp_bounded`]'s private value type: this
/// module owns the ARITHMETIC semantics, and a checker that shared its decoder
/// with a second checker would only establish that the two agree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Fp {
    /// True when the sign bit is set.
    sign: bool,
    /// Raw biased exponent field (`eb` bits).
    exponent: u64,
    /// Raw stored significand field (`sb - 1` bits, hidden bit excluded).
    significand: u64,
    /// Exponent width.
    eb: u32,
    /// Significand width, hidden bit included.
    sb: u32,
}

impl Fp {
    fn checked(sign: bool, exponent: u64, significand: u64, eb: u32, sb: u32) -> Option<Self> {
        if !(2..=MAX_EB).contains(&eb) || !(2..=MAX_SB).contains(&sb) {
            return None;
        }
        let max_exp = (1u64 << eb) - 1;
        let stored = sb - 1;
        let sig_mask = if stored >= 64 {
            u64::MAX
        } else {
            (1u64 << stored) - 1
        };
        if exponent > max_exp || significand > sig_mask {
            return None;
        }
        Some(Self {
            sign,
            exponent,
            significand,
            eb,
            sb,
        })
    }

    /// Decode a raw `eb + sb` bit pattern (MSB is the sign).
    fn from_bits(bits: &BigInt, eb: u32, sb: u32) -> Option<Self> {
        if !(2..=MAX_EB).contains(&eb) || !(2..=MAX_SB).contains(&sb) {
            return None;
        }
        let stored = sb - 1;
        let significand = bit_slice(bits, 0, stored)?;
        let exponent = bit_slice(bits, stored, eb)?;
        let sign = bit_slice(bits, stored.checked_add(eb)?, 1)? == 1;
        Self::checked(sign, exponent, significand, eb, sb)
    }

    fn max_exp(&self) -> u64 {
        (1u64 << self.eb) - 1
    }

    fn is_nan(&self) -> bool {
        self.exponent == self.max_exp() && self.significand != 0
    }

    fn is_infinite(&self) -> bool {
        self.exponent == self.max_exp() && self.significand == 0
    }

    fn is_zero(&self) -> bool {
        self.exponent == 0 && self.significand == 0
    }

    fn is_normal(&self) -> bool {
        self.exponent != 0 && self.exponent != self.max_exp()
    }

    fn is_subnormal(&self) -> bool {
        self.exponent == 0 && self.significand != 0
    }

    fn is_positive(&self) -> bool {
        !self.is_nan() && !self.sign
    }

    fn is_negative(&self) -> bool {
        !self.is_nan() && self.sign
    }

    fn abs(self) -> Self {
        Self {
            sign: false,
            ..self
        }
    }

    fn negated(self) -> Self {
        Self {
            sign: !self.sign,
            ..self
        }
    }

    fn zero(sign: bool, eb: u32, sb: u32) -> Option<Self> {
        Self::checked(sign, 0, 0, eb, sb)
    }

    fn infinity(sign: bool, eb: u32, sb: u32) -> Option<Self> {
        Self::checked(sign, (1u64 << eb) - 1, 0, eb, sb)
    }

    /// The canonical quiet NaN: exponent all ones, MSB of the stored
    /// significand set.
    fn nan(eb: u32, sb: u32) -> Option<Self> {
        if !(2..=MAX_SB).contains(&sb) || !(2..=MAX_EB).contains(&eb) {
            return None;
        }
        Self::checked(false, (1u64 << eb) - 1, 1u64 << (sb - 2), eb, sb)
    }

    fn largest_finite(sign: bool, eb: u32, sb: u32) -> Option<Self> {
        if !(2..=MAX_SB).contains(&sb) || !(2..=MAX_EB).contains(&eb) {
            return None;
        }
        let stored = sb - 1;
        let sig_mask = if stored >= 64 {
            u64::MAX
        } else {
            (1u64 << stored) - 1
        };
        Self::checked(sign, (1u64 << eb) - 2, sig_mask, eb, sb)
    }

    fn same_format(&self, other: &Self) -> bool {
        self.eb == other.eb && self.sb == other.sb
    }

    /// SMT-LIB structural equality on the FP sort: ONE abstract NaN, and `+0`
    /// distinct from `-0`. `None` when the formats differ (ill-sorted input).
    fn structural_eq(&self, other: &Self) -> Option<bool> {
        if !self.same_format(other) {
            return None;
        }
        if self.is_nan() || other.is_nan() {
            return Some(self.is_nan() && other.is_nan());
        }
        Some(
            self.sign == other.sign
                && self.exponent == other.exponent
                && self.significand == other.significand,
        )
    }

    /// Exact rational value of a FINITE number; `None` for NaN and infinities.
    fn to_rational(self) -> Option<BigRational> {
        if self.is_nan() || self.is_infinite() {
            return None;
        }
        if self.is_zero() {
            return Some(BigRational::zero());
        }
        let bias = (1u64 << (self.eb - 1)) - 1;
        let stored = self.sb - 1;
        let significand = if self.exponent == 0 {
            BigInt::from(self.significand)
        } else {
            (BigInt::one() << stored as usize) + BigInt::from(self.significand)
        };
        let shift = if self.exponent == 0 {
            1i64 - i64::try_from(bias).ok()? - i64::from(stored)
        } else {
            i64::try_from(self.exponent).ok()? - i64::try_from(bias).ok()? - i64::from(stored)
        };
        let magnitude = scale_by_pow2(&BigRational::from_integer(significand), shift)?;
        Some(if self.sign { -magnitude } else { magnitude })
    }

    /// Order on the extended reals for the IEEE comparison predicates.
    /// `None` exactly when a NaN is involved (every comparison is then false)
    /// or when the formats are incomparable.
    fn cmp_real(&self, other: &Self) -> Option<std::cmp::Ordering> {
        use std::cmp::Ordering;
        if self.is_nan() || other.is_nan() {
            return None;
        }
        if self.is_zero() && other.is_zero() {
            // `+0` and `-0` compare EQUAL under `fp.eq` / `fp.lt` / …; only
            // structural `=` distinguishes them.
            return Some(Ordering::Equal);
        }
        if self.same_format(other) {
            // Same format: the raw `(exponent, significand)` pair is monotone
            // in magnitude, so no rational arithmetic is needed.
            let magnitude = |v: &Self| (u128::from(v.exponent) << 64) | u128::from(v.significand);
            return Some(match (self.sign, other.sign) {
                (false, false) => magnitude(self).cmp(&magnitude(other)),
                (true, true) => magnitude(other).cmp(&magnitude(self)),
                (false, true) => Ordering::Greater,
                (true, false) => Ordering::Less,
            });
        }
        // Mixed formats: compare on the extended reals.
        let rank = |v: &Self| -> (i8, Option<BigRational>) {
            if v.is_infinite() {
                (if v.sign { -1 } else { 1 }, None)
            } else {
                (0, v.to_rational())
            }
        };
        let (left_rank, left_value) = rank(self);
        let (right_rank, right_value) = rank(other);
        match left_rank.cmp(&right_rank) {
            Ordering::Equal => match (left_value, right_value) {
                (Some(left), Some(right)) => Some(left.cmp(&right)),
                (None, None) => Some(Ordering::Equal),
                _ => None,
            },
            ordering => Some(ordering),
        }
    }
}

/// Read `width` bits of `bits` starting at `offset` (LSB = 0) as a `u64`.
fn bit_slice(bits: &BigInt, offset: u32, width: u32) -> Option<u64> {
    if bits.is_negative() || width > 64 {
        return None;
    }
    let shifted = bits >> offset as usize;
    let mask = (BigInt::one() << width as usize) - BigInt::one();
    (shifted & mask).to_u64()
}

/// `value * 2^shift` as an exact rational, refusing unbounded precision.
fn scale_by_pow2(value: &BigRational, shift: i64) -> Option<BigRational> {
    if shift.unsigned_abs() > MAX_RATIONAL_BITS {
        return None;
    }
    let magnitude = usize::try_from(shift.unsigned_abs()).ok()?;
    Some(if shift >= 0 {
        value * BigRational::from_integer(BigInt::one() << magnitude)
    } else {
        value / BigRational::from_integer(BigInt::one() << magnitude)
    })
}

fn rational_is_bounded(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

/// `floor(log2(a))` for a strictly positive rational.
fn floor_log2(a: &BigRational) -> Option<i64> {
    if !a.is_positive() {
        return None;
    }
    let numer_bits = i64::try_from(a.numer().bits()).ok()?;
    let denom_bits = i64::try_from(a.denom().bits()).ok()?;
    // `2^(n-1) <= numer < 2^n` and likewise for the denominator, so the true
    // exponent is within one of this estimate; correct it by exact comparison.
    let mut exponent = numer_bits - denom_bits;
    for _ in 0..4 {
        if &scale_by_pow2(&BigRational::one(), exponent)? > a {
            exponent -= 1;
            continue;
        }
        if &scale_by_pow2(&BigRational::one(), exponent + 1)? <= a {
            exponent += 1;
            continue;
        }
        return Some(exponent);
    }
    None
}

/// Integer square root (floor) of a non-negative `BigInt`, by Newton descent.
fn isqrt(value: &BigInt) -> Option<BigInt> {
    if value.is_negative() {
        return None;
    }
    if value.is_zero() {
        return Some(BigInt::zero());
    }
    let bits = value.bits();
    let mut guess = BigInt::one() << usize::try_from(bits / 2 + 1).ok()?;
    loop {
        let next = (&guess + value / &guess) >> 1u32;
        if next >= guess {
            break;
        }
        guess = next;
    }
    // Newton descent from an over-estimate converges to `floor(sqrt(value))`.
    if &guess * &guess > *value {
        return None;
    }
    let above = &guess + BigInt::one();
    if &above * &above <= *value {
        return None;
    }
    Some(guess)
}

/// Local parity helper (`num_integer::Integer` is not a dependency here).
fn is_even(value: &BigInt) -> bool {
    !value.bit(0)
}

/// Round a non-negative rational to an integer under `rm`, where `sign` is the
/// sign of the VALUE the magnitude belongs to (the directed modes are about the
/// signed value, not the magnitude).
fn round_magnitude(scaled: &BigRational, rm: Rm, sign: bool) -> Option<BigInt> {
    if scaled.is_negative() {
        return None;
    }
    let floor = scaled.floor().to_integer();
    let fraction = scaled - BigRational::from_integer(floor.clone());
    if fraction.is_zero() {
        return Some(floor);
    }
    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    let up = floor.clone() + BigInt::one();
    Some(match rm {
        Rm::Rtz => floor,
        Rm::Rtp => {
            if sign {
                floor
            } else {
                up
            }
        }
        Rm::Rtn => {
            if sign {
                up
            } else {
                floor
            }
        }
        Rm::Rna => {
            if fraction >= half {
                up
            } else {
                floor
            }
        }
        Rm::Rne => match fraction.cmp(&half) {
            std::cmp::Ordering::Greater => up,
            std::cmp::Ordering::Less => floor,
            std::cmp::Ordering::Equal => {
                if is_even(&floor) {
                    floor
                } else {
                    up
                }
            }
        },
    })
}

/// Normalize an already-rounded `(integral, ulp_exponent)` pair into `(eb, sb)`
/// and encode it, applying the IEEE 754 §7.4 overflow rule.
///
/// `integral * 2^ulp_exponent` is the magnitude; `sign` is the value's sign.
fn encode_rounded(
    mut integral: BigInt,
    mut ulp_exponent: i64,
    sign: bool,
    eb: u32,
    sb: u32,
    rm: Rm,
) -> Option<Fp> {
    if integral.is_negative() {
        return None;
    }
    if !(2..=MAX_EB).contains(&eb) || !(2..=MAX_SB).contains(&sb) {
        return None;
    }
    if integral.is_zero() {
        // Rounded all the way down (underflow): IEEE gives the zero the sign
        // of the exact result.
        return Fp::zero(sign, eb, sb);
    }
    let bias = i64::try_from((1u64 << (eb - 1)) - 1).ok()?;
    let emin = 1 - bias;
    let emax = bias;
    let precision = i64::from(sb) - 1;
    let two_pow_sb = BigInt::one() << sb as usize;
    let two_pow_sb_minus_1 = BigInt::one() << (sb - 1) as usize;

    if integral >= two_pow_sb {
        // A carry out of the significand: `integral` is exactly `2^sb`.
        if integral != two_pow_sb {
            return None;
        }
        integral = two_pow_sb_minus_1.clone();
        ulp_exponent = ulp_exponent.checked_add(1)?;
    }

    if integral >= two_pow_sb_minus_1 {
        let unbiased = ulp_exponent.checked_add(precision)?;
        if unbiased > emax {
            // Overflow: the rounded-with-unbounded-exponent result exceeds the
            // largest finite number (IEEE 754 §7.4).
            return match rm {
                Rm::Rne | Rm::Rna => Fp::infinity(sign, eb, sb),
                Rm::Rtz => Fp::largest_finite(sign, eb, sb),
                Rm::Rtp => {
                    if sign {
                        Fp::largest_finite(true, eb, sb)
                    } else {
                        Fp::infinity(false, eb, sb)
                    }
                }
                Rm::Rtn => {
                    if sign {
                        Fp::infinity(true, eb, sb)
                    } else {
                        Fp::largest_finite(false, eb, sb)
                    }
                }
            };
        }
        let biased = u64::try_from(unbiased.checked_add(bias)?).ok()?;
        let stored = (integral - two_pow_sb_minus_1).to_u64()?;
        return Fp::checked(sign, biased, stored, eb, sb);
    }

    // Subnormal: reachable only when the ulp exponent sits at the subnormal
    // floor. Anything else violates a kernel invariant, so fail closed.
    if ulp_exponent != emin - precision {
        return None;
    }
    Fp::checked(sign, 0, integral.to_u64()?, eb, sb)
}

/// The exact rounding kernel: encode `±magnitude` into `(eb, sb)` under `rm`,
/// where `magnitude` is a strictly positive rational.
///
/// Follows IEEE 754-2008 §4.3: round at the target precision with an UNBOUNDED
/// exponent range (clamped only BELOW, at the subnormal ulp), then let
/// [`encode_rounded`] apply the overflow rule.
fn round_positive_magnitude(
    magnitude: &BigRational,
    sign: bool,
    eb: u32,
    sb: u32,
    rm: Rm,
) -> Option<Fp> {
    if !magnitude.is_positive() || !rational_is_bounded(magnitude) {
        return None;
    }
    if !(2..=MAX_EB).contains(&eb) || !(2..=MAX_SB).contains(&sb) {
        return None;
    }
    let bias = i64::try_from((1u64 << (eb - 1)) - 1).ok()?;
    let emin = 1 - bias;
    let precision = i64::from(sb) - 1;

    let exponent = floor_log2(magnitude)?;
    let ulp_exponent = exponent.max(emin).checked_sub(precision)?;
    let scaled = scale_by_pow2(magnitude, -ulp_exponent)?;
    let integral = round_magnitude(&scaled, rm, sign)?;
    encode_rounded(integral, ulp_exponent, sign, eb, sb, rm)
}

/// Round an exact rational (possibly zero) into `(eb, sb)`.
///
/// `zero_sign` supplies the sign an EXACTLY zero result must carry; IEEE fixes
/// that per operation, so the caller decides rather than this kernel guessing.
fn round_rational(value: &BigRational, zero_sign: bool, eb: u32, sb: u32, rm: Rm) -> Option<Fp> {
    if !rational_is_bounded(value) {
        return None;
    }
    if value.is_zero() {
        return Fp::zero(zero_sign, eb, sb);
    }
    let sign = value.is_negative();
    let magnitude = if sign { -value.clone() } else { value.clone() };
    round_positive_magnitude(&magnitude, sign, eb, sb, rm)
}

/// The sign an exactly-zero arithmetic result carries: `+0` in every rounding
/// mode except `roundTowardNegative`, which gives `-0` (IEEE 754 §6.3).
fn cancellation_zero_sign(rm: Rm) -> bool {
    matches!(rm, Rm::Rtn)
}

// ===========================================================================
// IEEE 754 operations
// ===========================================================================

fn fp_add(rm: Rm, x: &Fp, y: &Fp) -> Option<Fp> {
    if !x.same_format(y) {
        return None;
    }
    let (eb, sb) = (x.eb, x.sb);
    if x.is_nan() || y.is_nan() {
        return Fp::nan(eb, sb);
    }
    if x.is_infinite() && y.is_infinite() {
        return if x.sign == y.sign {
            Some(*x)
        } else {
            Fp::nan(eb, sb)
        };
    }
    if x.is_infinite() {
        return Some(*x);
    }
    if y.is_infinite() {
        return Some(*y);
    }
    if x.is_zero() && y.is_zero() {
        return if x.sign == y.sign {
            Some(*x)
        } else {
            Fp::zero(cancellation_zero_sign(rm), eb, sb)
        };
    }
    let sum = x.to_rational()? + y.to_rational()?;
    round_rational(&sum, cancellation_zero_sign(rm), eb, sb, rm)
}

fn fp_mul(rm: Rm, x: &Fp, y: &Fp) -> Option<Fp> {
    if !x.same_format(y) {
        return None;
    }
    let (eb, sb) = (x.eb, x.sb);
    if x.is_nan() || y.is_nan() {
        return Fp::nan(eb, sb);
    }
    let sign = x.sign ^ y.sign;
    if (x.is_infinite() && y.is_zero()) || (x.is_zero() && y.is_infinite()) {
        return Fp::nan(eb, sb);
    }
    if x.is_infinite() || y.is_infinite() {
        return Fp::infinity(sign, eb, sb);
    }
    if x.is_zero() || y.is_zero() {
        return Fp::zero(sign, eb, sb);
    }
    let product = x.to_rational()? * y.to_rational()?;
    round_rational(&product, sign, eb, sb, rm)
}

fn fp_div(rm: Rm, x: &Fp, y: &Fp) -> Option<Fp> {
    if !x.same_format(y) {
        return None;
    }
    let (eb, sb) = (x.eb, x.sb);
    if x.is_nan() || y.is_nan() {
        return Fp::nan(eb, sb);
    }
    let sign = x.sign ^ y.sign;
    if (x.is_infinite() && y.is_infinite()) || (x.is_zero() && y.is_zero()) {
        return Fp::nan(eb, sb);
    }
    if x.is_infinite() || y.is_zero() {
        return Fp::infinity(sign, eb, sb);
    }
    if y.is_infinite() || x.is_zero() {
        return Fp::zero(sign, eb, sb);
    }
    let quotient = x.to_rational()? / y.to_rational()?;
    round_rational(&quotient, sign, eb, sb, rm)
}

fn fp_fma(rm: Rm, x: &Fp, y: &Fp, z: &Fp) -> Option<Fp> {
    if !x.same_format(y) || !x.same_format(z) {
        return None;
    }
    let (eb, sb) = (x.eb, x.sb);
    if x.is_nan() || y.is_nan() || z.is_nan() {
        return Fp::nan(eb, sb);
    }
    let product_sign = x.sign ^ y.sign;
    if (x.is_infinite() && y.is_zero()) || (x.is_zero() && y.is_infinite()) {
        return Fp::nan(eb, sb);
    }
    if x.is_infinite() || y.is_infinite() {
        return if z.is_infinite() && z.sign != product_sign {
            Fp::nan(eb, sb)
        } else {
            Fp::infinity(product_sign, eb, sb)
        };
    }
    if z.is_infinite() {
        return Some(*z);
    }
    // Every operand is finite: multiply and add EXACTLY, then round ONCE.
    let product = x.to_rational()? * y.to_rational()?;
    let total = product + z.to_rational()?;
    if total.is_zero() {
        // IEEE 754 §7.4: when the product and the addend are both zeros of the
        // same sign the result keeps that sign; an exact cancellation
        // otherwise yields `+0` (`-0` under roundTowardNegative).
        let product_is_zero = x.is_zero() || y.is_zero();
        if product_is_zero && z.is_zero() && product_sign == z.sign {
            return Fp::zero(product_sign, eb, sb);
        }
        return Fp::zero(cancellation_zero_sign(rm), eb, sb);
    }
    round_rational(&total, cancellation_zero_sign(rm), eb, sb, rm)
}

/// Correctly-rounded square root, decided by EXACT integer comparisons — the
/// true square root is irrational in general, so it is never materialized.
fn fp_sqrt(rm: Rm, x: &Fp) -> Option<Fp> {
    let (eb, sb) = (x.eb, x.sb);
    if x.is_nan() {
        return Fp::nan(eb, sb);
    }
    if x.is_zero() {
        // `sqrt(+0) = +0`, `sqrt(-0) = -0`.
        return Some(*x);
    }
    if x.sign {
        return Fp::nan(eb, sb);
    }
    if x.is_infinite() {
        return Fp::infinity(false, eb, sb);
    }
    let magnitude = x.to_rational()?;
    if !magnitude.is_positive() || !rational_is_bounded(&magnitude) {
        return None;
    }
    let bias = i64::try_from((1u64 << (eb - 1)) - 1).ok()?;
    let emin = 1 - bias;
    let precision = i64::from(sb) - 1;

    // `floor(log2(sqrt(a)))`, corrected by exact comparison against powers of
    // two: `2^(2e) <= a < 2^(2e+2)`.
    let mut exponent = floor_log2(&magnitude)?.div_euclid(2);
    let mut settled = false;
    for _ in 0..4 {
        if scale_by_pow2(&BigRational::one(), exponent.checked_mul(2)?)? > magnitude {
            exponent -= 1;
            continue;
        }
        if scale_by_pow2(
            &BigRational::one(),
            exponent.checked_mul(2)?.checked_add(2)?,
        )? <= magnitude
        {
            exponent += 1;
            continue;
        }
        settled = true;
        break;
    }
    if !settled {
        return None;
    }
    let ulp_exponent = exponent.max(emin).checked_sub(precision)?;

    // `scaled = sqrt(a) / 2^ulp = sqrt(a / 4^ulp)`.
    let inner = scale_by_pow2(&magnitude, -ulp_exponent.checked_mul(2)?)?;
    if !inner.is_positive() || !rational_is_bounded(&inner) {
        return None;
    }
    let (numerator, denominator) = (inner.numer().clone(), inner.denom().clone());
    // `floor(sqrt(p/q)) = floor(sqrt(p*q)/q)`.
    let floor_root = isqrt(&(&numerator * &denominator))? / &denominator;
    let floor_squared = BigRational::from_integer(&floor_root * &floor_root);

    let integral = if floor_squared == inner {
        // The square root is exact at this scale.
        floor_root
    } else {
        // Compare `sqrt(inner)` against `floor_root + 1/2` by squaring:
        // `inner` against `(2*floor_root + 1)^2 / 4`.
        let doubled = &floor_root * BigInt::from(2) + BigInt::one();
        let midpoint_squared = BigRational::new(&doubled * &doubled, BigInt::from(4));
        let against_midpoint = inner.cmp(&midpoint_squared);
        let up = &floor_root + BigInt::one();
        match rm {
            // `sqrt` of a positive value is positive, so `RTN` and `RTZ` agree.
            Rm::Rtz | Rm::Rtn => floor_root,
            Rm::Rtp => up,
            Rm::Rna => match against_midpoint {
                std::cmp::Ordering::Less => floor_root,
                _ => up,
            },
            Rm::Rne => match against_midpoint {
                std::cmp::Ordering::Less => floor_root,
                std::cmp::Ordering::Greater => up,
                std::cmp::Ordering::Equal => {
                    if is_even(&floor_root) {
                        floor_root
                    } else {
                        up
                    }
                }
            },
        }
    };
    encode_rounded(integral, ulp_exponent, false, eb, sb, rm)
}

/// `((_ to_fp eb sb) rm x)` where `x` is another FP value.
fn fp_convert(rm: Rm, x: &Fp, eb: u32, sb: u32) -> Option<Fp> {
    if x.is_nan() {
        return Fp::nan(eb, sb);
    }
    if x.is_infinite() {
        return Fp::infinity(x.sign, eb, sb);
    }
    if x.is_zero() {
        return Fp::zero(x.sign, eb, sb);
    }
    let value = x.to_rational()?;
    round_rational(&value, x.sign, eb, sb, rm)
}

// ===========================================================================
// Clause-level validation
// ===========================================================================

/// Validate a `TheoryLemmaKind::FpGroundEval` lemma in strict mode.
pub(crate) fn validate_fp_ground_eval(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_ground_eval clause must be non-empty".to_string(),
        });
    }
    for &literal in clause {
        if !matches!(terms.sort(literal), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason: format!(
                    "fp_ground_eval literal has non-Bool sort {:?}; lemma clauses \
                     must be propositional",
                    terms.sort(literal)
                ),
            });
        }
    }
    if clause_is_exact_fp_tautology(terms, clause) {
        return Ok(());
    }
    Err(ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: "fp_ground_eval clause is not proved valid by the independent \
                 exact IEEE-754 evaluator (unsupported operator, unbounded \
                 variable domain, exhausted budget, or a falsifying \
                 assignment); rejecting in fail-closed mode"
            .to_string(),
    })
}

/// Recognize a clause the strict `FpGroundEval` validator will accept.
///
/// The EXACT precondition of [`validate_fp_ground_eval`], plus the FP-content
/// hygiene gate, so the `ay-dpll` classifier can only assign this kind to
/// lemmas strict mode then accepts — no classifier/checker drift. All decision
/// logic lives in this module.
#[must_use]
pub fn recognize_fp_ground_eval(terms: &TermStore, clause: &[TermId]) -> bool {
    if clause.is_empty() {
        return false;
    }
    if clause
        .iter()
        .any(|&literal| !matches!(terms.sort(literal), Sort::Bool))
    {
        return false;
    }
    // Hygiene: a clause with no floating-point content is not an FP lemma even
    // if it happens to be a tautology, so the exported rule name stays honest.
    if !mentions_floating_point(terms, clause) {
        return false;
    }
    clause_is_exact_fp_tautology(terms, clause)
}

fn mentions_floating_point(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut stack: Vec<TermId> = clause.to_vec();
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(terms.sort(term), Sort::FloatingPoint(_, _)) {
            return true;
        }
        stack.extend(terms.children(term));
    }
    false
}

/// Whether `term`'s whole DAG is variable-free.
fn is_ground(terms: &TermStore, term: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(current) = stack.pop() {
        if !seen.insert(current) {
            continue;
        }
        if matches!(terms.get(current), TermData::Var(_, _)) {
            return false;
        }
        stack.extend(terms.children(current));
    }
    true
}

/// Collect the substitution the clause itself licenses.
///
/// A literal `(not (= v g))` with `v` a variable and `g` ground means: in any
/// valuation that FALSIFIES the clause, `v` and `g` denote the same value, so
/// replacing `v` by `g` everywhere preserves every literal's truth value. The
/// FIRST binding for a variable wins; a second one stays an ordinary literal —
/// which is exactly what makes `x = 1.0 ∧ x = 2.0` refutable here.
fn collect_bindings(terms: &TermStore, clause: &[TermId]) -> HashMap<TermId, TermId> {
    let mut bindings: HashMap<TermId, TermId> = HashMap::default();
    for &literal in clause {
        let TermData::Not(inner) = terms.get(literal) else {
            continue;
        };
        let TermData::App(symbol, args) = terms.get(*inner) else {
            continue;
        };
        if !matches!(symbol, Symbol::Named(name) if name == "=") || args.len() != 2 {
            continue;
        }
        let (left, right) = (args[0], args[1]);
        for (variable, value) in [(left, right), (right, left)] {
            if !matches!(terms.get(variable), TermData::Var(_, _)) {
                continue;
            }
            if bindings.contains_key(&variable) {
                continue;
            }
            if terms.sort(variable) != terms.sort(value) {
                continue;
            }
            if is_ground(terms, value) {
                bindings.insert(variable, value);
            }
        }
    }
    bindings
}

/// Collect the variables that survive the substitution, with their domain size
/// in bits. `None` when a surviving variable has no enumerable finite domain.
fn collect_residual_variables(
    terms: &TermStore,
    clause: &[TermId],
    bindings: &HashMap<TermId, TermId>,
) -> Option<Vec<(TermId, u32)>> {
    let mut stack: Vec<TermId> = clause.to_vec();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut found: Vec<(TermId, u32)> = Vec::new();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(terms.get(term), TermData::Var(_, _)) {
            if bindings.contains_key(&term) {
                // Substituted away; its ground replacement contributes no
                // variables, by construction of `collect_bindings`.
                continue;
            }
            let bits = match terms.sort(term) {
                Sort::Bool => 1,
                Sort::BitVec(bv) if bv.width <= MAX_BV_WIDTH => bv.width,
                Sort::FloatingPoint(eb, sb)
                    if (2..=MAX_EB).contains(eb) && (2..=MAX_SB).contains(sb) =>
                {
                    eb.checked_add(*sb)?
                }
                _ => return None,
            };
            found.push((term, bits));
            continue;
        }
        stack.extend(terms.children(term));
    }
    found.sort_unstable();
    Some(found)
}

fn clause_is_exact_fp_tautology(terms: &TermStore, clause: &[TermId]) -> bool {
    let bindings = collect_bindings(terms, clause);
    let Some(variables) = collect_residual_variables(terms, clause, &bindings) else {
        return false;
    };
    let mut total_bits: u32 = 0;
    for (_, bits) in &variables {
        let Some(next) = total_bits.checked_add(*bits) else {
            return false;
        };
        total_bits = next;
        if total_bits > MAX_ENUMERATION_BITS {
            return false;
        }
    }
    let mut evaluator = Evaluator::new(terms, bindings);
    evaluator.precompute_varying(clause);
    let assignments: u64 = 1u64 << total_bits;
    for pattern in 0..assignments {
        let mut assignment: HashMap<TermId, Val> = HashMap::default();
        let mut offset: u32 = 0;
        for (variable, bits) in &variables {
            let mask = (1u64 << bits) - 1;
            let slice = (pattern >> offset) & mask;
            let Some(value) = variable_value(terms, *variable, slice) else {
                return false;
            };
            assignment.insert(*variable, value);
            offset += bits;
        }
        // A falsifying assignment — or anything the evaluator cannot decide —
        // rejects the whole lemma.
        if evaluator.clause_holds(clause, &assignment) != Some(true) {
            return false;
        }
    }
    true
}

/// Build the value an enumerated variable takes for bit pattern `slice`.
fn variable_value(terms: &TermStore, variable: TermId, slice: u64) -> Option<Val> {
    match terms.sort(variable) {
        Sort::Bool => Some(Val::Bool(slice & 1 == 1)),
        Sort::BitVec(bv) => Some(Val::Bv(BigInt::from(slice), bv.width)),
        Sort::FloatingPoint(eb, sb) => {
            Some(Val::Fp(Fp::from_bits(&BigInt::from(slice), *eb, *sb)?))
        }
        _ => None,
    }
}

// ===========================================================================
// Evaluation
// ===========================================================================

/// A fully evaluated value.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Val {
    Bool(bool),
    Fp(Fp),
    /// A bitvector value in `[0, 2^width)`.
    Bv(BigInt, u32),
    Rm(Rm),
    Int(BigInt),
    Real(BigRational),
}

impl Val {
    fn as_bool(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => Some(*value),
            _ => None,
        }
    }
    fn as_fp(&self) -> Option<Fp> {
        match self {
            Self::Fp(value) => Some(*value),
            _ => None,
        }
    }
    fn as_rm(&self) -> Option<Rm> {
        match self {
            Self::Rm(value) => Some(*value),
            _ => None,
        }
    }
    fn as_bv(&self) -> Option<(BigInt, u32)> {
        match self {
            Self::Bv(value, width) => Some((value.clone(), *width)),
            _ => None,
        }
    }
    /// Exact rational view of a numeric value.
    fn as_rational(&self) -> Option<BigRational> {
        match self {
            Self::Int(value) => Some(BigRational::from_integer(value.clone())),
            Self::Real(value) => Some(value.clone()),
            _ => None,
        }
    }
}

struct Evaluator<'a> {
    terms: &'a TermStore,
    bindings: HashMap<TermId, TermId>,
    budget: usize,
    /// Values of terms that do NOT depend on any enumerated variable; shared
    /// across assignments so ground arithmetic is evaluated exactly once.
    stable: HashMap<TermId, Option<Val>>,
    /// Terms whose DAG reaches an enumerated variable. A term missing from the
    /// precomputation is treated as varying, which is merely slower.
    varying: HashSet<TermId>,
}

impl<'a> Evaluator<'a> {
    fn new(terms: &'a TermStore, bindings: HashMap<TermId, TermId>) -> Self {
        Self {
            terms,
            bindings,
            budget: FP_GROUND_WORK_LIMIT,
            stable: HashMap::default(),
            varying: HashSet::default(),
        }
    }

    fn spend(&mut self) -> Option<()> {
        self.budget = self.budget.checked_sub(1)?;
        Some(())
    }

    /// Mark every term whose DAG reaches an enumerated (unbound) variable, by
    /// an ITERATIVE post-order walk — an adversarial proof payload must not be
    /// able to recurse the checker off its stack.
    fn precompute_varying(&mut self, clause: &[TermId]) {
        let mut stack: Vec<(TermId, bool)> = clause.iter().map(|&term| (term, false)).collect();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some((term, expanded)) = stack.pop() {
            if expanded {
                let children = self.terms.children(term);
                let varies = match self.terms.get(term) {
                    TermData::Var(_, _) => !self.bindings.contains_key(&term),
                    _ => children.iter().any(|child| self.varying.contains(child)),
                };
                if varies {
                    self.varying.insert(term);
                }
                continue;
            }
            if !visited.insert(term) {
                continue;
            }
            stack.push((term, true));
            for child in self.terms.children(term) {
                stack.push((child, false));
            }
        }
    }

    fn is_varying(&self, term: TermId) -> bool {
        self.varying.contains(&term)
    }

    fn clause_holds(
        &mut self,
        clause: &[TermId],
        assignment: &HashMap<TermId, Val>,
    ) -> Option<bool> {
        let mut local: HashMap<TermId, Option<Val>> = HashMap::default();
        for &literal in clause {
            if self.eval(literal, assignment, &mut local, 0)?.as_bool()? {
                return Some(true);
            }
        }
        Some(false)
    }

    fn eval(
        &mut self,
        term: TermId,
        assignment: &HashMap<TermId, Val>,
        local: &mut HashMap<TermId, Option<Val>>,
        depth: usize,
    ) -> Option<Val> {
        if depth > MAX_DEPTH {
            return None;
        }
        if self.is_varying(term) {
            if let Some(cached) = local.get(&term) {
                return cached.clone();
            }
            self.spend()?;
            let value = self.eval_uncached(term, assignment, local, depth);
            local.insert(term, value.clone());
            return value;
        }
        if let Some(cached) = self.stable.get(&term) {
            return cached.clone();
        }
        self.spend()?;
        let value = self.eval_uncached(term, assignment, local, depth);
        self.stable.insert(term, value.clone());
        value
    }

    fn eval_uncached(
        &mut self,
        term: TermId,
        assignment: &HashMap<TermId, Val>,
        local: &mut HashMap<TermId, Option<Val>>,
        depth: usize,
    ) -> Option<Val> {
        match self.terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(Val::Bool(*value)),
            TermData::Const(Constant::Int(value)) => Some(Val::Int(value.clone())),
            TermData::Const(Constant::Rational(value)) => Some(Val::Real(value.0.clone())),
            TermData::Const(Constant::BitVec { value, width }) => {
                if *width > MAX_BV_WIDTH || value.is_negative() {
                    return None;
                }
                Some(Val::Bv(value.clone(), *width))
            }
            TermData::Var(_, _) => {
                if let Some(value) = assignment.get(&term) {
                    return Some(value.clone());
                }
                let bound = *self.bindings.get(&term)?;
                self.eval(bound, assignment, local, depth + 1)
            }
            TermData::Not(inner) => {
                let inner = *inner;
                Some(Val::Bool(
                    !self.eval(inner, assignment, local, depth + 1)?.as_bool()?,
                ))
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let (condition, then_branch, else_branch) =
                    (*condition, *then_branch, *else_branch);
                if self
                    .eval(condition, assignment, local, depth + 1)?
                    .as_bool()?
                {
                    self.eval(then_branch, assignment, local, depth + 1)
                } else {
                    self.eval(else_branch, assignment, local, depth + 1)
                }
            }
            TermData::App(symbol, args) => {
                let symbol = symbol.clone();
                let args = args.clone();
                self.eval_app(term, &symbol, &args, assignment, local, depth)
            }
            _ => None,
        }
    }

    #[allow(clippy::too_many_lines)]
    fn eval_app(
        &mut self,
        term: TermId,
        symbol: &Symbol,
        args: &[TermId],
        assignment: &HashMap<TermId, Val>,
        local: &mut HashMap<TermId, Option<Val>>,
        depth: usize,
    ) -> Option<Val> {
        let next = depth + 1;

        // ---- FP nullary literals `(_ +zero eb sb)` etc. ----
        //
        // The INDEXED form only, with indices that agree with the recorded FP
        // sort. `ay-frontend` classifies these five names `IndexedOnly`: the
        // `(_ …)` form is theory syntax no declaration can produce, but the
        // BARE `Symbol::Named("NaN")` spelling remains an ordinary declarable
        // identity, so keying on `sym.name()` alone would give IEEE semantics
        // to whatever the problem declared. Re-deriving the indexed shape here
        // keeps the check local instead of resting on the frontend minting
        // declared nullary symbols as `TermData::Var`.
        if let Symbol::Indexed(literal, indices) = symbol {
            if args.is_empty()
                && matches!(literal.as_str(), "+zero" | "-zero" | "+oo" | "-oo" | "NaN")
            {
                let Sort::FloatingPoint(eb, sb) = self.terms.sort(term) else {
                    return None;
                };
                let (eb, sb) = (*eb, *sb);
                if indices.as_slice() != [eb, sb] {
                    return None;
                }
                return Some(Val::Fp(match literal.as_str() {
                    "+zero" => Fp::zero(false, eb, sb)?,
                    "-zero" => Fp::zero(true, eb, sb)?,
                    "+oo" => Fp::infinity(false, eb, sb)?,
                    "-oo" => Fp::infinity(true, eb, sb)?,
                    _ => Fp::nan(eb, sb)?,
                }));
            }
            // ---- indexed conversions ----
            if matches!(literal.as_str(), "to_fp" | "to_fp_unsigned") {
                return self.eval_to_fp(term, literal, indices, args, assignment, local, next);
            }

            // No other indexed identifier has semantics in this evaluator. In
            // particular, `(_ fp.add ...)` and `(_ RNE ...)` are not aliases
            // for their named builtins.
            return None;
        }

        let Symbol::Named(name) = symbol else {
            return None;
        };
        let name = name.as_str();

        // ---- rounding-mode literals ----
        if args.is_empty() {
            if let Some(rounding_mode) = Rm::from_name(name) {
                return Some(Val::Rm(rounding_mode));
            }
        }

        match (name, args.len()) {
            // ---- Boolean structure ----
            ("not", 1) => Some(Val::Bool(
                !self.eval(args[0], assignment, local, next)?.as_bool()?,
            )),
            ("and", _) if !args.is_empty() => {
                for &arg in args {
                    if !self.eval(arg, assignment, local, next)?.as_bool()? {
                        return Some(Val::Bool(false));
                    }
                }
                Some(Val::Bool(true))
            }
            ("or", _) if !args.is_empty() => {
                for &arg in args {
                    if self.eval(arg, assignment, local, next)?.as_bool()? {
                        return Some(Val::Bool(true));
                    }
                }
                Some(Val::Bool(false))
            }
            ("xor", _) if !args.is_empty() => {
                let mut accumulator = false;
                for &arg in args {
                    accumulator ^= self.eval(arg, assignment, local, next)?.as_bool()?;
                }
                Some(Val::Bool(accumulator))
            }
            ("=>", _) if args.len() >= 2 => {
                let mut values = Vec::with_capacity(args.len());
                for &arg in args {
                    values.push(self.eval(arg, assignment, local, next)?.as_bool()?);
                }
                let mut accumulator = *values.last()?;
                for &value in values[..values.len() - 1].iter().rev() {
                    accumulator = !value || accumulator;
                }
                Some(Val::Bool(accumulator))
            }
            ("ite", 3) => {
                if self.eval(args[0], assignment, local, next)?.as_bool()? {
                    self.eval(args[1], assignment, local, next)
                } else {
                    self.eval(args[2], assignment, local, next)
                }
            }

            // ---- equality / distinct ----
            ("=", _) if args.len() >= 2 => {
                let first = self.eval(args[0], assignment, local, next)?;
                for &arg in &args[1..] {
                    let value = self.eval(arg, assignment, local, next)?;
                    if !values_equal(&first, &value)? {
                        return Some(Val::Bool(false));
                    }
                }
                Some(Val::Bool(true))
            }
            ("distinct", _) if args.len() >= 2 => {
                let mut values = Vec::with_capacity(args.len());
                for &arg in args {
                    values.push(self.eval(arg, assignment, local, next)?);
                }
                for left in 0..values.len() {
                    for right in (left + 1)..values.len() {
                        if values_equal(&values[left], &values[right])? {
                            return Some(Val::Bool(false));
                        }
                    }
                }
                Some(Val::Bool(true))
            }

            // ---- FP construction `(fp sign exponent significand)` ----
            ("fp", 3) => {
                let (sign, sign_width) = self.eval(args[0], assignment, local, next)?.as_bv()?;
                let (exponent, exponent_width) =
                    self.eval(args[1], assignment, local, next)?.as_bv()?;
                let (significand, significand_width) =
                    self.eval(args[2], assignment, local, next)?.as_bv()?;
                if sign_width != 1 {
                    return None;
                }
                Some(Val::Fp(Fp::checked(
                    sign.to_u64()? == 1,
                    exponent.to_u64()?,
                    significand.to_u64()?,
                    exponent_width,
                    significand_width.checked_add(1)?,
                )?))
            }

            // ---- FP sign / classification ----
            ("fp.abs", 1) => Some(Val::Fp(
                self.eval(args[0], assignment, local, next)?.as_fp()?.abs(),
            )),
            ("fp.neg", 1) => Some(Val::Fp(
                self.eval(args[0], assignment, local, next)?
                    .as_fp()?
                    .negated(),
            )),
            (
                "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
                | "fp.isPositive" | "fp.isNegative",
                1,
            ) => {
                let value = self.eval(args[0], assignment, local, next)?.as_fp()?;
                Some(Val::Bool(match name {
                    "fp.isNaN" => value.is_nan(),
                    "fp.isInfinite" => value.is_infinite(),
                    "fp.isZero" => value.is_zero(),
                    "fp.isNormal" => value.is_normal(),
                    "fp.isSubnormal" => value.is_subnormal(),
                    "fp.isPositive" => value.is_positive(),
                    _ => value.is_negative(),
                }))
            }

            // ---- FP comparisons (chainable, `:chainable` in SMT-LIB) ----
            ("fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq", _) if args.len() >= 2 => {
                use std::cmp::Ordering;
                let mut previous = self.eval(args[0], assignment, local, next)?.as_fp()?;
                for &arg in &args[1..] {
                    let current = self.eval(arg, assignment, local, next)?.as_fp()?;
                    // Any NaN operand makes every FP comparison false.
                    let Some(ordering) = previous.cmp_real(&current) else {
                        return Some(Val::Bool(false));
                    };
                    let holds = match name {
                        "fp.eq" => ordering == Ordering::Equal,
                        "fp.lt" => ordering == Ordering::Less,
                        "fp.leq" => ordering != Ordering::Greater,
                        "fp.gt" => ordering == Ordering::Greater,
                        _ => ordering != Ordering::Less,
                    };
                    if !holds {
                        return Some(Val::Bool(false));
                    }
                    previous = current;
                }
                Some(Val::Bool(true))
            }

            // ---- FP arithmetic (correctly rounded, exact rationals) ----
            ("fp.add" | "fp.sub" | "fp.mul" | "fp.div", 3) => {
                let rounding_mode = self.eval(args[0], assignment, local, next)?.as_rm()?;
                let left = self.eval(args[1], assignment, local, next)?.as_fp()?;
                let right = self.eval(args[2], assignment, local, next)?.as_fp()?;
                Some(Val::Fp(match name {
                    "fp.add" => fp_add(rounding_mode, &left, &right)?,
                    "fp.sub" => fp_add(rounding_mode, &left, &right.negated())?,
                    "fp.mul" => fp_mul(rounding_mode, &left, &right)?,
                    _ => fp_div(rounding_mode, &left, &right)?,
                }))
            }
            ("fp.fma", 4) => {
                let rounding_mode = self.eval(args[0], assignment, local, next)?.as_rm()?;
                let x = self.eval(args[1], assignment, local, next)?.as_fp()?;
                let y = self.eval(args[2], assignment, local, next)?.as_fp()?;
                let z = self.eval(args[3], assignment, local, next)?.as_fp()?;
                Some(Val::Fp(fp_fma(rounding_mode, &x, &y, &z)?))
            }
            ("fp.sqrt", 2) => {
                let rounding_mode = self.eval(args[0], assignment, local, next)?.as_rm()?;
                let x = self.eval(args[1], assignment, local, next)?.as_fp()?;
                Some(Val::Fp(fp_sqrt(rounding_mode, &x)?))
            }
            ("fp.to_real", 1) => {
                // NaN and the infinities have no real value: SMT-LIB leaves
                // `fp.to_real` unspecified there, so fail closed.
                let value = self.eval(args[0], assignment, local, next)?.as_fp()?;
                Some(Val::Real(value.to_rational()?))
            }

            // ---- exact numeric glue (Int / Real) ----
            ("+", _) if !args.is_empty() => {
                self.fold_numeric(args, assignment, local, next, |a, b| a + b)
            }
            ("*", _) if !args.is_empty() => {
                self.fold_numeric(args, assignment, local, next, |a, b| a * b)
            }
            ("-", 1) => {
                let value = self.eval(args[0], assignment, local, next)?.as_rational()?;
                Some(if matches!(self.terms.sort(args[0]), Sort::Int) {
                    Val::Int(-value.to_integer())
                } else {
                    Val::Real(-value)
                })
            }
            ("-", _) if args.len() >= 2 => {
                self.fold_numeric(args, assignment, local, next, |a, b| a - b)
            }
            ("/", _) if args.len() >= 2 => {
                let mut accumulator = self.eval(args[0], assignment, local, next)?.as_rational()?;
                for &arg in &args[1..] {
                    let value = self.eval(arg, assignment, local, next)?.as_rational()?;
                    if value.is_zero() {
                        // `(/ x 0)` is under-specified in SMT-LIB.
                        return None;
                    }
                    accumulator /= value;
                    if !rational_is_bounded(&accumulator) {
                        return None;
                    }
                }
                Some(Val::Real(accumulator))
            }
            ("<" | "<=" | ">" | ">=", 2) => {
                let left = self.eval(args[0], assignment, local, next)?.as_rational()?;
                let right = self.eval(args[1], assignment, local, next)?.as_rational()?;
                Some(Val::Bool(match name {
                    "<" => left < right,
                    "<=" => left <= right,
                    ">" => left > right,
                    _ => left >= right,
                }))
            }

            _ => None,
        }
    }

    fn fold_numeric(
        &mut self,
        args: &[TermId],
        assignment: &HashMap<TermId, Val>,
        local: &mut HashMap<TermId, Option<Val>>,
        depth: usize,
        combine: impl Fn(BigRational, BigRational) -> BigRational,
    ) -> Option<Val> {
        let mut accumulator = self
            .eval(args[0], assignment, local, depth)?
            .as_rational()?;
        let mut integral = matches!(self.terms.sort(args[0]), Sort::Int);
        for &arg in &args[1..] {
            let value = self.eval(arg, assignment, local, depth)?.as_rational()?;
            integral &= matches!(self.terms.sort(arg), Sort::Int);
            accumulator = combine(accumulator, value);
            if !rational_is_bounded(&accumulator) {
                return None;
            }
        }
        Some(if integral && accumulator.is_integer() {
            Val::Int(accumulator.to_integer())
        } else {
            Val::Real(accumulator)
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn eval_to_fp(
        &mut self,
        term: TermId,
        name: &str,
        indices: &[u32],
        args: &[TermId],
        assignment: &HashMap<TermId, Val>,
        local: &mut HashMap<TermId, Option<Val>>,
        depth: usize,
    ) -> Option<Val> {
        let [index_eb, index_sb] = indices else {
            return None;
        };
        // The declared result sort is authoritative and must agree with the
        // indices; a mismatch is a malformed term, not something to guess at.
        let Sort::FloatingPoint(eb, sb) = self.terms.sort(term) else {
            return None;
        };
        let (eb, sb) = (*eb, *sb);
        if eb != *index_eb || sb != *index_sb {
            return None;
        }
        if !(2..=MAX_EB).contains(&eb) || !(2..=MAX_SB).contains(&sb) {
            return None;
        }

        match (name, args.len()) {
            // `((_ to_fp eb sb) bv)`: reinterpret an `eb + sb`-bit pattern.
            ("to_fp", 1) => {
                let (bits, width) = self.eval(args[0], assignment, local, depth)?.as_bv()?;
                if width != eb.checked_add(sb)? {
                    return None;
                }
                Some(Val::Fp(Fp::from_bits(&bits, eb, sb)?))
            }
            // `((_ to_fp eb sb) rm x)`: convert from FP, Real, Int, or a
            // SIGNED bitvector. `((_ to_fp_unsigned eb sb) rm bv)`: unsigned.
            ("to_fp" | "to_fp_unsigned", 2) => {
                let rounding_mode = self.eval(args[0], assignment, local, depth)?.as_rm()?;
                let source = self.eval(args[1], assignment, local, depth)?;
                let signed = name == "to_fp";
                let value = match &source {
                    Val::Fp(inner) => {
                        if !signed {
                            return None;
                        }
                        return Some(Val::Fp(fp_convert(rounding_mode, inner, eb, sb)?));
                    }
                    Val::Bv(bits, width) => BigRational::from_integer(if signed {
                        signed_value(bits, *width)?
                    } else {
                        bits.clone()
                    }),
                    Val::Int(integer) => {
                        if !signed {
                            return None;
                        }
                        BigRational::from_integer(integer.clone())
                    }
                    Val::Real(real) => {
                        if !signed {
                            return None;
                        }
                        real.clone()
                    }
                    Val::Bool(_) | Val::Rm(_) => return None,
                };
                // A zero source converts to `+0` under every rounding mode.
                Some(Val::Fp(round_rational(
                    &value,
                    false,
                    eb,
                    sb,
                    rounding_mode,
                )?))
            }
            _ => None,
        }
    }
}

/// Two's-complement reading of a `width`-bit pattern.
fn signed_value(bits: &BigInt, width: u32) -> Option<BigInt> {
    if width == 0 || width > MAX_BV_WIDTH || bits.is_negative() {
        return None;
    }
    let modulus = BigInt::one() << width as usize;
    if bits >= &modulus {
        return None;
    }
    let half = BigInt::one() << (width - 1) as usize;
    Some(if bits >= &half {
        bits - modulus
    } else {
        bits.clone()
    })
}

/// SMT-LIB `=` on evaluated values: identity of the ABSTRACT value.
fn values_equal(left: &Val, right: &Val) -> Option<bool> {
    Some(match (left, right) {
        (Val::Bool(a), Val::Bool(b)) => a == b,
        (Val::Fp(a), Val::Fp(b)) => a.structural_eq(b)?,
        (Val::Bv(a, left_width), Val::Bv(b, right_width)) => {
            if left_width != right_width {
                return None;
            }
            a == b
        }
        (Val::Rm(a), Val::Rm(b)) => a == b,
        (Val::Int(a), Val::Int(b)) => a == b,
        (Val::Real(a), Val::Real(b)) => a == b,
        (Val::Int(a), Val::Real(b)) | (Val::Real(b), Val::Int(a)) => {
            &BigRational::from_integer(a.clone()) == b
        }
        // Mixed sorts are ill-sorted input; fail closed rather than guess.
        _ => return None,
    })
}

#[cfg(test)]
#[path = "fp_ground_tests.rs"]
mod fp_ground_tests;

#[cfg(test)]
#[path = "fp_ground_adversarial_audit_tests.rs"]
mod fp_ground_adversarial_audit_tests;
