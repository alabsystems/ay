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
//! `fp.min`, `fp.max` and `fp.to_ieee_bv`
//! remain unsupported. Float-to-bitvector conversions evaluate only finite
//! inputs whose rounded integer is in range; all under-specified cases refuse.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
#[cfg(test)]
use num_traits::One;
use num_traits::{Signed, ToPrimitive, Zero};

use super::ProofCheckError;

mod commutativity;
mod int_cast;
mod integral;
mod progress;
use progress::Arithmetic;
use progress::Meter;

#[cfg(test)]
fn with_local_meter<T>(action: impl FnOnce(&mut Meter<'_>) -> Option<T>) -> Option<T> {
    let mut no_caller = |_, _| true;
    action(&mut Meter::new(&mut no_caller))
}

// Kernel tests retain their direct entrypoints, but execute the exact same
// owned arithmetic with a fresh local bound for each independent test request.
#[cfg(test)]
macro_rules! local_math_entry {
    ($name:ident, $owned:ident, ($($arg:ident: $ty:ty),*), $result:ty) => {
        fn $name($($arg: $ty),*) -> Option<$result> {
            with_local_meter(|meter| $owned($($arg),*, meter))
        }
    };
}
#[cfg(test)]
local_math_entry!(scale_by_pow2, scale_by_pow2_owned, (value: &BigRational, shift: i64), BigRational);
#[cfg(test)]
local_math_entry!(round_rational, round_rational_owned, (value: &BigRational, sign: bool, eb: u32, sb: u32, rm: Rm), Fp);
#[cfg(test)]
local_math_entry!(fp_add, fp_add_owned, (rm: Rm, x: &Fp, y: &Fp), Fp);
#[cfg(test)]
local_math_entry!(fp_mul, fp_mul_owned, (rm: Rm, x: &Fp, y: &Fp), Fp);
#[cfg(test)]
local_math_entry!(fp_div, fp_div_owned, (rm: Rm, x: &Fp, y: &Fp), Fp);
#[cfg(test)]
local_math_entry!(fp_fma, fp_fma_owned, (rm: Rm, x: &Fp, y: &Fp, z: &Fp), Fp);
#[cfg(test)]
local_math_entry!(fp_sqrt, fp_sqrt_owned, (rm: Rm, x: &Fp), Fp);
#[cfg(test)]
local_math_entry!(fp_convert, fp_convert_owned, (rm: Rm, x: &Fp, eb: u32, sb: u32), Fp);
#[cfg(test)]
local_math_entry!(signed_value, signed_value_owned, (bits: &BigInt, width: u32), BigInt);

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
/// Match the solver's bounded ground arithmetic; two fixed limbs retain the
/// complete stored fraction without borrowing its decoder or evaluator.
const MAX_SB: u32 = 256;

/// Largest bitvector width this kernel will decode or enumerate.
const MAX_BV_WIDTH: u32 = 256;

/// Cap on the precision of exact rationals reaching the rounding kernel, as a
/// bit count on numerator and denominator. A proof payload cannot make the
/// checker allocate unbounded precision.
const MAX_RATIONAL_BITS: u64 = 1 << 16;

/// Whether the independent ground kernel can represent this format's fields.
/// Arithmetic can still decline on work/precision limits. This is dispatch
/// information, never evidence that a particular formula has been checked.
pub fn fp_ground_format_supported(eb: u32, sb: u32) -> bool {
    (2..=MAX_EB).contains(&eb) && (2..=MAX_SB).contains(&sb)
}

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
    significand: u128,
    /// High stored-fraction limb. The low limb above keeps bits 0..127.
    significand_high: u128,
    /// Exponent width.
    eb: u32,
    /// Significand width, hidden bit included.
    sb: u32,
}

impl Fp {
    fn checked(sign: bool, exponent: u64, significand: u128, eb: u32, sb: u32) -> Option<Self> {
        Self::checked_wide(sign, exponent, (0, significand), eb, sb)
    }

    fn fraction_mask(stored: u32) -> Option<(u128, u128)> {
        match stored {
            0..=127 => Some((0, (1u128 << stored) - 1)),
            128 => Some((0, u128::MAX)),
            129..=255 => Some(((1u128 << (stored - 128)) - 1, u128::MAX)),
            _ => None,
        }
    }

    fn checked_wide(
        sign: bool,
        exponent: u64,
        significand: (u128, u128),
        eb: u32,
        sb: u32,
    ) -> Option<Self> {
        if !fp_ground_format_supported(eb, sb) {
            return None;
        }
        let max_exp = (1u64 << eb) - 1;
        let stored = sb - 1;
        let sig_mask = Self::fraction_mask(stored)?;
        if exponent > max_exp || significand > sig_mask {
            return None;
        }
        Some(Self {
            sign,
            exponent,
            significand: significand.1,
            significand_high: significand.0,
            eb,
            sb,
        })
    }

    /// Decode a raw `eb + sb` bit pattern (MSB is the sign).
    #[cfg(test)]
    fn from_bits(bits: &BigInt, eb: u32, sb: u32) -> Option<Self> {
        with_local_meter(|meter| Self::from_bits_owned(bits, eb, sb, meter))
    }

    fn from_bits_owned(bits: &BigInt, eb: u32, sb: u32, meter: &mut Meter<'_>) -> Option<Self> {
        if !(2..=MAX_EB).contains(&eb) || !(2..=MAX_SB).contains(&sb) {
            return None;
        }
        if bits.is_negative() || bits.bits() > u64::from(eb.checked_add(sb)?) {
            return None;
        }
        let stored = sb.checked_sub(1)?;
        let significand = bit_slice_wide_owned(bits, 0, stored, meter)?;
        let exponent = bit_slice_owned(bits, stored, eb, meter)?;
        let sign = bit_slice_owned(bits, stored.checked_add(eb)?, 1, meter)? == 1;
        Self::checked_wide(sign, exponent, significand, eb, sb)
    }

    fn max_exp(&self) -> u64 {
        // The all-ones `eb`-bit field. `Fp::checked` bounds `eb` by `MAX_EB`,
        // so the shift never saturates for a constructed value.
        1u64.checked_shl(self.eb)
            .map_or(u64::MAX, |bit| bit.saturating_sub(1))
    }

    fn is_nan(&self) -> bool {
        self.exponent == self.max_exp() && (self.significand_high, self.significand) != (0, 0)
    }

    fn is_infinite(&self) -> bool {
        self.exponent == self.max_exp() && (self.significand_high, self.significand) == (0, 0)
    }

    fn is_zero(&self) -> bool {
        self.exponent == 0 && (self.significand_high, self.significand) == (0, 0)
    }

    fn is_normal(&self) -> bool {
        self.exponent != 0 && self.exponent != self.max_exp()
    }

    fn is_subnormal(&self) -> bool {
        self.exponent == 0 && (self.significand_high, self.significand) != (0, 0)
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
        Self::checked(sign, 1u64.checked_shl(eb)?.checked_sub(1)?, 0, eb, sb)
    }

    /// The canonical quiet NaN: exponent all ones, MSB of the stored
    /// significand set.
    fn nan(eb: u32, sb: u32) -> Option<Self> {
        if !(2..=MAX_SB).contains(&sb) || !(2..=MAX_EB).contains(&eb) {
            return None;
        }
        let bit = sb - 2;
        let fraction = if bit < 128 {
            (0, 1u128 << bit)
        } else {
            (1u128 << (bit - 128), 0)
        };
        Self::checked_wide(false, (1u64 << eb) - 1, fraction, eb, sb)
    }

    fn largest_finite(sign: bool, eb: u32, sb: u32) -> Option<Self> {
        if !(2..=MAX_SB).contains(&sb) || !(2..=MAX_EB).contains(&eb) {
            return None;
        }
        let stored = sb - 1;
        let sig_mask = Self::fraction_mask(stored)?;
        Self::checked_wide(sign, (1u64 << eb) - 2, sig_mask, eb, sb)
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
                && self.significand == other.significand
                && self.significand_high == other.significand_high,
        )
    }

    /// Exact rational value of a FINITE number; `None` for NaN and infinities.
    #[cfg(test)]
    fn to_rational(self) -> Option<BigRational> {
        with_local_meter(|meter| self.to_rational_owned(meter))
    }

    fn to_rational_owned(self, meter: &mut Meter<'_>) -> Option<BigRational> {
        meter.charge(1, 0)?;
        if self.is_nan() || self.is_infinite() {
            return None;
        }
        if self.is_zero() {
            let zero = meter.integer(0)?;
            return meter.rational_from_integer(zero);
        }
        let bias = (1u64 << (self.eb - 1)) - 1;
        let stored = self.sb - 1;
        let low = meter.integer(self.significand)?;
        let fraction = if self.significand_high == 0 {
            low
        } else {
            let high = meter.integer(self.significand_high)?;
            let high = meter.shift(&high, 128)?;
            meter.integer_binary(&high, &low, Arithmetic::Add)?
        };
        let significand = if self.exponent == 0 {
            fraction
        } else {
            let one = meter.integer(1)?;
            let hidden = meter.shift(&one, i64::from(stored))?;
            meter.integer_binary(&hidden, &fraction, Arithmetic::Add)?
        };
        let shift = if self.exponent == 0 {
            1i64 - i64::try_from(bias).ok()? - i64::from(stored)
        } else {
            i64::try_from(self.exponent).ok()? - i64::try_from(bias).ok()? - i64::from(stored)
        };
        let significand = meter.rational_from_integer(significand)?;
        let magnitude = scale_by_pow2_owned(&significand, shift, meter)?;
        Some(if self.sign { -magnitude } else { magnitude })
    }

    /// Order on the extended reals for the IEEE comparison predicates.
    /// `None` exactly when a NaN is involved (every comparison is then false)
    /// or when the formats are incomparable.
    #[cfg(test)]
    fn cmp_real(&self, other: &Self) -> Option<std::cmp::Ordering> {
        with_local_meter(|meter| self.cmp_real_owned(other, meter))
    }

    fn cmp_real_owned(&self, other: &Self, meter: &mut Meter<'_>) -> Option<std::cmp::Ordering> {
        meter.charge(1, 0)?;
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
            let magnitude = |v: &Self| (v.exponent, v.significand_high, v.significand);
            return Some(match (self.sign, other.sign) {
                (false, false) => magnitude(self).cmp(&magnitude(other)),
                (true, true) => magnitude(other).cmp(&magnitude(self)),
                (false, true) => Ordering::Greater,
                (true, false) => Ordering::Less,
            });
        }
        // Mixed formats: compare on the extended reals.
        let mut rank = |v: &Self| -> (i8, Option<BigRational>) {
            if v.is_infinite() {
                (if v.sign { -1 } else { 1 }, None)
            } else {
                (0, v.to_rational_owned(meter))
            }
        };
        let (left_rank, left_value) = rank(self);
        let (right_rank, right_value) = rank(other);
        match left_rank.cmp(&right_rank) {
            // Each `Option` is consumed whole: moving the payloads out of a
            // tuple pattern leaves a drop that switches on the niche-encoded
            // discriminant, whose `unreachable` default per-function
            // verification cannot rule out.
            Ordering::Equal => {
                if left_value.is_none() && right_value.is_none() {
                    Some(Ordering::Equal)
                } else {
                    left_value
                        .zip(right_value)
                        .and_then(|(left, right)| meter.rational_compare(&left, &right))
                }
            }
            ordering => Some(ordering),
        }
    }
}

/// Read `width` bits of `bits` starting at `offset` (LSB = 0) as a `u64`.
fn bit_slice_owned(bits: &BigInt, offset: u32, width: u32, meter: &mut Meter<'_>) -> Option<u64> {
    if width > 64 {
        return None;
    }
    u64::try_from(bit_slice_wide_owned(bits, offset, width, meter)?.1).ok()
}

fn bit_slice_wide_owned(
    bits: &BigInt,
    offset: u32,
    width: u32,
    meter: &mut Meter<'_>,
) -> Option<(u128, u128)> {
    if bits.is_negative() || width > 256 {
        return None;
    }
    let shifted = meter.shift(bits, -i64::from(offset))?;
    let one = meter.integer(1)?;
    let power = meter.shift(&one, i64::from(width))?;
    let mask = meter.integer_binary(&power, &one, Arithmetic::Subtract)?;
    let field = meter.bit_and(&shifted, &mask)?;
    if width <= 128 {
        return Some((0, field.to_u128()?));
    }
    let high = meter.shift(&field, -128)?.to_u128()?;
    let low_mask = meter.integer(u128::MAX)?;
    let low = meter.bit_and(&field, &low_mask)?.to_u128()?;
    Some((high, low))
}

fn fraction_from_integer_owned(
    bits: &BigInt,
    width: u32,
    meter: &mut Meter<'_>,
) -> Option<(u128, u128)> {
    if bits.is_negative() || bits.bits() > u64::from(width) {
        return None;
    }
    bit_slice_wide_owned(bits, 0, width, meter)
}

/// `value * 2^shift` as an exact rational, refusing unbounded precision.
fn scale_by_pow2_owned(
    value: &BigRational,
    shift: i64,
    meter: &mut Meter<'_>,
) -> Option<BigRational> {
    if shift.unsigned_abs() > MAX_RATIONAL_BITS {
        return None;
    }
    let one = meter.integer(1)?;
    let power = meter.shift(&one, i64::try_from(shift.unsigned_abs()).ok()?)?;
    let power = meter.rational_from_integer(power)?;
    if shift >= 0 {
        meter.rational_binary(value, &power, Arithmetic::Multiply)
    } else {
        meter.rational_binary(value, &power, Arithmetic::Divide)
    }
}

fn rational_is_bounded(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

/// `floor(log2(a))` for a strictly positive rational.
fn floor_log2_owned(a: &BigRational, meter: &mut Meter<'_>) -> Option<i64> {
    if !a.is_positive() {
        return None;
    }
    let numer_bits = i64::try_from(a.numer().bits()).ok()?;
    let denom_bits = i64::try_from(a.denom().bits()).ok()?;
    // `2^(n-1) <= numer < 2^n` and likewise for the denominator, so the true
    // exponent is within one of this estimate; correct it by exact comparison.
    let mut exponent = numer_bits.checked_sub(denom_bits)?;
    for _ in 0..4 {
        let one = meter.integer(1)?;
        let one = meter.rational_from_integer(one)?;
        let lower = scale_by_pow2_owned(&one, exponent, meter)?;
        if meter.rational_compare(&lower, a)? == std::cmp::Ordering::Greater {
            exponent = exponent.checked_sub(1)?;
            continue;
        }
        let upper = scale_by_pow2_owned(&one, exponent.checked_add(1)?, meter)?;
        if meter.rational_compare(&upper, a)? != std::cmp::Ordering::Greater {
            exponent = exponent.checked_add(1)?;
            continue;
        }
        return Some(exponent);
    }
    None
}

/// Integer square root (floor) of a non-negative `BigInt`, by Newton descent.
fn isqrt_owned(value: &BigInt, meter: &mut Meter<'_>) -> Option<BigInt> {
    if value.is_negative() {
        return None;
    }
    if value.is_zero() {
        return meter.integer(0);
    }
    let bits = value.bits();
    let one = meter.integer(1)?;
    let mut guess = meter.shift(&one, i64::try_from(bits / 2 + 1).ok()?)?;
    loop {
        let quotient = meter.integer_binary(value, &guess, Arithmetic::Divide)?;
        let sum = meter.integer_binary(&guess, &quotient, Arithmetic::Add)?;
        let next = meter.shift(&sum, -1)?;
        if !meter.integer_compare(&next, &guess)?.is_lt() {
            break;
        }
        guess = next;
    }
    // Newton descent from an over-estimate converges to `floor(sqrt(value))`.
    let square = meter.integer_binary(&guess, &guess, Arithmetic::Multiply)?;
    if meter.integer_compare(&square, value)?.is_gt() {
        return None;
    }
    let above = meter.integer_binary(&guess, &one, Arithmetic::Add)?;
    let above_square = meter.integer_binary(&above, &above, Arithmetic::Multiply)?;
    if !meter.integer_compare(&above_square, value)?.is_gt() {
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
fn round_magnitude_owned(
    scaled: &BigRational,
    rm: Rm,
    sign: bool,
    meter: &mut Meter<'_>,
) -> Option<BigInt> {
    if scaled.is_negative() {
        return None;
    }
    meter.numeric(Meter::rational_bits(scaled)?)?;
    let floor_rational = scaled.floor();
    meter.numeric(Meter::rational_bits(&floor_rational)?)?;
    let floor = floor_rational.to_integer();
    let floor_copy = meter.integer_copy(&floor)?;
    let floor_value = meter.rational_from_integer(floor_copy)?;
    let fraction = meter.rational_binary(scaled, &floor_value, Arithmetic::Subtract)?;
    if fraction.is_zero() {
        return Some(floor);
    }
    let one = meter.integer(1)?;
    let two = meter.integer(2)?;
    let half = meter.rational(one, two)?;
    let one = meter.integer(1)?;
    let up = meter.integer_binary(&floor, &one, Arithmetic::Add)?;
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
            if meter.rational_compare(&fraction, &half)? != std::cmp::Ordering::Less {
                up
            } else {
                floor
            }
        }
        Rm::Rne => match meter.rational_compare(&fraction, &half)? {
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
fn encode_rounded_owned(
    mut integral: BigInt,
    mut ulp_exponent: i64,
    sign: bool,
    eb: u32,
    sb: u32,
    rm: Rm,
    meter: &mut Meter<'_>,
) -> Option<Fp> {
    meter.charge(1, 0)?;
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
    let one = meter.integer(1)?;
    let two_pow_sb = meter.shift(&one, i64::from(sb))?;
    let two_pow_sb_minus_1 = meter.shift(&one, i64::from(sb - 1))?;

    if !meter.integer_compare(&integral, &two_pow_sb)?.is_lt() {
        // A carry out of the significand: `integral` is exactly `2^sb`.
        if !meter.integer_compare(&integral, &two_pow_sb)?.is_eq() {
            return None;
        }
        integral = meter.integer_copy(&two_pow_sb_minus_1)?;
        ulp_exponent = ulp_exponent.checked_add(1)?;
    }

    if !meter
        .integer_compare(&integral, &two_pow_sb_minus_1)?
        .is_lt()
    {
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
        let stored = meter.integer_binary(&integral, &two_pow_sb_minus_1, Arithmetic::Subtract)?;
        let fraction = fraction_from_integer_owned(&stored, sb - 1, meter)?;
        return Fp::checked_wide(sign, biased, fraction, eb, sb);
    }

    // Subnormal: reachable only when the ulp exponent sits at the subnormal
    // floor. Anything else violates a kernel invariant, so fail closed.
    if ulp_exponent != emin - precision {
        return None;
    }
    let fraction = fraction_from_integer_owned(&integral, sb - 1, meter)?;
    Fp::checked_wide(sign, 0, fraction, eb, sb)
}

/// The exact rounding kernel: encode `±magnitude` into `(eb, sb)` under `rm`,
/// where `magnitude` is a strictly positive rational.
///
/// Follows IEEE 754-2008 §4.3: round at the target precision with an UNBOUNDED
/// exponent range (clamped only BELOW, at the subnormal ulp), then let
/// [`encode_rounded_owned`] apply the overflow rule.
fn round_positive_magnitude_owned(
    magnitude: &BigRational,
    sign: bool,
    eb: u32,
    sb: u32,
    rm: Rm,
    meter: &mut Meter<'_>,
) -> Option<Fp> {
    meter.charge(1, 0)?;
    if !magnitude.is_positive() || !rational_is_bounded(magnitude) {
        return None;
    }
    if !(2..=MAX_EB).contains(&eb) || !(2..=MAX_SB).contains(&sb) {
        return None;
    }
    let bias = i64::try_from((1u64 << (eb - 1)) - 1).ok()?;
    let emin = 1 - bias;
    let precision = i64::from(sb) - 1;

    let exponent = floor_log2_owned(magnitude, meter)?;
    let ulp_exponent = exponent.max(emin).checked_sub(precision)?;
    let scaled = scale_by_pow2_owned(magnitude, -ulp_exponent, meter)?;
    let integral = round_magnitude_owned(&scaled, rm, sign, meter)?;
    encode_rounded_owned(integral, ulp_exponent, sign, eb, sb, rm, meter)
}

/// Round an exact rational (possibly zero) into `(eb, sb)`.
///
/// `zero_sign` supplies the sign an EXACTLY zero result must carry; IEEE fixes
/// that per operation, so the caller decides rather than this kernel guessing.
fn round_rational_owned(
    value: &BigRational,
    zero_sign: bool,
    eb: u32,
    sb: u32,
    rm: Rm,
    meter: &mut Meter<'_>,
) -> Option<Fp> {
    meter.charge(1, 0)?;
    if !rational_is_bounded(value) {
        return None;
    }
    if value.is_zero() {
        return Fp::zero(zero_sign, eb, sb);
    }
    let sign = value.is_negative();
    let magnitude = meter.rational_copy(value)?;
    let magnitude = if sign { -magnitude } else { magnitude };
    round_positive_magnitude_owned(&magnitude, sign, eb, sb, rm, meter)
}

/// The sign an exactly-zero arithmetic result carries: `+0` in every rounding
/// mode except `roundTowardNegative`, which gives `-0` (IEEE 754 §6.3).
fn cancellation_zero_sign(rm: Rm) -> bool {
    matches!(rm, Rm::Rtn)
}

// ===========================================================================
// IEEE 754 operations
// ===========================================================================

fn fp_add_owned(rm: Rm, x: &Fp, y: &Fp, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
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
    let left = x.to_rational_owned(meter)?;
    let right = y.to_rational_owned(meter)?;
    let sum = meter.rational_binary(&left, &right, Arithmetic::Add)?;
    round_rational_owned(&sum, cancellation_zero_sign(rm), eb, sb, rm, meter)
}

fn fp_mul_owned(rm: Rm, x: &Fp, y: &Fp, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
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
    let left = x.to_rational_owned(meter)?;
    let right = y.to_rational_owned(meter)?;
    let product = meter.rational_binary(&left, &right, Arithmetic::Multiply)?;
    round_rational_owned(&product, sign, eb, sb, rm, meter)
}

fn fp_div_owned(rm: Rm, x: &Fp, y: &Fp, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
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
    let left = x.to_rational_owned(meter)?;
    let right = y.to_rational_owned(meter)?;
    let quotient = meter.rational_binary(&left, &right, Arithmetic::Divide)?;
    round_rational_owned(&quotient, sign, eb, sb, rm, meter)
}

fn fp_fma_owned(rm: Rm, x: &Fp, y: &Fp, z: &Fp, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
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
    let left = x.to_rational_owned(meter)?;
    let right = y.to_rational_owned(meter)?;
    let product = meter.rational_binary(&left, &right, Arithmetic::Multiply)?;
    let addend = z.to_rational_owned(meter)?;
    let total = meter.rational_binary(&product, &addend, Arithmetic::Add)?;
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
    round_rational_owned(&total, cancellation_zero_sign(rm), eb, sb, rm, meter)
}

/// Correctly-rounded square root, decided by EXACT integer comparisons — the
/// true square root is irrational in general, so it is never materialized.
fn fp_sqrt_owned(rm: Rm, x: &Fp, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
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
    let magnitude = x.to_rational_owned(meter)?;
    if !magnitude.is_positive() || !rational_is_bounded(&magnitude) {
        return None;
    }
    let bias = i64::try_from(1u64.checked_shl(eb.checked_sub(1)?)?.checked_sub(1)?).ok()?;
    let emin = 1i64.checked_sub(bias)?;
    let precision = i64::from(sb).checked_sub(1)?;

    // `floor(log2(sqrt(a)))`, corrected by exact comparison against powers of
    // two: `2^(2e) <= a < 2^(2e+2)`.
    let mut exponent = floor_log2_owned(&magnitude, meter)?.div_euclid(2);
    let mut settled = false;
    for _ in 0..4 {
        let one = meter.integer(1)?;
        let one = meter.rational_from_integer(one)?;
        let lower = scale_by_pow2_owned(&one, exponent.checked_mul(2)?, meter)?;
        if meter.rational_compare(&lower, &magnitude)? == std::cmp::Ordering::Greater {
            exponent = exponent.checked_sub(1)?;
            continue;
        }
        let upper = scale_by_pow2_owned(&one, exponent.checked_mul(2)?.checked_add(2)?, meter)?;
        if meter.rational_compare(&upper, &magnitude)? != std::cmp::Ordering::Greater {
            exponent = exponent.checked_add(1)?;
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
    let inner = scale_by_pow2_owned(&magnitude, -ulp_exponent.checked_mul(2)?, meter)?;
    if !inner.is_positive() || !rational_is_bounded(&inner) {
        return None;
    }
    let numerator = meter.integer_copy(inner.numer())?;
    let denominator = meter.integer_copy(inner.denom())?;
    // `floor(sqrt(p/q)) = floor(sqrt(p*q)/q)`.
    let product = meter.integer_binary(&numerator, &denominator, Arithmetic::Multiply)?;
    let root = isqrt_owned(&product, meter)?;
    let floor_root = meter.integer_binary(&root, &denominator, Arithmetic::Divide)?;
    let squared = meter.integer_binary(&floor_root, &floor_root, Arithmetic::Multiply)?;
    let floor_squared = meter.rational_from_integer(squared)?;

    let integral = if meter.rational_compare(&floor_squared, &inner)? == std::cmp::Ordering::Equal {
        // The square root is exact at this scale.
        floor_root
    } else {
        // Compare `sqrt(inner)` against `floor_root + 1/2` by squaring:
        // `inner` against `(2*floor_root + 1)^2 / 4`.
        let two = meter.integer(2)?;
        let one = meter.integer(1)?;
        let twice = meter.integer_binary(&floor_root, &two, Arithmetic::Multiply)?;
        let doubled = meter.integer_binary(&twice, &one, Arithmetic::Add)?;
        let numerator = meter.integer_binary(&doubled, &doubled, Arithmetic::Multiply)?;
        let four = meter.integer(4)?;
        let midpoint_squared = meter.rational(numerator, four)?;
        let against_midpoint = meter.rational_compare(&inner, &midpoint_squared)?;
        let up = meter.integer_binary(&floor_root, &one, Arithmetic::Add)?;
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
    encode_rounded_owned(integral, ulp_exponent, false, eb, sb, rm, meter)
}

/// `((_ to_fp eb sb) rm x)` where `x` is another FP value.
fn fp_convert_owned(rm: Rm, x: &Fp, eb: u32, sb: u32, meter: &mut Meter<'_>) -> Option<Fp> {
    meter.charge(1, 0)?;
    if x.is_nan() {
        return Fp::nan(eb, sb);
    }
    if x.is_infinite() {
        return Fp::infinity(x.sign, eb, sb);
    }
    if x.is_zero() {
        return Fp::zero(x.sign, eb, sb);
    }
    let value = x.to_rational_owned(meter)?;
    round_rational_owned(&value, x.sign, eb, sb, rm, meter)
}

// ===========================================================================
// Clause-level validation
// ===========================================================================

/// Validate a `TheoryLemmaKind::FpGroundEval` lemma in strict mode.
#[cfg(test)]
pub(crate) fn validate_fp_ground_eval(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_fp_ground_eval_with_progress(terms, step_id, clause, &mut |_, _| true)
}

pub(crate) fn validate_fp_ground_eval_with_progress(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut meter = Meter::new(progress);
    meter.charge(0, 0).ok_or(ProofCheckError::ResourceLimit)?;
    if clause.is_empty() {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step: step_id,
            reason: "fp_ground_eval clause must be non-empty".to_string(),
        });
    }
    for &literal in clause {
        meter.node().ok_or(ProofCheckError::ResourceLimit)?;
        if !matches!(terms.sort(literal), Sort::Bool) {
            return Err(ProofCheckError::InvalidTheoryLemma {
                step: step_id,
                reason:
                    "fp_ground_eval literal has non-Bool sort; lemma clauses must be propositional"
                        .to_owned(),
            });
        }
    }
    let valid = clause_is_exact_fp_tautology(terms, clause, &mut meter, ResidualDomain::Bounded);
    if meter.refused() {
        return Err(ProofCheckError::ResourceLimit);
    }
    if valid {
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
/// The EXACT precondition of `validate_fp_ground_eval`, plus the FP-content
/// hygiene gate, so the `ay-dpll` classifier can only assign this kind to
/// lemmas strict mode then accepts — no classifier/checker drift. All decision
/// logic lives in this module.
#[must_use]
pub fn recognize_fp_ground_eval(terms: &TermStore, clause: &[TermId]) -> bool {
    recognize_fp_ground_eval_with_progress(terms, clause, &mut |_, _| true)
}

/// Recognize with the caller's original work, storage and cancellation owner.
/// A refused debit is terminal; this grants no proof-installation authority.
#[must_use]
pub fn recognize_fp_ground_eval_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> bool {
    recognize_in_domain(terms, clause, progress, ResidualDomain::Bounded)
}

/// Recognize exact symbolic schemas and closed or completely ground-pinned
/// clauses without enumerating a residual variable domain. This advisory
/// producer entry borrows the original owner; independent proof replay retains
/// bounded enumeration. No successful observation grants installation authority.
#[must_use]
pub fn recognize_fp_ground_eval_without_enumeration_with_progress(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> bool {
    recognize_in_domain(terms, clause, progress, ResidualDomain::Absent)
}

#[derive(Clone, Copy)]
enum ResidualDomain {
    Bounded,
    Absent,
}

fn recognize_in_domain(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
    domain: ResidualDomain,
) -> bool {
    let mut meter = Meter::new(progress);
    if clause.is_empty() {
        return false;
    }
    for &literal in clause {
        if meter.node().is_none() || !matches!(terms.sort(literal), Sort::Bool) {
            return false;
        }
    }
    // Hygiene: a clause with no floating-point content is not an FP lemma even
    // if it happens to be a tautology, so the exported rule name stays honest.
    if mentions_floating_point(terms, clause, &mut meter) != Some(true) {
        return false;
    }
    clause_is_exact_fp_tautology(terms, clause, &mut meter, domain) && !meter.refused()
}

/// The hygiene gate of [`recognize_fp_ground_eval`], on its own.
///
/// Exported for the same reason as
/// [`crate::recognize_string_ground_eval`]'s gate. A completed walk is monotone
/// in the clause; exhaustion declines this gate rather than granting absence
/// of FP. The same local node bound applies to the uncontrolled recognizer.
pub fn clause_mentions_floating_point(terms: &TermStore, clause: &[TermId]) -> bool {
    let mut no_caller = |_, _| true;
    mentions_floating_point(terms, clause, &mut Meter::new(&mut no_caller)) == Some(true)
}

fn mentions_floating_point(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut Meter<'_>,
) -> Option<bool> {
    meter.entries::<TermId>(clause.len())?;
    let mut stack: Vec<TermId> = clause.to_vec();
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(term) = stack.pop() {
        meter.node()?;
        if seen.contains(&term) {
            continue;
        }
        meter.entries::<TermId>(1)?;
        if !seen.insert(term) {
            continue;
        }
        if matches!(terms.sort(term), Sort::FloatingPoint(_, _)) {
            return Some(true);
        }
        let children = meter.children(terms, term)?;
        meter.entries::<TermId>(children.len())?;
        stack.extend(children);
    }
    Some(false)
}

/// Whether `term`'s whole DAG is variable-free.
fn is_ground(terms: &TermStore, term: TermId, meter: &mut Meter<'_>) -> Option<bool> {
    meter.entries::<TermId>(1)?;
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::default();
    while let Some(current) = stack.pop() {
        meter.node()?;
        if seen.contains(&current) {
            continue;
        }
        meter.entries::<TermId>(1)?;
        if !seen.insert(current) {
            continue;
        }
        if matches!(terms.get(current), TermData::Var(_, _)) {
            return Some(false);
        }
        let children = meter.children(terms, current)?;
        meter.entries::<TermId>(children.len())?;
        stack.extend(children);
    }
    Some(true)
}

/// Collect the substitution the clause itself licenses.
///
/// A literal `(not (= v g))` with `v` a variable and `g` ground means: in any
/// valuation that FALSIFIES the clause, `v` and `g` denote the same value, so
/// replacing `v` by `g` everywhere preserves every literal's truth value. The
/// FIRST binding for a variable wins; a second one stays an ordinary literal —
/// which is exactly what makes `x = 1.0 ∧ x = 2.0` refutable here.
fn collect_bindings(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut Meter<'_>,
) -> Option<HashMap<TermId, TermId>> {
    let mut bindings: HashMap<TermId, TermId> = HashMap::default();
    for &literal in clause {
        meter.node()?;
        let TermData::Not(inner) = terms.get(literal) else {
            continue;
        };
        let TermData::App(symbol, args) = terms.get(*inner) else {
            continue;
        };
        if !matches!(symbol, Symbol::Named(name) if name == "=")
            || args.len() != 2
            || terms.is_declared_function(symbol.name())
        {
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
            if is_ground(terms, value, meter)? {
                meter.entries::<(TermId, TermId)>(1)?;
                bindings.insert(variable, value);
            }
        }
    }
    Some(bindings)
}

/// Collect the variables that survive the substitution, with their domain size
/// in bits. `None` when a surviving variable has no enumerable finite domain.
fn collect_residual_variables(
    terms: &TermStore,
    clause: &[TermId],
    bindings: &HashMap<TermId, TermId>,
    meter: &mut Meter<'_>,
) -> Option<Vec<(TermId, u32)>> {
    meter.entries::<TermId>(clause.len())?;
    let mut stack: Vec<TermId> = clause.to_vec();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut found: Vec<(TermId, u32)> = Vec::new();
    let mut total_bits = 0u32;
    while let Some(term) = stack.pop() {
        meter.node()?;
        if seen.contains(&term) {
            continue;
        }
        meter.entries::<TermId>(1)?;
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
            total_bits = total_bits.checked_add(bits)?;
            if total_bits > MAX_ENUMERATION_BITS {
                return None;
            }
            meter.entries::<(TermId, u32)>(1)?;
            found.push((term, bits));
            continue;
        }
        let children = meter.children(terms, term)?;
        meter.entries::<TermId>(children.len())?;
        stack.extend(children);
    }
    meter.charge(found.len().checked_mul(found.len())?, 0)?;
    found.sort_unstable();
    Some(found)
}

fn clause_is_exact_fp_tautology(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut Meter<'_>,
    domain: ResidualDomain,
) -> bool {
    let Some(commutative) = commutativity::clause_is_theorem(terms, clause, meter) else {
        return false;
    };
    if commutative {
        return true;
    }
    // Shared-operand `fp.eq` conflict — the one family the bounded enumerator
    // below cannot reach, because the shared operand is a full-width symbolic
    // variable. If two literals `(not (fp.eq t c1))` / `(not (fp.eq t c2))`
    // share the operand `t` and the GROUND constants are not `fp.eq`-equal
    // themselves, the clause is valid: falsifying it requires `t` to be
    // IEEE-equal to both, `fp.eq` demands non-NaN numeric equality on both
    // sides, and numeric equality is transitive — forcing `fp.eq c1 c2`,
    // contradiction. (A NaN constant makes its literal unconditionally true
    // and is covered by the same test, since `fp.eq` with NaN is false.)
    // Extra literals only weaken nothing: a clause containing a valid
    // sub-disjunction is valid.
    let Some(shared_conflict) = clause_has_shared_operand_fp_eq_conflict(terms, clause, meter)
    else {
        return false;
    };
    if shared_conflict {
        return true;
    }
    let Some(bindings) = collect_bindings(terms, clause, meter) else {
        return false;
    };
    let Some(variables) = collect_residual_variables(terms, clause, &bindings, meter) else {
        return false;
    };
    if matches!(domain, ResidualDomain::Absent) && !variables.is_empty() {
        return false;
    }
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
    let mut evaluator = Evaluator::new(terms, bindings, meter);
    if evaluator.precompute_varying(clause).is_none() {
        return false;
    }
    // `total_bits <= MAX_ENUMERATION_BITS`, so none of these shifts or sums
    // can fail; a failure would reject the lemma (fail closed).
    let Some(assignments) = 1u64.checked_shl(total_bits) else {
        return false;
    };
    for pattern in 0..assignments {
        if evaluator.meter.node().is_none() {
            return false;
        }
        let mut assignment: HashMap<TermId, Val> = HashMap::default();
        let mut offset: u32 = 0;
        for (variable, bits) in &variables {
            if evaluator.meter.entries::<(TermId, Val)>(1).is_none()
                || evaluator.meter.numeric(u64::from(*bits)).is_none()
            {
                return false;
            }
            let Some(mask) = 1u64.checked_shl(*bits).and_then(|bit| bit.checked_sub(1)) else {
                return false;
            };
            let Some(shifted) = pattern.checked_shr(offset) else {
                return false;
            };
            let slice = shifted & mask;
            let Some(value) = variable_value(terms, *variable, slice, evaluator.meter) else {
                return false;
            };
            assignment.insert(*variable, value);
            let Some(next_offset) = offset.checked_add(*bits) else {
                return false;
            };
            offset = next_offset;
        }
        // A falsifying assignment — or anything the evaluator cannot decide —
        // rejects the whole lemma.
        if evaluator.clause_holds(clause, &assignment) != Some(true) {
            return false;
        }
    }
    true
}

/// The shared-operand `fp.eq` conflict test backing the fast path in
/// [`clause_is_exact_fp_tautology`]. Ground constants are evaluated by the
/// same exact evaluator (empty assignment), so every constant form the
/// evaluator understands — `(fp ...)`, `(_ +zero eb sb)`, ground conversions —
/// participates; anything it cannot evaluate simply never pins the operand
/// (fail-closed).
fn clause_has_shared_operand_fp_eq_conflict(
    terms: &TermStore,
    clause: &[TermId],
    meter: &mut Meter<'_>,
) -> Option<bool> {
    let mut evaluator = Evaluator::new(terms, HashMap::default(), meter);
    let assignment: HashMap<TermId, Val> = HashMap::default();
    let mut local: HashMap<TermId, Option<Val>> = HashMap::default();
    let mut pinned: Vec<(TermId, Fp)> = Vec::new();
    for &literal in clause {
        evaluator.meter.node()?;
        let TermData::Not(inner) = terms.get(literal) else {
            continue;
        };
        let TermData::App(symbol, args) = terms.get(*inner) else {
            continue;
        };
        if !matches!(symbol, Symbol::Named(name) if name == "fp.eq")
            || args.len() != 2
            || terms.is_declared_function(symbol.name())
        {
            continue;
        }
        let Some(format) = fp_comparison_format(terms, *inner, args) else {
            continue;
        };
        for (operand, constant) in [(args[0], args[1]), (args[1], args[0])] {
            if let Some(Val::Fp(fp)) = evaluator.eval(constant, &assignment, &mut local, 0) {
                if (fp.eb, fp.sb) == format {
                    evaluator.meter.entries::<(TermId, Fp)>(1)?;
                    pinned.push((operand, fp));
                }
            }
        }
    }
    for (i, (operand_a, fp_a)) in pinned.iter().enumerate() {
        for (operand_b, fp_b) in pinned.iter().skip(i.saturating_add(1)) {
            evaluator.meter.node()?;
            if operand_a != operand_b || !fp_a.same_format(fp_b) {
                continue;
            }
            let ieee_equal = !fp_a.is_nan()
                && !fp_b.is_nan()
                && fp_a.cmp_real_owned(fp_b, evaluator.meter) == Some(std::cmp::Ordering::Equal);
            if !ieee_equal {
                return Some(true);
            }
        }
    }
    Some(false)
}

/// Builtin FP comparisons have a Bool result and one common operand format.
/// Validate the raw store signature too; evaluating a malformed application
/// must not grant it the builtin's semantics.
fn fp_comparison_format(terms: &TermStore, term: TermId, args: &[TermId]) -> Option<(u32, u32)> {
    if args.len() < 2 || terms.sort(term) != &Sort::Bool {
        return None;
    }
    let Sort::FloatingPoint(eb, sb) = terms.sort(args[0]) else {
        return None;
    };
    let format = (*eb, *sb);
    (fp_ground_format_supported(format.0, format.1)
        && args
            .iter()
            .all(|&arg| terms.sort(arg) == &Sort::FloatingPoint(format.0, format.1)))
    .then_some(format)
}

/// Build the value an enumerated variable takes for bit pattern `slice`.
fn variable_value(
    terms: &TermStore,
    variable: TermId,
    slice: u64,
    meter: &mut Meter<'_>,
) -> Option<Val> {
    match terms.sort(variable) {
        Sort::Bool => Some(Val::Bool(slice & 1 == 1)),
        Sort::BitVec(bv) => Some(Val::Bv(meter.integer(u128::from(slice))?, bv.width)),
        Sort::FloatingPoint(eb, sb) => {
            let bits = meter.integer(u128::from(slice))?;
            Some(Val::Fp(Fp::from_bits_owned(&bits, *eb, *sb, meter)?))
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
    fn as_bv(&self, meter: &mut Meter<'_>) -> Option<(BigInt, u32)> {
        match self {
            Self::Bv(value, width) => Some((meter.integer_copy(value)?, *width)),
            _ => None,
        }
    }
    /// Exact rational view of a numeric value.
    fn as_rational(&self, meter: &mut Meter<'_>) -> Option<BigRational> {
        match self {
            Self::Int(value) => {
                let integer = meter.integer_copy(value)?;
                meter.rational_from_integer(integer)
            }
            Self::Real(value) => meter.rational_copy(value),
            _ => None,
        }
    }
}

struct Evaluator<'a, 'm, 'p> {
    terms: &'a TermStore,
    bindings: HashMap<TermId, TermId>,
    meter: &'m mut Meter<'p>,
    /// Values of terms that do NOT depend on any enumerated variable; shared
    /// across assignments so ground arithmetic is evaluated exactly once.
    stable: HashMap<TermId, Option<Val>>,
    /// Terms whose DAG reaches an enumerated variable. A term missing from the
    /// precomputation is treated as varying, which is merely slower.
    varying: HashSet<TermId>,
}

impl<'a, 'm, 'p> Evaluator<'a, 'm, 'p> {
    fn new(
        terms: &'a TermStore,
        bindings: HashMap<TermId, TermId>,
        meter: &'m mut Meter<'p>,
    ) -> Self {
        Self {
            terms,
            bindings,
            meter,
            stable: HashMap::default(),
            varying: HashSet::default(),
        }
    }

    fn spend(&mut self) -> Option<()> {
        self.meter.node()
    }

    /// Mark every term whose DAG reaches an enumerated (unbound) variable, by
    /// an ITERATIVE post-order walk — an adversarial proof payload must not be
    /// able to recurse the checker off its stack.
    fn precompute_varying(&mut self, clause: &[TermId]) -> Option<()> {
        self.meter.entries::<(TermId, bool)>(clause.len())?;
        let mut stack: Vec<(TermId, bool)> = clause.iter().map(|&term| (term, false)).collect();
        let mut visited: HashSet<TermId> = HashSet::default();
        while let Some((term, expanded)) = stack.pop() {
            self.meter.node()?;
            if expanded {
                let children = self.meter.children(self.terms, term)?;
                let varies = match self.terms.get(term) {
                    TermData::Var(_, _) => !self.bindings.contains_key(&term),
                    _ => children.iter().any(|child| self.varying.contains(child)),
                };
                if varies {
                    self.meter.entries::<TermId>(1)?;
                    self.varying.insert(term);
                }
                continue;
            }
            if visited.contains(&term) {
                continue;
            }
            self.meter.entries::<TermId>(1)?;
            visited.insert(term);
            self.meter.entries::<(TermId, bool)>(1)?;
            stack.push((term, true));
            let children = self.meter.children(self.terms, term)?;
            self.meter.entries::<(TermId, bool)>(children.len())?;
            for child in children {
                stack.push((child, false));
            }
        }
        Some(())
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
        self.spend()?;
        if self.is_varying(term) {
            if let Some(cached) = local.get(&term) {
                self.meter.value_clone(cached.as_ref())?;
                return cached.clone();
            }
            let value = self.eval_uncached(term, assignment, local, depth);
            if self.meter.refused() {
                return None;
            }
            self.meter.entries::<(TermId, Option<Val>)>(1)?;
            self.meter.value_clone(value.as_ref())?;
            local.insert(term, value.clone());
            return value;
        }
        if let Some(cached) = self.stable.get(&term) {
            self.meter.value_clone(cached.as_ref())?;
            return cached.clone();
        }
        let value = self.eval_uncached(term, assignment, local, depth);
        if self.meter.refused() {
            return None;
        }
        self.meter.entries::<(TermId, Option<Val>)>(1)?;
        self.meter.value_clone(value.as_ref())?;
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
        let terms = self.terms;
        match terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(Val::Bool(*value)),
            TermData::Const(Constant::Int(value)) => {
                self.meter.literal_integer(value)?;
                Some(Val::Int(value.clone()))
            }
            TermData::Const(Constant::Rational(value)) => {
                self.meter.literal_rational(&value.0)?;
                Some(Val::Real(value.0.clone()))
            }
            TermData::Const(Constant::BitVec { value, width }) => {
                if *width == 0
                    || *width > MAX_BV_WIDTH
                    || value.is_negative()
                    || value.bits() > u64::from(*width)
                    || !matches!(terms.sort(term), Sort::BitVec(sort) if sort.width == *width)
                {
                    return None;
                }
                self.meter.literal_integer(value)?;
                Some(Val::Bv(value.clone(), *width))
            }
            TermData::Var(_, _) => {
                if let Some(value) = assignment.get(&term) {
                    self.meter.value_clone(Some(value))?;
                    return Some(value.clone());
                }
                let bound = *self.bindings.get(&term)?;
                self.eval(bound, assignment, local, depth.checked_add(1)?)
            }
            TermData::Not(inner) => {
                let inner = *inner;
                let next = depth.checked_add(1)?;
                Some(Val::Bool(
                    !self.eval(inner, assignment, local, next)?.as_bool()?,
                ))
            }
            TermData::Ite(condition, then_branch, else_branch) => {
                let (condition, then_branch, else_branch) =
                    (*condition, *then_branch, *else_branch);
                let next = depth.checked_add(1)?;
                if self.eval(condition, assignment, local, next)?.as_bool()? {
                    self.eval(then_branch, assignment, local, next)
                } else {
                    self.eval(else_branch, assignment, local, next)
                }
            }
            // Check the indexed shape before the generic application clone:
            // a malformed extract must not copy an unbounded argument list.
            TermData::App(Symbol::Indexed(name, indices), args) if name == "extract" => self
                .eval_indexed_extract(
                    term,
                    indices,
                    args,
                    assignment,
                    local,
                    depth.checked_add(1)?,
                ),
            TermData::App(symbol, args) => {
                // Borrow the immutable source application; never clone an
                // attacker-sized argument/name buffer before charging it.
                self.meter.inspect(args.len())?;
                self.eval_app(term, symbol, args, assignment, local, depth)
            }
            _ => None,
        }
    }

    /// SMT-LIB extraction: shift the canonical unsigned input, then mask to
    /// `high - low + 1` bits. Both integer operations are bounded by the
    /// existing BV-width limit; evaluation retains the same depth/work meter.
    fn eval_indexed_extract(
        &mut self,
        term: TermId,
        indices: &[u32],
        args: &[TermId],
        assignment: &HashMap<TermId, Val>,
        local: &mut HashMap<TermId, Option<Val>>,
        depth: usize,
    ) -> Option<Val> {
        let ([high, low], [arg]) = (indices, args) else {
            return None;
        };
        let Sort::BitVec(source) = self.terms.sort(*arg) else {
            return None;
        };
        let source_width = source.width;
        if source_width == 0 || source_width > MAX_BV_WIDTH || low > high || *high >= source_width {
            return None;
        }
        let result_width = high - low + 1;
        if !matches!(self.terms.sort(term), Sort::BitVec(sort) if sort.width == result_width) {
            return None;
        }
        let Val::Bv(value, width) = self.eval(*arg, assignment, local, depth)? else {
            return None;
        };
        if width != source_width || value.is_negative() || value.bits() > u64::from(width) {
            return None;
        }
        let one = self.meter.integer(1)?;
        let power = self.meter.shift(&one, i64::from(result_width))?;
        let mask = self
            .meter
            .integer_binary(&power, &one, Arithmetic::Subtract)?;
        let shifted = self.meter.shift(&value, -i64::from(*low))?;
        Some(Val::Bv(self.meter.bit_and(&shifted, &mask)?, result_width))
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
        // Declarations carry meaning independently of spelling. A registered
        // UF with a theory-looking name is not an interpreted FP/Bool/BV op.
        self.meter.inspect(symbol.name().len())?;
        if self.terms.is_declared_function(symbol.name()) {
            return None;
        }
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
            if matches!(literal.as_str(), "fp.to_sbv" | "fp.to_ubv") {
                let [width] = indices.as_slice() else {
                    return None;
                };
                if args.len() != 2
                    || !matches!(self.terms.sort(term), Sort::BitVec(sort) if sort.width == *width)
                {
                    return None;
                }
                let rm = self.eval(args[0], assignment, local, next)?.as_rm()?;
                let value = self.eval(args[1], assignment, local, next)?.as_fp()?;
                return Some(Val::Bv(
                    int_cast::fp_to_bv_owned(
                        &value,
                        rm,
                        *width,
                        if literal == "fp.to_sbv" {
                            int_cast::IntTarget::Signed
                        } else {
                            int_cast::IntTarget::Unsigned
                        },
                        self.meter,
                    )?,
                    *width,
                ));
            }

            // Extract is handled before cloning in `eval_uncached`. No other
            // indexed identifier has semantics in this evaluator. In
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
                self.meter.entries::<bool>(args.len())?;
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
                    if !values_equal(&first, &value, self.meter)? {
                        return Some(Val::Bool(false));
                    }
                }
                Some(Val::Bool(true))
            }
            ("distinct", _) if args.len() >= 2 => {
                self.meter.entries::<Val>(args.len())?;
                let mut values = Vec::with_capacity(args.len());
                for &arg in args {
                    values.push(self.eval(arg, assignment, local, next)?);
                }
                for left in 0..values.len() {
                    for right in (left + 1)..values.len() {
                        if values_equal(&values[left], &values[right], self.meter)? {
                            return Some(Val::Bool(false));
                        }
                    }
                }
                Some(Val::Bool(true))
            }

            // ---- FP construction `(fp sign exponent significand)` ----
            ("fp", 3) => {
                let (sign, sign_width) = self
                    .eval(args[0], assignment, local, next)?
                    .as_bv(self.meter)?;
                let (exponent, exponent_width) = self
                    .eval(args[1], assignment, local, next)?
                    .as_bv(self.meter)?;
                let (significand, significand_width) = self
                    .eval(args[2], assignment, local, next)?
                    .as_bv(self.meter)?;
                if sign_width != 1 {
                    return None;
                }
                let fraction =
                    fraction_from_integer_owned(&significand, significand_width, self.meter)?;
                Some(Val::Fp(Fp::checked_wide(
                    sign.to_u64()? == 1,
                    exponent.to_u64()?,
                    fraction,
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
                let format = fp_comparison_format(self.terms, term, args)?;
                let mut previous = self.eval(args[0], assignment, local, next)?.as_fp()?;
                if (previous.eb, previous.sb) != format {
                    return None;
                }
                for &arg in &args[1..] {
                    let current = self.eval(arg, assignment, local, next)?.as_fp()?;
                    if (current.eb, current.sb) != format {
                        return None;
                    }
                    // Any NaN operand makes every FP comparison false.
                    let Some(ordering) = previous.cmp_real_owned(&current, self.meter) else {
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
                    "fp.add" => fp_add_owned(rounding_mode, &left, &right, self.meter)?,
                    "fp.sub" => fp_add_owned(rounding_mode, &left, &right.negated(), self.meter)?,
                    "fp.mul" => fp_mul_owned(rounding_mode, &left, &right, self.meter)?,
                    _ => fp_div_owned(rounding_mode, &left, &right, self.meter)?,
                }))
            }
            ("fp.fma", 4) => {
                let rounding_mode = self.eval(args[0], assignment, local, next)?.as_rm()?;
                let x = self.eval(args[1], assignment, local, next)?.as_fp()?;
                let y = self.eval(args[2], assignment, local, next)?.as_fp()?;
                let z = self.eval(args[3], assignment, local, next)?.as_fp()?;
                Some(Val::Fp(fp_fma_owned(
                    rounding_mode,
                    &x,
                    &y,
                    &z,
                    self.meter,
                )?))
            }
            ("fp.sqrt", 2) => {
                let rounding_mode = self.eval(args[0], assignment, local, next)?.as_rm()?;
                let x = self.eval(args[1], assignment, local, next)?.as_fp()?;
                Some(Val::Fp(fp_sqrt_owned(rounding_mode, &x, self.meter)?))
            }
            ("fp.roundToIntegral", 2) => {
                if !matches!(self.terms.sort(args[0]), Sort::Uninterpreted(name) if name == "RoundingMode")
                    || !matches!(self.terms.sort(term), Sort::FloatingPoint(_, _))
                    || self.terms.sort(term) != self.terms.sort(args[1])
                {
                    return None;
                }
                let mode = self.eval(args[0], assignment, local, next)?.as_rm()?;
                let value = self.eval(args[1], assignment, local, next)?.as_fp()?;
                if self.terms.sort(term) != &Sort::FloatingPoint(value.eb, value.sb) {
                    return None;
                }
                Some(Val::Fp(integral::round_to_integral_owned(
                    mode, &value, self.meter,
                )?))
            }
            ("fp.rem", 2) => {
                if !matches!(self.terms.sort(term), Sort::FloatingPoint(_, _))
                    || self.terms.sort(term) != self.terms.sort(args[0])
                    || self.terms.sort(term) != self.terms.sort(args[1])
                {
                    return None;
                }
                let left = self.eval(args[0], assignment, local, next)?.as_fp()?;
                let right = self.eval(args[1], assignment, local, next)?.as_fp()?;
                if self.terms.sort(term) != &Sort::FloatingPoint(left.eb, left.sb) {
                    return None;
                }
                Some(Val::Fp(integral::remainder_owned(
                    &left, &right, self.meter,
                )?))
            }
            ("fp.to_real", 1) => {
                // NaN and the infinities have no real value: SMT-LIB leaves
                // `fp.to_real` unspecified there, so fail closed.
                let value = self.eval(args[0], assignment, local, next)?.as_fp()?;
                Some(Val::Real(value.to_rational_owned(self.meter)?))
            }

            // ---- exact numeric glue (Int / Real) ----
            ("+", _) if !args.is_empty() => {
                self.fold_numeric(args, assignment, local, next, Arithmetic::Add)
            }
            ("*", _) if !args.is_empty() => {
                self.fold_numeric(args, assignment, local, next, Arithmetic::Multiply)
            }
            ("-", 1) => {
                let value = self
                    .eval(args[0], assignment, local, next)?
                    .as_rational(self.meter)?;
                Some(if matches!(self.terms.sort(args[0]), Sort::Int) {
                    Val::Int(-self.meter.rational_to_integer(&value)?)
                } else {
                    Val::Real(-value)
                })
            }
            ("-", _) if args.len() >= 2 => {
                self.fold_numeric(args, assignment, local, next, Arithmetic::Subtract)
            }
            ("/", _) if args.len() >= 2 => {
                let mut accumulator = self
                    .eval(args[0], assignment, local, next)?
                    .as_rational(self.meter)?;
                for &arg in &args[1..] {
                    let value = self
                        .eval(arg, assignment, local, next)?
                        .as_rational(self.meter)?;
                    if value.is_zero() {
                        // `(/ x 0)` is under-specified in SMT-LIB.
                        return None;
                    }
                    accumulator =
                        self.meter
                            .rational_binary(&accumulator, &value, Arithmetic::Divide)?;
                    if !rational_is_bounded(&accumulator) {
                        return None;
                    }
                }
                Some(Val::Real(accumulator))
            }
            ("<" | "<=" | ">" | ">=", 2) => {
                let left = self
                    .eval(args[0], assignment, local, next)?
                    .as_rational(self.meter)?;
                let right = self
                    .eval(args[1], assignment, local, next)?
                    .as_rational(self.meter)?;
                let comparison = self.meter.rational_compare(&left, &right)?;
                Some(Val::Bool(match name {
                    "<" => comparison.is_lt(),
                    "<=" => !comparison.is_gt(),
                    ">" => comparison.is_gt(),
                    _ => !comparison.is_lt(),
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
        operation: Arithmetic,
    ) -> Option<Val> {
        let (&first, rest) = args.split_first()?;
        let mut accumulator = self
            .eval(first, assignment, local, depth)?
            .as_rational(self.meter)?;
        let mut integral = matches!(self.terms.sort(first), Sort::Int);
        for &arg in rest {
            let value = self
                .eval(arg, assignment, local, depth)?
                .as_rational(self.meter)?;
            integral &= matches!(self.terms.sort(arg), Sort::Int);
            accumulator = self
                .meter
                .rational_binary(&accumulator, &value, operation)?;
            if !rational_is_bounded(&accumulator) {
                return None;
            }
        }
        Some(if integral && accumulator.is_integer() {
            Val::Int(self.meter.rational_to_integer(&accumulator)?)
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
                let (bits, width) = self
                    .eval(args[0], assignment, local, depth)?
                    .as_bv(self.meter)?;
                if width != eb.checked_add(sb)? {
                    return None;
                }
                Some(Val::Fp(Fp::from_bits_owned(&bits, eb, sb, self.meter)?))
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
                        return Some(Val::Fp(fp_convert_owned(
                            rounding_mode,
                            inner,
                            eb,
                            sb,
                            self.meter,
                        )?));
                    }
                    Val::Bv(bits, width) => {
                        let integer = if signed {
                            signed_value_owned(bits, *width, self.meter)?
                        } else {
                            self.meter.integer_copy(bits)?
                        };
                        self.meter.rational_from_integer(integer)?
                    }
                    Val::Int(integer) => {
                        if !signed {
                            return None;
                        }
                        let value = self.meter.integer_copy(integer)?;
                        self.meter.rational_from_integer(value)?
                    }
                    Val::Real(real) => {
                        if !signed {
                            return None;
                        }
                        self.meter.rational_copy(real)?
                    }
                    Val::Bool(_) | Val::Rm(_) => return None,
                };
                // A zero source converts to `+0` under every rounding mode.
                Some(Val::Fp(round_rational_owned(
                    &value,
                    false,
                    eb,
                    sb,
                    rounding_mode,
                    self.meter,
                )?))
            }
            _ => None,
        }
    }
}

/// Two's-complement reading of a `width`-bit pattern.
fn signed_value_owned(bits: &BigInt, width: u32, meter: &mut Meter<'_>) -> Option<BigInt> {
    if width == 0 || width > MAX_BV_WIDTH || bits.is_negative() {
        return None;
    }
    let one = meter.integer(1)?;
    let modulus = meter.shift(&one, i64::from(width))?;
    if !meter.integer_compare(bits, &modulus)?.is_lt() {
        return None;
    }
    let half = meter.shift(&one, i64::from(width - 1))?;
    if !meter.integer_compare(bits, &half)?.is_lt() {
        meter.integer_binary(bits, &modulus, Arithmetic::Subtract)
    } else {
        meter.integer_copy(bits)
    }
}

/// SMT-LIB `=` on evaluated values: identity of the ABSTRACT value.
fn values_equal(left: &Val, right: &Val, meter: &mut Meter<'_>) -> Option<bool> {
    meter.node()?;
    Some(match (left, right) {
        (Val::Bool(a), Val::Bool(b)) => a == b,
        (Val::Fp(a), Val::Fp(b)) => a.structural_eq(b)?,
        (Val::Bv(a, left_width), Val::Bv(b, right_width)) => {
            if left_width != right_width {
                return None;
            }
            meter.integer_compare(a, b)?.is_eq()
        }
        (Val::Rm(a), Val::Rm(b)) => a == b,
        (Val::Int(a), Val::Int(b)) => meter.integer_compare(a, b)?.is_eq(),
        (Val::Real(a), Val::Real(b)) => meter.rational_compare(a, b)? == std::cmp::Ordering::Equal,
        (Val::Int(a), Val::Real(b)) | (Val::Real(b), Val::Int(a)) => {
            let integer = meter.integer_copy(a)?;
            let rational = meter.rational_from_integer(integer)?;
            meter.rational_compare(&rational, b)? == std::cmp::Ordering::Equal
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

#[cfg(test)]
#[path = "fp_ground_extract_tests.rs"]
mod fp_ground_extract_tests;

#[cfg(test)]
#[path = "fp_ground_int_cast_tests.rs"]
mod fp_ground_int_cast_tests;

#[cfg(test)]
#[path = "fp_ground/progress_tests.rs"]
mod progress_tests;
