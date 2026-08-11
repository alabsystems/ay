// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact SMT-LIB floating-point evaluation for the independent gate.
//!
//! # Why this exists
//!
//! `fp.to_real` used to be the gate's ONLY floating-point operator. Everything
//! else — `fp.eq`, `fp.lt`, `fp.isNaN`, the arithmetic, the `(fp s e m)`
//! literal, every rounding `to_fp` — either reached
//! [`crate::GateVerdict::CannotConfirm`] (a correct `sat` published as
//! `unknown`) or, worse, fell through to the uninterpreted-function path, which
//! ADOPTS the solver's own committed value for the application. That is the
//! right treatment for a genuinely uninterpreted symbol and the wrong one for an
//! interpreted predicate: it means the gate confirmed `(fp.eq a b)` because the
//! solver said so, without ever comparing `a` to `b`.
//!
//! Mutation testing is what exposed the second failure. Feeding the gate a
//! deliberately WRONG `to_fp` result — reading a signed bitvector as unsigned,
//! so `-1` became `4294967295` — changed no verdict, because the wrong value was
//! only ever handed to an adopted `fp.eq`.
//!
//! # Why implementing rounding here is still independent
//!
//! An earlier note in `eval.rs` declined the rounding forms of `to_fp` on the
//! grounds that "an independent gate must not confirm a model using the same
//! rounding routine that produced it, and an approximate reimplementation could
//! confirm a WRONG model". The first half is the real constraint and it is
//! honoured: nothing here calls into `ay-fp`, `ay-theories`, or any solver code.
//! The second half does not apply, because none of this is approximate.
//!
//! Every operation below is computed on EXACT `BigInt` / `BigRational`
//! arithmetic, derived from the IEEE-754 and SMT-LIB definitions:
//!
//!  * an FP datum is converted to its exact rational value from its stored
//!    fields (no host `f32`/`f64` ever appears in this file, or in the crate);
//!  * arithmetic is performed on those exact rationals, so the intermediate is
//!    the true unrounded result, and it is rounded ONCE — never double-rounded;
//!  * rounding to the target format is decided by comparing an exact rational
//!    against an exact half-way point, so ties are classified exactly rather
//!    than by an epsilon;
//!  * `fp.sqrt` — the one irrational result — is decided by exact INTEGER square
//!    roots and integer midpoint comparisons rather than materialised at all;
//!  * the comparison predicates never build a rational: within one format the
//!    encoding is monotonic in magnitude, so ordering is a field comparison.
//!
//! An exact reimplementation from the spec cannot confirm a wrong model: it
//! agrees with the correctly-rounded result by construction, and any case it
//! cannot compute exactly returns `Err` and keeps failing closed.
//!
//! The special cases are not decoration. NaN propagation, the infinities, and
//! above all the SIGN of a zero result are where a plausible-looking
//! implementation goes wrong: `BigRational` has no negative zero, so the sign of
//! an exactly-zero result cannot be recovered from the arithmetic and has to be
//! supplied by the rule IEEE gives for that operation.
//!
//! # Envelope
//!
//! [`ModelValue::FloatingPoint`] stores the exponent and significand fields in
//! `u64`, so formats wider than that are not representable and are DECLINED
//! here rather than truncated. `Float16`, `Float32` and `Float64` are all well
//! inside the envelope; `Float128` (`sb = 113`) is not representable by the
//! value type at all and declines. Separately, every `2^k` this module
//! materialises is bounded by [`MAX_SHIFT`], so a pathological format or a
//! pathological Real cannot turn a gate pass into an allocation storm. Crossing
//! that bound turns a possible confirmation into a refusal, never the reverse.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::ModelValue;

/// Largest exponent-field width handled. Fixed by `all_ones` and the exponent
/// bias having to stay inside `u64`/`i64`; every format SMT-LIB names in
/// practice is far inside it (`Float256` is `eb = 19`).
const EB_MAX: u32 = 63;

/// Largest significand precision handled, hidden bit included. Fixed by
/// [`ModelValue::FloatingPoint`] storing the stored fraction in a `u64`: at
/// `sb = 65` the field bound `1u64 << (sb - 1)` itself overflows, so the
/// envelope stops one short of that rather than computing a wrong bound.
const SB_MAX: u32 = 64;

/// Largest power of two this module will materialise, as an exponent.
///
/// A shift width is an allocation size. Clamping an out-of-range one (rather
/// than refusing) would turn a nonsense exponent into a multi-gigabyte integer,
/// and the whole point of the guard is that it is a RESOURCE bound: crossing it
/// yields `Err`, which the caller fails closed on. `2^MAX_SHIFT` is a 128 KiB
/// integer, and no in-envelope format needs a shift anywhere near it (the
/// widest, `eb = 20`, needs about `2^19`).
const MAX_SHIFT: i64 = 1 << 20;

/// Marker error for a result SMT-LIB deliberately leaves UNCONSTRAINED.
///
/// Distinct from every other `Err` here, which means "the gate cannot compute
/// this". These are cases where there is nothing to compute: the standard
/// permits more than one answer (`fp.min` of `+0` and `-0`, `fp.to_real` of a
/// NaN or an infinity, `fp.to_ieee_bv` of a NaN), so the operator behaves as an
/// UNINTERPRETED function on that input.
///
/// The caller re-routes them through the gate's uninterpreted-application
/// machinery, which adopts the model's committed value and enforces
/// single-valuedness across equal arguments. That is sound for exactly the
/// reason it is sound for a genuine UF: any value the standard ADMITS is a legal
/// interpretation, so adopting one cannot admit a model the standard forbids,
/// and every SPECIFIED part of the formula is still checked compositionally.
///
/// "Admits" is load-bearing. Underspecified is not unconstrained-in-sort: the
/// residue that IS fixed must still be enforced on whatever gets adopted, or the
/// branch launders a solver bug into a confirmed `sat`. See
/// [`check_ieee_nan_encoding`] and [`check_min_max_choice`].
pub const UNDERSPECIFIED: &str = "SMT-LIB leaves this result unconstrained";

/// SMT-LIB rounding mode.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RoundingMode {
    /// `roundNearestTiesToEven` (`RNE`).
    Rne,
    /// `roundNearestTiesToAway` (`RNA`).
    Rna,
    /// `roundTowardPositive` (`RTP`).
    Rtp,
    /// `roundTowardNegative` (`RTN`).
    Rtn,
    /// `roundTowardZero` (`RTZ`).
    Rtz,
}

impl RoundingMode {
    /// Both the short and long SMT-LIB spellings name the same mode.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "RNE" | "roundNearestTiesToEven" => Some(Self::Rne),
            "RNA" | "roundNearestTiesToAway" => Some(Self::Rna),
            "RTP" | "roundTowardPositive" => Some(Self::Rtp),
            "RTN" | "roundTowardNegative" => Some(Self::Rtn),
            "RTZ" | "roundTowardZero" => Some(Self::Rtz),
            _ => None,
        }
    }
}

/// The IEEE class of a floating-point value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FpClass {
    /// Not a number.
    NaN,
    /// Positive or negative infinity.
    Infinite,
    /// Positive or negative zero.
    Zero,
    /// A nonzero value below the smallest normal.
    Subnormal,
    /// An ordinary value with an implicit leading one.
    Normal,
}

/// The IEEE fields of one floating-point datum, plus its format — validated.
#[derive(Clone, Copy, Debug)]
pub struct Fp {
    /// Sign bit (`true` means negative).
    pub(crate) sign: bool,
    /// Biased exponent field.
    pub(crate) exponent: u64,
    /// Stored fraction, without the hidden bit.
    pub(crate) significand: u64,
    /// Exponent-field width.
    pub(crate) eb: u32,
    /// Significand precision including the hidden bit.
    pub(crate) sb: u32,
}

/// Historic name for [`Fp`], kept because the decoded fields read better as
/// `Fields` at the call sites that only inspect them.
pub type Fields = Fp;

/// An FP datum's value on the extended reals: the domain the arithmetic rules
/// below are stated over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Ext {
    /// Not a number. Unordered with everything, itself included.
    Nan,
    /// `+oo` when `false`, `-oo` when `true`.
    Inf(bool),
    /// A finite value. Both zeros map to `0`; the sign of a zero is recovered
    /// from [`Fp::sign`] where it matters (`fp.isNegative`, multiplication).
    Fin(BigRational),
}

/// `2^eb - 1`: the exponent field that encodes NaN and the infinities.
fn all_ones(eb: u32) -> u64 {
    (1u64 << eb) - 1
}

/// The exponent bias of a format, `2^(eb-1) - 1`.
fn bias_of(eb: u32) -> i64 {
    (1i64 << (eb - 1)) - 1
}

/// Whether `(eb, sb)` is a format this module can represent exactly.
///
/// Checked at every entry point that takes a format from the TERM (`to_fp`'s
/// indices) rather than from an already-validated datum: `Fp::nan(15, 113)`
/// would shift a `u64` by 111 places, so an unchecked format is a panic, not
/// merely a wrong answer.
fn check_format(eb: u32, sb: u32) -> Result<(), String> {
    if !(2..=EB_MAX).contains(&eb) || !(2..=SB_MAX).contains(&sb) {
        return Err("unsupported floating-point format".to_string());
    }
    Ok(())
}

/// `2^k` exactly, refusing rather than clamping an absurd `k`.
fn pow2(k: i64) -> Result<BigInt, String> {
    if !(0..=MAX_SHIFT).contains(&k) {
        return Err("floating-point scaling is out of the exact envelope".to_string());
    }
    let shift = usize::try_from(k).map_err(|_| "shift out of range".to_string())?;
    Ok(BigInt::one() << shift)
}

/// `a * 2^k`, exactly.
fn scale_pow2(a: &BigRational, k: i64) -> Result<BigRational, String> {
    if k >= 0 {
        Ok(a * BigRational::from_integer(pow2(k)?))
    } else {
        let down = k
            .checked_neg()
            .ok_or_else(|| "shift out of range".to_string())?;
        Ok(a / BigRational::from_integer(pow2(down)?))
    }
}

/// `floor(log2(a))` for `a > 0`, exactly.
///
/// The bit-length difference of numerator and denominator is within one of the
/// answer, so two guarded adjustments settle it. Comparisons are done by
/// cross-multiplication, never by converting to a float. The shifts are bounded
/// by the operand's own bit length, so this is proportional work rather than
/// amplification.
fn floor_log2(a: &BigRational) -> i64 {
    let n_bits = i64::try_from(a.numer().bits()).unwrap_or(i64::MAX);
    let d_bits = i64::try_from(a.denom().bits()).unwrap_or(i64::MAX);
    let mut e = n_bits - d_bits;
    while !pow2_le(e, a) {
        e -= 1;
    }
    while pow2_le(e + 1, a) {
        e += 1;
    }
    e
}

/// `2^e <= a`, for `a > 0`, by cross-multiplication.
fn pow2_le(e: i64, a: &BigRational) -> bool {
    if e >= 0 {
        let Ok(shift) = usize::try_from(e) else {
            return false;
        };
        (a.denom() << shift) <= *a.numer()
    } else {
        let Ok(shift) = usize::try_from(-e) else {
            return true;
        };
        *a.denom() <= (a.numer() << shift)
    }
}

impl Fp {
    /// Read the IEEE fields out of a gate value, validating the payload.
    ///
    /// Declines an out-of-envelope format or a field that does not fit its
    /// width — a malformed payload is not something to coerce.
    pub fn from_value(value: &ModelValue) -> Result<Self, String> {
        let &ModelValue::FloatingPoint {
            sign,
            exponent,
            significand,
            exponent_bits: eb,
            significand_bits: sb,
        } = value
        else {
            return Err("expected a floating-point value".to_string());
        };
        check_format(eb, sb)?;
        if exponent > all_ones(eb) || significand >= (1u64 << (sb - 1)) {
            return Err("malformed floating-point payload".to_string());
        }
        Ok(Self {
            sign,
            exponent,
            significand,
            eb,
            sb,
        })
    }

    /// Re-encode as a gate value.
    #[must_use]
    pub fn to_value(self) -> ModelValue {
        ModelValue::FloatingPoint {
            sign: self.sign,
            exponent: self.exponent,
            significand: self.significand,
            exponent_bits: self.eb,
            significand_bits: self.sb,
        }
    }

    /// Exponent-field width.
    #[must_use]
    pub fn exponent_bits(self) -> u32 {
        self.eb
    }

    /// Significand precision, hidden bit included.
    #[must_use]
    pub fn significand_bits(self) -> u32 {
        self.sb
    }

    pub(crate) fn is_nan(self) -> bool {
        self.exponent == all_ones(self.eb) && self.significand != 0
    }

    pub(crate) fn is_inf(self) -> bool {
        self.exponent == all_ones(self.eb) && self.significand == 0
    }

    pub(crate) fn is_zero(self) -> bool {
        self.exponent == 0 && self.significand == 0
    }

    fn is_subnormal(self) -> bool {
        self.exponent == 0 && self.significand != 0
    }

    fn is_normal(self) -> bool {
        self.exponent != 0 && self.exponent != all_ones(self.eb)
    }

    fn bias(self) -> i64 {
        bias_of(self.eb)
    }

    /// This value's IEEE class.
    #[must_use]
    pub fn class(self) -> FpClass {
        if self.exponent == all_ones(self.eb) {
            if self.significand == 0 {
                FpClass::Infinite
            } else {
                FpClass::NaN
            }
        } else if self.exponent == 0 {
            if self.significand == 0 {
                FpClass::Zero
            } else {
                FpClass::Subnormal
            }
        } else {
            FpClass::Normal
        }
    }

    /// The datum's exact value on the extended reals.
    fn ext(self) -> Result<Ext, String> {
        if self.is_nan() {
            return Ok(Ext::Nan);
        }
        if self.is_inf() {
            return Ok(Ext::Inf(self.sign));
        }
        let stored = self.sb - 1;
        let mut m = BigInt::from(self.significand);
        if self.exponent != 0 {
            m += BigInt::one() << stored as usize;
        }
        if m.is_zero() {
            return Ok(Ext::Fin(BigRational::from_integer(BigInt::zero())));
        }
        // Subnormals share the smallest normal's exponent; normals carry their
        // own. Both then drop the `sb - 1` fractional places of the significand.
        let biased = if self.exponent == 0 {
            1i64
        } else {
            i64::try_from(self.exponent).map_err(|_| "exponent out of range".to_string())?
        };
        let e = biased
            .checked_sub(self.bias())
            .and_then(|v| v.checked_sub(i64::from(stored)))
            .ok_or_else(|| "exponent out of range".to_string())?;
        let magnitude = scale_pow2(&BigRational::from_integer(m), e)?;
        Ok(Ext::Fin(if self.sign { -magnitude } else { magnitude }))
    }

    fn same_format(self, other: Self) -> bool {
        self.eb == other.eb && self.sb == other.sb
    }

    /// The exact rational value, or `None` for NaN, the infinities, and any
    /// datum whose exponent is outside the exact envelope.
    #[must_use]
    pub fn exact_value(self) -> Option<BigRational> {
        match self.ext() {
            Ok(Ext::Fin(x)) => Some(x),
            _ => None,
        }
    }

    fn zero(sign: bool, eb: u32, sb: u32) -> Self {
        Self {
            sign,
            exponent: 0,
            significand: 0,
            eb,
            sb,
        }
    }

    fn inf(sign: bool, eb: u32, sb: u32) -> Self {
        Self {
            sign,
            exponent: all_ones(eb),
            significand: 0,
            eb,
            sb,
        }
    }

    fn nan(eb: u32, sb: u32) -> Self {
        Self {
            sign: false,
            exponent: all_ones(eb),
            significand: 1u64 << (sb - 2),
            eb,
            sb,
        }
    }

    fn max_finite(sign: bool, eb: u32, sb: u32) -> Self {
        Self {
            sign,
            exponent: all_ones(eb) - 1,
            significand: (1u64 << (sb - 1)) - 1,
            eb,
            sb,
        }
    }
}

/// Read an FP model value, rejecting formats and payloads outside the
/// representation rather than reinterpreting them.
pub fn fields(value: &ModelValue) -> Result<Fp, String> {
    Fp::from_value(value)
}

// ===========================================================================
// rounding kernel
// ===========================================================================

/// Round a non-negative rational to an integer.
///
/// `negative` is the sign of the value the magnitude `q` came from, which is
/// what makes the two DIRECTED modes asymmetric: rounding toward `+oo` on a
/// negative value truncates its magnitude, and toward `-oo` extends it.
fn round_magnitude(q: &BigRational, negative: bool, rm: RoundingMode) -> BigInt {
    let floor = q.floor().to_integer();
    let frac = q - BigRational::from_integer(floor.clone());
    if frac.is_zero() {
        return floor;
    }
    let up = floor.clone() + BigInt::one();
    match rm {
        RoundingMode::Rtz => floor,
        RoundingMode::Rtp => {
            if negative {
                floor
            } else {
                up
            }
        }
        RoundingMode::Rtn => {
            if negative {
                up
            } else {
                floor
            }
        }
        RoundingMode::Rne | RoundingMode::Rna => {
            let half = BigRational::new(BigInt::one(), BigInt::from(2u8));
            match frac.cmp(&half) {
                core::cmp::Ordering::Less => floor,
                core::cmp::Ordering::Greater => up,
                core::cmp::Ordering::Equal => {
                    if rm == RoundingMode::Rna || (&floor % BigInt::from(2u8)) != BigInt::zero() {
                        up
                    } else {
                        floor
                    }
                }
            }
        }
    }
}

/// Round a rational to an integer under `rm`, honouring its sign.
///
/// This is the integer half of `fp.roundToIntegral`, `fp.to_ubv` / `fp.to_sbv`
/// and `fp.rem`: the same tie and direction rules as [`round_to_format`],
/// stopping at the integer rather than continuing into a format.
#[must_use]
pub fn round_to_integer(value: &BigRational, rm: RoundingMode) -> BigInt {
    let negative = value.is_negative();
    let magnitude = round_magnitude(&value.abs(), negative, rm);
    if negative {
        -magnitude
    } else {
        magnitude
    }
}

/// IEEE-754 §7.4: which value an overflowing magnitude rounds to.
fn overflow(negative: bool, eb: u32, sb: u32, rm: RoundingMode) -> Fp {
    let to_infinity = match rm {
        RoundingMode::Rne | RoundingMode::Rna => true,
        RoundingMode::Rtz => false,
        RoundingMode::Rtp => !negative,
        RoundingMode::Rtn => negative,
    };
    if to_infinity {
        Fp::inf(negative, eb, sb)
    } else {
        Fp::max_finite(negative, eb, sb)
    }
}

/// Correctly round an exact rational into the format `(eb, sb)`.
///
/// `zero_sign` decides the sign of a `±0` result, which the magnitude alone
/// cannot carry: SMT-LIB and IEEE fix it per operation (`x + (-x)` is `+0` in
/// every mode but `roundTowardNegative`, while `(-2) * 0` is `-0` in all of
/// them), so the caller supplies it. It applies only to an EXACTLY zero input;
/// a nonzero value that UNDERFLOWS keeps its own sign, which [`encode`] does.
pub fn round_to_format(
    x: &BigRational,
    eb: u32,
    sb: u32,
    rm: RoundingMode,
    zero_sign: bool,
) -> Result<Fp, String> {
    check_format(eb, sb)?;
    if x.is_zero() {
        return Ok(Fp::zero(zero_sign, eb, sb));
    }
    let negative = x.is_negative();
    let magnitude = x.abs();

    let bias = bias_of(eb);
    let emin = 1 - bias;
    let emax = bias;

    let e_exact = floor_log2(&magnitude);
    // A magnitude at or above `2^(emax+1)` exceeds every finite value of the
    // format and cannot round back into range. Deciding it here rather than
    // after scaling also keeps a wildly out-of-range Real from demanding a
    // multi-megabyte shift it would only throw away.
    if e_exact > emax {
        return Ok(overflow(negative, eb, sb, rm));
    }
    // Clamping to `emin` is what produces subnormals: below it the spacing
    // stops halving, so the significand is scaled at the fixed subnormal
    // exponent and simply loses leading precision.
    let e = e_exact.max(emin);
    let k = i64::from(sb - 1)
        .checked_sub(e)
        .ok_or_else(|| "exponent out of range".to_string())?;
    let scaled = scale_pow2(&magnitude, k)?;
    let m = round_magnitude(&scaled, negative, rm);
    encode(negative, e, m, eb, sb, rm)
}

/// Assemble the IEEE fields from a rounded significand `m` at exponent `e`,
/// handling the carry out of the significand, overflow, and the
/// normal/subnormal split.
///
/// Shared by every rounding entry point so the boundary behaviour is written
/// once: [`sqrt`] computes its `(e, m)` by integer arithmetic rather than by
/// scaling a rational, but the encoding rules are identical.
fn encode(
    negative: bool,
    mut e: i64,
    mut m: BigInt,
    eb: u32,
    sb: u32,
    rm: RoundingMode,
) -> Result<Fp, String> {
    let bias = bias_of(eb);
    let emax = bias;

    // Rounding up can carry out of the top of the significand, and only ever
    // to exactly `2^sb` — one more exponent, significand halved exactly.
    let two_sb = BigInt::one() << sb as usize;
    if m >= two_sb {
        e = e
            .checked_add(1)
            .ok_or_else(|| "exponent out of range".to_string())?;
        m >>= 1;
    }
    if e > emax {
        return Ok(overflow(negative, eb, sb, rm));
    }

    if m.is_zero() {
        // Underflowed all the way: the sign of an exact-zero result is the
        // sign of the value being rounded, not `zero_sign`.
        return Ok(Fp::zero(negative, eb, sb));
    }
    let hidden = BigInt::one() << (sb - 1) as usize;
    let (exponent, significand) = if m < hidden {
        // Subnormal: the exponent field is 0 and the hidden bit is absent.
        (BigInt::zero(), m)
    } else {
        let biased = e
            .checked_add(bias)
            .ok_or_else(|| "exponent out of range".to_string())?;
        (BigInt::from(biased), m - &hidden)
    };
    let exponent = u64::try_from(exponent).map_err(|_| "exponent out of range".to_string())?;
    let significand =
        u64::try_from(significand).map_err(|_| "significand out of range".to_string())?;
    // The assembled fields must sit inside the format. No input can violate
    // this, so no test can trigger it; it is here because the cost of being
    // wrong is a well-formed float holding a DIFFERENT number, which the gate
    // would happily confirm. A refusal is the recoverable failure.
    if exponent > all_ones(eb) || significand >= (1u64 << (sb - 1)) {
        return Err("rounded floating-point result is out of range".to_string());
    }
    Ok(Fp {
        sign: negative,
        exponent,
        significand,
        eb,
        sb,
    })
}

// ===========================================================================
// classification and comparison
// ===========================================================================

/// The seven SMT-LIB classification predicates. Exact field tests: no rounding
/// and no arithmetic is involved.
///
/// `Ok(None)` means `name` is not one of them, so the caller can keep
/// dispatching.
pub fn classify(name: &str, value: &ModelValue) -> Result<Option<bool>, String> {
    let known = matches!(
        name,
        "fp.isNaN"
            | "fp.isInfinite"
            | "fp.isZero"
            | "fp.isNormal"
            | "fp.isSubnormal"
            | "fp.isNegative"
            | "fp.isPositive"
    );
    if !known {
        return Ok(None);
    }
    let fp = Fp::from_value(value)?;
    Ok(Some(match name {
        "fp.isNaN" => fp.is_nan(),
        "fp.isInfinite" => fp.is_inf(),
        "fp.isZero" => fp.is_zero(),
        "fp.isNormal" => fp.is_normal(),
        "fp.isSubnormal" => fp.is_subnormal(),
        // NaN is neither negative nor positive, and the zeros keep their sign
        // here: `fp.isNegative(-0)` is true.
        "fp.isNegative" => fp.sign && !fp.is_nan(),
        _ => !fp.sign && !fp.is_nan(),
    }))
}

/// [`classify`], for a caller that has already decided `name` is a predicate.
pub fn predicate(name: &str, value: &ModelValue) -> Result<bool, String> {
    classify(name, value)?.ok_or_else(|| format!("unsupported floating-point predicate {name}"))
}

/// The IEEE ordering of two data in the SAME format.
///
/// Returns `Ok(None)` when the pair is UNORDERED — that is, when either is NaN.
/// `None` is not "not less than": every comparison involving NaN is false, and
/// collapsing that to a boolean at this level would make `fp.geq` the negation
/// of `fp.lt`, which IEEE says it is not.
///
/// Decided from the fields, with no rational ever built. Within one format and
/// one sign the encoding is monotonic in magnitude, so comparing
/// `(exponent, significand)` lexicographically orders subnormals, normals and
/// infinity in one step — exactly, and in any format the value type can hold.
/// The extended ordering over `Ext`: NaN is UNORDERED with everything
/// (including itself), and the infinities bound the finite values.
///
/// Kept as a named helper because both lineages' test suites unit-test this
/// relation directly — it is the fact that makes `fp.geq` not the negation of
/// `fp.lt`.
#[cfg(test)]
pub(crate) fn ext_cmp(a: &Ext, b: &Ext) -> Option<core::cmp::Ordering> {
    use core::cmp::Ordering;
    match (a, b) {
        (Ext::Nan, _) | (_, Ext::Nan) => None,
        (Ext::Inf(false), Ext::Inf(false)) | (Ext::Inf(true), Ext::Inf(true)) => {
            Some(Ordering::Equal)
        }
        (Ext::Inf(false), _) | (_, Ext::Inf(true)) => Some(Ordering::Greater),
        (Ext::Inf(true), _) | (_, Ext::Inf(false)) => Some(Ordering::Less),
        (Ext::Fin(x), Ext::Fin(y)) => Some(x.cmp(y)),
    }
}

pub fn compare_fields(a: &Fp, b: &Fp) -> Result<Option<core::cmp::Ordering>, String> {
    use core::cmp::Ordering;
    if a.eb != b.eb || a.sb != b.sb {
        return Err("comparing floating-point values of different formats".to_string());
    }
    if a.is_nan() || b.is_nan() {
        return Ok(None);
    }
    // The two zeros compare EQUAL under IEEE comparison even though their
    // encodings — and SMT-LIB's structural `=` — distinguish them.
    if a.is_zero() && b.is_zero() {
        return Ok(Some(Ordering::Equal));
    }
    if a.sign != b.sign {
        return Ok(Some(if a.sign {
            Ordering::Less
        } else {
            Ordering::Greater
        }));
    }
    let magnitude = (a.exponent, a.significand).cmp(&(b.exponent, b.significand));
    Ok(Some(if a.sign {
        magnitude.reverse()
    } else {
        magnitude
    }))
}

/// The five SMT-LIB comparison predicates, which are CHAINABLE: `(fp.lt a b c)`
/// abbreviates `(and (fp.lt a b) (fp.lt b c))`.
///
/// Every one is false as soon as a NaN participates — including `fp.eq` of NaN
/// with itself, and `fp.geq`, which is why this is not written as the negation
/// of the opposite test — and `fp.eq` identifies `+0` with `-0`, which is why
/// the comparison domain drops the zero sign while structural `=` keeps it.
///
/// Operands of DIFFERENT formats are ill-sorted and are refused rather than
/// compared by value: `(fp.eq <Float32> <Float64>)` is not a well-formed term,
/// and answering it would be answering a question that was never asked.
///
/// `Ok(None)` means `name` is not one of the five.
pub fn compare(name: &str, values: &[ModelValue]) -> Result<Option<bool>, String> {
    use core::cmp::Ordering;
    let accept: fn(Ordering) -> bool = match name {
        "fp.eq" => |o| o == Ordering::Equal,
        "fp.lt" => |o| o == Ordering::Less,
        "fp.leq" => |o| o != Ordering::Greater,
        "fp.gt" => |o| o == Ordering::Greater,
        "fp.geq" => |o| o != Ordering::Less,
        _ => return Ok(None),
    };
    if values.len() < 2 {
        return Err(format!("{name} expects at least two arguments"));
    }
    let operands = values
        .iter()
        .map(Fp::from_value)
        .collect::<Result<Vec<_>, _>>()?;
    for pair in operands.windows(2) {
        match compare_fields(&pair[0], &pair[1])? {
            None => return Ok(Some(false)),
            Some(order) if !accept(order) => return Ok(Some(false)),
            Some(_) => {}
        }
    }
    Ok(Some(true))
}

/// [`compare`], for a caller that has already decided `name` is a comparison.
pub fn comparison(name: &str, values: &[ModelValue]) -> Result<bool, String> {
    compare(name, values)?.ok_or_else(|| format!("unsupported floating-point comparison {name}"))
}

/// `fp.abs` / `fp.neg`: sign-bit rewrites, which IEEE defines on every value
/// including NaN, and which never round.
///
/// `Ok(None)` means `name` is neither.
pub fn unary_sign(name: &str, value: &ModelValue) -> Result<Option<ModelValue>, String> {
    let mut fp = Fp::from_value(value)?;
    match name {
        "fp.abs" => fp.sign = false,
        "fp.neg" => fp.sign = !fp.sign,
        _ => return Ok(None),
    }
    Ok(Some(fp.to_value()))
}

/// [`unary_sign`], for a caller that has already decided `name` is one of them.
pub fn sign_op(name: &str, value: &ModelValue) -> Result<ModelValue, String> {
    unary_sign(name, value)?.ok_or_else(|| format!("unsupported floating-point operator {name}"))
}

// ===========================================================================
// the `(fp s e m)` literal
// ===========================================================================

/// `(fp <sign-bv1> <exp-bv> <sig-bv>)`: assemble a datum from its three field
/// bitvectors. Pure bit placement, no rounding.
///
/// A literal is not something to take anyone's word for. This used to reach the
/// uninterpreted-function path, so the gate adopted the SOLVER's reading of the
/// three bitvectors instead of assembling them itself — the operand of nearly
/// every FP assertion, trusted rather than checked.
pub fn from_field_bitvectors(values: &[ModelValue]) -> Result<ModelValue, String> {
    let [s, e, m] = <&[ModelValue; 3]>::try_from(values)
        .map_err(|_| "fp expects three bitvector arguments".to_string())?;
    let bv = |v: &ModelValue| -> Result<(u32, u64), String> {
        let ModelValue::BitVec { width, value } = v else {
            return Err("fp expects bitvector arguments".to_string());
        };
        let value = u64::try_from(value).map_err(|_| "fp field too wide".to_string())?;
        Ok((*width, value))
    };
    let (sw, sv) = bv(s)?;
    let (eb, ev) = bv(e)?;
    let (mw, mv) = bv(m)?;
    if sw != 1 || sv > 1 {
        return Err("fp expects a 1-bit sign".to_string());
    }
    let sb = mw
        .checked_add(1)
        .ok_or_else(|| "unsupported floating-point format".to_string())?;
    check_format(eb, sb)?;
    // A field wider than its declared width is a malformed literal, not
    // something to mask down into a plausible value.
    if ev > all_ones(eb) || mv >= (1u64 << (sb - 1)) {
        return Err("malformed floating-point literal field".to_string());
    }
    Ok(Fp {
        sign: sv == 1,
        exponent: ev,
        significand: mv,
        eb,
        sb,
    }
    .to_value())
}

/// The `(fp s e m)` literal, under the name the operator has in SMT-LIB.
pub fn literal(values: &[ModelValue]) -> Result<ModelValue, String> {
    from_field_bitvectors(values)
}

// ===========================================================================
// arithmetic
// ===========================================================================

/// The exact result of a binary arithmetic operation, before rounding.
///
/// `Ok(Ok(exact))` means the operands are all finite and the caller should round
/// `exact`; `Ok(Err(special))` is a result the extended-real rules fix outright.
/// The special-value rules are decided here because they are stated on the
/// extended reals, not on the rounded result.
fn arith_exact(
    name: &str,
    a: Fp,
    b: Fp,
    eb: u32,
    sb: u32,
    rm: RoundingMode,
) -> Result<Result<BigRational, Fp>, String> {
    let (x, y) = (a.ext()?, b.ext()?);
    if x == Ext::Nan || y == Ext::Nan {
        return Ok(Err(Fp::nan(eb, sb)));
    }
    let sign_xor = a.sign ^ b.sign;
    match name {
        "fp.add" | "fp.sub" => {
            // `fp.sub a b` is `fp.add a (fp.neg b)`; the caller has already
            // flipped `b`'s sign for us, so both land here as an addition.
            // Defining subtraction that way rather than separately means there
            // is only one place to get the zero signs wrong.
            match (&x, &y) {
                // `(+oo) + (-oo)` is the one invalid sum.
                (Ext::Inf(p), Ext::Inf(q)) if p != q => Ok(Err(Fp::nan(eb, sb))),
                (Ext::Inf(p), _) => Ok(Err(Fp::inf(*p, eb, sb))),
                (_, Ext::Inf(q)) => Ok(Err(Fp::inf(*q, eb, sb))),
                (Ext::Fin(p), Ext::Fin(q)) => {
                    let sum = p + q;
                    if sum.is_zero() {
                        // IEEE-754 §6.3: a zero sum of like-signed zeros keeps
                        // that sign; every other exactly-zero sum is `+0`,
                        // except under `RTN` where it is `-0`.
                        let sign = if a.is_zero() && b.is_zero() && a.sign == b.sign {
                            a.sign
                        } else {
                            rm == RoundingMode::Rtn
                        };
                        return Ok(Err(Fp::zero(sign, eb, sb)));
                    }
                    Ok(Ok(sum))
                }
                (Ext::Nan, _) | (_, Ext::Nan) => unreachable!("NaN handled above"),
            }
        }
        "fp.mul" => match (&x, &y) {
            (Ext::Inf(_), Ext::Fin(q)) if q.is_zero() => Ok(Err(Fp::nan(eb, sb))),
            (Ext::Fin(p), Ext::Inf(_)) if p.is_zero() => Ok(Err(Fp::nan(eb, sb))),
            (Ext::Inf(_), _) | (_, Ext::Inf(_)) => Ok(Err(Fp::inf(sign_xor, eb, sb))),
            (Ext::Fin(p), Ext::Fin(q)) => {
                let product = p * q;
                if product.is_zero() {
                    return Ok(Err(Fp::zero(sign_xor, eb, sb)));
                }
                Ok(Ok(product))
            }
            (Ext::Nan, _) | (_, Ext::Nan) => unreachable!("NaN handled above"),
        },
        "fp.div" => match (&x, &y) {
            (Ext::Inf(_), Ext::Inf(_)) => Ok(Err(Fp::nan(eb, sb))),
            (Ext::Inf(_), Ext::Fin(_)) => Ok(Err(Fp::inf(sign_xor, eb, sb))),
            (Ext::Fin(_), Ext::Inf(_)) => Ok(Err(Fp::zero(sign_xor, eb, sb))),
            (Ext::Fin(p), Ext::Fin(q)) => {
                if q.is_zero() {
                    if p.is_zero() {
                        return Ok(Err(Fp::nan(eb, sb)));
                    }
                    return Ok(Err(Fp::inf(sign_xor, eb, sb)));
                }
                let quotient = p / q;
                if quotient.is_zero() {
                    return Ok(Err(Fp::zero(sign_xor, eb, sb)));
                }
                Ok(Ok(quotient))
            }
            (Ext::Nan, _) | (_, Ext::Nan) => unreachable!("NaN handled above"),
        },
        _ => Err(format!("unsupported floating-point operator {name}")),
    }
}

/// `fp.add` / `fp.sub` / `fp.mul` / `fp.div`, each computed on the EXACT
/// rational result and then correctly rounded once — never double-rounded.
///
/// `Ok(None)` means `name` is none of the four.
pub fn arith(
    name: &str,
    rm: RoundingMode,
    values: &[ModelValue],
) -> Result<Option<ModelValue>, String> {
    if !matches!(name, "fp.add" | "fp.sub" | "fp.mul" | "fp.div") {
        return Ok(None);
    }
    let [a, b] = <&[ModelValue; 2]>::try_from(values)
        .map_err(|_| format!("{name} expects two floating-point arguments"))?;
    let a = Fp::from_value(a)?;
    let mut b = Fp::from_value(b)?;
    if a.eb != b.eb || a.sb != b.sb {
        return Err(format!("{name} operands have different formats"));
    }
    let (eb, sb) = (a.eb, a.sb);
    if name == "fp.sub" {
        b.sign = !b.sign;
    }
    let zero_sign = match name {
        "fp.mul" | "fp.div" => a.sign ^ b.sign,
        _ => rm == RoundingMode::Rtn,
    };
    match arith_exact(name, a, b, eb, sb, rm)? {
        Err(special) => Ok(Some(special.to_value())),
        Ok(exact) => Ok(Some(
            round_to_format(&exact, eb, sb, rm, zero_sign)?.to_value(),
        )),
    }
}

/// `fp.fma a b c` — one rounding of the EXACT `a*b + c`, which is precisely what
/// distinguishes it from `fp.add (fp.mul a b) c`.
///
/// The single rounding is the whole point of the operation: rounding the product
/// first would give a different — and, for the gate, a wrongly confirmed —
/// answer.
pub fn fma(rm: RoundingMode, values: &[ModelValue]) -> Result<ModelValue, String> {
    let [a, b, c] = <&[ModelValue; 3]>::try_from(values)
        .map_err(|_| "fp.fma expects three floating-point arguments".to_string())?;
    let a = Fp::from_value(a)?;
    let b = Fp::from_value(b)?;
    let c = Fp::from_value(c)?;
    if a.eb != b.eb || a.sb != b.sb || a.eb != c.eb || a.sb != c.sb {
        return Err("fp.fma operands have different formats".to_string());
    }
    let (eb, sb) = (a.eb, a.sb);
    let (x, y, z) = (a.ext()?, b.ext()?, c.ext()?);
    if x == Ext::Nan || y == Ext::Nan || z == Ext::Nan {
        return Ok(Fp::nan(eb, sb).to_value());
    }
    let product_sign = a.sign ^ b.sign;
    let product = match (&x, &y) {
        (Ext::Inf(_), Ext::Fin(q)) if q.is_zero() => return Ok(Fp::nan(eb, sb).to_value()),
        (Ext::Fin(p), Ext::Inf(_)) if p.is_zero() => return Ok(Fp::nan(eb, sb).to_value()),
        (Ext::Inf(_), _) | (_, Ext::Inf(_)) => Ext::Inf(product_sign),
        (Ext::Fin(p), Ext::Fin(q)) => Ext::Fin(p * q),
        (Ext::Nan, _) | (_, Ext::Nan) => unreachable!("NaN handled above"),
    };
    match (&product, &z) {
        // An infinite product plus the opposite infinity is undefined.
        (Ext::Inf(p), Ext::Inf(q)) if p != q => Ok(Fp::nan(eb, sb).to_value()),
        (Ext::Inf(p), _) => Ok(Fp::inf(*p, eb, sb).to_value()),
        (_, Ext::Inf(q)) => Ok(Fp::inf(*q, eb, sb).to_value()),
        (Ext::Fin(p), Ext::Fin(q)) => {
            let sum = p + q;
            if sum.is_zero() {
                let sign = if p.is_zero() && q.is_zero() && product_sign == c.sign {
                    product_sign
                } else {
                    rm == RoundingMode::Rtn
                };
                return Ok(Fp::zero(sign, eb, sb).to_value());
            }
            Ok(round_to_format(&sum, eb, sb, rm, rm == RoundingMode::Rtn)?.to_value())
        }
        (Ext::Nan, _) | (_, Ext::Nan) => unreachable!("NaN handled above"),
    }
}

/// `fp.sqrt`: correctly rounded, computed by INTEGER square roots.
///
/// The result is irrational in general, so it cannot be materialised as a
/// rational and handed to [`round_to_format`]. It does not need to be: rounding
/// only ever asks where `sqrt(a)` sits relative to an integer and a half-way
/// point, and both questions become exact INTEGER comparisons once squared.
///
/// With `q = sqrt(a) * 2^(sb-1-e)` written as `sqrt(P)/D` in lowest terms:
///
///  * `floor(q) = isqrt(P) / D`, because `n*D` is an integer and
///    `(n*D)^2 <= P  ⟺  n*D <= isqrt(P)`;
///  * `q` is exactly `n` iff `P == (n*D)^2`;
///  * `q` compares against `n + 1/2` as `4P` against `((2n+1)*D)^2`.
///
/// `D` is 1 for every operand this can be called on (the scaling is chosen so
/// the radicand comes out integral), but it is carried through the midpoint
/// test anyway: an identity that happens to hold is not a reason to write a
/// formula that would be WRONG if it stopped holding.
///
/// Nothing here approximates: a tie is recognised by an exact integer equality,
/// so `RNE` breaks it correctly rather than on the wrong side of an epsilon.
pub fn sqrt(rm: RoundingMode, value: &ModelValue) -> Result<ModelValue, String> {
    let fp = Fp::from_value(value)?;
    let (eb, sb) = (fp.eb, fp.sb);
    let a = match fp.ext()? {
        Ext::Nan => return Ok(Fp::nan(eb, sb).to_value()),
        // `sqrt(-oo)` is NaN; `sqrt(+oo)` is `+oo`.
        Ext::Inf(true) => return Ok(Fp::nan(eb, sb).to_value()),
        Ext::Inf(false) => return Ok(Fp::inf(false, eb, sb).to_value()),
        Ext::Fin(x) => {
            if x.is_zero() {
                // IEEE-754 §6.3: `sqrt(-0)` is `-0`, sign preserved.
                return Ok(Fp::zero(fp.sign, eb, sb).to_value());
            }
            if x.is_negative() {
                return Ok(Fp::nan(eb, sb).to_value());
            }
            x
        }
    };

    let bias = bias_of(eb);
    let emin = 1 - bias;

    // `log2(sqrt(a)) = log2(a)/2`, so the floor is within one of the halved
    // bit-length; settle it exactly by squaring the candidate power of two.
    let log_a = floor_log2(&a);
    let mut e = log_a.div_euclid(2);
    while !pow2_le(2 * e, &a) {
        e -= 1;
    }
    while pow2_le(2 * (e + 1), &a) {
        e += 1;
    }
    e = e.max(emin);

    // `scaled = a * 2^(2k)`, whose square root is the `q` we must round.
    let k = i64::from(sb - 1)
        .checked_sub(e)
        .ok_or_else(|| "exponent out of range".to_string())?;
    let two_k = k
        .checked_mul(2)
        .ok_or_else(|| "exponent out of range".to_string())?;
    let scaled = scale_pow2(&a, two_k)?;
    let (numerator, denominator) = (scaled.numer().clone(), scaled.denom().clone());
    let product = &numerator * &denominator; // P, so that q = sqrt(P)/D
    let root = product.sqrt(); // floor(sqrt(P)), exact integer square root
    let n = &root / &denominator;

    let n_times_d = &n * &denominator;
    let m = if &n_times_d * &n_times_d == product {
        n // exact: no rounding to do
    } else {
        let up = &n + BigInt::one();
        let midpoint = ((&n << 1u32) + BigInt::one()) * &denominator; // (2n+1)*D
        match (&product << 2u32).cmp(&(&midpoint * &midpoint)) {
            core::cmp::Ordering::Less => match rm {
                RoundingMode::Rtp => up,
                _ => n,
            },
            core::cmp::Ordering::Greater => match rm {
                RoundingMode::Rtz | RoundingMode::Rtn => n,
                _ => up,
            },
            core::cmp::Ordering::Equal => match rm {
                RoundingMode::Rtz | RoundingMode::Rtn => n,
                RoundingMode::Rtp | RoundingMode::Rna => up,
                RoundingMode::Rne => {
                    if (&n % BigInt::from(2u8)).is_zero() {
                        n
                    } else {
                        up
                    }
                }
            },
        }
    };
    // `sqrt` of a finite positive value can never overflow the format, so the
    // shared encoder's overflow arm is unreachable here.
    Ok(encode(false, e, m, eb, sb, rm)?.to_value())
}

/// `fp.rem`: the IEEE-754 REMAINDER, which is EXACT and therefore takes no
/// rounding mode. It is not C's `fmod`.
///
/// `r = a - b * n` where `n` is `a/b` rounded to the nearest integer, ties to
/// even. `|r| <= |b|/2`, so the result is always representable in the operands'
/// format and the re-encoding below cannot change it.
///
/// That last sentence is a claim about IEEE, and it is CHECKED rather than
/// asserted: if the re-encoded value is not the exact remainder, the gate
/// refuses instead of confirming a number it cannot justify.
pub fn rem(values: &[ModelValue]) -> Result<ModelValue, String> {
    let [a, b] = <&[ModelValue; 2]>::try_from(values)
        .map_err(|_| "fp.rem expects two floating-point arguments".to_string())?;
    let a = Fp::from_value(a)?;
    let b = Fp::from_value(b)?;
    if a.eb != b.eb || a.sb != b.sb {
        return Err("fp.rem operands have different formats".to_string());
    }
    let (eb, sb) = (a.eb, a.sb);
    let (x, y) = (a.ext()?, b.ext()?);
    match (&x, &y) {
        (Ext::Nan, _) | (_, Ext::Nan) => Ok(Fp::nan(eb, sb).to_value()),
        // An infinite dividend, or a zero divisor, is invalid.
        (Ext::Inf(_), _) => Ok(Fp::nan(eb, sb).to_value()),
        (Ext::Fin(_), Ext::Fin(q)) if q.is_zero() => Ok(Fp::nan(eb, sb).to_value()),
        // A finite dividend by an infinite divisor is the dividend itself.
        (Ext::Fin(_), Ext::Inf(_)) => Ok(a.to_value()),
        (Ext::Fin(p), Ext::Fin(q)) => {
            let n = round_to_integer(&(p / q), RoundingMode::Rne);
            let remainder = p - q * BigRational::from_integer(n);
            if remainder.is_zero() {
                // A zero remainder carries the sign of the DIVIDEND.
                return Ok(Fp::zero(a.sign, eb, sb).to_value());
            }
            let rounded = round_to_format(&remainder, eb, sb, RoundingMode::Rne, a.sign)?;
            if rounded.ext()? != Ext::Fin(remainder) {
                return Err("floating-point remainder is not exactly representable".to_string());
            }
            Ok(rounded.to_value())
        }
    }
}

/// `fp.roundToIntegral`: exact, and never overflows — an integral value of the
/// format is always representable in it.
pub fn round_to_integral(rm: RoundingMode, value: &ModelValue) -> Result<ModelValue, String> {
    let fp = Fp::from_value(value)?;
    match fp.ext()? {
        // NaN and the infinities come back UNCHANGED rather than canonicalised:
        // IEEE `roundToIntegral` preserves the operand, and there is nothing to
        // gain from rewriting a payload the standard leaves alone.
        Ext::Nan | Ext::Inf(_) => Ok(fp.to_value()),
        Ext::Fin(x) => {
            if x.is_zero() {
                // `roundToIntegral` preserves the sign of a zero operand.
                return Ok(fp.to_value());
            }
            let negative = x.is_negative();
            let rounded = round_magnitude(&x.abs(), negative, rm);
            if rounded.is_zero() {
                // A value that rounds to zero keeps ITS sign:
                // `roundToIntegral(RTZ, -0.5)` is `-0`, not `+0`.
                return Ok(Fp::zero(negative, fp.eb, fp.sb).to_value());
            }
            let mut exact = BigRational::from_integer(rounded);
            if negative {
                exact = -exact;
            }
            Ok(round_to_format(&exact, fp.eb, fp.sb, rm, negative)?.to_value())
        }
    }
}

/// `fp.min` / `fp.max`.
///
/// SMT-LIB leaves the result UNDER-SPECIFIED when the arguments are `+0` and
/// `-0` (either may be returned), so that case reports [`UNDERSPECIFIED`]
/// rather than picking one — a guess there could confirm a model the solver
/// disagrees with. The caller adopts the model's own choice and validates it
/// with [`check_min_max_choice`].
///
/// `Ok(None)` means `name` is neither operator.
pub fn min_max(name: &str, values: &[ModelValue]) -> Result<Option<ModelValue>, String> {
    let want_min = match name {
        "fp.min" => true,
        "fp.max" => false,
        _ => return Ok(None),
    };
    let [a, b] = <&[ModelValue; 2]>::try_from(values)
        .map_err(|_| format!("{name} expects two floating-point arguments"))?;
    let a = Fp::from_value(a)?;
    let b = Fp::from_value(b)?;
    if a.eb != b.eb || a.sb != b.sb {
        return Err(format!("{name} operands have different formats"));
    }
    // A number beats a NaN; two NaNs give a NaN.
    if a.is_nan() {
        return Ok(Some(b.to_value()));
    }
    if b.is_nan() {
        return Ok(Some(a.to_value()));
    }
    if a.is_zero() && b.is_zero() && a.sign != b.sign {
        // Either zero is a legal answer, so this is a CHOICE, not a
        // computation — see [`UNDERSPECIFIED`].
        return Err(UNDERSPECIFIED.to_string());
    }
    let order = compare_fields(&a, &b)?.ok_or_else(|| "unordered operands".to_string())?;
    let pick_a = if want_min {
        order != core::cmp::Ordering::Greater
    } else {
        order != core::cmp::Ordering::Less
    };
    Ok(Some(if pick_a { a.to_value() } else { b.to_value() }))
}

/// Dispatch an FP operation that takes a ROUNDING MODE.
pub fn rounded_op(name: &str, rm: RoundingMode, args: &[ModelValue]) -> Result<ModelValue, String> {
    match name {
        "fp.add" | "fp.sub" | "fp.mul" | "fp.div" => arith(name, rm, args)?
            .ok_or_else(|| format!("unsupported floating-point operator {name}")),
        "fp.fma" => fma(rm, args),
        "fp.sqrt" | "fp.roundToIntegral" => {
            let [x] = <&[ModelValue; 1]>::try_from(args)
                .map_err(|_| format!("{name} expects one floating-point argument"))?;
            if name == "fp.sqrt" {
                sqrt(rm, x)
            } else {
                round_to_integral(rm, x)
            }
        }
        _ => Err(format!("unsupported floating-point operator {name}")),
    }
}

/// Dispatch an FP operation that takes NO rounding mode.
pub fn unrounded_op(name: &str, args: &[ModelValue]) -> Result<ModelValue, String> {
    match name {
        "fp.rem" => rem(args),
        "fp.min" | "fp.max" => min_max(name, args)?
            .ok_or_else(|| format!("unsupported floating-point operator {name}")),
        _ => Err(format!("unsupported floating-point operator {name}")),
    }
}

// ===========================================================================
// conversions
// ===========================================================================

/// `((_ to_fp eb sb) rm x)` and `((_ to_fp_unsigned eb sb) rm bv)`.
///
/// `x` may be a Real, an Int, a signed bitvector, or another floating-point
/// value; each has an exact rational value, so all four reduce to one correctly
/// rounded conversion. `to_fp` of a bitvector reads it as TWO'S COMPLEMENT and
/// `to_fp_unsigned` reads the same bits as unsigned — that difference is the
/// whole distinction between the two operators, and reading a signed bitvector
/// unsigned is exactly the mutation that first showed the gate was not checking
/// its FP operands at all.
///
/// `to_fp_unsigned` is defined ONLY on bitvectors, so a Real/Int/FP operand
/// under that name is refused rather than quietly treated as `to_fp`.
pub fn to_fp_rounded(
    unsigned: bool,
    eb: u32,
    sb: u32,
    rm: RoundingMode,
    value: &ModelValue,
) -> Result<ModelValue, String> {
    // Checked BEFORE the special-value shortcuts below, which construct data in
    // the TARGET format directly: an unvalidated `sb` there would shift a `u64`
    // out of range rather than decline.
    check_format(eb, sb)?;
    let exact: BigRational = match value {
        ModelValue::BitVec { width, value } => {
            if *width == 0 {
                return Err("to_fp expects a non-empty bitvector".to_string());
            }
            let modulus = BigInt::one() << *width as usize;
            // A payload outside its own width is malformed input, not something
            // to reduce modulo the width and then round.
            if value.is_negative() || *value >= modulus {
                return Err("bitvector value outside its width".to_string());
            }
            let mut n = value.clone();
            if !unsigned && n >= (BigInt::one() << (*width - 1) as usize) {
                // Two's complement: the top bit carries `-2^(width-1)`.
                n -= modulus;
            }
            BigRational::from_integer(n)
        }
        // `to_fp_unsigned` is defined only on bitvectors; every other form is
        // `to_fp`.
        _ if unsigned => {
            return Err("to_fp_unsigned expects a bitvector".to_string());
        }
        ModelValue::Real(r) => r.clone(),
        ModelValue::Int(n) => BigRational::from_integer(n.clone()),
        ModelValue::FloatingPoint { .. } => {
            // A format conversion. NaN, the infinities and the zeros have no
            // rational value to round, and each carries information (the zero's
            // sign) that a trip through `BigRational` would lose.
            let fp = Fp::from_value(value)?;
            match fp.ext()? {
                Ext::Nan => {
                    return Ok(Fp {
                        sign: fp.sign,
                        ..Fp::nan(eb, sb)
                    }
                    .to_value())
                }
                Ext::Inf(sign) => return Ok(Fp::inf(sign, eb, sb).to_value()),
                Ext::Fin(x) => {
                    if x.is_zero() {
                        // A zero converts to a zero of the SAME sign.
                        return Ok(Fp::zero(fp.sign, eb, sb).to_value());
                    }
                    x
                }
            }
        }
        _ => return Err("to_fp expects a numeric or floating-point argument".to_string()),
    };
    // A zero source is a `+0` result for the numeric sources (SMT-LIB reals,
    // ints and bitvectors have no signed zero); the FP source returned above.
    Ok(round_to_format(&exact, eb, sb, rm, false)?.to_value())
}

/// `((_ fp.to_sbv m) rm x)` / `((_ fp.to_ubv m) rm x)`.
///
/// SMT-LIB leaves the result UNSPECIFIED when `x` is NaN, infinite, or rounds
/// outside the target width, so those decline rather than wrap — wrapping would
/// let the gate confirm a value the solver never claimed. Declining is the
/// conservative reading: it costs completeness only.
pub fn to_bv(
    unsigned: bool,
    width: u32,
    rm: RoundingMode,
    value: &ModelValue,
) -> Result<ModelValue, String> {
    if width == 0 || width > 1024 {
        return Err("unsupported bitvector width".to_string());
    }
    let fp = Fp::from_value(value)?;
    let Ext::Fin(x) = fp.ext()? else {
        return Err("fp.to_sbv/to_ubv is unspecified for NaN and infinity".to_string());
    };
    let n = round_to_integer(&x, rm);
    let (low, high) = if unsigned {
        (BigInt::zero(), (BigInt::one() << width as usize) - 1)
    } else {
        let half = BigInt::one() << (width - 1) as usize;
        (-half.clone(), half - 1)
    };
    if n < low || n > high {
        return Err("fp.to_sbv/to_ubv result is out of range (unspecified)".to_string());
    }
    let encoded = if n.is_negative() {
        n + (BigInt::one() << width as usize)
    } else {
        n
    };
    Ok(ModelValue::bitvec(encoded, width))
}

/// [`to_bv`], selected by the SMT-LIB operator name.
pub fn to_bv_named(
    name: &str,
    rm: RoundingMode,
    width: u32,
    value: &ModelValue,
) -> Result<ModelValue, String> {
    let unsigned = match name {
        "fp.to_ubv" => true,
        "fp.to_sbv" => false,
        _ => return Err(format!("unsupported floating-point operator {name}")),
    };
    to_bv(unsigned, width, rm, value)
}

// ===========================================================================
// identity, encoding, and the underspecified residues
// ===========================================================================

/// SMT-LIB `=` on two floating-point data: identity of the DENOTED ELEMENT.
///
/// Raw-field identity everywhere EXCEPT NaN. A `(_ FloatingPoint eb sb)` sort
/// has exactly ONE NaN element while IEEE has many NaN bit-patterns for it, so
/// two different NaN encodings of one format are the same value — z3 agrees
/// (`(= (fp #b0 #b11111111 #b0…01) (fp #b1 #b11111111 #b1…1))` is `sat`).
///
/// Comparing the raw fields instead made the gate report `(= x ((_ to_fp 8 24)
/// #xffc00000))` as FALSE under a model that prints `x = (_ NaN 8 24)` — a
/// correct `sat` downgraded to `unknown`, with the invalid-model banner fired
/// at a perfectly good model. It cuts the other way too: `(not (= x <some other
/// NaN spelling>))` is unsatisfiable, and raw-field comparison would have let
/// the gate CONFIRM it.
///
/// Everything else stays exact identity. `+0`/`-0` and `+oo`/`-oo` are DISTINCT
/// elements under `=` even though `fp.eq` equates the zeros; that IEEE ordering
/// lives in [`compare`], not here. Values of different formats are different
/// sorts and never equal.
#[must_use]
pub fn same_element(a: &ModelValue, b: &ModelValue) -> bool {
    let (
        ModelValue::FloatingPoint {
            sign: sign_a,
            exponent: exponent_a,
            significand: significand_a,
            exponent_bits: eb_a,
            significand_bits: sb_a,
        },
        ModelValue::FloatingPoint {
            sign: sign_b,
            exponent: exponent_b,
            significand: significand_b,
            exponent_bits: eb_b,
            significand_bits: sb_b,
        },
    ) = (a, b)
    else {
        return false;
    };
    if (eb_a, sb_a) != (eb_b, sb_b) {
        return false;
    }
    // Max exponent with a non-zero stored significand. The width guard keeps
    // `all_ones` in range for any payload the value type can hold; an
    // out-of-range width falls through to exact field identity, which is what
    // this comparison did for every value before NaN was distinguished.
    let is_nan = |exponent: &u64, significand: &u64| {
        (1..64).contains(eb_a) && *exponent == all_ones(*eb_a) && *significand != 0
    };
    if is_nan(exponent_a, significand_a) && is_nan(exponent_b, significand_b) {
        return true;
    }
    (sign_a, exponent_a, significand_a) == (sign_b, exponent_b, significand_b)
}

/// `(fp.to_ieee_bv x)` — the IEEE-754 interchange encoding of `x`.
///
/// Pure re-reading of the datum's own stored fields: no rounding, no value
/// change, no host float. It is the exact inverse of `((_ to_fp eb sb) <bv>)`,
/// which the gate already computes the same way (`fp_from_ieee_bits`), so it is
/// as independent of the solver as that direction is.
///
/// NaN is the one input SMT-LIB does not determine, and it is genuinely
/// UNDERSPECIFIED rather than merely hard: a `(_ FloatingPoint eb sb)` sort has
/// exactly ONE NaN element while IEEE has many NaN bit-patterns for it. Handing
/// back the operand's own raw bits there would be WRONG, not just arbitrary —
/// `fp.neg` flips the raw sign bit of a NaN (IEEE 754-2008 §5.5.1) although
/// `(= (fp.neg NaN) NaN)` holds, so the raw bits are not a function of the
/// denoted element and would let the gate report two values for one function at
/// one argument. That case reports [`UNDERSPECIFIED`], and the caller resolves
/// it from the model's own committed encoding — checked by
/// [`check_ieee_nan_encoding`] before it is believed.
pub fn to_ieee_bv(value: &ModelValue) -> Result<ModelValue, String> {
    let fp = Fp::from_value(value)?;
    if fp.is_nan() {
        return Err(UNDERSPECIFIED.to_string());
    }
    let stored = (fp.sb - 1) as usize;
    let mut bits = BigInt::from(fp.significand) | (BigInt::from(fp.exponent) << stored);
    if fp.sign {
        bits |= BigInt::one() << (fp.eb as usize + stored);
    }
    Ok(ModelValue::bitvec(bits, fp.eb + fp.sb))
}

/// Whether `fp.to_ieee_bv` of this value is the unspecified case.
///
/// A caller that routes the underspecified branch itself, rather than matching
/// on [`UNDERSPECIFIED`], asks this first.
#[must_use]
pub fn to_ieee_bv_unspecified(value: &ModelValue) -> bool {
    Fp::from_value(value).is_ok_and(Fp::is_nan)
}

/// Whether `encoding` is an admissible `(fp.to_ieee_bv x)` result for a NaN `x`
/// of `operand`'s format.
///
/// The pattern is free in the sign bit and in the payload, but it must still BE
/// a NaN encoding — exponent all ones, stored significand non-zero — because
/// reinterpreting the result back with `((_ to_fp eb sb) <bv>)` has to recover
/// NaN. `#x00000000` is not an unspecified answer for Float32, it is a wrong one
/// (z3 refutes it too), so anything outside the admissible set is rejected and
/// the gate keeps failing closed instead of confirming it. This is what keeps
/// the underspecified branch from laundering a solver or evaluator bug into a
/// confirmed `sat`.
pub fn check_ieee_nan_encoding(operand: &ModelValue, encoding: &ModelValue) -> Result<(), String> {
    let fp = Fp::from_value(operand)?;
    if !fp.is_nan() {
        return Err("fp.to_ieee_bv is not underspecified on this operand".to_string());
    }
    let ModelValue::BitVec { width, value } = encoding else {
        return Err("fp.to_ieee_bv must denote a bitvector".to_string());
    };
    if *width != fp.eb + fp.sb {
        return Err("fp.to_ieee_bv result has the wrong width".to_string());
    }
    let stored = (fp.sb - 1) as usize;
    let all_exponent_ones = (BigInt::one() << fp.eb as usize) - BigInt::one();
    let payload = value.clone() & ((BigInt::one() << stored) - BigInt::one());
    let exponent = (value.clone() >> stored) & all_exponent_ones.clone();
    if exponent != all_exponent_ones || payload.is_zero() {
        return Err("fp.to_ieee_bv of NaN must denote a NaN encoding".to_string());
    }
    Ok(())
}

/// [`check_ieee_nan_encoding`] as a predicate: whether `bits` is a NaN encoding
/// of the same format as `like`.
#[must_use]
pub fn is_nan_encoding(bits: &ModelValue, like: &ModelValue) -> bool {
    check_ieee_nan_encoding(like, bits).is_ok()
}

/// Whether `fp.min` / `fp.max` on these operands is the case SMT-LIB leaves
/// UNSPECIFIED: two zeros of opposite signs in one format.
///
/// The standard declares the result underspecified there — either zero is a
/// legal interpretation — so the gate cannot compute it and must not refuse it
/// either. The caller adopts the model's own choice, as it does for
/// `fp.to_real` at NaN, and [`check_min_max_choice`] checks that what it adopted
/// is one of the two answers the standard actually allows.
#[must_use]
pub fn min_max_unspecified(name: &str, values: &[ModelValue]) -> bool {
    if !matches!(name, "fp.min" | "fp.max") {
        return false;
    }
    let [a, b] = values else { return false };
    let (Ok(x), Ok(y)) = (Fp::from_value(a), Fp::from_value(b)) else {
        return false;
    };
    x.is_zero() && y.is_zero() && x.sign != y.sign && x.same_format(y)
}

/// Whether `value` is a zero in the same format as `like`.
#[must_use]
pub fn is_zero_of_format(value: &ModelValue, like: &ModelValue) -> bool {
    let (Ok(v), Ok(l)) = (Fp::from_value(value), Fp::from_value(like)) else {
        return false;
    };
    v.is_zero() && v.same_format(l)
}

/// Whether `adopted` is an admissible `fp.min` / `fp.max` result for `operands`
/// that hit the underspecified `+0` / `-0` case.
///
/// The counterpart of [`check_ieee_nan_encoding`], and it exists for the same
/// reason: SMT-LIB frees the CHOICE between the two zeros, it does not free the
/// result from being a zero of that format. Adopting the model's value without
/// this check would let any value of the sort through — including a `1.0` that
/// no reading of the standard permits — and that is precisely how an adoption
/// branch turns into a hole.
pub fn check_min_max_choice(operands: &[ModelValue], adopted: &ModelValue) -> Result<(), String> {
    let [a, b] = operands else {
        return Err("fp.min/fp.max expects two floating-point arguments".to_string());
    };
    let x = Fp::from_value(a)?;
    let y = Fp::from_value(b)?;
    if !(x.is_zero() && y.is_zero() && x.sign != y.sign && x.same_format(y)) {
        return Err("fp.min/fp.max is not underspecified on these operands".to_string());
    }
    let z = Fp::from_value(adopted)?;
    if !(z.is_zero() && z.same_format(x)) {
        return Err("fp.min/fp.max of +0 and -0 must be a zero of that format".to_string());
    }
    Ok(())
}

#[cfg(test)]
#[path = "fp_tests.rs"]
mod tests;
