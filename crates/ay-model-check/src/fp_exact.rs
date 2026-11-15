// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent exact floating-point data and selected operations, without solver code.
use crate::ModelValue;
use num_bigint::{BigInt, BigUint};
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};
use std::cmp::Ordering;
use std::sync::Arc;

mod arithmetic;
mod conversion;
pub(crate) use arithmetic::{plan as arithmetic_plan, scan_work as arithmetic_scan_work};
pub(crate) use conversion::{
    plan as conversion_plan, scan_work as conversion_scan_work,
    Interpretation as ConversionInterpretation,
};
mod round_integral;
pub(crate) use round_integral::plan as integral_plan;
pub(crate) use round_integral::scan_work as integral_scan_work;
mod to_bv;
pub(crate) use to_bv::plan as bv_plan;
pub(crate) use to_bv::Signedness as BvSignedness;

/// Actual occupied bits, not a whitelist of declared formats. Sparse declared
/// widths remain cheap. Refusal is a resource boundary, never a false value.
const MAX_FIELD_BITS: u64 = (crate::MODEL_DATA_WORK_LIMIT as u64) * 8;

fn valid(eb: u32, sb: u32, exponent: &BigUint, fraction: &BigUint) -> bool {
    eb >= 2
        && sb >= 2
        && exponent.bits() <= u64::from(eb)
        && fraction.bits() <= u64::from(sb - 1)
        && exponent.bits().saturating_add(fraction.bits()) <= MAX_FIELD_BITS
}

pub(crate) fn construct(
    sign: bool,
    exponent: BigUint,
    fraction: BigUint,
    eb: u32,
    sb: u32,
) -> Option<ModelValue> {
    if !valid(eb, sb, &exponent, &fraction) {
        return None;
    }
    construct_shared(sign, Arc::new(exponent), Arc::new(fraction), eb, sb)
}

pub(crate) fn construct_shared(
    sign: bool,
    exponent: Arc<BigUint>,
    fraction: Arc<BigUint>,
    eb: u32,
    sb: u32,
) -> Option<ModelValue> {
    if !valid(eb, sb, &exponent, &fraction) {
        return None;
    }
    // Retain raw immutable DATA. Abstract NaN normalization is performed by
    // the checked views after the evaluator has charged actual field reads;
    // ingress must not scan an exponent or copy a payload ahead of its owner.
    Some(ModelValue::FloatingPointExact {
        sign,
        exponent,
        significand: fraction,
        exponent_bits: eb,
        significand_bits: sb,
    })
}

#[derive(Clone, Copy)]
enum Field<'a> {
    Native(u128),
    Big(&'a BigUint),
}
impl Field<'_> {
    fn occupied_bytes(self) -> usize {
        let bits = match self {
            Self::Native(n) => u64::from(128 - n.leading_zeros()),
            Self::Big(n) => n.bits(),
        };
        // valid() already bounded occupied fields by MAX_FIELD_BITS.
        bits.div_ceil(8) as usize
    }

    fn bit(self, bit: u64) -> bool {
        match self {
            Self::Native(n) => u32::try_from(bit)
                .ok()
                .and_then(|b| n.checked_shr(b))
                .is_some_and(|n| n & 1 != 0),
            Self::Big(n) => n.bit(bit),
        }
    }

    fn trailing(self) -> Option<u64> {
        match self {
            Self::Native(0) => None,
            Self::Native(n) => Some(u64::from(n.trailing_zeros())),
            Self::Big(n) => n.trailing_zeros(),
        }
    }
    fn zero(self) -> bool {
        match self {
            Self::Native(n) => n == 0,
            Self::Big(n) => n.is_zero(),
        }
    }
    fn all_ones(self, width: u32) -> bool {
        match self {
            Self::Native(n) => width < 128 && n == (1u128 << width) - 1,
            Self::Big(n) => n.bits() == u64::from(width) && n.trailing_ones() == u64::from(width),
        }
    }
    fn compare(self, other: Self) -> Ordering {
        match (self, other) {
            (Self::Native(a), Self::Native(b)) => a.cmp(&b),
            (Self::Big(a), Self::Big(b)) => a.cmp(b),
            (Self::Big(a), Self::Native(b)) => a.cmp(&BigUint::from(b)),
            (Self::Native(a), Self::Big(b)) => BigUint::from(a).cmp(b),
        }
    }
}

pub(crate) struct View<'a> {
    sign: bool,
    exponent: Field<'a>,
    fraction: Field<'a>,
    pub(crate) eb: u32,
    pub(crate) sb: u32,
}
impl View<'_> {
    fn nan(&self) -> bool {
        self.exponent.all_ones(self.eb) && !self.fraction.zero()
    }
    fn infinite(&self) -> bool {
        self.exponent.all_ones(self.eb) && self.fraction.zero()
    }
    fn zero(&self) -> bool {
        self.exponent.zero() && self.fraction.zero()
    }
    fn numeric(&self, other: &Self) -> Result<Option<Ordering>, String> {
        if (self.eb, self.sb) != (other.eb, other.sb) {
            return Err("mixed floating-point formats".into());
        }
        if self.nan() || other.nan() {
            return Ok(None);
        }
        if self.zero() && other.zero() {
            return Ok(Some(Ordering::Equal));
        }
        if self.sign != other.sign {
            return Ok(Some(if self.sign {
                Ordering::Less
            } else {
                Ordering::Greater
            }));
        }
        let order = self
            .exponent
            .compare(other.exponent)
            .then_with(|| self.fraction.compare(other.fraction));
        Ok(Some(if self.sign { order.reverse() } else { order }))
    }
}

pub(crate) fn view(value: &ModelValue) -> Result<View<'_>, String> {
    match value {
        ModelValue::FloatingPoint {
            sign,
            exponent,
            significand,
            exponent_bits: eb,
            significand_bits: sb,
        } if crate::fp::data_fields_fit(*eb, *sb, *exponent, *significand) => Ok(View {
            sign: *sign,
            exponent: Field::Native(u128::from(*exponent)),
            fraction: Field::Native(*significand),
            eb: *eb,
            sb: *sb,
        }),
        ModelValue::FloatingPointExact {
            sign,
            exponent,
            significand,
            exponent_bits: eb,
            significand_bits: sb,
        } if valid(*eb, *sb, exponent, significand) => Ok(View {
            sign: *sign,
            exponent: Field::Big(exponent),
            fraction: Field::Big(significand),
            eb: *eb,
            sb: *sb,
        }),
        _ => Err("malformed or excessive floating-point fields".into()),
    }
}

pub(crate) fn bytes(value: &ModelValue) -> Result<usize, String> {
    view(value)?;
    Ok(match value {
        ModelValue::FloatingPointExact {
            exponent,
            significand,
            ..
        } => (exponent.bits() + significand.bits()).div_ceil(8) as usize + 32,
        _ => 32,
    })
}

pub(crate) fn same_element(a: &ModelValue, b: &ModelValue) -> Result<bool, String> {
    let a = view(a)?;
    let b = view(b)?;
    Ok((a.eb, a.sb) == (b.eb, b.sb)
        && ((a.nan() && b.nan())
            || (a.sign == b.sign
                && a.exponent.compare(b.exponent).is_eq()
                && a.fraction.compare(b.fraction).is_eq())))
}

pub(crate) fn unary_sign(name: &str, value: &ModelValue) -> Result<Option<ModelValue>, String> {
    if !matches!(name, "fp.abs" | "fp.neg") {
        return Ok(None);
    }
    let v = view(value)?;
    let mut result = value.clone();
    if let ModelValue::FloatingPointExact { sign, .. } = &mut result {
        *sign = !v.nan() && name == "fp.neg" && !v.sign;
        if name == "fp.abs" {
            *sign = false;
        }
    }
    Ok(Some(result))
}

pub(crate) fn opposite_zeros(a: &ModelValue, b: &ModelValue) -> bool {
    let (Ok(a), Ok(b)) = (view(a), view(b)) else {
        return false;
    };
    (a.eb, a.sb) == (b.eb, b.sb) && a.zero() && b.zero() && a.sign != b.sign
}

pub(crate) fn is_zero_of_format(value: &ModelValue, like: &ModelValue) -> bool {
    let (Ok(value), Ok(like)) = (view(value), view(like)) else {
        return false;
    };
    value.zero() && (value.eb, value.sb) == (like.eb, like.sb)
}

/// IEEE minimum/maximum selects an input; it does not round or reencode it.
/// Return its immutable fields directly, after independently comparing them.
pub(crate) fn min_max(name: &str, values: &[ModelValue]) -> Result<Option<ModelValue>, String> {
    let want_min = match name {
        "fp.min" => true,
        "fp.max" => false,
        _ => return Ok(None),
    };
    let [a, b] = values else {
        return Err(format!("{name} expects two floating-point arguments"));
    };
    let (x, y) = (view(a)?, view(b)?);
    if (x.eb, x.sb) != (y.eb, y.sb) {
        return Err(format!("{name} operands have different formats"));
    }
    if x.nan() {
        return Ok(Some(b.clone()));
    }
    if y.nan() {
        return Ok(Some(a.clone()));
    }
    if x.zero() && y.zero() && x.sign != y.sign {
        return Err(crate::fp::UNDERSPECIFIED.to_owned());
    }
    let order = x.numeric(&y)?.ok_or("unordered operands")?;
    let pick_a = if want_min {
        !order.is_gt()
    } else {
        !order.is_lt()
    };
    Ok(Some(if pick_a { a.clone() } else { b.clone() }))
}

pub(crate) fn classify(name: &str, value: &ModelValue) -> Result<Option<bool>, String> {
    if !matches!(
        name,
        "fp.isNaN"
            | "fp.isInfinite"
            | "fp.isZero"
            | "fp.isNormal"
            | "fp.isSubnormal"
            | "fp.isNegative"
            | "fp.isPositive"
    ) {
        return Ok(None);
    }
    let v = view(value)?;
    Ok(Some(match name {
        "fp.isNaN" => v.nan(),
        "fp.isInfinite" => v.infinite(),
        "fp.isZero" => v.zero(),
        "fp.isNormal" => !v.exponent.zero() && !v.exponent.all_ones(v.eb),
        "fp.isSubnormal" => v.exponent.zero() && !v.fraction.zero(),
        "fp.isNegative" => v.sign && !v.nan(),
        _ => !v.sign && !v.nan(),
    }))
}

pub(crate) fn compare(name: &str, values: &[ModelValue]) -> Result<Option<bool>, String> {
    if !matches!(name, "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq") {
        return Ok(None);
    }
    if values.len() < 2 {
        return Err("FP comparison needs two operands".into());
    }
    for pair in values.windows(2) {
        let a = view(&pair[0])?;
        let b = view(&pair[1])?;
        let Some(order) = a.numeric(&b)? else {
            return Ok(Some(false));
        };
        let accepted = match name {
            "fp.eq" => order.is_eq(),
            "fp.lt" => order.is_lt(),
            "fp.leq" => !order.is_gt(),
            "fp.gt" => order.is_gt(),
            _ => !order.is_lt(),
        };
        if !accepted {
            return Ok(Some(false));
        }
    }
    Ok(Some(true))
}

/// Bridge only declared native data formats; callers still check arithmetic.
pub(crate) fn native(value: &ModelValue) -> Option<ModelValue> {
    let v = view(value).ok()?;
    if !crate::fp::data_format_supported(v.eb, v.sb) {
        return None;
    }
    match value {
        ModelValue::FloatingPoint { .. } => Some(value.clone()),
        ModelValue::FloatingPointExact {
            exponent,
            significand,
            ..
        } => Some(ModelValue::FloatingPoint {
            sign: v.sign,
            exponent: exponent.to_u64()?,
            significand: significand.to_u128()?,
            exponent_bits: v.eb,
            significand_bits: v.sb,
        }),
        _ => None,
    }
}

/// Independent exact split; occupied input bounds scratch before any copy.
pub(crate) fn decode(bits: &BigInt, width: u32, eb: u32, sb: u32) -> Option<ModelValue> {
    if eb < 2
        || sb < 2
        || u64::from(width) != u64::from(eb) + u64::from(sb)
        || bits.bits() > u64::from(width)
        || bits.bits() > MAX_FIELD_BITS
    {
        return None;
    }
    let mut payload = bits.to_biguint()?;
    let sign = payload.bit(u64::from(width) - 1);
    if sign {
        payload ^= BigUint::one() << usize::try_from(width - 1).ok()?;
    }
    let stored = usize::try_from(sb - 1).ok()?;
    let exponent = &payload >> stored;
    let fraction = payload - (&exponent << stored);
    let exact = construct(sign, exponent, fraction, eb, sb)?;
    Some(native(&exact).unwrap_or(exact))
}

pub(crate) fn literal(values: &[ModelValue]) -> Result<ModelValue, String> {
    let [ModelValue::BitVec {
        width: sw,
        value: s,
    }, ModelValue::BitVec {
        width: eb,
        value: e,
    }, ModelValue::BitVec {
        width: fw,
        value: f,
    }] = values
    else {
        return Err("FP literal needs three bitvectors".into());
    };
    if *sw != 1
        || !(s.is_zero() || s.is_one())
        || e.bits().saturating_add(f.bits()) > MAX_FIELD_BITS
    {
        return Err("malformed FP literal".into());
    }
    let exact = construct(
        s.is_one(),
        e.to_biguint().ok_or("negative FP exponent")?,
        f.to_biguint().ok_or("negative FP fraction")?,
        *eb,
        fw.checked_add(1).ok_or("FP precision overflow")?,
    )
    .ok_or("malformed FP literal fields")?;
    Ok(native(&exact).unwrap_or(exact))
}

pub(crate) fn special_work(name: &str, indices: &[u32]) -> Option<usize> {
    let [eb, sb] = indices else {
        return None;
    };
    if *eb < 2 || *sb < 2 {
        return None;
    }
    match name {
        "+zero" | "-zero" => Some(32),
        "+oo" | "-oo" | "NaN" if u64::from(*eb) <= MAX_FIELD_BITS => {
            Some((*eb as usize).div_ceil(8) + 32)
        }
        _ => None,
    }
}

pub(crate) fn special(name: &str, indices: &[u32]) -> Option<ModelValue> {
    special_work(name, indices)?;
    let [eb, sb] = indices else {
        return None;
    };
    let exponent = if name.ends_with("zero") {
        BigUint::zero()
    } else {
        (BigUint::one() << usize::try_from(*eb).ok()?) - BigUint::one()
    };
    construct(
        name.starts_with('-'),
        exponent,
        if name == "NaN" {
            BigUint::one()
        } else {
            BigUint::zero()
        },
        *eb,
        *sb,
    )
}

// IEEE interchange is raw data, not a grant of rounded arithmetic support.
pub(crate) fn ieee_work(value: &ModelValue) -> Result<(u32, usize), String> {
    let v = view(value)?;
    let width = v.eb.checked_add(v.sb).ok_or("IEEE width overflow")?;
    let occupied = if v.sign || v.nan() {
        u64::from(width)
    } else if !v.exponent.zero() {
        u64::from(v.sb - 1)
            + match v.exponent {
                Field::Native(n) => u64::from(u128::BITS - n.leading_zeros()),
                Field::Big(n) => n.bits(),
            }
    } else {
        match v.fraction {
            Field::Native(n) => u64::from(u128::BITS - n.leading_zeros()),
            Field::Big(n) => n.bits(),
        }
    };
    if occupied > MAX_FIELD_BITS {
        return Err("IEEE encoding exceeds existing model data work bound".into());
    }
    // Account input reads, shifted/packed scratch and the retained output using
    // the existing evaluator owner; no declared-width mask or fresh allowance.
    let output = usize::try_from(occupied.div_ceil(8)).map_err(|_| "IEEE size overflow")?;
    let work = bytes(value)?
        .checked_add(output.checked_mul(4).ok_or("IEEE size overflow")?)
        .and_then(|n| n.checked_add(64))
        .ok_or("IEEE size overflow")?;
    Ok((width, work))
}

fn field_integer(field: Field<'_>) -> BigInt {
    match field {
        Field::Native(n) => BigInt::from(n),
        Field::Big(n) => BigInt::from(n.clone()),
    }
}

/// A borrowed dyadic conversion plan. Constructing the plan never copies a
/// field or materializes a power of two; the evaluator admits its original
/// work and storage before calling `materialize`.
pub(crate) struct RealPlan<'a> {
    value: View<'a>,
    shift: i64,
    cancelled: u32,
    pub(crate) work: usize,
    pub(crate) storage: usize,
    // Numerator plus denominator bits after dyadic cancellation; size metadata,
    // independent of the work policy used to admit their materialization.
    pub(super) materialized_bits: usize,
}

pub(crate) fn real_plan(value: &ModelValue) -> Result<RealPlan<'_>, String> {
    let value = view(value)?;
    let (shift, cancelled, numerator_bits, denominator_bits) =
        if value.nan() || value.infinite() || value.zero() {
            (0, 0, 0, 0)
        } else {
            // Unlike a declared-width BigUint mask, this checked scalar bias has
            // constant storage. Exponents outside its exact range refuse rather
            // than allocating a value from an arbitrarily large declared format.
            let bias = 1u128
                .checked_shl(value.eb - 1)
                .and_then(|n| n.checked_sub(1))
                .ok_or("FP exact exponent exceeds resource bound")?;
            let exponent = match value.exponent {
                Field::Native(n) => n,
                Field::Big(n) => n
                    .to_u128()
                    .ok_or("FP exact exponent exceeds resource bound")?,
            };
            let effective = exponent.max(1);
            let unbiased = if effective >= bias {
                i128::try_from(effective - bias)
                    .map_err(|_| "FP exact exponent exceeds resource bound")?
            } else {
                -i128::try_from(bias - effective)
                    .map_err(|_| "FP exact exponent exceeds resource bound")?
            };
            // M = 2^k + fraction for a normal, M = fraction otherwise.
            // Since fraction < 2^k, its trailing zero count is also M's,
            // except that a zero fraction makes a normal M exactly 2^k.
            // Inspect the borrowed field after the evaluator pays its input
            // scan. Never build that potentially enormous hidden integer.
            let trailing = match value.fraction {
                Field::Native(0) => u64::from(value.sb - 1),
                Field::Native(n) => u64::from(n.trailing_zeros()),
                Field::Big(n) => n.trailing_zeros().unwrap_or(u64::from(value.sb - 1)),
            };
            let cancelled = u32::try_from(trailing).map_err(|_| "FP cancellation overflow")?;
            let reduced_stored = (value.sb - 1)
                .checked_sub(cancelled)
                .ok_or("FP cancellation exceeds field width")?;
            let shift = unbiased
                .checked_sub(i128::from(reduced_stored))
                .and_then(|n| i64::try_from(n).ok())
                .ok_or("FP exact exponent exceeds resource bound")?;
            // Reuse the independent converter's existing dyadic shift bound.
            if shift.unsigned_abs() > crate::fp::MAX_SHIFT as u64 {
                return Err("FP exact exponent exceeds resource bound".into());
            }
            let occupied = if exponent != 0 {
                u64::from(reduced_stored) + 1
            } else {
                match value.fraction {
                    Field::Native(n) => u64::from(u128::BITS - n.leading_zeros()),
                    Field::Big(n) => n.bits(),
                }
                .checked_sub(trailing)
                .ok_or("FP cancellation exceeds payload")?
            };
            (
                shift,
                cancelled,
                occupied + shift.max(0) as u64,
                if shift < 0 {
                    shift.unsigned_abs() + 1
                } else {
                    1
                },
            )
        };
    let bits = numerator_bits
        .checked_add(denominator_bits)
        .ok_or("FP real size overflow")?;
    let materialized_bits = usize::try_from(bits).map_err(|_| "FP real size overflow")?;
    let work = materialized_bits
        .checked_add(64)
        .ok_or("FP real work overflow")?;
    // Inputs, numerator, denominator and normalization scratch remain charged
    // conservatively even after transient allocations have been released.
    let storage = usize::try_from(bits.div_ceil(64))
        .ok()
        .and_then(|n| n.checked_mul(4 * std::mem::size_of::<u64>()))
        .and_then(|n| n.checked_add(256))
        .ok_or("FP real storage overflow")?;
    Ok(RealPlan {
        value,
        shift,
        cancelled,
        work,
        storage,
        materialized_bits,
    })
}

impl RealPlan<'_> {
    /// None denotes the existing SMT-LIB underspecified nonfinite case, not a
    /// guessed real or permission to adopt any result of a finite conversion.
    pub(crate) fn materialize(self) -> Option<BigRational> {
        if self.value.nan() || self.value.infinite() {
            return None;
        }
        if self.value.zero() {
            return Some(BigRational::from_integer(BigInt::zero()));
        }
        // Shift the BORROWED BigUint before its conversion. Cloning it first
        // would allocate the unreduced payload outside the admitted plan.
        let mut numerator = match self.value.fraction {
            Field::Native(n) => BigInt::from(n.checked_shr(self.cancelled).unwrap_or(0)),
            Field::Big(n) => BigInt::from(n >> self.cancelled as usize),
        };
        if !self.value.exponent.zero() {
            numerator += BigInt::one() << (self.value.sb - 1 - self.cancelled) as usize;
        }
        if self.value.sign {
            numerator = -numerator;
        }
        Some(if self.shift >= 0 {
            BigRational::from_integer(numerator << self.shift as usize)
        } else {
            BigRational::new(
                numerator,
                BigInt::one() << self.shift.unsigned_abs() as usize,
            )
        })
    }
}

pub(crate) fn to_ieee_bv(value: &ModelValue) -> Result<ModelValue, String> {
    let (width, _) = ieee_work(value)?;
    let v = view(value)?;
    if v.nan() {
        return Err(crate::fp::UNDERSPECIFIED.into());
    }
    let mut bits = field_integer(v.fraction);
    if !v.exponent.zero() {
        bits |= field_integer(v.exponent) << (v.sb - 1) as usize;
    }
    if v.sign {
        bits |= BigInt::one() << (width - 1) as usize;
    }
    Ok(ModelValue::bitvec(bits, width))
}

pub(crate) fn ieee_unspecified(value: &ModelValue) -> bool {
    view(value).is_ok_and(|v| v.nan())
}

pub(crate) fn check_ieee_nan_encoding(
    operand: &ModelValue,
    encoding: &ModelValue,
) -> Result<(), String> {
    let (expected, _) = ieee_work(operand)?;
    let v = view(operand)?;
    if !v.nan() {
        return Err("fp.to_ieee_bv is not underspecified on this operand".into());
    }
    let ModelValue::BitVec { width, value } = encoding else {
        return Err("fp.to_ieee_bv must denote a bitvector".into());
    };
    if *width != expected {
        return Err("fp.to_ieee_bv result has the wrong width".into());
    }
    let decoded = decode(value, *width, v.eb, v.sb).ok_or("malformed IEEE encoding")?;
    if !view(&decoded)?.nan() {
        return Err("fp.to_ieee_bv of NaN must denote a NaN encoding".into());
    }
    Ok(())
}

fn round_increment(
    rm: crate::fp::RoundingMode,
    negative: bool,
    guard: bool,
    sticky: bool,
    odd: bool,
) -> bool {
    use crate::fp::RoundingMode::*;
    match rm {
        Rtz => false,
        Rtp => !negative && (guard || sticky),
        Rtn => negative && (guard || sticky),
        Rna => guard,
        Rne => guard && (sticky || odd),
    }
}

/// Guard and sticky bits of the exact significand below a nonzero cut.
fn discarded_bits(
    fraction: Field<'_>,
    cut: u64,
    hidden: Option<u64>,
    trailing: Option<u64>,
) -> (bool, bool) {
    let guard = cut - 1;
    (
        fraction.bit(guard) || hidden == Some(guard),
        trailing.is_some_and(|low| low < guard) || hidden.is_some_and(|bit| bit < guard),
    )
}
