// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! SMT-LIB FloatingPoint `to_fp`: round an exact numeric value once, using
//! the independent quotient/midpoint kernel (IEEE-754 §5.4.2).
use super::*;
use crate::fp::RoundingMode;
use num_traits::Signed;

pub(crate) fn scan_work(value: &ModelValue) -> Result<usize, String> {
    let bits = match value {
        ModelValue::Int(n) | ModelValue::BitVec { value: n, .. } => n.bits(),
        ModelValue::Real(r) => r
            .numer()
            .bits()
            .checked_add(r.denom().bits())
            .ok_or("conversion size overflow")?,
        ModelValue::FloatingPoint { .. } | ModelValue::FloatingPointExact { .. } => {
            return bytes(value)
        }
        _ => return Err("to_fp expects a numeric or floating-point argument".into()),
    };
    usize::try_from(bits.div_ceil(8)).map_err(|_| "conversion size overflow".into())
}

pub(crate) enum Interpretation {
    Signed,
    Unsigned,
}

pub(crate) struct ConversionPlan<'a> {
    value: &'a ModelValue,
    dyadic: Option<RealPlan<'a>>,
    interpretation: Interpretation,
    eb: u32,
    sb: u32,
    rm: RoundingMode,
    pub(crate) work: usize,
    pub(crate) storage: usize,
}

pub(crate) fn plan(
    value: &ModelValue,
    interpretation: Interpretation,
    eb: u32,
    sb: u32,
    rm: RoundingMode,
) -> Result<ConversionPlan<'_>, String> {
    if !(2..=63).contains(&eb) || !(2..=crate::fp::MAX_SHIFT as u32).contains(&sb) {
        return Err("wide floating-point conversion exceeds exact envelope".into());
    }
    if matches!(interpretation, Interpretation::Unsigned)
        && !matches!(value, ModelValue::BitVec { .. })
    {
        return Err("to_fp_unsigned expects a bitvector".into());
    }
    if matches!(value, ModelValue::Real(r) if r.denom() <= &BigInt::zero()) {
        return Err("to_fp expects a positive rational denominator".into());
    }
    let mut dyadic = None;
    let (input_bits, extra_work, extra_storage) = match value {
        ModelValue::Int(n) => (
            usize::try_from(n.bits()).map_err(|_| "conversion size overflow")?,
            0,
            0,
        ),
        ModelValue::Real(r) => (
            usize::try_from(
                r.numer()
                    .bits()
                    .checked_add(r.denom().bits())
                    .ok_or("conversion size overflow")?,
            )
            .map_err(|_| "conversion size overflow")?,
            0,
            0,
        ),
        ModelValue::BitVec { width, value } => {
            if *width == 0 || value.is_negative() || value.bits() > u64::from(*width) {
                return Err("bitvector value outside its width".into());
            }
            // Only a set sign bit requires a width-sized two's-complement
            // subtraction. Sparse positive words never build 2^width.
            let bits = value.bits()
                + u64::from(
                    matches!(interpretation, Interpretation::Signed)
                        && value.bits() == u64::from(*width),
                );
            (
                usize::try_from(bits).map_err(|_| "conversion size overflow")?,
                0,
                0,
            )
        }
        ModelValue::FloatingPoint { .. } | ModelValue::FloatingPointExact { .. } => {
            let p = real_plan(value)?;
            let data = (p.materialized_bits, p.work, p.storage);
            dyadic = Some(p);
            data
        }
        _ => return Err("to_fp expects a numeric or floating-point argument".into()),
    };
    // Same original rounding envelope as wide arithmetic: magnitude, scale,
    // quotient/remainder, midpoint and result buffers. All are admitted before
    // any source clone, two's-complement subtraction, rational or output shift.
    let constant_output = match value {
        ModelValue::Int(n) | ModelValue::BitVec { value: n, .. } => n.is_zero(),
        ModelValue::Real(r) => r.is_zero(),
        _ => dyadic
            .as_ref()
            .is_some_and(|p| p.value.nan() || p.value.infinite() || p.value.zero()),
    };
    // Special values and numeric zero never enter dense rounding. Do not price
    // a declared-width fraction buffer that this path never constructs.
    let bits = input_bits
        .checked_add(if constant_output { 0 } else { sb as usize })
        .and_then(|n| n.checked_add(64))
        .and_then(|n| n.checked_mul(4))
        .ok_or("conversion size overflow")?;
    let limbs = bits.div_ceil(64);
    let work = limbs
        .checked_mul(limbs)
        .and_then(|n| n.checked_mul(32))
        .and_then(|n| n.checked_add(bits.checked_mul(8)?))
        .and_then(|n| n.checked_add(extra_work))
        .ok_or("conversion work overflow")?;
    let storage = limbs
        .checked_mul(32 * size_of::<u64>())
        .and_then(|n| n.checked_add(extra_storage))
        .ok_or("conversion storage overflow")?;
    Ok(ConversionPlan {
        value,
        dyadic,
        interpretation,
        eb,
        sb,
        rm,
        work,
        storage,
    })
}

impl ConversionPlan<'_> {
    pub(crate) fn materialize(self) -> Result<ModelValue, String> {
        let exact = if let Some(p) = self.dyadic {
            let v = &p.value;
            if v.nan() || v.infinite() || v.zero() {
                let exponent = if v.zero() { 0 } else { (1u64 << self.eb) - 1 };
                let result = construct(
                    v.sign,
                    exponent.into(),
                    u8::from(v.nan()).into(),
                    self.eb,
                    self.sb,
                )
                .ok_or("invalid converted special value")?;
                return preserve_carrier(result, self.eb, self.sb);
            }
            p.materialize().ok_or("finite conversion unavailable")?
        } else {
            match self.value {
                ModelValue::Int(n) => BigRational::from_integer(n.clone()),
                ModelValue::Real(r) => r.clone(),
                ModelValue::BitVec { width, value } => {
                    let n = if matches!(self.interpretation, Interpretation::Signed)
                        && value.bits() == u64::from(*width)
                    {
                        value - (BigInt::one() << *width as usize)
                    } else {
                        value.clone()
                    };
                    BigRational::from_integer(n)
                }
                _ => return Err("invalid conversion plan".into()),
            }
        };
        let result = crate::fp::round_to_exact_format(&exact, self.eb, self.sb, self.rm, false)?;
        preserve_carrier(result, self.eb, self.sb)
    }
}

fn preserve_carrier(value: ModelValue, eb: u32, sb: u32) -> Result<ModelValue, String> {
    if crate::fp::format_supported(eb, sb) {
        native(&value).ok_or_else(|| "rounded result does not fit native fields".into())
    } else {
        Ok(value)
    }
}
