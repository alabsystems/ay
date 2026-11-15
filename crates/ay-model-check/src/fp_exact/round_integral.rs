// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Round a binary significand to an integer in the same format.
//! https://smt-lib.org/theories-FloatingPoint.shtml

use super::*;
use crate::fp::RoundingMode;

enum ResultFields {
    Original,
    Zero,
    One,
    Carry,
    Fraction { cut: u64, increment: bool },
}

pub(crate) struct IntegralPlan<'a> {
    input: &'a ModelValue,
    result: ResultFields,
    pub(crate) work: usize,
    pub(crate) storage: usize,
}

pub(crate) fn scan_work(input: &ModelValue) -> Result<usize, String> {
    let v = view(input)?;
    // NaN/infinity and bias classification can scan the exponent four times.
    // Fraction trailing zeros and carry detection need at most two scans.
    Ok(64 + 4 * v.exponent.occupied_bytes() + 2 * v.fraction.occupied_bytes())
}

// Classify E-bias without materializing the bias, even for very wide E.
// Only exponents from -1 through p-1 can require fractional rounding.
fn exponent(e: &BigUint, eb: u32, p: u32) -> i64 {
    let high = eb - 1;
    if e.bits() == u64::from(eb) {
        let mut low = 0u32;
        for (i, mut digit) in e.iter_u32_digits().enumerate() {
            if i == (high / 32) as usize {
                digit &= !(1 << (high % 32));
            }
            if i == 0 {
                low = digit;
            } else if digit != 0 {
                return i64::from(p);
            }
        }
        return (i64::from(low) + 1).min(i64::from(p));
    }
    if e.bits() < u64::from(high) {
        return -2;
    }
    if e.trailing_ones() == u64::from(high) {
        return 0;
    }
    // bias-1 has every bit below the leading bit set except bit zero.
    if e.iter_u32_digits().enumerate().all(|(i, digit)| {
        let remaining = high - i as u32 * 32;
        let mask = u32::MAX >> (32 - remaining.min(32));
        digit == if i == 0 { mask & !1 } else { mask }
    }) {
        -1
    } else {
        -2
    }
}

pub(crate) fn plan(input: &ModelValue, rm: RoundingMode) -> Result<IntegralPlan<'_>, String> {
    let v = view(input)?;
    let ModelValue::FloatingPointExact { exponent: raw, .. } = input else {
        return Err("exact FP fields required".into());
    };
    let p = v.sb - 1;
    let result = if v.nan() || v.infinite() || v.zero() {
        ResultFields::Original
    } else {
        let e = exponent(raw, v.eb, p);
        if raw.is_zero() || e < 0 {
            let (guard, sticky) = if raw.is_zero() && v.eb == 2 {
                discarded_bits(v.fraction, u64::from(p), None, v.fraction.trailing())
            } else if e == -1 && !raw.is_zero() {
                (true, !v.fraction.zero())
            } else {
                (false, true)
            };
            if round_increment(rm, v.sign, guard, sticky, false) {
                ResultFields::One
            } else {
                ResultFields::Zero
            }
        } else if e >= i64::from(p) {
            ResultFields::Original
        } else {
            let cut = u64::from(p) - e as u64;
            let trailing = v.fraction.trailing();
            if trailing.is_none_or(|n| n >= cut) {
                ResultFields::Original
            } else {
                let (guard, sticky) = discarded_bits(v.fraction, cut, None, trailing);
                let increment =
                    round_increment(rm, v.sign, guard, sticky, e == 0 || v.fraction.bit(cut));
                if increment && (e == 0 || retained_all_ones(v.fraction, cut, u64::from(p))) {
                    ResultFields::Carry
                } else {
                    ResultFields::Fraction { cut, increment }
                }
            }
        }
    };
    let bits = match result {
        ResultFields::Original | ResultFields::Zero => 0,
        ResultFields::One => u64::from(v.eb - 1),
        ResultFields::Carry => (raw.bits() + 1).min(u64::from(v.eb)),
        ResultFields::Fraction { cut, increment } => {
            let ModelValue::FloatingPointExact { significand, .. } = input else {
                return Err("exact FP fields required".into());
            };
            let kept = significand.bits().saturating_sub(cut);
            let output = if increment {
                (kept + 1 + cut).min(u64::from(p))
            } else if kept == 0 {
                0
            } else {
                kept + cut
            };
            output
        }
    };
    let retained_exponent = if matches!(result, ResultFields::Fraction { .. }) {
        raw.bits()
    } else {
        0
    };
    if bits + retained_exponent > MAX_FIELD_BITS {
        return Err("FP integral rounding output exceeds occupied field bound".into());
    }
    let bytes = bits.div_ceil(8) as usize;
    let work = bytes
        .checked_mul(4)
        .and_then(|n| n.checked_add(64))
        .ok_or("FP integral rounding work overflow")?;
    let storage = bytes
        .div_ceil(8)
        .checked_mul(8 * 8)
        .and_then(|n| n.checked_add(256))
        .ok_or("FP integral rounding storage overflow")?;
    Ok(IntegralPlan {
        input,
        result,
        work,
        storage,
    })
}

impl IntegralPlan<'_> {
    pub(crate) fn materialize(self) -> Result<ModelValue, String> {
        let ModelValue::FloatingPointExact {
            sign,
            exponent,
            significand,
            exponent_bits: eb,
            significand_bits: sb,
        } = self.input
        else {
            return Err("exact FP fields required".into());
        };
        let (exp, frac) = match self.result {
            ResultFields::Original => return Ok(self.input.clone()),
            ResultFields::Zero => (Arc::new(BigUint::zero()), BigUint::zero()),
            ResultFields::Carry => (Arc::new(exponent.as_ref() + 1u8), BigUint::zero()),
            ResultFields::One => (
                Arc::new((BigUint::one() << (eb - 1)) - 1u8),
                BigUint::zero(),
            ),
            ResultFields::Fraction { cut, increment } => {
                let mut kept = significand.as_ref() >> cut;
                if increment {
                    kept += 1u8;
                }
                (Arc::clone(exponent), kept << cut)
            }
        };
        construct_shared(*sign, exp, Arc::new(frac), *eb, *sb)
            .ok_or_else(|| "FP integral rounding result exceeds field bounds".into())
    }
}

fn retained_all_ones(fraction: Field<'_>, cut: u64, p: u64) -> bool {
    let Field::Big(n) = fraction else {
        return false;
    };
    n.bits() == p
        && n.iter_u32_digits()
            .enumerate()
            .skip((cut / 32) as usize)
            .all(|(i, digit)| {
                let start = i as u64 * 32;
                let low = cut.saturating_sub(start) as u32;
                let high = (p - start).min(32) as u32;
                let mask = (u32::MAX >> (32 - high)) & (u32::MAX << low);
                digit & mask == mask
            })
}
