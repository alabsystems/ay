// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed, cumulatively admitted wide arithmetic. IEEE-754 §5.4.1 and §6.3;
//! https://smt-lib.org/theories-FloatingPoint.shtml
//! The independent rational/special-value/rounding kernels are shared with the
//! native carrier. This plan changes storage, never the operation's semantics.
use super::*;
use crate::fp::{Ext, RoundingMode, Special};
use num_traits::Signed;

pub(crate) struct ArithmeticPlan<'a> {
    name: &'a str,
    rm: RoundingMode,
    inputs: [Option<RealPlan<'a>>; 3],
    pub(crate) work: usize,
    pub(crate) storage: usize,
    eb: u32,
    sb: u32,
    remainder_result: Option<RemainderResult<'a>>,
}

enum RemainderResult<'a> {
    Nan,
    Dividend(&'a ModelValue),
}

pub(crate) fn scan_work(values: &[ModelValue]) -> Result<usize, String> {
    values.iter().try_fold(64usize, |sum, value| {
        // Covers repeated classification and RealPlan's trailing-zero scan.
        sum.checked_add(bytes(value)?.checked_mul(8).ok_or("FP scan overflow")?)
            .ok_or_else(|| "FP scan overflow".into())
    })
}

pub(crate) fn plan<'a>(
    name: &'a str,
    rm: RoundingMode,
    values: &'a [ModelValue],
) -> Result<ArithmeticPlan<'a>, String> {
    let count = match name {
        "fp.add" | "fp.sub" | "fp.mul" | "fp.div" | "fp.rem" => 2,
        "fp.fma" => 3,
        "fp.sqrt" => 1,
        _ => return Err("unsupported exact FP arithmetic".into()),
    };
    if values.len() != count {
        return Err("wrong exact FP arithmetic arity".into());
    }
    let first = view(&values[0])?;
    let (eb, sb) = (first.eb, first.sb);
    // Bias/shift arithmetic is checked, not an arbitrary precision whitelist.
    // Dense output and scaling must fit the shared exact rounding envelope.
    if !(2..=63).contains(&eb) || !(2..=crate::fp::MAX_SHIFT as u32).contains(&sb) {
        return Err("exact FP arithmetic format exceeds resource envelope".into());
    }
    // Validate every operand before selecting a field-only result. A special
    // first operand must not conceal a malformed or differently typed second.
    for value in values {
        let v = view(value)?;
        if (v.eb, v.sb) != (eb, sb) {
            return Err("exact FP arithmetic operands have different formats".into());
        }
    }
    if name == "fp.rem" {
        let second = view(&values[1])?;
        // IEEE-754 remainder special cases precede rational conversion. The
        // evaluator has paid the occupied-field scan before entering this plan.
        let remainder_result = if first.nan() || second.nan() || first.infinite() || second.zero() {
            Some(RemainderResult::Nan)
        } else if second.infinite() || first.zero() {
            Some(RemainderResult::Dividend(&values[0]))
        } else {
            None
        };
        if let Some(result) = remainder_result {
            let storage = match result {
                // One fixed-size result, two Arc control blocks/BigUint
                // headers and two primitive-constructor limb buffers. Vec's
                // minimum nonzero capacity is four u32/u64 digits here; price
                // four u64 digits per BigUint, not just its occupied limb.
                // eb<=63 bounds the mask; the fraction is one, not dense.
                RemainderResult::Nan => {
                    std::mem::size_of::<ModelValue>()
                        + 2 * (std::mem::size_of::<BigUint>() + 2 * std::mem::size_of::<usize>())
                        + 2 * 4 * std::mem::size_of::<u64>()
                }
                // Cloning exact DATA shares its immutable Arc fields. Legacy
                // native DATA is fixed-size too. No rational or field copy.
                RemainderResult::Dividend(_) => std::mem::size_of::<ModelValue>(),
            };
            return Ok(ArithmeticPlan {
                name,
                rm,
                inputs: [None, None, None],
                work: storage,
                storage,
                eb,
                sb,
                remainder_result: Some(result),
            });
        }
    }
    let mut inputs = [None, None, None];
    let mut input_bits = 0usize;
    let mut input_storage = 0usize;
    let mut input_work = 0usize;
    for (index, value) in values.iter().enumerate() {
        let dyadic = real_plan(value)?;
        input_bits = input_bits
            .checked_add(dyadic.materialized_bits)
            .ok_or("FP intermediate size overflow")?;
        input_work = input_work
            .checked_add(dyadic.work)
            .ok_or("FP work overflow")?;
        input_storage = input_storage
            .checked_add(dyadic.storage)
            .ok_or("FP storage overflow")?;
        inputs[index] = Some(dyadic);
    }
    // Sum/product/quotient/FMA numerator and denominator widths grow by sums
    // of input widths. Scaling/rounding adds at most the output precision and
    // those same input widths. Retain four times that total, plus 32 live limb
    // buffers for rational normalization, division, midpoint and output scratch.
    // Quadratic limb work bounds one non-interruptible BigInt operation. The
    // ORIGINAL evaluator must admit this whole plan before materialization.
    let bits = input_bits
        .checked_add(sb as usize)
        .and_then(|n| n.checked_add(64))
        .and_then(|n| n.checked_mul(4))
        .ok_or("FP intermediate size overflow")?;
    let limbs = bits.div_ceil(64);
    // Newton integer square root performs a logarithmic number of full-width
    // divisions. Price those iterations before entering its non-interruptible
    // BigInt kernel; the surrounding original-owner callbacks remain mandatory.
    let iterations = if name == "fp.sqrt" {
        bits.ilog2() as usize + 2
    } else {
        1
    };
    // Remainder performs a rational quotient and exact subtraction, then a
    // second reconstruction to CHECK that re-encoding did not round it. Price
    // both phases cumulatively before either one starts; no new grant is made
    // for the validation phase.
    let phases = if name == "fp.rem" { 2 } else { 1 };
    let work = limbs
        .checked_mul(limbs)
        .and_then(|n| n.checked_mul(32))
        .and_then(|n| n.checked_mul(iterations))
        .and_then(|n| n.checked_add(bits.checked_mul(8)?))
        .and_then(|n| n.checked_mul(phases))
        .and_then(|n| n.checked_add(input_work))
        .ok_or("FP work overflow")?;
    let storage = limbs
        .checked_mul(32 * std::mem::size_of::<u64>())
        .and_then(|n| n.checked_mul(phases))
        .and_then(|n| n.checked_add(input_storage))
        .ok_or("FP storage overflow")?;
    Ok(ArithmeticPlan {
        name,
        rm,
        inputs,
        work,
        storage,
        eb,
        sb,
        remainder_result: None,
    })
}

fn extended(plan: RealPlan<'_>) -> Result<Ext, String> {
    let v = &plan.value;
    if v.nan() {
        Ok(Ext::Nan)
    } else if v.infinite() {
        Ok(Ext::Inf(v.sign))
    } else {
        // A finite RealPlan always materializes, including signed zero.
        plan.materialize()
            .map(Ext::Fin)
            .ok_or_else(|| "finite FP conversion refused".into())
    }
}

impl ArithmeticPlan<'_> {
    pub(crate) fn materialize(mut self) -> Result<ModelValue, String> {
        if let Some(result) = self.remainder_result.take() {
            return match result {
                RemainderResult::Nan => self.special(Special::Nan),
                RemainderResult::Dividend(value) => Ok(value.clone()),
            };
        }
        let a = self.inputs[0].take().ok_or("missing FP operand")?;
        if self.name == "fp.sqrt" {
            let sign = a.value.sign;
            let special = match extended(a)? {
                Ext::Nan | Ext::Inf(true) => Special::Nan,
                Ext::Inf(false) => Special::Inf(false),
                Ext::Fin(value) if value.is_zero() => Special::Zero(sign),
                Ext::Fin(value) if value.is_negative() => Special::Nan,
                Ext::Fin(value) => {
                    return crate::fp::sqrt_positive_to_exact_format(
                        &value, self.eb, self.sb, self.rm,
                    );
                }
            };
            return self.special(special);
        }
        let b = self.inputs[1].take().ok_or("missing FP operand")?;
        let a_sign = a.value.sign;
        let mut b_sign = b.value.sign;
        let x = extended(a)?;
        let mut y = extended(b)?;
        if self.name == "fp.rem" {
            return match (&x, &y) {
                (Ext::Nan, _) | (_, Ext::Nan) | (Ext::Inf(_), _) => self.special(Special::Nan),
                (Ext::Fin(_), Ext::Fin(divisor)) if divisor.is_zero() => self.special(Special::Nan),
                (Ext::Fin(dividend), Ext::Inf(_)) => crate::fp::round_to_exact_format(
                    dividend,
                    self.eb,
                    self.sb,
                    RoundingMode::Rne,
                    a_sign,
                ),
                (Ext::Fin(dividend), Ext::Fin(divisor)) => {
                    let nearest =
                        crate::fp::round_to_integer(&(dividend / divisor), RoundingMode::Rne);
                    let exact = dividend - divisor * BigRational::from_integer(nearest);
                    if exact.is_zero() {
                        return self.special(Special::Zero(a_sign));
                    }
                    let result = crate::fp::round_to_exact_format(
                        &exact,
                        self.eb,
                        self.sb,
                        RoundingMode::Rne,
                        a_sign,
                    )?;
                    if real_plan(&result)?.materialize().as_ref() != Some(&exact) {
                        return Err("floating-point remainder is not exactly representable".into());
                    }
                    Ok(result)
                }
            };
        }
        if self.name == "fp.sub" {
            b_sign = !b_sign;
            y = match y {
                Ext::Fin(value) => Ext::Fin(-value),
                Ext::Inf(sign) => Ext::Inf(!sign),
                Ext::Nan => Ext::Nan,
            };
        }
        let result = if self.name == "fp.fma" {
            let c = self.inputs[2].take().ok_or("missing FP operand")?;
            let c_sign = c.value.sign;
            crate::fp::fma_exact(x, y, extended(c)?, a_sign, b_sign, c_sign, self.rm)
        } else {
            crate::fp::arith_exact(self.name, x, y, a_sign, b_sign, self.rm)?
        };
        match result {
            Ok(exact) => crate::fp::round_to_exact_format(
                &exact,
                self.eb,
                self.sb,
                self.rm,
                self.rm == RoundingMode::Rtn,
            ),
            Err(special) => self.special(special),
        }
    }

    fn special(&self, special: Special) -> Result<ModelValue, String> {
        let all = (1u64 << self.eb) - 1;
        let (sign, exponent, fraction) = match special {
            Special::Nan => (false, all, 1u8),
            Special::Inf(sign) => (sign, all, 0),
            Special::Zero(sign) => (sign, 0, 0),
        };
        construct(sign, exponent.into(), fraction.into(), self.eb, self.sb)
            .ok_or_else(|| "invalid exact FP special result".into())
    }
}
