// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact dyadic integer rounding, independently of the solver. SMT-LIB's
//! FloatingPoint theory (https://smt-lib.org/theories-FloatingPoint.shtml)
//! specifies the five rounding modes and signed/unsigned conversion residues.
//! As in `fp::round_to_integer`, ties compare the exact remainder with half;
//! here a power-of-two denominator needs only quotient, guard and sticky bits.

use super::*;
use crate::fp::{RoundingMode, UNDERSPECIFIED};

pub(crate) struct BvPlan<'a> {
    dyadic: RealPlan<'a>,
    width: u32,
    signedness: Signedness,
    rm: RoundingMode,
    pub(crate) work: usize,
    pub(crate) storage: usize,
}

pub(crate) enum Signedness {
    Signed,
    Unsigned,
}

pub(crate) fn plan(
    value: &ModelValue,
    width: u32,
    signedness: Signedness,
    rm: RoundingMode,
) -> Result<BvPlan<'_>, String> {
    if width == 0 || width > 1024 {
        return Err("unsupported bitvector width".into());
    }
    // Scalar metadata only. Retain the existing dyadic MAX_SHIFT and original
    // plan envelope; no rational, hidden significand or denominator is built.
    let dyadic = real_plan(value)?;
    let cells = usize::try_from(u64::from(width).div_ceil(64) + 1)
        .map_err(|_| "FP conversion size overflow")?;
    // Result-sized quotient plus carry-growth capacity; encoding modulus,
    // subtraction destination/growth and shrinking copy. There is NO rational
    // numerator/denominator here; RealPlan supplies only scalar dyadic metadata.
    let storage = cells
        .checked_mul(6 * 8)
        .and_then(|n| n.checked_add(256))
        .ok_or("FP conversion storage overflow")?;
    // Four possible all-ones exponent scans across planning/materialization,
    // and two trailing-zero fraction scans; price the fields independently.
    // The evaluator separately paid the first input inspection before planning.
    let scans = dyadic
        .value
        .exponent
        .occupied_bytes()
        .checked_mul(4)
        .and_then(|n| {
            dyadic
                .value
                .fraction
                .occupied_bytes()
                .checked_mul(2)
                .and_then(|fraction| n.checked_add(fraction))
        })
        .ok_or("FP conversion scan overflow")?;
    let work = usize::try_from(width)
        .ok()
        .and_then(|n| n.checked_mul(8))
        .and_then(|n| n.checked_add(scans))
        .and_then(|n| n.checked_add(64))
        .ok_or("FP conversion work overflow")?;
    Ok(BvPlan {
        dyadic,
        width,
        signedness,
        rm,
        work,
        storage,
    })
}

impl Field<'_> {
    fn shifted(self, shift: u64) -> BigUint {
        match self {
            Self::Native(n) => BigUint::from(
                u32::try_from(shift)
                    .ok()
                    .and_then(|s| n.checked_shr(s))
                    .unwrap_or(0),
            ),
            Self::Big(n) => n >> shift,
        }
    }
}

impl BvPlan<'_> {
    /// Called only after original owner work/storage admission. Intermediates
    /// are bounded by the target width even when declared FP precision is huge.
    pub(crate) fn materialize(self) -> Result<ModelValue, String> {
        let v = &self.dyadic.value;
        if v.nan() || v.infinite() {
            return Err(UNDERSPECIFIED.into());
        }
        if v.zero() {
            return Ok(ModelValue::BitVec {
                value: BigInt::zero(),
                width: self.width,
            });
        }
        let normal = !v.exponent.zero();
        let hidden = u64::from(v.sb - 1);
        let occupied = if normal {
            hidden + 1
        } else {
            match v.fraction {
                Field::Native(n) => u64::from(128 - n.leading_zeros()),
                Field::Big(n) => n.bits(),
            }
        };
        let cancelled = u64::from(self.dyadic.cancelled);
        let reduced_bits = occupied
            .checked_sub(cancelled)
            .ok_or("FP cancellation overflow")?;
        let integer_bits = i128::from(reduced_bits) + i128::from(self.dyadic.shift);
        // Even truncation is out of range. Prove that before copying a single
        // input limb; no huge intermediate is needed to establish this residue.
        if integer_bits > i128::from(self.width) {
            return Err(UNDERSPECIFIED.into());
        }
        let discarded = self.dyadic.shift.unsigned_abs() * u64::from(self.dyadic.shift < 0);
        let cut = cancelled
            .checked_add(discarded)
            .ok_or("FP conversion shift overflow")?;
        let mut q = v.fraction.shifted(cut);
        if normal && hidden >= cut {
            q += BigUint::one() << (hidden - cut);
        }
        if self.dyadic.shift > 0 {
            q <<= self.dyadic.shift as u64;
        }
        let (guard, sticky) = if cut == 0 {
            (false, false)
        } else {
            super::discarded_bits(
                v.fraction,
                cut,
                normal.then_some(hidden),
                v.fraction.trailing(),
            )
        };
        if super::round_increment(self.rm, v.sign, guard, sticky, q.bit(0)) {
            q += BigUint::one();
        }
        let fits = if matches!(self.signedness, Signedness::Unsigned) {
            (!v.sign || q.is_zero()) && q.bits() <= u64::from(self.width)
        } else {
            q.bits() < u64::from(self.width)
                || v.sign
                    && q.bits() == u64::from(self.width)
                    && q.trailing_zeros() == Some(u64::from(self.width - 1))
        };
        if !fits {
            return Err(UNDERSPECIFIED.into());
        }
        let encoded = if v.sign && !q.is_zero() {
            (BigUint::one() << self.width) - q
        } else {
            q
        };
        Ok(ModelValue::BitVec {
            value: BigInt::from(encoded),
            width: self.width,
        })
    }
}
