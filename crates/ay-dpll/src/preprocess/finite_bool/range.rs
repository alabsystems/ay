// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) struct Range {
    pub(super) lo: BigInt,
    pub(super) hi: BigInt,
    /// Every source value covered here is nonzero, including disjoint choices
    /// whose interval hull alone contains zero.
    pub(super) nonzero: bool,
}

#[derive(Clone, Copy)]
pub(super) enum DivisionResult {
    Quotient,
    Remainder,
}

/// Pre-admit occupied operands and a conservative result/scratch envelope.
/// Integer multiplication is priced quadratically in occupied machine words;
/// other arithmetic and comparisons linearly. No new width allowance exists.
pub(super) fn pay_binary(a: u64, b: u64, multiply: bool, owner: &CountedAdmission) -> Result<()> {
    let words_a = usize::try_from(a.div_ceil(64))
        .map_err(|_| overflow(owner))?
        .max(1);
    let words_b = usize::try_from(b.div_ceil(64))
        .map_err(|_| overflow(owner))?
        .max(1);
    let work = if multiply {
        words_a.checked_mul(words_b)
    } else {
        words_a.checked_add(words_b)
    }
    .ok_or_else(|| overflow(owner))?;
    let bytes = words_a
        .checked_add(words_b)
        .and_then(|n| n.checked_add(2))
        .and_then(|n| n.checked_mul(32))
        .ok_or_else(|| overflow(owner))?;
    owner.admit(work.checked_add(1).ok_or_else(|| overflow(owner))?, bytes)?;
    Ok(())
}

pub(super) fn paid_copy(value: &BigInt, owner: &CountedAdmission) -> Result<BigInt> {
    pay_binary(value.bits(), 0, false, owner)?;
    Ok(value.clone())
}

impl Range {
    fn owned(lo: BigInt, hi: BigInt, nonzero: bool) -> Self {
        let nonzero = nonzero || lo.is_positive() || hi.is_negative();
        Self { lo, hi, nonzero }
    }
    pub(super) fn between(lo: &BigInt, hi: &BigInt, owner: &CountedAdmission) -> Result<Self> {
        Ok(Self::owned(
            paid_copy(lo, owner)?,
            paid_copy(hi, owner)?,
            false,
        ))
    }
    pub(super) fn point(value: &BigInt, owner: &CountedAdmission) -> Result<Self> {
        Ok(Self::owned(
            paid_copy(value, owner)?,
            paid_copy(value, owner)?,
            !value.is_zero(),
        ))
    }
    pub(super) fn copied(&self, owner: &CountedAdmission) -> Result<Self> {
        Ok(Self {
            lo: paid_copy(&self.lo, owner)?,
            hi: paid_copy(&self.hi, owner)?,
            nonzero: self.nonzero,
        })
    }
    pub(super) fn hull(&self, other: &Self, owner: &CountedAdmission) -> Result<Self> {
        pay_binary(self.lo.bits(), other.lo.bits(), false, owner)?;
        pay_binary(self.hi.bits(), other.hi.bits(), false, owner)?;
        Ok(Self::owned(
            paid_copy(std::cmp::min(&self.lo, &other.lo), owner)?,
            paid_copy(std::cmp::max(&self.hi, &other.hi), owner)?,
            self.nonzero && other.nonzero,
        ))
    }
    pub(super) fn negated(&self, owner: &CountedAdmission) -> Result<Self> {
        Ok(Self::owned(
            -paid_copy(&self.hi, owner)?,
            -paid_copy(&self.lo, owner)?,
            self.nonzero,
        ))
    }
    pub(super) fn add(&self, other: &Self, owner: &CountedAdmission) -> Result<Self> {
        pay_binary(self.lo.bits(), other.lo.bits(), false, owner)?;
        let lo = &self.lo + &other.lo;
        pay_binary(self.hi.bits(), other.hi.bits(), false, owner)?;
        Ok(Self::owned(lo, &self.hi + &other.hi, false))
    }
    pub(super) fn sub(&self, other: &Self, owner: &CountedAdmission) -> Result<Self> {
        pay_binary(self.lo.bits(), other.hi.bits(), false, owner)?;
        let lo = &self.lo - &other.hi;
        pay_binary(self.hi.bits(), other.lo.bits(), false, owner)?;
        Ok(Self::owned(lo, &self.hi - &other.lo, false))
    }
    pub(super) fn mul(&self, other: &Self, owner: &CountedAdmission) -> Result<Self> {
        let mut values = Vec::new();
        reserve_counted(&mut values, 4, owner)?;
        for a in [&self.lo, &self.hi] {
            for b in [&other.lo, &other.hi] {
                pay_binary(a.bits(), b.bits(), true, owner)?;
                values.push(a * b);
            }
        }
        let mut lo = 0;
        let mut hi = 0;
        for i in 1..4 {
            pay_binary(values[i].bits(), values[lo].bits(), false, owner)?;
            if values[i] < values[lo] {
                lo = i;
            }
            pay_binary(values[i].bits(), values[hi].bits(), false, owner)?;
            if values[i] > values[hi] {
                hi = i;
            }
        }
        Ok(Self::owned(
            paid_copy(&values[lo], owner)?,
            paid_copy(&values[hi], owner)?,
            self.nonzero && other.nonzero,
        ))
    }
    fn max_abs(&self, owner: &CountedAdmission) -> Result<BigInt> {
        let lo = paid_copy(&self.lo, owner)?.abs();
        let hi = paid_copy(&self.hi, owner)?.abs();
        pay_binary(lo.bits(), hi.bits(), false, owner)?;
        Ok(std::cmp::max(lo, hi))
    }

    /// Euclidean division has |q| <= |a| for integral nonzero b, and
    /// 0 <= mod(a,b) < |b|. These conservative covers avoid pointwise source
    /// enumeration. See https://smt-lib.org/theories-Ints.shtml.
    pub(super) fn divided(
        &self,
        divisor: &Self,
        result: DivisionResult,
        owner: &CountedAdmission,
    ) -> Result<Self> {
        if !divisor.nonzero {
            return Err(Error::Unsupported);
        }
        if matches!(result, DivisionResult::Remainder) {
            let magnitude = divisor.max_abs(owner)?;
            pay_binary(magnitude.bits(), 1, false, owner)?;
            Ok(Self::owned(
                BigInt::zero(),
                magnitude - BigInt::one(),
                false,
            ))
        } else {
            let magnitude = self.max_abs(owner)?;
            let lower = -paid_copy(&magnitude, owner)?;
            Ok(Self::owned(lower, magnitude, false))
        }
    }
    pub(super) fn width(&self) -> Result<u32> {
        u32::try_from(self.lo.bits().max(self.hi.bits()))
            .ok()
            .and_then(|bits| bits.checked_add(1))
            .ok_or(Error::Unsupported)
    }
}
