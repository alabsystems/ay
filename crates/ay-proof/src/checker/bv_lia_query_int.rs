// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded owned-integer operations for the independent BV/LIA interpreter.

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive};

use super::{
    bv_mask, BvLiaUnsatAuthenticationError, QueryChecker, MAX_INTEGER_BITS, MAX_LIVE_INTEGER_LIMBS,
};

pub(super) fn integer_limb_units(value: &BigInt) -> u64 {
    value.bits().div_ceil(64).max(1)
}

impl QueryChecker<'_> {
    pub(super) fn ensure_integer_magnitude(
        &self,
        value: &BigInt,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        if value.bits() > MAX_INTEGER_BITS {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer magnitude",
            });
        }
        Ok(())
    }

    pub(super) fn clone_bounded_int(
        &mut self,
        value: &BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(value)?;
        self.meter.charge(integer_limb_units(value))?;
        Ok(value.clone())
    }

    pub(super) fn clone_retained_int(
        &mut self,
        value: &BigInt,
        concurrent_int_limbs: u64,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(value)?;
        self.meter.charge(integer_limb_units(value))?;
        let retained = self.preflight_retained_integer(None, value, concurrent_int_limbs)?;
        let clone = value.clone();
        self.retained_int_limbs = retained;
        Ok(clone)
    }

    pub(super) fn preflight_retained_integer(
        &self,
        replaced: Option<&BigInt>,
        value: &BigInt,
        concurrent_int_limbs: u64,
    ) -> Result<u64, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(value)?;
        let replaced_limbs = replaced.map(integer_limb_units).unwrap_or(0);
        let retained = self
            .retained_int_limbs
            .checked_sub(replaced_limbs)
            .and_then(|limbs| limbs.checked_add(integer_limb_units(value)))
            .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer storage accounting",
            })?;
        let total = retained.checked_add(concurrent_int_limbs).ok_or(
            BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer storage accounting",
            },
        )?;
        if total > MAX_LIVE_INTEGER_LIMBS {
            return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "live integer storage",
            });
        }
        Ok(retained)
    }

    pub(super) fn add_bounded_ints(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.charge_linear_integer_op(left, right)?;
        let result = left + right;
        self.ensure_integer_magnitude(&result)?;
        Ok(result)
    }

    pub(super) fn subtract_bounded_ints(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.charge_linear_integer_op(left, right)?;
        let result = left - right;
        self.ensure_integer_magnitude(&result)?;
        Ok(result)
    }

    fn charge_linear_integer_op(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(left)?;
        self.ensure_integer_magnitude(right)?;
        self.meter
            .charge(integer_limb_units(left).max(integer_limb_units(right)))
    }

    pub(super) fn charge_integer_comparison(
        &mut self,
        left: &BigInt,
        right: &BigInt,
    ) -> Result<(), BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(left)?;
        self.ensure_integer_magnitude(right)?;
        self.meter
            .charge(integer_limb_units(left).max(integer_limb_units(right)))
    }

    pub(super) fn negate_bounded_int(
        &mut self,
        value: BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(&value)?;
        self.meter.charge(integer_limb_units(&value))?;
        let result = -value;
        self.ensure_integer_magnitude(&result)?;
        Ok(result)
    }

    pub(super) fn abs_bounded_int(
        &mut self,
        value: BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(&value)?;
        self.meter.charge(integer_limb_units(&value))?;
        let result = value.abs();
        self.ensure_integer_magnitude(&result)?;
        Ok(result)
    }

    pub(super) fn modulo_bounded_ints(
        &mut self,
        dividend: &BigInt,
        divisor: &BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(dividend)?;
        self.ensure_integer_magnitude(divisor)?;
        if !divisor.is_positive() {
            return Err(BvLiaUnsatAuthenticationError::UnsupportedFragment {
                reason: "integer modulus divisor must be positive".to_string(),
            });
        }
        let work = integer_limb_units(dividend)
            .checked_mul(integer_limb_units(divisor))
            .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                resource: "integer division accounting",
            })?;
        self.meter.charge(work.max(1))?;
        let mut residue = dividend % divisor;
        if residue.is_negative() {
            residue = self.add_bounded_ints(&residue, divisor)?;
        }
        self.ensure_integer_magnitude(&residue)?;
        Ok(residue)
    }

    pub(super) fn residue_bounded_int(
        &mut self,
        value: &BigInt,
        width: u32,
    ) -> Result<Option<u64>, BvLiaUnsatAuthenticationError> {
        if width == 0 || width > 64 {
            return Ok(None);
        }
        self.ensure_integer_magnitude(value)?;
        let modulus = BigInt::one() << width;
        let residue = self.modulo_bounded_ints(value, &modulus)?;
        Ok(residue.to_u64().map(|value| value & bv_mask(width)))
    }

    pub(super) fn multiply_bounded_ints(
        &mut self,
        left: BigInt,
        right: BigInt,
    ) -> Result<BigInt, BvLiaUnsatAuthenticationError> {
        self.ensure_integer_magnitude(&left)?;
        self.ensure_integer_magnitude(&right)?;
        let left_bits = left.bits();
        let right_bits = right.bits();
        if left_bits != 0 && right_bits != 0 {
            let minimum_result_bits = left_bits
                .checked_add(right_bits)
                .and_then(|sum| sum.checked_sub(1))
                .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "integer magnitude accounting",
                })?;
            if minimum_result_bits > MAX_INTEGER_BITS {
                return Err(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "integer magnitude",
                });
            }
            let work = integer_limb_units(&left)
                .checked_mul(integer_limb_units(&right))
                .ok_or(BvLiaUnsatAuthenticationError::ResourceLimit {
                    resource: "integer multiplication accounting",
                })?;
            self.meter.charge(work.max(1))?;
        } else {
            self.meter.charge(1)?;
        }
        let result = left * right;
        self.ensure_integer_magnitude(&result)?;
        Ok(result)
    }
}
