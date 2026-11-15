// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact unsigned model payloads. This boundary never applies modulo reduction
//! or interprets a negative integer as a signed bit-vector spelling. Widths
//! above 128 have one canonical BigBitVec carrier, even for the numeric zero.

use super::*;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::ToPrimitive;
use std::sync::Arc;

fn width_matches(width: u32, expected: u32) -> bool {
    width == expected && (1..=crate::MAX_BITVECTOR_WIDTH).contains(&width)
}

impl Codec<'_, '_> {
    pub(super) fn decode_bitvec(
        &mut self,
        value: &BigInt,
        width: u32,
        expected: u32,
    ) -> Option<SmtValue> {
        if !width_matches(width, expected)
            || value.sign() == Sign::Minus
            || value.bits() > u64::from(width)
        {
            return None;
        }
        if width <= 128 {
            return Some(SmtValue::BitVec(value.to_u128()?, width));
        }
        let limbs = usize::try_from(value.bits().div_ceil(64)).ok()?;
        self.control.charge(limbs.max(1))?;
        // Borrowed magnitude/sign/bit count checks precede the sole bigint
        // clone and Arc allocation. Zero never allocates a width-sized mask.
        let payload = limbs.checked_mul(8)?;
        let owned = payload
            .checked_add(std::mem::size_of::<BigUint>())?
            .checked_add(2 * std::mem::size_of::<usize>())?;
        self.copy(owned.checked_mul(2)?)?;
        Some(SmtValue::BigBitVec(
            Arc::new(value.magnitude().clone()),
            width,
        ))
    }

    pub(super) fn write_small_bitvec(
        &mut self,
        value: u128,
        width: u32,
        expected: u32,
    ) -> Option<()> {
        if !width_matches(width, expected) || width > 128 || 128 - value.leading_zeros() > width {
            return None;
        }
        // Fixed-size decimal formatting is bounded independently of width;
        // no shift by 128 or larger is used for unsigned range validation.
        self.copy(64)?;
        self.push(&format!("(_ bv{value} {width})"))
    }

    pub(super) fn write_big_bitvec(
        &mut self,
        value: &BigUint,
        width: u32,
        expected: u32,
    ) -> Option<()> {
        if !width_matches(width, expected) || width <= 128 || value.bits() > u64::from(width) {
            return None;
        }
        let width_bytes = usize::try_from(width).ok()?;
        let bytes = width_bytes.checked_add(2)?;
        self.text
            .len()
            .checked_add(bytes)
            .filter(|n| *n <= MAX_OUTPUT)?;
        self.control.charge(width_bytes.div_ceil(64))?;
        // A linear, width-exact binary spelling avoids opaque bigint decimal
        // conversion and its scratch. Charge retained output/capacity before
        // reserving; subsequent 64-bit batches allocate no temporary buffers.
        self.copy(bytes.checked_mul(2)?)?;
        self.text.try_reserve(bytes).ok()?;
        self.text.push_str("#b");
        let mut remaining = width;
        while remaining != 0 {
            self.control.poll()?;
            let next = remaining.saturating_sub(64);
            for bit in (next..remaining).rev() {
                self.text
                    .push(if value.bit(u64::from(bit)) { '1' } else { '0' });
            }
            remaining = next;
        }
        self.control.poll()
    }
}

#[cfg(test)]
mod tests;
