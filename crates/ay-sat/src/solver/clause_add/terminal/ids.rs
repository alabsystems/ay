// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

// Same deterministic hashbrown set and insertion order as ordinary replay.
// Conservative bucket/control/alignment bounds match the admitted Literal set.
pub(super) fn new(len: usize, owner: &CountedAdmission) -> AdmissionResult<DetHashSet<u64>> {
    owner.admit(8, 0)?;
    let buckets = reserved_buckets(len)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let bytes = buckets
        .checked_mul(size_of::<u64>() + 1)
        .and_then(|n| n.checked_add(31))
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let work = bytes
        .checked_mul(2)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, bytes)?;
    let mut values = crate::kani_compat::det_hash_set_new();
    values
        .try_reserve(len)
        .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    if values.allocation_size() > bytes || values.capacity() < len {
        return Err(invalid(
            owner,
            "counted terminal ID filter exceeds admitted layout",
        ));
    }
    Ok(values)
}

pub(super) fn probe(values: &DetHashSet<u64>, owner: &CountedAdmission) -> AdmissionResult<()> {
    let work = values
        .capacity()
        .checked_mul(16)
        .and_then(|n| n.checked_add(64))
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, 0)
}

// hashbrown 0.15.5 raw::capacity_to_buckets: tables below 15 entries
// need an empty bucket, including at capacity 4. Literal and u64 both have
// element sizes >=4, so their minimum is four buckets for every supported
// 8/16-byte control group. Keep the existing conservative empty-set charge.
fn reserved_buckets(len: usize) -> Option<usize> {
    if len < 15 {
        return Some(if len < 4 {
            4
        } else if len < 8 {
            8
        } else {
            16
        });
    }
    len.checked_mul(8)
        .map(|n| n / 7)
        .and_then(usize::checked_next_power_of_two)
}

#[cfg(test)]
mod tests;
