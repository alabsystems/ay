// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{CountedAdmission, CountedAdmissionError, Literal, Result};

pub(super) fn reserve_append<T>(
    values: &mut Vec<T>,
    additional: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(1, 0)?;
    let required = values
        .len()
        .checked_add(additional)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    if required <= values.capacity() {
        return Ok(());
    }
    let capacity = values
        .capacity()
        .checked_mul(2)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let target = required.max(capacity).max(4);
    let bytes = target
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let work = target
        .checked_add(values.len())
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    // Geometric growth keeps repeated small clauses amortized linear. Price
    // the new allocation and possible relocation before asking the allocator.
    owner.admit(work, bytes)?;
    values
        .try_reserve_exact(target - values.len())
        .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))
}

pub(super) fn append_literals(
    target: &mut Vec<Literal>,
    source: &[Literal],
    owner: &CountedAdmission,
) -> Result<()> {
    reserve_append(target, source.len(), owner)?;
    for literal in source {
        owner.admit(1, std::mem::size_of::<Literal>())?;
        target.push(*literal);
    }
    Ok(())
}
