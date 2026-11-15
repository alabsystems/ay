// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fallible storage operations sharing the invocation's original owner.

use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

pub(crate) type Result<T> = std::result::Result<T, CountedAdmissionError>;

/// Admit the entire replacement allocation and relocation before requesting it.
pub(crate) fn try_reserve<T>(
    owner: &CountedAdmission,
    values: &mut Vec<T>,
    additional: usize,
) -> Result<()> {
    owner.admit(1, 0)?;
    let required = values
        .len()
        .checked_add(additional)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    if required <= values.capacity() {
        return Ok(());
    }
    let doubled = values
        .capacity()
        .checked_mul(2)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    // Match RawVec's ordinary amortized-growth floor. Capacities feed solver
    // memory heuristics, so an arbitrary minimum could alter search cadence.
    let element_bytes = std::mem::size_of::<T>();
    let minimum = if element_bytes == 1 {
        8
    } else if element_bytes <= 1024 {
        4
    } else {
        1
    };
    let target = required.max(doubled).max(minimum);
    let bytes = target
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    let work = target
        .checked_add(values.len())
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, bytes)?;
    values
        .try_reserve_exact(target - values.len())
        .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))
}

/// Match an ordinary initial `Vec::with_capacity` reservation exactly.
pub(crate) fn try_reserved_exact<T>(owner: &CountedAdmission, capacity: usize) -> Result<Vec<T>> {
    owner.admit(1, 0)?;
    let bytes = capacity
        .checked_mul(std::mem::size_of::<T>())
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    owner.admit(capacity, bytes)?;
    let mut values = Vec::new();
    values
        .try_reserve_exact(capacity)
        .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    Ok(values)
}

/// Construct each bounded, nonallocating element only after its admission.
/// The caller supplies any separate admission needed by an allocating value.
pub(crate) fn try_vec_with<T>(
    owner: &CountedAdmission,
    len: usize,
    mut make: impl FnMut(usize) -> T,
) -> Result<Vec<T>> {
    let mut values = try_reserved_exact(owner, len)?;
    for index in 0..len {
        owner.admit(1, std::mem::size_of::<T>())?;
        values.push(make(index));
    }
    Ok(values)
}

pub(crate) fn checked_double(owner: &CountedAdmission, value: usize) -> Result<usize> {
    owner.admit(1, 0)?;
    value
        .checked_mul(2)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))
}

#[cfg(test)]
pub(crate) fn test_owner(work: u64, storage: usize) -> CountedAdmission {
    CountedAdmission::new(
        ay_core::original_query::FiniteAdmissionGrant::new(work, storage),
        None,
        std::sync::Arc::new(|| false),
    )
    .unwrap()
}

#[cfg(test)]
mod tests;
