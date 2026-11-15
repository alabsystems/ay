// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fallible geometric growth, charged BEFORE allocation/rehashing/copying.
//! These are cumulative logical-storage charges, not a promise about allocator
//! metadata or RSS. Ambient memory authorities remain independently enforced.

use std::hash::Hash;
use std::mem::size_of;

use ay_core::kani_compat::DetHashMap;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

use super::{Error, Result};

fn storage(owner: &CountedAdmission) -> Error {
    Error::Stopped(owner.refuse(CountedAdmissionError::StorageExhausted))
}

fn capacity(len: usize, old: usize, extra: usize, owner: &CountedAdmission) -> Result<usize> {
    let needed = len.checked_add(extra).ok_or_else(|| storage(owner))?;
    if needed <= old {
        return Ok(old);
    }
    Ok(needed
        .max(old.checked_mul(2).ok_or_else(|| storage(owner))?)
        .max(4))
}

pub(super) fn vector<T>(value: &mut Vec<T>, extra: usize, owner: &CountedAdmission) -> Result<()> {
    let next = capacity(value.len(), value.capacity(), extra, owner)?;
    if next == value.capacity() {
        return Ok(());
    }
    let bytes = next
        .checked_mul(size_of::<T>())
        .ok_or_else(|| storage(owner))?;
    owner.admit(value.len(), bytes)?;
    value
        .try_reserve_exact(next - value.len())
        .map_err(|_| storage(owner))
}

pub(super) fn map<K: Eq + Hash, V>(
    value: &mut DetHashMap<K, V>,
    extra: usize,
    owner: &CountedAdmission,
) -> Result<()> {
    let next = capacity(value.len(), value.capacity(), extra, owner)?;
    if next == value.capacity() {
        return Ok(());
    }
    // Charge a conservative logical bucket envelope and the existing entries
    // that growth can rehash. Successful lookups/inserts are charged by callers.
    let bytes = size_of::<(K, V)>()
        .checked_add(32)
        .and_then(|size| size.checked_mul(4))
        .and_then(|size| size.checked_mul(next))
        .ok_or_else(|| storage(owner))?;
    owner.admit(value.len(), bytes)?;
    value
        .try_reserve(next - value.len())
        .map_err(|_| storage(owner))
}
