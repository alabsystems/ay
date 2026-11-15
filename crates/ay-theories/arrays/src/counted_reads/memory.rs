// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::hash::Hash;
use std::mem::size_of;

fn storage(owner: &CountedAdmission) -> Error {
    owner.refuse(CountedAdmissionError::StorageExhausted).into()
}
fn work(owner: &CountedAdmission) -> Error {
    owner.refuse(CountedAdmissionError::WorkExhausted).into()
}
pub(super) fn reserve<T>(out: &mut Vec<T>, extra: usize, owner: &CountedAdmission) -> Result<()> {
    owner.admit(extra.checked_mul(3).ok_or_else(|| work(owner))?, 0)?;
    let needed = out.len().checked_add(extra).ok_or_else(|| storage(owner))?;
    if needed <= out.capacity() {
        return Ok(());
    }
    let target = needed
        .max(
            out.capacity()
                .checked_mul(2)
                .ok_or_else(|| storage(owner))?,
        )
        .max(4);
    owner.admit(
        out.len(),
        target
            .checked_mul(size_of::<T>())
            .ok_or_else(|| storage(owner))?,
    )?;
    out.try_reserve_exact(target - out.len())
        .map_err(|_| storage(owner))
}
pub(super) fn push<T>(out: &mut Vec<T>, value: T, owner: &CountedAdmission) -> Result<()> {
    reserve(out, 1, owner)?;
    out.push(value);
    Ok(())
}
pub(super) fn filled<T: Copy>(count: usize, value: T, owner: &CountedAdmission) -> Result<Vec<T>> {
    let mut out = Vec::new();
    reserve(&mut out, count, owner)?;
    out.resize(count, value);
    Ok(out)
}
pub(super) fn map<K: Eq + Hash, V>(
    out: &mut DetHashMap<K, V>,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(3, 0)?;
    if out.len() < out.capacity() {
        return Ok(());
    }
    let target = out
        .capacity()
        .checked_mul(2)
        .ok_or_else(|| storage(owner))?
        .max(4);
    let bytes = size_of::<(K, V)>()
        .checked_add(32)
        .and_then(|n| n.checked_mul(4))
        .and_then(|n| n.checked_mul(target))
        .ok_or_else(|| storage(owner))?;
    owner.admit(
        out.len().checked_add(target).ok_or_else(|| work(owner))?,
        bytes,
    )?;
    out.try_reserve(target - out.len())
        .map_err(|_| storage(owner))
}
