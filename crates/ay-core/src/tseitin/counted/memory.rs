// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn work(owner: &CountedAdmission) -> Error {
    owner.refuse(CountedAdmissionError::WorkExhausted).into()
}
pub(super) fn storage(owner: &CountedAdmission) -> Error {
    owner.refuse(CountedAdmissionError::StorageExhausted).into()
}
pub(super) fn reserve<T>(out: &mut Vec<T>, extra: usize, owner: &CountedAdmission) -> Result<()> {
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
    let bytes = target
        .checked_mul(size_of::<T>())
        .ok_or_else(|| storage(owner))?;
    owner.admit(
        target.checked_add(out.len()).ok_or_else(|| work(owner))?,
        bytes,
    )?;
    out.try_reserve_exact(target - out.len())
        .map_err(|_| storage(owner))
}
pub(super) fn filled<T: Copy>(len: usize, value: T, owner: &CountedAdmission) -> Result<Vec<T>> {
    let mut out = Vec::new();
    reserve(&mut out, len, owner)?;
    owner.admit(len, 0)?;
    out.resize(len, value);
    Ok(out)
}
pub(super) fn copy<T: Copy>(source: &[T], owner: &CountedAdmission) -> Result<Vec<T>> {
    let mut out = Vec::new();
    reserve(&mut out, source.len(), owner)?;
    owner.admit(source.len(), 0)?;
    out.extend_from_slice(source);
    Ok(out)
}
pub(super) fn push<T>(out: &mut Vec<T>, value: T, owner: &CountedAdmission) -> Result<()> {
    reserve(out, 1, owner)?;
    owner.admit(1, 0)?;
    out.push(value);
    Ok(())
}
