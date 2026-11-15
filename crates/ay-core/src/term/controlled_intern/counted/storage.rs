// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::mem::size_of;

pub(in crate::term::controlled_intern) fn work(
    owner: &dyn TermConstructionAdmission,
) -> CountedTermError {
    owner.refuse(CountedAdmissionError::WorkExhausted).into()
}

pub(in crate::term::controlled_intern) fn storage(
    owner: &dyn TermConstructionAdmission,
) -> CountedTermError {
    owner.refuse(CountedAdmissionError::StorageExhausted).into()
}

pub(in crate::term::controlled_intern) fn reserve<T>(
    values: &mut Vec<T>,
    extra: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<()> {
    let Some(target) = capacity(
        values.len(),
        values.capacity(),
        extra,
        size_of::<T>(),
        owner,
    )?
    else {
        return Ok(());
    };
    values
        .try_reserve_exact(target - values.len())
        .map_err(|_| storage(owner))
}

pub(super) fn reserve_string(
    value: &mut String,
    extra: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<()> {
    let Some(target) = capacity(value.len(), value.capacity(), extra, 1, owner)? else {
        return Ok(());
    };
    value
        .try_reserve_exact(target - value.len())
        .map_err(|_| storage(owner))
}

fn capacity(
    len: usize,
    current: usize,
    extra: usize,
    element: usize,
    owner: &dyn TermConstructionAdmission,
) -> Result<Option<usize>> {
    let required = len.checked_add(extra).ok_or_else(|| storage(owner))?;
    if required <= current {
        return Ok(None);
    }
    let target = required
        .max(current.checked_mul(2).ok_or_else(|| storage(owner))?)
        .max(4);
    let bytes = target.checked_mul(element).ok_or_else(|| storage(owner))?;
    owner.admit(len.checked_add(target).ok_or_else(|| work(owner))?, bytes)?;
    Ok(Some(target))
}

pub(super) fn text(source: &str, owner: &dyn TermConstructionAdmission) -> Result<String> {
    owner.admit(
        source.len().checked_add(1).ok_or_else(|| work(owner))?,
        source.len(),
    )?;
    let mut result = String::new();
    result
        .try_reserve_exact(source.len())
        .map_err(|_| storage(owner))?;
    result.push_str(source);
    Ok(result)
}
