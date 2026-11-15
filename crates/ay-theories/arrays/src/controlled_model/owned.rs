// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::mem::{align_of, size_of};

pub(super) fn checked(
    value: Option<usize>,
    work: &mut WorkBudget<'_>,
) -> Result<usize, QueryError> {
    value.ok_or_else(|| work.refuse_exhaustion())
}

pub(super) fn reserve_vec<T>(
    count: usize,
    work: &mut WorkBudget<'_>,
) -> Result<Vec<T>, QueryError> {
    let bytes = checked(
        count
            .checked_mul(size_of::<T>())
            .and_then(|n| n.checked_mul(8))
            .and_then(|n| n.checked_add(4 * size_of::<Vec<T>>())),
        work,
    )?;
    let visits = checked(count.checked_mul(8).and_then(|n| n.checked_add(1)), work)?;
    work.admit(visits, bytes)?;
    let mut result = Vec::new();
    result
        .try_reserve_exact(count)
        .map_err(|_| work.refuse_exhaustion())?;
    work.charge(0)?;
    Ok(result)
}

pub(super) fn text(source: &str, work: &mut WorkBudget<'_>) -> Result<String, QueryError> {
    let bytes = checked(
        source
            .len()
            .checked_mul(8)
            .and_then(|n| n.checked_add(8 * size_of::<String>())),
        work,
    )?;
    let visits = checked(
        source.len().checked_mul(3).and_then(|n| n.checked_add(4)),
        work,
    )?;
    work.admit(visits, bytes)?;
    let mut result = String::new();
    result
        .try_reserve_exact(source.len())
        .map_err(|_| work.refuse_exhaustion())?;
    let mut begin = 0;
    while begin < source.len() {
        let mut end = begin.saturating_add(128).min(source.len());
        while !source.is_char_boundary(end) {
            end -= 1;
        }
        work.charge(end - begin + 4)?;
        // 128-byte windows lose at most three UTF-8 bytes at their boundary.
        let chunk = source
            .get(begin..end)
            .ok_or_else(|| work.refuse_exhaustion())?;
        result.push_str(chunk);
        begin = end;
    }
    work.charge(0)?;
    Ok(result)
}

pub(super) fn optional_text(
    source: Option<&str>,
    work: &mut WorkBudget<'_>,
) -> Result<Option<String>, QueryError> {
    source.map(|value| text(value, work)).transpose()
}

pub(super) fn interpretation(
    source: &ArrayInterpretation,
    work: &mut WorkBudget<'_>,
) -> Result<ArrayInterpretation, QueryError> {
    work.charge(0)?;
    let mut stores = reserve_vec(source.stores.len(), work)?;
    for (key, value) in &source.stores {
        stores.push((text(key, work)?, text(value, work)?));
    }
    let default = optional_text(source.default.as_deref(), work)?;
    let index_sort = sort::optional(source.index_sort.as_ref(), work)?;
    let element_sort = sort::optional(source.element_sort.as_ref(), work)?;
    Ok(ArrayInterpretation {
        default,
        stores,
        index_sort,
        element_sort,
    })
}

// Pinned hashbrown 0.15.5: capacity_to_buckets <=4n+32; table layout adds
// <=max(align(T),16)-1 padding and 16 control bytes. Fresh reservations only.
// Borrowed source backing is charged separately BEFORE iterator bucket scans.
fn buckets(count: usize, work: &mut WorkBudget<'_>) -> Result<usize, QueryError> {
    if size_of::<usize>() > 8 {
        return Err(work.refuse_exhaustion());
    }
    // Also cover tiny/ZST minimum tables and the static empty group's scan.
    checked(count.checked_mul(4).and_then(|n| n.checked_add(32)), work)
}

pub(super) fn scan_table<T>(
    allocation_bytes: usize,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    if size_of::<usize>() > 8 {
        return Err(work.refuse_exhaustion());
    }
    // Pinned hashbrown raw::TableLayout: allocation >= buckets * size_of(T).
    // capacity() is items + growth_left: tombstones can lower it without
    // shrinking the backing. This bounds visits, not RSS or a new byte grant.
    // Checked division refuses ZST callers; native map/set entries contain TermId.
    let bound = checked(
        allocation_bytes
            .checked_div(size_of::<T>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    let visits = checked(bound.checked_mul(8).and_then(|n| n.checked_add(1)), work)?;
    work.charge(visits)
}

pub(super) fn reserve_table<T>(
    count: usize,
    work: &mut WorkBudget<'_>,
) -> Result<usize, QueryError> {
    let bound = buckets(count, work)?;
    let bytes = checked(
        size_of::<T>()
            .checked_add(1)
            .and_then(|size| bound.checked_mul(size))
            .and_then(|n| n.checked_add(align_of::<T>().max(16)))
            .and_then(|n| n.checked_add(16))
            .and_then(|n| n.checked_mul(4)),
        work,
    )?;
    let visits = checked(bound.checked_mul(16).and_then(|n| n.checked_add(1)), work)?;
    work.admit(visits, bytes)?;
    Ok(bound)
}

pub(super) fn table_insert(bound: usize, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    let visits = checked(bound.checked_mul(8).and_then(|n| n.checked_add(512)), work)?;
    // TermId hashing/equality is fixed scalar; even a worst-case full probe
    // cannot scan more than the reserved buckets before its empty sentinel.
    work.charge(visits)
}

pub(super) fn finish<T>(
    result: Result<T, QueryError>,
    work: &mut WorkBudget<'_>,
) -> Result<T, QueryError> {
    match result {
        Err(error) => {
            let _ = work.charge(0);
            Err(error)
        }
        Ok(value) => match work.charge(0) {
            Ok(()) => Ok(value),
            Err(error) => {
                drop(value);
                let _ = work.charge(0);
                Err(error)
            }
        },
    }
}
