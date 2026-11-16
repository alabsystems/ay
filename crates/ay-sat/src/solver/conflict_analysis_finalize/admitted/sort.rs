// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Keep ordinary unstable sorting exactly, including equal-key ghost order.
//! The sealed core ipnsort has at most 2*floor(log2(n)) partition levels,
//! small-sort leaves <=32, then heapsort. Prepay a conservative per-element
//! bound for those passes and logical recursion frames; no heap allocation
//! occurs in sort_unstable. This is a bound, not an exact comparator count.
//! Reference: Trust library/core/src/slice/sort/{unstable,shared/smallsort}.

use super::*;

pub(super) fn prepay_unstable(len: usize, owner: &CountedAdmission) -> AdmissionResult<()> {
    let levels = len.bit_width() as usize + 1;
    let work = len
        .checked_mul(levels)
        .and_then(|n| n.checked_mul(64))
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    let bytes = levels
        .checked_mul(256)
        .and_then(|frames| frames.checked_add(4096))
        .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
    owner.admit(work, bytes)
}

/// Bottom-up stable mergesort (Knuth, TAOCP vol. 3, section 5.2.4).
/// One fallible scratch allocation; exact descending level and stable ties.
/// Every pass is O(n), never a quadratic wide-clause insertion sort.
pub(super) fn stable_by_level(
    values: &mut [Literal],
    data: &[VarData],
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    owner.admit(1, 0)?;
    let len = values.len();
    if len < 2 {
        return Ok(());
    }
    let mut scratch = crate::counted_storage::try_reserved_exact(owner, len)?;
    owner.admit(len, 0)?;
    scratch.extend_from_slice(values);
    let mut width = 1usize;
    while width < len {
        owner.admit(len, 0)?;
        scratch.copy_from_slice(values);
        let mut start = 0;
        while start < len {
            owner.admit(1, 0)?;
            let mid = start.saturating_add(width).min(len);
            let end = mid.saturating_add(width).min(len);
            merge(values, &scratch, data, start, mid, end, owner)?;
            start = end;
        }
        width = width.saturating_mul(2);
    }
    owner.check()
}

fn merge(
    values: &mut [Literal],
    source: &[Literal],
    data: &[VarData],
    start: usize,
    mid: usize,
    end: usize,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    let (mut left, mut right) = (start, mid);
    for slot in &mut values[start..end] {
        owner.admit(1, 0)?;
        let take_left = if right == end {
            true
        } else if left == mid {
            false
        } else {
            owner.admit(1, 0)?;
            data[source[left].variable().index()].level
                >= data[source[right].variable().index()].level
        };
        if take_left {
            *slot = source[left];
            left += 1;
        } else {
            *slot = source[right];
            right += 1;
        }
    }
    Ok(())
}
