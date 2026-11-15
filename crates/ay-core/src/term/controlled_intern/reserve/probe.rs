// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Full allocated-domain fixed-u64 lookup bound for hashbrown 0.15.5.
//! No length-only probe estimate, new allowance, or average-case assumption.

use super::{limit, product, Result, TermId};
use std::mem::{align_of, size_of};

pub(super) fn work(allocation: usize, len: usize) -> Result<usize> {
    checked_work(
        allocation,
        len,
        size_of::<(u64, Vec<TermId>)>(),
        align_of::<(u64, Vec<TermId>)>(),
    )
}

fn checked_work(allocation: usize, len: usize, size: usize, align: usize) -> Result<usize> {
    if size != 32 || align != 8 {
        return Err(limit());
    }
    if allocation == 0 {
        return if len == 0 { Ok(640) } else { Err(limit()) };
    }
    let (buckets, group) = geometry(allocation, len)?;
    let (groups, candidates) = if buckets < group {
        // One initial padded group plus the insertion-only aligned correction.
        // At most two stored tag copies per FULL entry; never discount mirrors.
        (2, product(len, 2)?)
    } else {
        // Tombstones can eliminate EMPTY tags in every earlier group even at
        // small len. The entire allocated partition, not len/group, is prepaid.
        (buckets / group, len)
    };
    product(groups, 128)?
        .checked_add(product(candidates, 32)?)
        .and_then(|n| n.checked_add(512))
        .ok_or_else(limit)
}

fn geometry(allocation: usize, len: usize) -> Result<(usize, usize)> {
    // Pinned TableLayout, tuple size32/align8: L=32B+B+g=33B+g.
    let buckets = allocation / 33;
    let group = allocation % 33;
    if buckets < 4 || !buckets.is_power_of_two() || !matches!(group, 4 | 8 | 16) {
        return Err(limit());
    }
    if allocation > (isize::MAX as usize) - (group.max(8) - 1) {
        return Err(limit());
    }
    let capacity = if buckets <= 8 {
        buckets - 1
    } else {
        product(buckets / 8, 7)?
    };
    if len > capacity {
        return Err(limit());
    }
    Ok((buckets, group))
}

#[cfg(test)]
mod tests;
