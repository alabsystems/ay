// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pinned hashbrown 0.15.5 group-work bound; no new resource allowance.
//!
//! The exact allocated layout authenticates B and g, including tombstones.
//! Each insertion completes one previously unprocessed item even through
//! in-place swaps. At step j at most floor(j/g) groups can be entirely FULL.
//! See the development design notes for the source bound.

use super::{limit, product, Result, TermId};
use std::mem::{align_of, size_of};

pub(super) fn scans(allocation: usize, len: usize) -> Result<usize> {
    checked_scans(
        allocation,
        len,
        size_of::<(u64, Vec<TermId>)>(),
        align_of::<(u64, Vec<TermId>)>(),
    )
}

fn checked_scans(allocation: usize, len: usize, size: usize, align: usize) -> Result<usize> {
    if size != 32 || align != 8 {
        return Err(limit());
    }
    if allocation == 0 {
        return if len == 0 { Ok(100) } else { Err(limit()) };
    }
    let (buckets, group) = geometry(allocation, len)?;
    let mut probes = group_probes(len, group)?;
    if buckets < group {
        // Small tables may load one additional aligned correction group.
        probes = probes.checked_add(len).ok_or_else(limit)?;
    }
    let bulk = product(buckets, 3)?.checked_add(96).ok_or_else(limit)?;
    // Two original 128-unit bundles per group: packed control processing and
    // scalar selection/probe advancement. This is not a CPU timing claim.
    bulk.checked_add(product(probes, 2)?)
        .and_then(|n| n.checked_add(len.checked_mul(32)?))
        .ok_or_else(limit)
}

fn geometry(allocation: usize, len: usize) -> Result<(usize, usize)> {
    // TableLayout: 32*B needs no padding; L=32*B+B+g=33*B+g.
    // g is a Group width from the pinned dispatch, not a user chosen mode.
    let buckets = allocation / 33;
    let group = allocation % 33;
    if buckets < 4 || !buckets.is_power_of_two() || !matches!(group, 4 | 8 | 16) {
        return Err(limit());
    }
    let ctrl_align = group.max(8);
    if allocation > (isize::MAX as usize) - (ctrl_align - 1) {
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

fn group_probes(len: usize, group: usize) -> Result<usize> {
    if !matches!(group, 4 | 8 | 16) {
        return Err(limit());
    }
    let quotient = len / group;
    let remainder = len % group;
    let previous = quotient.saturating_sub(1);
    // Divide before multiplying; all subsequent products/sums are checked.
    let triangle = if quotient % 2 == 0 {
        product(quotient / 2, previous)?
    } else {
        product(quotient, previous / 2)?
    };
    product(group, triangle)?
        .checked_add(product(quotient, remainder)?)
        .and_then(|n| n.checked_add(len))
        .ok_or_else(limit)
}

#[cfg(test)]
mod tests;
