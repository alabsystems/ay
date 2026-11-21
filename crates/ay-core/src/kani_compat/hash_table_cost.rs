// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked source-work prices for the pinned hashbrown 0.15.5/FixedState tables.
//!
//! This is accounting, not a resource owner or permission to perform a table
//! operation. Callers must admit the returned price before touching the table.
//! Layouts are recovered from the actual allocation, including retained empty
//! buckets/tombstones. Unknown layouts and arithmetic overflow return `None`.
//! This does not price arbitrary user `Hash`/`Eq` code: consumers here select
//! scalar fixed keys or String/str with the pinned FixedState hasher.

use std::mem::{align_of, size_of};

/// One existing 128-unit packed/scalar group bundle. No caller grant is changed.
const GROUP_FEE: usize = 128;

/// Admission for one `try_reserve(1)` on an actual table.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReserveCost {
    /// Work, including table controls, header moves and fixed-key hashing.
    pub work: usize,
    /// Old/new backing coexistence; payloads behind moved headers are not copied.
    pub storage_bytes: usize,
    /// Whether the reserve can hash old keys. Variable key payload is separate.
    pub rehashes: bool,
}

#[derive(Clone, Copy, Debug)]
struct Geometry {
    buckets: usize,
    group: usize,
    allocation: usize,
}

fn add(a: usize, b: usize) -> Option<usize> {
    a.checked_add(b)
}

fn mul(a: usize, b: usize) -> Option<usize> {
    a.checked_mul(b)
}

fn capacity(buckets: usize) -> Option<usize> {
    if buckets < 8 {
        buckets.checked_sub(1)
    } else {
        mul(buckets / 8, 7)
    }
}

fn allocation<T>(buckets: usize, group: usize) -> Option<usize> {
    let align = align_of::<T>().max(group);
    let data = mul(size_of::<T>(), buckets)?;
    let offset = add(data, align.checked_sub(1)?)? & !align.checked_sub(1)?;
    let bytes = add(add(offset, buckets)?, group)?;
    (bytes <= (isize::MAX as usize).checked_sub(align - 1)?).then_some(bytes)
}

// TableLayout can pad only small tables: for B>=16, size_of::<T>()*B is
// divisible by every pinned group width, as well as by align_of::<T>().
fn geometries<T>(
    bytes: usize,
    len: usize,
    mut visit: impl FnMut(Geometry) -> Option<()>,
) -> Option<()> {
    if size_of::<T>() == 0 || bytes == 0 {
        return None;
    }
    let mut found = false;
    for group in [4, 8, 16] {
        for buckets in [4, 8] {
            if len <= capacity(buckets)? && allocation::<T>(buckets, group) == Some(bytes) {
                visit(Geometry {
                    buckets,
                    group,
                    allocation: bytes,
                })?;
                found = true;
            }
        }
        let adjusted = bytes.checked_sub(group);
        if let Some(adjusted) = adjusted {
            let divisor = add(size_of::<T>(), 1)?;
            let buckets = adjusted / divisor;
            if adjusted % divisor == 0
                && buckets >= 16
                && buckets.is_power_of_two()
                && len <= capacity(buckets)?
                && allocation::<T>(buckets, group) == Some(bytes)
            {
                visit(Geometry {
                    buckets,
                    group,
                    allocation: bytes,
                })?;
                found = true;
            }
        }
    }
    found.then_some(())
}

fn search(g: Geometry, len: usize) -> Option<(usize, usize)> {
    if g.buckets < g.group {
        Some((2, mul(len, 2)?))
    } else {
        Some((g.buckets / g.group, len))
    }
}

fn lookup<T>(bytes: usize, len: usize, candidate: usize, header: usize) -> Option<usize> {
    if bytes == 0 {
        return (len == 0).then(|| header.checked_add(GROUP_FEE)).flatten();
    }
    let mut maximum = 0;
    geometries::<T>(bytes, len, |g| {
        let (groups, candidates) = search(g, len)?;
        let work = add(
            add(header, mul(groups, GROUP_FEE)?)?,
            mul(candidates, candidate)?,
        )?;
        maximum = maximum.max(work);
        Some(())
    })?;
    Some(maximum)
}

/// Full allocated-domain lookup/insert for scalar fixed keys (at most u64).
/// Includes tombstones, small-table mirrored candidates, hashing and geometry.
pub fn fixed_lookup<T>(bytes: usize, len: usize) -> Option<usize> {
    lookup::<T>(bytes, len, 32, 512)
}

/// Full lookup/insert for a borrowed string key, including one incoming hash.
/// Each possible equality visits both byte strings, bounded by incoming width.
pub fn string_lookup<T>(bytes: usize, len: usize, incoming_bytes: usize) -> Option<usize> {
    let candidate = add(64, mul(incoming_bytes, 2)?)?;
    let header = add(1024, string_hash_payload(incoming_bytes)?)?;
    lookup::<T>(bytes, len, candidate, header)
}

/// Sparse iteration price before a caller walks keys to inspect/hash metadata.
/// Lookup's full-domain/mirror envelope also bounds this simpler iteration.
pub fn iteration<T>(bytes: usize, len: usize) -> Option<usize> {
    fixed_lookup::<T>(bytes, len)
}

/// Extra variable byte work for a String hash; the fixed state is priced by
/// lookup or rehash. Pinned foldhash visits <=16 logical byte/scalar records
/// per input byte beyond that fixed state, including overlapping tail reads.
pub fn string_hash_payload(bytes: usize) -> Option<usize> {
    mul(bytes, 16)
}

fn group_probes(len: usize, group: usize) -> Option<usize> {
    let quotient = len / group;
    let remainder = len % group;
    let previous = quotient.saturating_sub(1);
    let triangle = if quotient % 2 == 0 {
        mul(quotient / 2, previous)?
    } else {
        mul(quotient, previous / 2)?
    };
    add(add(mul(group, triangle)?, mul(quotient, remainder)?)?, len)
}

fn buckets_for<T>(requested: usize, group: usize) -> Option<usize> {
    if requested < 15 {
        let min = match (group, size_of::<T>()) {
            (16, 0..=1) => 14,
            (16, 2..=3) | (8, 0..=1) => 7,
            _ => 3,
        };
        return Some(match requested.max(min) {
            0..=3 => 4,
            4..=7 => 8,
            _ => 16,
        });
    }
    (mul(requested, 8)? / 7).checked_next_power_of_two()
}

fn reserve<T>(g: Geometry, len: usize) -> Option<ReserveCost> {
    let full = capacity(g.buckets)?;
    let in_place = add(len, 1)? <= full / 2;
    let new_buckets = if in_place {
        g.buckets
    } else {
        buckets_for::<T>(add(len, 1)?.max(add(full, 1)?), g.group)?
    };
    let mut probes = group_probes(len, g.group)?;
    // For small tables the actual target can need one aligned correction load.
    if new_buckets < g.group {
        probes = add(probes, len)?;
    }
    // Same two 128-unit bundles/group and same 32 bundles/finalized item as the
    // existing fixed-u64 proof. Header widths are additionally priced below.
    let bulk = if in_place {
        add(mul(g.buckets, 3)?, 96)?
    } else {
        add(add(g.buckets, new_buckets)?, 96)?
    };
    let scans = add(add(bulk, mul(probes, 2)?)?, mul(len, 32)?)?;
    let work = add(mul(scans, GROUP_FEE)?, mul(mul(len, size_of::<T>())?, 8)?)?;
    let storage_bytes = if in_place {
        0
    } else {
        add(g.allocation, allocation::<T>(new_buckets, g.group)?)?
    };
    Some(ReserveCost {
        work,
        storage_bytes,
        rehashes: true,
    })
}

/// Price `try_reserve(1)` using actual allocation, length, and `map.capacity()`.
/// The latter includes remaining growth, so a tombstone-heavy table may need
/// in-place rehash even when its allocated bucket count is unchanged. If more
/// than one pinned group layout matches, maxima cover every compatible one.
/// Callers separately prepay one String hash payload for each retained key.
pub fn reserve_one<T>(bytes: usize, len: usize, remaining_capacity: usize) -> Option<ReserveCost> {
    if len > remaining_capacity {
        return None;
    }
    if bytes == 0 {
        if len != 0 || remaining_capacity != 0 || size_of::<T>() == 0 {
            return None;
        }
        let mut storage_bytes = 0;
        for group in [4, 8, 16] {
            storage_bytes = storage_bytes.max(allocation::<T>(buckets_for::<T>(1, group)?, group)?);
        }
        return Some(ReserveCost {
            work: 100 * GROUP_FEE,
            storage_bytes,
            rehashes: false,
        });
    }
    let mut maximum = ReserveCost {
        work: 0,
        storage_bytes: 0,
        rehashes: false,
    };
    let mut compatible_capacity = false;
    geometries::<T>(bytes, len, |g| {
        if remaining_capacity > capacity(g.buckets)? {
            // Allocation alone may describe a different small-table layout.
            // Actual remaining capacity excludes this candidate; it cannot
            // veto another compatible layout or grant a zero-price result.
            return Some(());
        }
        compatible_capacity = true;
        let cost = if len < remaining_capacity {
            ReserveCost {
                // Fixed checked layout/price arithmetic, with no table scan,
                // payload hash, allocation, or moved header.
                work: 512,
                storage_bytes: 0,
                rehashes: false,
            }
        } else {
            reserve::<T>(g, len)?
        };
        maximum.work = maximum.work.max(cost.work);
        maximum.storage_bytes = maximum.storage_bytes.max(cost.storage_bytes);
        maximum.rehashes |= cost.rehashes;
        Some(())
    })?;
    compatible_capacity.then_some(maximum)
}

#[cfg(test)]
mod tests;
