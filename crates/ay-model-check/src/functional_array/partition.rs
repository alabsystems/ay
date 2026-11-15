// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete piecewise-constant refinement, not a set of sampled indices.
//! Select/store semantics: https://smt-lib.org/theories-ArraysEx.shtml
//! Modular arithmetic: https://smt-lib.org/theories-FixedSizeBitVectors.shtml

use super::topology::{SnapshotKind, SnapshotTopology};
use super::{ArraySnapshot, FunctionalArrayError, ModelValue};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

mod cuts;
mod fill;
mod meter;
mod read;
use meter::Meter;

const N: u128 = 1u128 << 64;

/// Exact preimage of a source cut under `(i - lo + source_lo) mod 2^64`.
fn preimage(cut: u128, lo: u64, source_lo: u64) -> u128 {
    (cut % N + N + u128::from(lo) - u128::from(source_lo)) % N
}

fn fixed(value: &BigInt, meter: &mut Meter<'_>) -> Result<u64, FunctionalArrayError> {
    meter.pay(128)?;
    if value.is_negative() || value.bits() > 64 {
        return Err(FunctionalArrayError::Value);
    }
    value.to_u64().ok_or(FunctionalArrayError::Value)
}

fn key(value: &ModelValue, meter: &mut Meter<'_>) -> Result<u64, FunctionalArrayError> {
    meter.pay(64)?;
    match value {
        ModelValue::BitVec { width: 64, value } => fixed(value, meter),
        _ => Err(FunctionalArrayError::Sort),
    }
}

fn cell_width(sort: &ay_core::Sort) -> Option<u32> {
    let ay_core::Sort::Array(sort) = sort else {
        return None;
    };
    if !matches!(&sort.index_sort, ay_core::Sort::BitVec(index) if index.width == 64) {
        return None;
    }
    match &sort.element_sort {
        ay_core::Sort::Bool => Some(0),
        ay_core::Sort::BitVec(cell) if (1..=128).contains(&cell.width) => Some(cell.width),
        _ => None,
    }
}

/// Exact borrowed equality for the flat, topology-validated cell domain.
/// ModelValue deliberately has no generic PartialEq: other domains require
/// their own denotational evidence. No values are cloned or reconstructed here.
fn cells_equal(left: &ModelValue, right: &ModelValue) -> bool {
    match (left, right) {
        (ModelValue::Bool(left), ModelValue::Bool(right)) => left == right,
        (
            ModelValue::BitVec {
                value: left,
                width: left_width,
            },
            ModelValue::BitVec {
                value: right,
                width: right_width,
            },
        ) => left_width == right_width && left == right,
        _ => false,
    }
}

impl ArraySnapshot {
    /// Confirm the WHOLE BV64 range-copy relation from complete MODEL DATA.
    /// `false` means unestablished, never a native refutation/publication seal.
    /// The caller retains original source/owner authority and supplies the SAME
    /// finite progress ledger. All captures are validated, even for empty ranges.
    /// Scratch disposal precedes the final progress poll. Returned DATA carries
    /// no query identity, assumption, SAT token, or new allowance.
    pub fn confirms_range_copy_with_progress(
        &self,
        destination: &Self,
        source: &Self,
        lo: u64,
        hi: u64,
        source_lo: u64,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, FunctionalArrayError> {
        let mut meter = Meter::new(progress);
        let result = compare(self, destination, source, lo, hi, source_lo, &mut meter);
        // compare owns all topology/cut scratch; it has dropped on every exit.
        if matches!(
            &result,
            Err(FunctionalArrayError::Resource | FunctionalArrayError::Allocation)
        ) {
            meter.refuse();
            // Preserve the typed constructor error; the caller must latch it
            // on its retained owner. No later local offer can revive this call.
            return result;
        }
        meter.poll()?;
        result
    }
}

fn compare(
    target: &ArraySnapshot,
    destination: &ArraySnapshot,
    source: &ArraySnapshot,
    lo: u64,
    hi: u64,
    source_lo: u64,
    meter: &mut Meter<'_>,
) -> Result<bool, FunctionalArrayError> {
    meter.pay(256)?;
    // Inspect only fixed headers before equality; malformed nested sorts must
    // not trigger an unpriced recursive Sort comparison on this new route.
    let cell = cell_width(target.sort()).ok_or(FunctionalArrayError::Sort)?;
    if cell_width(destination.sort()) != Some(cell) || cell_width(source.sort()) != Some(cell) {
        return Err(FunctionalArrayError::Sort);
    }
    let target = target.topology_with_progress(&mut |w, b| meter.offer(w, b))?;
    let destination = destination.topology_with_progress(&mut |w, b| meter.offer(w, b))?;
    let source = source.topology_with_progress(&mut |w, b| meter.offer(w, b))?;
    let target_cuts = cuts::derive(&target, meter)?;
    let destination_cuts = cuts::derive(&destination, meter)?;
    let source_cuts = cuts::derive(&source, meter)?;
    let mut union = Vec::new();
    cuts::append(&mut union, &target_cuts, meter)?;
    cuts::append(&mut union, &destination_cuts, meter)?;
    cuts::push(&mut union, u128::from(lo), meter)?;
    cuts::push(&mut union, u128::from(hi), meter)?;
    // 0 and N are source cuts; their preimage explicitly includes the wrap seam.
    for cut in &source_cuts {
        meter.pay(128)?;
        cuts::push(&mut union, preimage(*cut, lo, source_lo), meter)?;
    }
    cuts::canonical(&mut union, meter)?;
    for window in union.windows(2) {
        meter.pay(128)?;
        let index = u64::try_from(window[0]).map_err(|_| FunctionalArrayError::Value)?;
        let left = read::value(&target, index, meter)?;
        let right = if lo <= index && index < hi {
            let mapped = index.wrapping_sub(lo).wrapping_add(source_lo);
            read::value(&source, mapped, meter)?
        } else {
            read::value(&destination, index, meter)?
        };
        meter.pay(256)?;
        if !cells_equal(left, right) {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
