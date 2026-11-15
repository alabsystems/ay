// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete interval Fill truth from actual MODEL DATA and a borrowed literal.

use super::{cell_width, cuts, read, ArraySnapshot, FunctionalArrayError, Meter, ModelValue};
use ay_core::term::Constant;
use num_traits::Signed;

pub(super) fn literal_width(value: &Constant) -> Option<u32> {
    match value {
        Constant::Bool(_) => Some(0),
        Constant::BitVec { value, width }
            if (1..=128).contains(width)
                && !value.is_negative()
                && value.bits() <= u64::from(*width) =>
        {
            Some(*width)
        }
        _ => None,
    }
}

fn equal(value: &ModelValue, literal: &Constant) -> bool {
    match (value, literal) {
        (ModelValue::Bool(a), Constant::Bool(b)) => a == b,
        (
            ModelValue::BitVec {
                value: a,
                width: aw,
            },
            Constant::BitVec {
                value: b,
                width: bw,
            },
        ) => aw == bw && a == b,
        _ => false,
    }
}

impl ArraySnapshot {
    /// Confirm EVERY BV64 cell of a literal half-open Fill relation.
    /// This borrows the existing literal, never constructs a BigInt/expected
    /// snapshot or supplies query/owner/publication authority. The caller must
    /// retain the original ledger and latch returned resource/allocation errors.
    pub fn confirms_range_fill_with_progress(
        &self,
        destination: &Self,
        lo: u64,
        hi: u64,
        value: &Constant,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<bool, FunctionalArrayError> {
        let mut meter = Meter::new(progress);
        let result = compare(self, destination, lo, hi, value, &mut meter);
        if matches!(
            &result,
            Err(FunctionalArrayError::Resource | FunctionalArrayError::Allocation)
        ) {
            meter.refuse();
            return result;
        }
        // compare owns and has dropped ALL topology/cut storage on every exit.
        meter.poll()?;
        result
    }
}

fn compare(
    target: &ArraySnapshot,
    destination: &ArraySnapshot,
    lo: u64,
    hi: u64,
    literal: &Constant,
    meter: &mut Meter<'_>,
) -> Result<bool, FunctionalArrayError> {
    meter.pay(256)?;
    let cell = cell_width(target.sort()).ok_or(FunctionalArrayError::Sort)?;
    if cell_width(destination.sort()) != Some(cell) {
        return Err(FunctionalArrayError::Sort);
    }
    meter.pay(128)?;
    if literal_width(literal) != Some(cell) {
        return Err(FunctionalArrayError::Value);
    }
    let target = target.topology_with_progress(&mut |w, b| meter.offer(w, b))?;
    let destination = destination.topology_with_progress(&mut |w, b| meter.offer(w, b))?;
    let target_cuts = cuts::derive(&target, meter)?;
    let destination_cuts = cuts::derive(&destination, meter)?;
    let mut union = Vec::new();
    cuts::append(&mut union, &target_cuts, meter)?;
    cuts::append(&mut union, &destination_cuts, meter)?;
    cuts::push(&mut union, u128::from(lo), meter)?;
    cuts::push(&mut union, u128::from(hi), meter)?;
    cuts::canonical(&mut union, meter)?;
    for window in union.windows(2) {
        meter.pay(128)?;
        let index = u64::try_from(window[0]).map_err(|_| FunctionalArrayError::Value)?;
        let left = read::value(&target, index, meter)?;
        if lo <= index && index < hi {
            meter.pay(256)?;
            if !equal(left, literal) {
                return Ok(false);
            }
        } else {
            let right = read::value(&destination, index, meter)?;
            meter.pay(256)?;
            if !super::cells_equal(left, right) {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
