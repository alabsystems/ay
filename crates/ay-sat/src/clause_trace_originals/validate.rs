// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Allocation-free fixed-mode storage/event validation. Not a RUP checker.

use super::{ClauseTrace, OriginalArena};

/// Units of validation one call of the caller's `work` is handed.
pub(super) const CHUNK: u64 = 4096;

/// Hands the caller's `work` the units of a validation in chunks.
///
/// A unit is one row, literal, hint or binary-search step, a few
/// instructions. Every `work` call polls each control the transfer captured
/// (the caller's stop callback, interrupt, deadline and Guard) several times
/// over, so handing it the units one call each cost far more than the
/// validation: the 8-bit `bvsdiv`/`bvsrem` identity of
/// `bv_div_rem_identity_4873`, whose search takes 0.4 s, spent 60 s in those
/// polls while its trust discharge handed over its trace (release, fd4e00f75;
/// 2.3 s for the whole query on b12ea8a0f).
///
/// The chunks add up to the units the walk read: an accepted validation
/// hands over exactly the units a call per unit did, each phase settles its
/// units before the next phase reads, and a structural refusal still hands
/// over the units it read ([`structure`]). So every admission and every
/// Guard debit decides as before. A refusal by the caller is seen at most
/// one chunk later and is final: no later charge or settle asks again.
struct Meter<'w> {
    work: &'w mut dyn FnMut(u64) -> bool,
    pending: u64,
    refused: bool,
}

impl Meter<'_> {
    /// Charge `units`; the caller is asked once a chunk is pending.
    fn charge(&mut self, units: u64) -> bool {
        if self.refused {
            return false;
        }
        self.pending = self.pending.saturating_add(units);
        self.pending < CHUNK || self.settle()
    }

    /// Hand the caller every pending unit (with none, a bare poll).
    fn settle(&mut self) -> bool {
        if self.refused {
            return false;
        }
        let units = std::mem::take(&mut self.pending);
        self.refused = !(self.work)(units);
        !self.refused
    }
}

pub(super) fn structure(
    trace: &ClauseTrace,
    originals: &OriginalArena,
    num_vars: usize,
    work: &mut dyn FnMut(u64) -> bool,
) -> bool {
    let mut meter = Meter {
        work,
        pending: 0,
        refused: false,
    };
    if metered(trace, originals, num_vars, &mut meter) {
        return true;
    }
    // A structural refusal still pays for the units it read. After a refusal
    // by the caller nothing is pending, and the caller is not asked again.
    if meter.pending > 0 {
        let _ = meter.settle();
    }
    false
}

fn metered(
    trace: &ClauseTrace,
    originals: &OriginalArena,
    num_vars: usize,
    meter: &mut Meter<'_>,
) -> bool {
    if !original_rows(originals, num_vars, &mut |units| meter.charge(units))
        || !meter.settle()
        || !derived_rows(trace, originals, num_vars, &mut |units| meter.charge(units))
        || !meter.settle()
    {
        return false;
    }
    let total = originals.ids.len().checked_add(trace.meta.len());
    let Some(total) = total else { return false };
    let mut work = |units| meter.charge(units);
    for (index, row) in trace.meta.iter().enumerate() {
        if !work(1) {
            return false;
        }
        let event = row.original_prefix_len as usize + index;
        let start = row.hints_off as usize;
        let Some(end) = start.checked_add(row.hints_len as usize) else {
            return false;
        };
        let Some(hints) = trace.hint_pool.get(start..end) else {
            return false;
        };
        if row.clause_len == 0 && event.checked_add(1) != Some(total) {
            return false;
        }
        for &id in hints {
            if !work(1) || id == 0 || !hint_precedes(trace, originals, id, event, &mut work) {
                return false;
            }
        }
    }
    meter.settle()
}

fn original_rows(
    originals: &OriginalArena,
    num_vars: usize,
    work: &mut dyn FnMut(u64) -> bool,
) -> bool {
    if originals.ids.len() != originals.offsets.len()
        || originals.offsets.first().is_some_and(|offset| *offset != 0)
        || (originals.ids.is_empty() && !originals.literals.is_empty())
    {
        return false;
    }
    let mut previous = 0;
    for (index, &id) in originals.ids.iter().enumerate() {
        if !work(1) || id <= previous {
            return false;
        }
        previous = id;
        let Some(row) = originals.entry(index) else {
            return false;
        };
        // Original empty rows are unsupported: native replay requires a
        // derived terminal. Keep the ordinary path for original-empty input.
        if row.clause.is_empty() {
            return false;
        }
        for literal in row.clause {
            if !work(1) || literal.variable().0 as usize >= num_vars {
                return false;
            }
        }
    }
    true
}

fn derived_rows(
    trace: &ClauseTrace,
    originals: &OriginalArena,
    num_vars: usize,
    work: &mut dyn FnMut(u64) -> bool,
) -> bool {
    let mut previous_id = 0;
    let mut prefix = 0;
    let mut original_index = 0;
    for row in &trace.meta {
        if !work(1)
            || row.is_original
            || row.id <= previous_id
            || row.original_prefix_len < prefix
            || row.original_prefix_len as usize > originals.ids.len()
        {
            return false;
        }
        previous_id = row.id;
        prefix = row.original_prefix_len;
        // The two separately monotone ID streams can be checked for overlap
        // without a duplicate-ID map or changing event order.
        while original_index < originals.ids.len() && originals.ids[original_index] < row.id {
            if !work(1) {
                return false;
            }
            original_index += 1;
        }
        if originals.ids.get(original_index) == Some(&row.id) {
            return false;
        }
        let start = row.clause_off as usize;
        let Some(end) = start.checked_add(row.clause_len as usize) else {
            return false;
        };
        let Some(literals) = trace.lit_pool.get(start..end) else {
            return false;
        };
        for literal in literals {
            if !work(1) || literal.variable().0 as usize >= num_vars {
                return false;
            }
        }
    }
    true
}

fn find_id(
    len: usize,
    id: u64,
    at: impl Fn(usize) -> u64,
    work: &mut dyn FnMut(u64) -> bool,
) -> Option<usize> {
    let mut low = 0;
    let mut high = len;
    while low < high {
        if !work(1) {
            return None;
        }
        let middle = low + (high - low) / 2;
        match at(middle).cmp(&id) {
            std::cmp::Ordering::Less => low = middle + 1,
            std::cmp::Ordering::Greater => high = middle,
            std::cmp::Ordering::Equal => return Some(middle),
        }
    }
    None
}

fn hint_precedes(
    trace: &ClauseTrace,
    originals: &OriginalArena,
    id: u64,
    event: usize,
    work: &mut dyn FnMut(u64) -> bool,
) -> bool {
    if let Some(index) = find_id(originals.ids.len(), id, |i| originals.ids[i], work) {
        let mut low = 0;
        let mut high = trace.meta.len();
        while low < high {
            if !work(1) {
                return false;
            }
            let mid = low + (high - low) / 2;
            if trace.meta[mid].original_prefix_len as usize <= index {
                low = mid + 1;
            } else {
                high = mid;
            }
        }
        return index
            .checked_add(low)
            .is_some_and(|position| position < event);
    }
    // The caller's refusal is sticky, so a failed lookup cannot restart work.
    let Some(index) = find_id(trace.meta.len(), id, |i| trace.meta[i].id, work) else {
        return false;
    };
    (trace.meta[index].original_prefix_len as usize)
        .checked_add(index)
        .is_some_and(|position| position < event)
}
