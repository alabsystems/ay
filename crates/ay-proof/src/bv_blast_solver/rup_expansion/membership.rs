// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preserve first-occurrence clause order without quadratic membership scans.
//! Every table is charged and reserved before use. Hashes only locate entries;
//! complete literal equality decides membership, including polarity.

use super::{reserve_rup_map, try_reserve_rup_map, BvSolvedExportError, Lit, RupExpansionState};
use std::collections::HashMap;

pub(super) const INDEX_THRESHOLD: usize = 16;

pub(super) fn resolve(
    a: &[Lit],
    b: &[Lit],
    pivot: u32,
    capacity: usize,
    state: &mut RupExpansionState<'_>,
) -> Result<Option<Vec<Lit>>, BvSolvedExportError> {
    reserve_rup_map::<Lit, ()>(state, capacity)?;
    #[expect(
        clippy::zero_sized_map_values,
        reason = "the charged reservation prices the exact HashMap<Lit, ()> layout"
    )]
    let mut seen = HashMap::new();
    try_reserve_rup_map(&mut seen, capacity, state)?;
    let mut out = state.resolution_buffer(capacity)?;
    for &lit in a.iter().chain(b) {
        state.charge_work(1)?;
        if lit.var == pivot {
            continue;
        }
        state.charge_work(1)?;
        if seen.contains_key(&lit.negated()) {
            return Ok(None);
        }
        state.charge_work(1)?;
        if seen.insert(lit, ()).is_none() {
            out.push(lit);
        }
    }
    Ok(Some(out))
}

pub(super) fn equal(
    a: &[Lit],
    b: &[Lit],
    state: &mut RupExpansionState<'_>,
) -> Result<bool, BvSolvedExportError> {
    reserve_rup_map::<Lit, bool>(state, a.len())?;
    let mut seen = HashMap::new();
    try_reserve_rup_map(&mut seen, a.len(), state)?;
    for &lit in a {
        state.charge_work(1)?;
        seen.insert(lit, false);
    }
    let mut matched = 0;
    for lit in b {
        state.charge_work(1)?;
        match seen.get_mut(lit) {
            Some(mark) => {
                matched += usize::from(!*mark);
                *mark = true;
            }
            None => return Ok(false),
        }
    }
    Ok(matched == seen.len())
}

/// Whether every literal of `a` occurs, with its polarity, in `b`. The RUP
/// expander asks this only of a weakened LRAT step (`stronger_resolvent`).
pub(super) fn subset(
    a: &[Lit],
    b: &[Lit],
    state: &mut RupExpansionState<'_>,
) -> Result<bool, BvSolvedExportError> {
    reserve_rup_map::<Lit, ()>(state, b.len())?;
    #[expect(
        clippy::zero_sized_map_values,
        reason = "the charged reservation prices the exact HashMap<Lit, ()> layout"
    )]
    let mut members = HashMap::new();
    try_reserve_rup_map(&mut members, b.len(), state)?;
    for &lit in b {
        state.charge_work(1)?;
        members.insert(lit, ());
    }
    for lit in a {
        state.charge_work(1)?;
        if !members.contains_key(lit) {
            return Ok(false);
        }
    }
    Ok(true)
}

#[cfg(test)]
mod tests;
