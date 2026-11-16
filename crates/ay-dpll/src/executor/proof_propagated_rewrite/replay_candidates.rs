// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded L1 candidate discovery, never proof authority.

use super::*;

const MAX_AND_DEPTH: usize = 64;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum CensusDecline {
    BoundedMiss,
    Stopped,
}

struct Census<'a> {
    remaining: usize,
    progress: &'a dyn Fn(usize, usize) -> bool,
}

impl Census<'_> {
    fn charge(&mut self, work: usize, bytes: usize) -> Result<(), CensusDecline> {
        let debit = work
            .checked_add(bytes.div_ceil(64))
            .ok_or(CensusDecline::BoundedMiss)?;
        self.remaining = self
            .remaining
            .checked_sub(debit)
            .ok_or(CensusDecline::BoundedMiss)?;
        if !(self.progress)(work, bytes) {
            return Err(CensusDecline::Stopped);
        }
        Ok(())
    }
}

/// One breadth-first census across every recorded after-root. Sorted parents
/// make a partial resource refusal deterministic; no root resets the budget.
/// Only live, Bool-sorted raw AND edges nominate descendants. The caller must
/// still derive each nominated term from the original authored proof scope.
pub(super) fn and_descendants(
    terms: &TermStore,
    records: &HashMap<TermId, (TermId, u32)>,
    progress: &dyn Fn(usize, usize) -> bool,
) -> Result<HashSet<TermId>, CensusDecline> {
    let mut meter = Census {
        remaining: PLAN_NODE_BUDGET,
        progress,
    };
    meter.charge(0, 0)?;
    let count = records.len();
    let sort_work = count
        .checked_mul(count.bit_width() as usize)
        .ok_or(CensusDecline::BoundedMiss)?;
    meter.charge(
        sort_work,
        count.checked_mul(96).ok_or(CensusDecline::BoundedMiss)?,
    )?;
    let mut parents = Vec::new();
    parents
        .try_reserve_exact(count)
        .map_err(|_| CensusDecline::Stopped)?;
    parents.extend(records.keys().copied());
    parents.sort_unstable();
    let mut queue = Vec::new();
    queue
        .try_reserve_exact(count)
        .map_err(|_| CensusDecline::Stopped)?;
    let mut seen = HashSet::default();
    seen.try_reserve(count)
        .map_err(|_| CensusDecline::Stopped)?;
    for parent in parents {
        if parent.index() >= terms.len() {
            return Err(CensusDecline::BoundedMiss);
        }
        if seen.insert(parent) {
            queue.push((parent, 0usize));
        }
    }
    let mut cursor = 0;
    while cursor < queue.len() {
        meter.charge(1, 0)?;
        let (term, depth) = queue[cursor];
        cursor += 1;
        if depth == MAX_AND_DEPTH || terms.sort(term) != &Sort::Bool {
            continue;
        }
        let TermData::App(Symbol::Named(name), children) = terms.get(term) else {
            continue;
        };
        if name != "and" {
            continue;
        }
        // Charge every edge, including duplicate occurrences, before reserve
        // or lookup. This bounds fanout and retained queue/hash-table growth.
        meter.charge(
            children.len(),
            children
                .len()
                .checked_mul(96)
                .ok_or(CensusDecline::BoundedMiss)?,
        )?;
        queue
            .try_reserve(children.len())
            .map_err(|_| CensusDecline::Stopped)?;
        seen.try_reserve(children.len())
            .map_err(|_| CensusDecline::Stopped)?;
        for &child in children {
            if child.index() >= terms.len() || terms.sort(child) != &Sort::Bool {
                return Err(CensusDecline::BoundedMiss);
            }
            if seen.insert(child) {
                queue.push((child, depth + 1));
            }
        }
    }
    meter.charge(0, 0)?;
    Ok(seen)
}

#[cfg(test)]
mod tests;
