// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::hash::Hash;

// Only fixed one/two-TermId keys can use the scalar hash/probe allowance.
pub(super) trait Key: Copy + Eq + Hash {}
impl Key for TermId {}
impl Key for (TermId, TermId) {}

// RawTable::find_or_find_insert_slot begins reserve(1), even on replacement.
// Exact single-entry reservations preserve fresh insert growth/rehash order.
pub(super) fn insert<K: Key, V>(
    map: &mut HashMap<K, V>,
    key: K,
    value: V,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    layout::<K, V>(work)?;
    work.charge(16)?;
    let entries = map.len();
    let spare = owned::checked(map.capacity().checked_sub(entries), work)?;
    let count = owned::checked(entries.checked_add(1), work)?;
    let target = owned::reserve_table::<(K, V)>(count, work)?;
    rehash(entries, spare, target, work)?;
    map.try_reserve(1).map_err(|_| work.refuse_exhaustion())?;
    // A cleared source may have a much larger retained backing than len()+1.
    // Charge actual allocated probe width, not the fresh reservation hint.
    let bound = owned::checked(
        map.allocation_size()
            .checked_div(size_of::<(K, V)>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    owned::table_insert(bound, work)?;
    map.insert(key, value);
    work.charge(0)
}

fn entry<'a, K: Key, V: Default>(
    map: &'a mut HashMap<K, V>,
    key: K,
    work: &mut WorkBudget<'_>,
) -> Result<&'a mut V, QueryError> {
    layout::<K, V>(work)?;
    let current = owned::checked(
        map.allocation_size()
            .checked_div(size_of::<(K, V)>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    owned::table_insert(current, work)?;
    // Legacy entry() does not grow an occupied table. Reserving unconditionally
    // could rehash before a later select and change legacy iteration order.
    if !map.contains_key(&key) {
        work.charge(16)?;
        let entries = map.len();
        let spare = owned::checked(map.capacity().checked_sub(entries), work)?;
        let count = owned::checked(entries.checked_add(1), work)?;
        let target = owned::reserve_table::<(K, V)>(count, work)?;
        rehash(entries, spare, target, work)?;
        map.try_reserve(1).map_err(|_| work.refuse_exhaustion())?;
    }
    let bound = owned::checked(
        map.allocation_size()
            .checked_div(size_of::<(K, V)>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    owned::table_insert(bound, work)?;
    Ok(map.entry(key).or_default())
}

pub(super) fn layout<K: Key, V>(work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.charge(1)?;
    // All current values are scalar pairs, Vec headers or ArrayVarData. Keep
    // their fixed move/hash allowance truthful on other ABIs/future changes.
    if size_of::<K>() > 8 || size_of::<(K, V)>() > 128 {
        return Err(work.refuse_exhaustion());
    }
    Ok(())
}

pub(super) fn select(
    view: &mut ArraySolver<'_>,
    term: TermId,
    array: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let data: &mut ArrayVarData = entry(&mut view.array_vars, array, work)?;
    push(&mut data.parent_selects, term, work)
}

pub(super) fn reverse(
    view: &mut ArraySolver<'_>,
    operand: TermId,
    equality: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let terms = entry(&mut view.term_to_equalities, operand, work)?;
    push(terms, equality, work)
}

fn push(
    values: &mut Vec<TermId>,
    value: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    let count = owned::checked(values.len().checked_add(1), work)?;
    // No throwaway reservation. Pinned grow_amortized uses max(2*capacity,
    // required, MIN_NON_ZERO_CAP<=8) for these non-ZST TermId vectors.
    let old = values.capacity();
    let new = owned::checked(old.checked_mul(2), work)?.max(count).max(8);
    let slots = owned::checked(old.checked_add(new), work)?;
    let bytes = owned::checked(
        slots
            .checked_mul(size_of::<TermId>())
            .and_then(|n| n.checked_mul(8))
            .and_then(|n| n.checked_add(8 * size_of::<Vec<TermId>>())),
        work,
    )?;
    let visits = owned::checked(slots.checked_mul(8).and_then(|n| n.checked_add(32)), work)?;
    work.admit(visits, bytes)?;
    values
        .try_reserve(1)
        .map_err(|_| work.refuse_exhaustion())?;
    values.push(value);
    work.charge(0)
}

fn rehash(
    entries: usize,
    spare: usize,
    bound: usize,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    // Fresh/cleared tables have no deleted controls. A growth can reinsert
    // every old fixed-key entry, each through a worst-case full probe.
    // Pinned capacity()=items+growth_left and try_reserve(1) calls rehash iff
    // 1>growth_left. The caller prepaid these metadata/branch reads; spare
    // capacity therefore proves no resize, not an average-case hash guess.
    if spare >= 1 {
        return Ok(());
    }
    let row = owned::checked(bound.checked_mul(8).and_then(|n| n.checked_add(512)), work)?;
    let visits = owned::checked(entries.checked_mul(row), work)?;
    work.charge(visits)
}

pub(super) fn assignments(
    source: &ArraySolver<'_>,
    view: &mut ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    owned::scan_table::<(TermId, bool)>(source.assigns.allocation_size(), work)?;
    for (&term, &value) in &source.assigns {
        scan::live(source, term, work)?;
        insert(&mut view.assigns, term, value, work)?;
    }
    owned::scan_table::<((TermId, TermId), ())>(source.external_diseqs.allocation_size(), work)?;
    for &(left, right) in &source.external_diseqs {
        shape::child(source, left, work)?;
        shape::child(source, right, work)?;
        pair(
            &mut view.diseq_set,
            ArraySolver::ordered_pair(left, right),
            work,
        )?;
    }
    Ok(())
}

pub(super) fn false_assignment(
    view: &mut ArraySolver<'_>,
    equality: TermId,
    left: TermId,
    right: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    if let Some(value) = scan::lookup(&view.assigns, equality, work)? {
        if *value {
            return Err(work.refuse_exhaustion());
        }
        pair(
            &mut view.diseq_set,
            ArraySolver::ordered_pair(left, right),
            work,
        )?;
    }
    Ok(())
}

fn pair(
    set: &mut crate::HashSet<(TermId, TermId)>,
    key: (TermId, TermId),
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(16)?;
    let entries = set.len();
    let spare = owned::checked(set.capacity().checked_sub(entries), work)?;
    let count = owned::checked(entries.checked_add(1), work)?;
    let bound = owned::reserve_table::<((TermId, TermId), ())>(count, work)?;
    rehash(entries, spare, bound, work)?;
    set.try_reserve(1).map_err(|_| work.refuse_exhaustion())?;
    owned::table_insert(bound, work)?;
    set.insert(key);
    work.charge(0)
}
