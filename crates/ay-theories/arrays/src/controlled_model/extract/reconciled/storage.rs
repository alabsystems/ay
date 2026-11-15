// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct State {
    pub(super) model: ArrayModel,
    pub(super) order: Vec<TermId>,
}

pub(super) fn empty(
    solver: &ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<State, QueryError> {
    work.admit(64, 8 * size_of::<State>())?;
    Ok(State {
        model: ArrayModel::default(),
        // Every inserted key is a distinct live TermId; the complete arena
        // frontier bounds all initial/class/base insertions, without growth.
        order: owned::reserve_vec(solver.terms.len(), work)?,
    })
}

pub(super) fn contains<T>(
    map: &HashMap<TermId, T>,
    key: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    Ok(scan::lookup(map, key, work)?.is_some())
}

pub(super) fn insert(
    state: &mut State,
    key: TermId,
    value: ArrayInterpretation,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    if contains(&state.model.array_values, key, work)? {
        return Err(work.refuse_exhaustion());
    }
    let map = &mut state.model.array_values;
    work.charge(64)?;
    if size_of::<(TermId, ArrayInterpretation)>() > 512 {
        return Err(work.refuse_exhaustion());
    }
    let count = owned::checked(map.len().checked_add(1), work)?;
    let spare = owned::checked(map.capacity().checked_sub(map.len()), work)?;
    let bound = owned::reserve_table::<(TermId, ArrayInterpretation)>(count, work)?;
    if spare == 0 {
        let old = owned::checked(
            map.allocation_size()
                .checked_div(size_of::<(TermId, ArrayInterpretation)>())
                .and_then(|n| n.checked_add(32)),
            work,
        )?;
        let row = owned::checked(bound.checked_mul(8).and_then(|n| n.checked_add(1024)), work)?;
        let visits = owned::checked(
            map.len()
                .checked_mul(row)
                .and_then(|n| {
                    old.checked_add(bound)
                        .and_then(|b| b.checked_mul(16))
                        .and_then(|b| n.checked_add(b))
                })
                .and_then(|n| n.checked_add(128)),
            work,
        )?;
        work.charge(visits)?;
    }
    map.try_reserve(1).map_err(|_| work.refuse_exhaustion())?;
    let actual = owned::checked(
        map.allocation_size()
            .checked_div(size_of::<(TermId, ArrayInterpretation)>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    owned::table_insert(actual, work)?;
    if state.order.len() >= state.order.capacity() {
        return Err(work.refuse_exhaustion());
    }
    work.charge(16)?;
    state.order.push(key);
    map.insert(key, value);
    work.charge(0)
}

pub(super) fn copy(source: &State, work: &mut WorkBudget<'_>) -> Result<State, QueryError> {
    work.admit(64, 8 * size_of::<State>())?;
    let mut result = State {
        model: ArrayModel::default(),
        order: owned::reserve_vec(source.order.capacity(), work)?,
    };
    for &key in &source.order {
        work.charge(16)?;
        let value = scan::lookup(&source.model.array_values, key, work)?
            .ok_or_else(|| work.refuse_exhaustion())?;
        let value = owned::interpretation(value, work)?;
        insert(&mut result, key, value, work)?;
    }
    work.charge(0)?;
    Ok(result)
}

pub(super) fn interpretation<'a>(
    solver: &ArraySolver<'_>,
    state: &'a mut State,
    term: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<&'a mut ArrayInterpretation, QueryError> {
    if !contains(&state.model.array_values, term, work)? {
        scan::live(solver, term, work)?;
        let Sort::Array(sort) = solver.terms.sort(term) else {
            return Err(work.refuse_exhaustion());
        };
        let value = ArrayInterpretation {
            index_sort: super::super::super::sort::optional(Some(&sort.index_sort), work)?,
            element_sort: super::super::super::sort::optional(Some(&sort.element_sort), work)?,
            ..ArrayInterpretation::default()
        };
        insert(state, term, value, work)?;
    }
    let bound = owned::checked(
        state
            .model
            .array_values
            .allocation_size()
            .checked_div(size_of::<(TermId, ArrayInterpretation)>())
            .and_then(|n| n.checked_add(32)),
        work,
    )?;
    owned::table_insert(bound, work)?;
    state
        .model
        .array_values
        .get_mut(&term)
        .ok_or_else(|| work.refuse_exhaustion())
}

pub(super) fn push<T>(
    values: &mut Vec<T>,
    value: T,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    work.charge(32)?;
    let count = owned::checked(values.len().checked_add(1), work)?;
    if values.len() == values.capacity() {
        let old = values.capacity();
        let new = owned::checked(old.checked_mul(2), work)?.max(count).max(8);
        let slots = owned::checked(old.checked_add(new), work)?;
        let bytes = owned::checked(
            slots
                .checked_mul(size_of::<T>())
                .and_then(|n| n.checked_mul(8))
                .and_then(|n| n.checked_add(8 * size_of::<Vec<T>>())),
            work,
        )?;
        let units = owned::checked(slots.checked_mul(8).and_then(|n| n.checked_add(64)), work)?;
        work.admit(units, bytes)?;
        values
            .try_reserve(1)
            .map_err(|_| work.refuse_exhaustion())?;
    }
    values.push(value);
    work.charge(0)
}

pub(super) fn equal(
    left: &str,
    right: &str,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    work.charge(16)?;
    if left.len() != right.len() {
        return Ok(false);
    }
    for begin in (0..left.len()).step_by(128) {
        let end = begin.saturating_add(128).min(left.len());
        work.charge(2 * (end - begin) + 16)?;
        if left.as_bytes()[begin..end] != right.as_bytes()[begin..end] {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn missing_row(
    interpretation: &mut ArrayInterpretation,
    key: &str,
    value: &str,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    for (existing, _) in &interpretation.stores {
        if equal(existing, key, work)? {
            return Ok(());
        }
    }
    let row = (owned::text(key, work)?, owned::text(value, work)?);
    push(&mut interpretation.stores, row, work)
}
