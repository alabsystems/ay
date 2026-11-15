// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controlled extraction from already-current native caches; bounded classes only.

use super::{owned, ArrayModelConstruction, CellAuthority, ModelCellKey, ModelCellRow};
use crate::{ArrayInterpretation, ArrayModel, ArraySolver, HashMap, Sort, TermId};
use ay_core::original_query::{QueryError, WorkBudget};
use ay_core::term::TermData;

mod classes;
mod reconciled;
mod registration;
mod scan;
#[cfg(test)]
mod tests;

impl ArraySolver<'_> {
    /// Extract the warm store/default/select subset under ONE original ledger.
    /// Store-free, flat-sort equality classes also preserve the legacy ordered
    /// DATA when their existing defaults are uniformly present or absent.
    /// Dirty/pending caches, class-bearing store chains and unfinished default
    /// reconciliation refuse; no cache preparation or new grant occurs.
    /// Legacy `extract_model` remains available with its original semantics.
    /// Output is ordinary DATA, not a solve/publication/source credential.
    /// Bucket layout and later output/source disposal remain caller-owned.
    pub fn try_extract_prepared_model_with_budget(
        &self,
        values: &HashMap<TermId, String>,
        work: &mut WorkBudget<'_>,
    ) -> Result<ArrayModel, QueryError> {
        let result = extract(self, values, work);
        owned::finish(result, work)
    }
}

fn prepared(solver: &ArraySolver<'_>, work: &mut WorkBudget<'_>) -> Result<(), QueryError> {
    work.charge(16)?;
    if solver.dirty
        || solver.var_layer_dirty
        || solver.assign_dirty
        || solver.shadow_uf_stale
        || solver.populated_terms != solver.terms.len()
        || !solver.pending_registered_equalities.is_empty()
        || !solver.eq_adj.is_empty()
        || !solver.array_var_merge_log.is_empty()
    {
        return Err(work.refuse_exhaustion());
    }
    Ok(())
}

fn extract(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    work: &mut WorkBudget<'_>,
) -> Result<ArrayModel, QueryError> {
    let classes = if solver.eq_adj.is_empty() {
        prepared(solver, work)?;
        None
    } else {
        Some(classes::prepare(solver, work)?)
    };
    let reads = scan::reads(solver, values, work)?;
    let arrays = scan::arrays(solver, values, &reads, work)?;
    let mut output = ArrayModel::default();
    let maximum = match &classes {
        Some(plan) => owned::checked(arrays.len().checked_add(plan.additional_entries()), work)?,
        None => arrays.len(),
    };
    let buckets = owned::reserve_table::<(TermId, ArrayInterpretation)>(maximum, work)?;
    output
        .array_values
        .try_reserve(maximum)
        .map_err(|_| work.refuse_exhaustion())?;
    let conflict_buckets = owned::reserve_table::<TermId>(arrays.len(), work)?;
    output
        .read_conflicted
        .try_reserve(arrays.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for &array in &arrays {
        if let Some((interpretation, conflict)) = entry(solver, values, &reads, array, work)? {
            owned::table_insert(buckets, work)?;
            output.array_values.insert(array, interpretation);
            if conflict {
                owned::table_insert(conflict_buckets, work)?;
                output.read_conflicted.insert(array);
            }
        }
    }
    if let Some(plan) = classes {
        plan.propagate(solver, &mut output, buckets, work)?;
        plan.finish(work)?;
    }
    let visits = arrays
        .len()
        .checked_add(reads.len())
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.charge(visits)?;
    drop(arrays);
    drop(reads);
    work.charge(0)?;
    Ok(output)
}

fn entry(
    solver: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    reads: &[scan::Read<'_>],
    array: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<Option<(ArrayInterpretation, bool)>, QueryError> {
    scan::live(solver, array, work)?;
    let Sort::Array(sort) = solver.terms.sort(array) else {
        return Err(work.refuse_exhaustion());
    };
    let (original, mut default) = originals(solver, values, array, work)?;
    if let Some(&term) = scan::lookup(&solver.default_cache, array, work)? {
        let value = scan::value(solver, values, term, work)?;
        if default.is_none() {
            default = value.filter(|value| !value.is_empty());
        }
    }
    work.charge(reads.len())?;
    let count = reads.iter().filter(|read| read.array == array).count();
    let mut observations = owned::reserve_vec(count, work)?;
    for read in reads {
        work.charge(1)?;
        if read.array == array {
            observations.push(read.row);
        }
    }
    if original.is_empty() && default.is_none() && observations.is_empty() {
        return Ok(None);
    }
    let mut one = super::construct(
        ArrayModelConstruction {
            array,
            default,
            index_sort: Some(&sort.index_sort),
            element_sort: Some(&sort.element_sort),
            original: &original,
            observations: &observations,
        },
        work,
    )?;
    let remove_bound = one
        .array_values
        .capacity()
        .checked_mul(4)
        .and_then(|value| value.checked_add(32))
        .ok_or_else(|| work.refuse_exhaustion())?;
    owned::table_insert(remove_bound, work)?;
    let Some(interpretation) = one.array_values.remove(&array) else {
        return Err(work.refuse_exhaustion());
    };
    let conflict = one.has_withheld_arrays();
    let visits = original
        .len()
        .checked_add(observations.len())
        .and_then(|n| n.checked_add(1))
        .ok_or_else(|| work.refuse_exhaustion())?;
    work.charge(visits)?;
    drop(one);
    drop(original);
    drop(observations);
    work.charge(0)?;
    Ok(Some((interpretation, conflict)))
}

type Original<'a> = (ModelCellRow<'a>, CellAuthority);

fn originals<'a>(
    solver: &'a ArraySolver<'_>,
    values: &'a HashMap<TermId, String>,
    array: TermId,
    work: &mut WorkBudget<'_>,
) -> Result<(Vec<Original<'a>>, Option<&'a str>), QueryError> {
    if scan::lookup(&solver.array_vars, array, work)?.is_none() {
        return Ok((Vec::new(), None));
    }
    let (count, base) = scan::chain(solver, array, work)?;
    let mut original = owned::reserve_vec(count, work)?;
    let mut current = array;
    for _ in 0..count {
        let Some(&(parent, index, term)) = scan::lookup(&solver.store_cache, current, work)? else {
            return Err(work.refuse_exhaustion());
        };
        let index = scan::value(solver, values, index, work)?.unwrap_or("");
        let value = scan::value(solver, values, term, work)?.unwrap_or("");
        if value.is_empty() && matches!(solver.terms.sort(term), Sort::Array(_)) {
            return Err(work.refuse_exhaustion());
        }
        if !index.is_empty() && !value.is_empty() {
            let authority = if matches!(solver.terms.get(term), TermData::Const(_)) {
                CellAuthority::Concrete
            } else {
                CellAuthority::Soft
            };
            original.push((
                ModelCellRow {
                    key: ModelCellKey::Text(index),
                    value,
                },
                authority,
            ));
        }
        current = parent;
    }
    let default = match scan::lookup(&solver.const_array_cache, base, work)? {
        Some(&term) => scan::value(solver, values, term, work)?,
        None => None,
    };
    Ok((original, default))
}
