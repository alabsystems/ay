// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owned native array DATA under one borrowed original ledger.
//! This is a constituent, not cache preparation, solve admission or a credential.

use super::{
    ArrayInterpretation, ArrayModel, HashMap, HashSet, PendingArrayDefinition, Sort, TermId,
};
use crate::indexed_model_cells::{CellAuthority, IndexedModelCells, ModelCellKey, ModelCellRow};
use ay_core::original_query::{QueryError, WorkBudget};

mod extract;
mod owned;
mod sort;
#[cfg(test)]
mod tests;

/// Borrowed, already selected native spellings; no default/model authority is added.
pub struct ArrayModelConstruction<'a> {
    /// The existing array term to associate with this DATA.
    pub array: TermId,
    /// Exact default spelling, including the distinction between None and empty.
    pub default: Option<&'a str>,
    /// Existing index sort, without sort inference.
    pub index_sort: Option<&'a Sort>,
    /// Existing element sort, without sort inference.
    pub element_sort: Option<&'a Sort>,
    /// Original newest-first rows and their original key-wide authority.
    pub original: &'a [(ModelCellRow<'a>, CellAuthority)],
    /// Selected committed observations in the original iteration order.
    pub observations: &'a [ModelCellRow<'a>],
}

impl ArrayInterpretation {
    /// Copy all owned payloads before publication under the same original ledger.
    /// Recursive sorts at depth 56 and unknown future variants refuse.
    /// This preserves row/Option values, not solver validation or source authority.
    pub fn try_clone_with_budget(&self, work: &mut WorkBudget<'_>) -> Result<Self, QueryError> {
        let result = owned::interpretation(self, work);
        owned::finish(result, work)
    }
}

impl ArrayModel {
    /// Copy all model DATA, including pending definitions, Some(empty)
    /// candidates and protected conflict IDs.
    /// Map bucket/iteration layout is NOT preserved; exact DATA contents and row
    /// order are. Do not substitute this for layout-sensitive traversal/Clone.
    /// Legacy Clone and extraction remain unchanged and separately available.
    pub fn try_clone_with_budget(&self, work: &mut WorkBudget<'_>) -> Result<Self, QueryError> {
        let result = clone_model(self, work);
        owned::finish(result, work)
    }

    /// Construct one array DATA entry with the original FIFO/soft/poison rules.
    /// Only Text keys have native spellings here; Bool/BV keys refuse BEFORE
    /// index allocation instead of inventing an encoding. The 94m index retains
    /// its independent full BigInt comparison API; this wrapper never truncates.
    /// No cache traversal, class/default completion, native solve or fresh grant
    /// occurs. Original/select rows must already be chosen by the caller.
    /// Returned DATA/source disposal and later caller polls remain caller-owned.
    pub fn try_from_indexed_rows(
        input: ArrayModelConstruction<'_>,
        work: &mut WorkBudget<'_>,
    ) -> Result<Self, QueryError> {
        let result = construct(input, work);
        owned::finish(result, work)
    }
}

fn clone_model(source: &ArrayModel, work: &mut WorkBudget<'_>) -> Result<ArrayModel, QueryError> {
    work.charge(0)?;
    let array_values = copy_map(&source.array_values, work)?;
    let read_conflicted = copy_conflicts(&source.read_conflicted, work)?;
    let pending_definitions = copy_pending(&source.pending_definitions, work)?;
    let pending_definition_dependents =
        copy_conflicts(&source.pending_definition_dependents, work)?;
    let store_chain_class_candidate = match &source.store_chain_class_candidate {
        Some(candidate) => Some(copy_map(candidate, work)?),
        None => None,
    };
    let definition_authoritative = copy_conflicts(&source.definition_authoritative, work)?;
    Ok(ArrayModel {
        array_values,
        read_conflicted,
        pending_definitions,
        pending_definition_dependents,
        store_chain_class_candidate,
        definition_authoritative,
    })
}

fn copy_pending(
    source: &HashMap<TermId, PendingArrayDefinition>,
    work: &mut WorkBudget<'_>,
) -> Result<HashMap<TermId, PendingArrayDefinition>, QueryError> {
    owned::scan_table::<(TermId, PendingArrayDefinition)>(source.allocation_size(), work)?;
    let mut result = HashMap::default();
    let buckets = owned::reserve_table::<(TermId, PendingArrayDefinition)>(source.len(), work)?;
    result
        .try_reserve(source.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for (&source, &record) in source {
        owned::table_insert(buckets, work)?;
        result.insert(source, record);
    }
    work.charge(0)?;
    Ok(result)
}

fn copy_map(
    source: &HashMap<TermId, ArrayInterpretation>,
    work: &mut WorkBudget<'_>,
) -> Result<HashMap<TermId, ArrayInterpretation>, QueryError> {
    owned::scan_table::<(TermId, ArrayInterpretation)>(source.allocation_size(), work)?;
    let mut result = HashMap::default();
    let buckets = owned::reserve_table::<(TermId, ArrayInterpretation)>(source.len(), work)?;
    result
        .try_reserve(source.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for (&key, value) in source {
        let value = owned::interpretation(value, work)?;
        owned::table_insert(buckets, work)?;
        result.insert(key, value);
    }
    work.charge(0)?;
    Ok(result)
}

fn copy_conflicts(
    source: &HashSet<TermId>,
    work: &mut WorkBudget<'_>,
) -> Result<HashSet<TermId>, QueryError> {
    owned::scan_table::<(TermId, ())>(source.allocation_size(), work)?;
    let mut result = HashSet::default();
    let buckets = owned::reserve_table::<TermId>(source.len(), work)?;
    result
        .try_reserve(source.len())
        .map_err(|_| work.refuse_exhaustion())?;
    for &key in source {
        owned::table_insert(buckets, work)?;
        result.insert(key);
    }
    work.charge(0)?;
    Ok(result)
}

fn construct(
    input: ArrayModelConstruction<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<ArrayModel, QueryError> {
    work.charge(0)?;
    for (row, _) in input.original {
        require_text(row.key, work)?;
    }
    for row in input.observations {
        require_text(row.key, work)?;
    }
    let maximum = input
        .original
        .len()
        .checked_add(input.observations.len())
        .ok_or_else(|| work.refuse_exhaustion())?;
    let mut cells = IndexedModelCells::new(maximum, work)?;
    for &(row, authority) in input.original {
        cells.push_original(row, authority)?;
    }
    for &row in input.observations {
        cells.observe(row)?;
    }
    let rows = cells.finish()?;
    let conflicted = rows.read_conflicted();
    let mut stores = owned::reserve_vec(rows.rows().len(), work)?;
    for row in rows.rows() {
        let key = require_text(row.key, work)?;
        stores.push((owned::text(key, work)?, owned::text(row.value, work)?));
    }
    work.charge(rows.rows().len())?;
    drop(rows);
    work.charge(0)?;
    let interpretation = ArrayInterpretation {
        default: owned::optional_text(input.default, work)?,
        stores,
        index_sort: sort::optional(input.index_sort, work)?,
        element_sort: sort::optional(input.element_sort, work)?,
    };
    let mut result = ArrayModel::default();
    let buckets = owned::reserve_table::<(TermId, ArrayInterpretation)>(1, work)?;
    result
        .array_values
        .try_reserve(1)
        .map_err(|_| work.refuse_exhaustion())?;
    owned::table_insert(buckets, work)?;
    result.array_values.insert(input.array, interpretation);
    if conflicted {
        let buckets = owned::reserve_table::<TermId>(1, work)?;
        result
            .read_conflicted
            .try_reserve(1)
            .map_err(|_| work.refuse_exhaustion())?;
        owned::table_insert(buckets, work)?;
        result.read_conflicted.insert(input.array);
    }
    Ok(result)
}

fn require_text<'a>(
    key: ModelCellKey<'a>,
    work: &mut WorkBudget<'_>,
) -> Result<&'a str, QueryError> {
    work.charge(1)?;
    match key {
        ModelCellKey::Text(text) => Ok(text),
        _ => Err(work.refuse_exhaustion()),
    }
}
