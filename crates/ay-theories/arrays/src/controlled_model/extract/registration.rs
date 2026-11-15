// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Extraction-only cold registration, not a production-ready solver/cache.

use super::*;
use crate::{AffineCache, ArrayVarData};
use ay_core::term::{Symbol, TermStoreSnapshotStamp};
use std::mem::{align_of, size_of};

mod backing;
mod binding;
mod maps;
mod shape;
#[cfg(test)]
mod tests;

impl ArraySolver<'_> {
    /// Extract existing warm DATA, or prepare a cold class-free extraction view.
    ///
    /// The cold lane requires dirty structural AND assignment layers, the exact
    /// registered source scope, flat arrays, and no active true equality. It
    /// reconstructs only extraction-read inventories; it does not publish
    /// caches, replay native queues, solve, or grant model/source authority.
    /// Stores, maps, as-array, lambda, nested arrays and dirty merge classes
    /// refuse. The existing warm API and its ordered class behavior are exact.
    /// One fixed legacy Rc allocation is prepaid but allocator abort remains
    /// outside fallible Vec/map reservations. Later output disposal is caller-owned.
    pub fn try_extract_registered_model_with_budget(
        &self,
        values: &HashMap<TermId, String>,
        work: &mut WorkBudget<'_>,
    ) -> Result<ArrayModel, QueryError> {
        work.charge(16)?;
        if !self.dirty {
            return self.try_extract_prepared_model_with_budget(values, work);
        }
        let result = cold(self, values, work);
        owned::finish(result, work)
    }
}

fn cold(
    source: &ArraySolver<'_>,
    values: &HashMap<TermId, String>,
    work: &mut WorkBudget<'_>,
) -> Result<ArrayModel, QueryError> {
    let binding = binding::Binding::capture(source, work)?;
    shape::source(source, work)?;
    // Covers constructor value/header writes, moves and complete destruction.
    // Pinned RcInner<T> has two usize cells followed by aligned T. All its
    // AffineCache maps are empty: no BigInt/string/vector payload is allocated.
    let rc = owned::checked(
        size_of::<AffineCache>()
            .checked_add(2 * size_of::<usize>())
            .and_then(|n| n.checked_add(2 * align_of::<AffineCache>().max(align_of::<usize>()))),
        work,
    )?;
    let bytes = owned::checked(
        size_of::<ArraySolver<'_>>()
            .checked_add(rc)
            .and_then(|n| n.checked_mul(8)),
        work,
    )?;
    // Byte/header visits conservatively cover every pinned constructor field
    // and its initialization/move/drop, rather than guessing a field count.
    work.admit(bytes, bytes)?;
    let mut view = ArraySolver::new(source.terms);
    let result = prepare(source, &mut view, work)
        .and_then(|()| view.try_extract_prepared_model_with_budget(values, work));
    // Every variable-capacity backing/move/drop was prepaid before reservation.
    // No view or its native caches can escape this extraction-only function.
    drop(view);
    let stable = binding.verify(source, work);
    drop(binding);
    work.charge(0)?;
    stable?;
    result
}

fn prepare(
    source: &ArraySolver<'_>,
    view: &mut ArraySolver<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    backing::restore(source, view, work)?;
    maps::assignments(source, view, work)?;
    view.var_layer_terms = owned::reserve_vec(source.terms.len(), work)?;
    for index in 0..source.terms.len() {
        work.charge(1)?;
        let term = TermId(u32::try_from(index).map_err(|_| work.refuse_exhaustion())?);
        if !shape::scoped(source, term, work)? {
            continue;
        }
        shape::term(source, term, work)?;
        if let TermData::App(symbol, args) = source.terms.get(term) {
            register(view, term, symbol, args, work)?;
        }
    }
    // Every admitted equality is false or unassigned; no proof forest edge is
    // fabricated. Native event queues are intentionally not made usable here.
    view.populated_terms = source.terms.len();
    view.dirty = false;
    view.var_layer_dirty = false;
    view.assign_dirty = false;
    view.shadow_uf_stale = false;
    work.charge(0)
}

fn register(
    view: &mut ArraySolver<'_>,
    term: TermId,
    symbol: &Symbol,
    args: &[TermId],
    work: &mut WorkBudget<'_>,
) -> Result<(), QueryError> {
    // Shape validation already prepaid borrowed argument reads. This separate
    // header/name offer precedes dispatch and repeated scalar cache accesses.
    let visits = owned::checked(symbol.name().len().checked_add(32), work)?;
    work.charge(visits)?;
    match symbol.name() {
        "select" => {
            maps::insert(&mut view.select_cache, term, (args[0], args[1]), work)?;
            maps::insert(&mut view.select_pair_index, (args[0], args[1]), term, work)?;
            view.var_layer_terms.push(term);
            maps::select(view, term, args[0], work)?;
        }
        "const-array" => {
            maps::insert(&mut view.const_array_cache, term, args[0], work)?;
        }
        "default" => {
            maps::insert(&mut view.default_cache, args[0], term, work)?;
            view.var_layer_terms.push(term);
        }
        "=" => {
            maps::insert(&mut view.equality_cache, term, (args[0], args[1]), work)?;
            maps::reverse(view, args[0], term, work)?;
            maps::reverse(view, args[1], term, work)?;
            maps::insert(
                &mut view.eq_pair_index,
                ArraySolver::ordered_pair(args[0], args[1]),
                term,
                work,
            )?;
            if matches!(view.terms.sort(args[0]), Sort::Array(_)) {
                view.var_layer_terms.push(term);
            }
            maps::false_assignment(view, term, args[0], args[1], work)?;
        }
        _ => {}
    }
    Ok(())
}
