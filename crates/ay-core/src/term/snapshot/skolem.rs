// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-metered restoration of independently authenticated Skolem names.

use super::*;

#[cfg(test)]
mod tests;

impl TermStore {
    /// Move independently authenticated Skolem names into this store under
    /// the caller's shared work, allocation, and cancellation envelope.
    ///
    /// The caller MUST establish exact substitution, freshness, uniqueness,
    /// and dependency provenance before supplying names. This function does
    /// not authenticate them: like [`Self::mark_skolem_symbol`], registration
    /// changes authority consumed by the strict proof checker.
    ///
    /// Input Strings and their Vec already exist and are moved, not cloned;
    /// only new registry allocations are charged here. Use the same callback
    /// as snapshot reconstruction and name authentication to retain one total
    /// envelope. The private table's actual allocation/capacity is used, never
    /// producer memory ledgers or the number of terms.
    ///
    /// This consumes the store so no partially restored store escapes an
    /// error, including refusal at the final cancellation poll. Existing
    /// registrations are preserved; duplicates do not advance checker-visible
    /// metadata generation. Entries, snapshot identity, and choice definitions
    /// are unchanged.
    pub fn with_skolem_symbols_with_progress(
        mut self,
        names: Vec<String>,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<Self, TermSnapshotError> {
        charge(progress, 0, 0)?;
        // Also pay iteration/drop of the owned input if a later poll refuses.
        charge(progress, checked_add(names.len(), 1)?, 0)?;
        for name in names {
            charge(progress, 1, 0)?;
            registry_lookup(&self, &name, progress)?;
            if self.skolem_symbols.contains(name.as_str()) {
                continue;
            }
            // The legacy mutator's overflow is a panic. Check BEFORE changing
            // authority, and preserve duplicate/no-bump semantics at u64::MAX.
            let next_generation = self
                .checker_visible_metadata_generation
                .checked_add(1)
                .ok_or(TermSnapshotError::ResourceLimit)?;
            prepare_registry_insert(&mut self, &name, progress)?;
            if self.skolem_symbols.insert(name) {
                self.checker_visible_metadata_generation = next_generation;
            }
        }
        charge(progress, 0, 0)?;
        Ok(self)
    }
}

fn registry_lookup(store: &TermStore, name: &str, progress: Progress<'_>) -> SnapshotResult<()> {
    let entries = store.skolem_symbols.len();
    // No registry operation removes keys. With no tombstones, an occupied
    // collision cluster contains at most `entries` keys before its empty end.
    let comparisons = checked_add(entries, 1)?;
    charge(
        progress,
        checked_mul(comparisons, checked_add(name.len(), 2)?)?,
        0,
    )
}

fn prepare_registry_insert(
    store: &mut TermStore,
    name: &str,
    progress: Progress<'_>,
) -> SnapshotResult<()> {
    // `contains` and `insert` are separate searches. Reserve below may move
    // buckets but not change occupied cardinality; pay this search separately.
    registry_lookup(store, name, progress)?;
    if store.skolem_symbols.len() == store.skolem_symbols.capacity() {
        prepare_native_growth(store, progress)?;
    }
    charge(progress, 0, 0)
}

fn native_growth_bounds(allocation: usize) -> SnapshotResult<(usize, usize)> {
    // Locked hashbrown 0.15.5: reserve_rehash_inner(additional=1) either
    // rehashes in place or doubles the raw bucket count. calculate_layout_for
    // then needs no more than twice the old allocation. Empty String tables
    // start at four buckets; 128 covers alignment and control-group slack
    // (the supported Group widths are at most 16). Price both cases before
    // reserve rather than guessing hidden capacity or amortizing old credit.
    let initial = checked_add(checked_mul(4, size_of::<String>())?, 128)?;
    let bytes = checked_add(checked_mul(allocation, 2)?, initial)?;
    // Every raw bucket owns a String slot and a control byte, so division
    // yields a conservative upper bound despite alignment/control padding.
    let buckets = bytes / checked_add(size_of::<String>(), 1)?;
    Ok((bytes, buckets))
}

fn prepare_native_growth(store: &mut TermStore, progress: Progress<'_>) -> SnapshotResult<()> {
    let old_allocation = store.skolem_symbols.allocation_size();
    let (new_bytes, destination_buckets) = native_growth_bounds(old_allocation)?;
    let old_buckets = old_allocation / checked_add(size_of::<String>(), 1)?;
    let migration = checked_mul(
        store.skolem_symbols.len(),
        checked_add(destination_buckets, 1)?,
    )?;
    let controls = checked_add(checked_add(old_buckets, destination_buckets)?, 1)?;
    charge(progress, checked_add(migration, controls)?, new_bytes)?;
    // Iterating a hash table scans its raw capacity, priced above. Rehashing
    // also reads every old name, even when the new name is only one byte long.
    for old_name in &store.skolem_symbols {
        charge(progress, checked_add(old_name.len(), 1)?, 0)?;
    }
    store
        .skolem_symbols
        .try_reserve(1)
        .map_err(|_| TermSnapshotError::ResourceLimit)
}
