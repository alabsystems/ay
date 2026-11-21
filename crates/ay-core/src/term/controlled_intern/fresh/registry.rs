// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::kani_compat::hash_table_cost as table;

fn limit() -> ControlledTermInternError {
    ControlledTermInternError::ResourceLimit
}

pub(in crate::term::controlled_intern) fn probe(
    store: &TermStore,
    admission: &mut Admission<'_>,
) -> Result<()> {
    admission.pay(
        table::iteration::<(String, (TermId, Sort))>(
            store.names.allocation_size(),
            store.names.len(),
        )
        .ok_or_else(limit)?,
        0,
    )
}

pub(in crate::term::controlled_intern) fn insert_probe(
    store: &TermStore,
    name: &str,
    admission: &mut Admission<'_>,
) -> Result<()> {
    admission.pay(
        table::string_lookup::<(String, (TermId, Sort))>(
            store.names.allocation_size(),
            store.names.len(),
            name.len(),
        )
        .ok_or_else(limit)?,
        0,
    )
}

pub(in crate::term::controlled_intern) fn reserve(
    store: &mut TermStore,
    key_bytes: usize,
    admission: &mut Admission<'_>,
) -> Result<()> {
    store.true_memory_cache.set(0);
    let cost = table::reserve_one::<(String, (TermId, Sort))>(
        store.names.allocation_size(),
        store.names.len(),
        store.names.capacity(),
    )
    .ok_or_else(limit)?;
    admission.pay(cost.work, cost.storage_bytes)?;
    if cost.rehashes {
        // The earlier paid freshness scan collected ALL original key bytes.
        // Rehash moves headers and hashes each key once, even through swaps.
        admission.pay(table::string_hash_payload(key_bytes).ok_or_else(limit)?, 0)?;
    }
    store.names.try_reserve(1).map_err(|_| limit())
}
