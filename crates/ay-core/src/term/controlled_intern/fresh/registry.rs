// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn limit() -> ControlledTermInternError {
    ControlledTermInternError::ResourceLimit
}

fn mul(a: usize, b: usize) -> Result<usize> {
    a.checked_mul(b).ok_or_else(limit)
}

fn slots(store: &TermStore) -> Result<usize> {
    (store.names.allocation_size() / size_of::<(String, (TermId, Sort))>())
        .checked_add(32)
        .ok_or_else(limit)
}

pub(super) fn probe(store: &TermStore, admission: &mut Admission<'_>) -> Result<()> {
    admission.pay(mul(slots(store)?, 64)?, 0)
}

pub(super) fn reserve(
    store: &mut TermStore,
    key_bytes: usize,
    admission: &mut Admission<'_>,
) -> Result<()> {
    store.true_memory_cache.set(0);
    if store.names.capacity() == store.names.len() {
        let old = slots(store)?;
        let items = store.names.len().checked_add(1).ok_or_else(limit)?;
        let future = mul(
            old.checked_add(items)
                .and_then(|n| n.checked_add(32))
                .ok_or_else(limit)?,
            4,
        )?;
        // Displaced rehash can repeatedly hash old variable-length keys.
        // Bound whole key payload plus every possible old/new-table probe
        // per key, never an average distribution or scalar-key assumption.
        let per_key = old
            .checked_add(future)
            .and_then(|n| n.checked_add(key_bytes))
            .and_then(|n| n.checked_add(1))
            .ok_or_else(limit)?;
        let work = mul(mul(items, per_key)?, 128)?;
        let bytes = mul(
            old.checked_add(future).ok_or_else(limit)?,
            size_of::<(String, (TermId, Sort))>() + 32,
        )?;
        admission.pay(work, mul(bytes, 8)?)?;
    } else {
        admission.pay(1, 0)?;
    }
    store.names.try_reserve(1).map_err(|_| limit())
}
