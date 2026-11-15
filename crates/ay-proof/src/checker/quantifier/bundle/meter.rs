// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked allocation/lookup charges for whole-proof Skolem registries.

use super::*;
use std::mem::size_of;

pub(super) fn add(a: usize, b: usize) -> Result<usize, ProofCheckError> {
    a.checked_add(b).ok_or(ProofCheckError::ResourceLimit)
}

pub(super) fn mul(a: usize, b: usize) -> Result<usize, ProofCheckError> {
    a.checked_mul(b).ok_or(ProofCheckError::ResourceLimit)
}

pub(super) fn proof_id(index: usize) -> Result<ProofId, ProofCheckError> {
    Ok(ProofId(
        u32::try_from(index).map_err(|_| ProofCheckError::ResourceLimit)?,
    ))
}

pub(super) fn invalid_named(
    meter: &mut QuantifierMeter<'_, '_>,
    step: ProofId,
    message: &'static str,
    names: &[&str],
) -> Result<ProofCheckError, ProofCheckError> {
    let mut bound = add(message.len(), 32)?;
    for name in names {
        bound = add(bound, add(mul(name.len(), 10)?, 4)?)?;
    }
    let bound = mul(bound, 4)?;
    meter.charge(bound, bound)?;
    Ok(invalid(step, format!("{message}: {names:?}")))
}

fn insert_storage<T>(
    meter: &mut QuantifierMeter<'_, '_>,
    entries: usize,
) -> Result<(), ProofCheckError> {
    if entries >= SKOLEM_TERM_WORK_LIMIT {
        return Err(ProofCheckError::ResourceLimit);
    }
    meter.charge(1, add(mul(size_of::<T>(), 4)?, 128)?)
}

pub(super) fn id_map_entry<V>(
    meter: &mut QuantifierMeter<'_, '_>,
    map: &HashMap<TermId, V>,
    key: TermId,
) -> Result<(), ProofCheckError> {
    meter.lookup("", map.len())?;
    let existing = map.contains_key(&key);
    meter.lookup("", map.len())?; // The caller's entry/insert probes again.
    if existing {
        return Ok(());
    }
    let growing = map.len() == map.capacity();
    if growing {
        meter.charge(mul(map.len(), add(map.len(), 1)?)?, 0)?;
    }
    insert_storage::<(TermId, V)>(meter, map.len())
}

pub(super) fn insert_id(
    meter: &mut QuantifierMeter<'_, '_>,
    set: &mut HashSet<TermId>,
    id: TermId,
) -> Result<(), ProofCheckError> {
    meter.lookup("", set.len())?;
    if set.contains(&id) {
        return Ok(());
    }
    meter.lookup("", set.len())?;
    let growing = set.len() == set.capacity();
    if growing {
        meter.charge(mul(set.len(), add(set.len(), 1)?)?, 0)?;
    }
    insert_storage::<TermId>(meter, set.len())?;
    set.insert(id);
    Ok(())
}
