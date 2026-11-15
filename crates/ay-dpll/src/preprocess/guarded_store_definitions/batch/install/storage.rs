// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn validate(
    terms: &TermStore,
    originals: &[TermId],
    working: &[TermId],
    source_sets: &[Vec<TermId>],
    batch: &GuardedStoreBatch,
    progress: Progress<'_>,
) -> Option<()> {
    if !progress(1, 0)
        || originals.len() != batch.original_roots.len()
        || working.len() != source_sets.len()
    {
        return None;
    }
    for (&actual, &retained) in originals.iter().zip(&batch.original_roots) {
        if !progress(1, 0) || actual != retained {
            return None;
        }
        boolean(terms, actual)?;
    }
    for (&root, sources) in working.iter().zip(source_sets) {
        if !progress(1, 0) {
            return None;
        }
        boolean(terms, root)?;
        for &source in sources {
            if !progress(1, 0) {
                return None;
            }
            boolean(terms, source)?;
        }
    }
    Some(())
}

fn boolean(terms: &TermStore, term: TermId) -> Option<()> {
    ((term.0 as usize) < terms.len() && terms.sort(term) == &Sort::Bool).then_some(())
}

pub(super) fn allocate(
    working: &[TermId],
    source_sets: &[Vec<TermId>],
    units: usize,
    progress: Progress<'_>,
) -> Option<PreparedArrayUnits> {
    use std::mem::{align_of, size_of};

    let rows = units.checked_add(working.len())?;
    let mut sources = 0usize;
    for set in source_sets {
        // Debit the sizing walk separately from validation and copying.
        if !progress(1, 0) {
            return None;
        }
        sources = sources.checked_add(set.len())?;
    }
    let row_bytes = rows.checked_mul(size_of::<TermId>() + size_of::<Vec<TermId>>())?;
    let source_bytes = sources.checked_mul(size_of::<TermId>())?;
    // ArcInner has two usize counters and may pad before its Proof payload.
    // Proof's existing buffers transfer ownership; no clause/step clone occurs.
    let arc_bytes = size_of::<Proof>()
        .checked_add(2 * size_of::<usize>())?
        .checked_add(align_of::<Proof>())?;
    let unit_bytes = units.checked_mul(arc_bytes.checked_add(size_of::<ArrayUnitDerivation>())?)?;
    let bytes = row_bytes
        .checked_add(source_bytes)?
        .checked_add(unit_bytes)?;
    let work = rows.checked_add(sources)?.checked_add(units)?;
    if !progress(work, bytes) {
        return None;
    }
    let mut assertions = Vec::new();
    let mut source_sets = Vec::new();
    let mut array_units = Vec::new();
    assertions.try_reserve_exact(rows).ok()?;
    source_sets.try_reserve_exact(rows).ok()?;
    array_units.try_reserve_exact(units).ok()?;
    Some(PreparedArrayUnits {
        assertions,
        source_sets,
        array_units,
    })
}
