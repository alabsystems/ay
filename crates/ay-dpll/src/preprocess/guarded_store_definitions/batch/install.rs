// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prepare source-derived units without changing any caller-owned assertions.
//!
//! The early-ABV caller supplies its original-snapshot working rows before
//! other preprocessing. This helper preserves those rows and their source
//! sets; it neither fills missing originals nor authenticates arbitrary source
//! sets as authored premises. Derived units retain separate proof provenance.

use std::sync::Arc;

use super::*;
use crate::preprocess::propagate_values::ArrayUnitDerivation;

mod storage;
#[cfg(test)]
mod tests;

/// A complete candidate working state, not solver or source-premise authority.
/// No part is exposed until all units have been freshly authenticated.
pub(crate) struct PreparedArrayUnits {
    assertions: Vec<TermId>,
    source_sets: Vec<Vec<TermId>>,
    array_units: Vec<ArrayUnitDerivation>,
}

impl PreparedArrayUnits {
    /// Move the data into the caller's working state. Consumers must still
    /// reauthenticate each immutable unit against their current originals.
    pub(crate) fn into_parts(self) -> (Vec<TermId>, Vec<Vec<TermId>>, Vec<ArrayUnitDerivation>) {
        (self.assertions, self.source_sets, self.array_units)
    }

    fn push_checked(
        &mut self,
        terms: &TermStore,
        original_roots: &[TermId],
        term: TermId,
        proof: Proof,
        conclusion: ProofId,
        progress: Progress<'_>,
    ) -> Option<()> {
        // The Arc header and the moved Proof object were prepaid by storage;
        // its existing steps/clauses are moved, never deeply cloned here.
        let unit = ArrayUnitDerivation::checked(
            terms,
            original_roots,
            Arc::new(proof),
            conclusion,
            term,
            progress,
        )?;
        self.assertions.push(term);
        self.source_sets.push(Vec::new());
        self.array_units.push(unit);
        Some(())
    }
}

/// Consume an already discovered batch using the same monotone progress
/// callback used for discovery. All supplied working rows/source sets survive
/// unchanged, after definitions and then activated units; duplicates survive.
///
/// Retained original IDs must match exactly, and every proof is freshly checked
/// against the actual term store and complete originals. Caller inputs are
/// borrowed and never mutated, including on allocation or final-poll refusal.
pub(crate) fn prepare(
    terms: &TermStore,
    original_roots: &[TermId],
    working_roots: &[TermId],
    source_sets: &[Vec<TermId>],
    batch: GuardedStoreBatch,
    progress: Progress<'_>,
) -> Option<PreparedArrayUnits> {
    storage::validate(
        terms,
        original_roots,
        working_roots,
        source_sets,
        &batch,
        progress,
    )?;
    let count = batch
        .definitions
        .len()
        .checked_add(batch.activated_units.len())?;
    let mut prepared = storage::allocate(working_roots, source_sets, count, progress)?;
    for definition in batch.definitions {
        prepared.push_checked(
            terms,
            original_roots,
            definition.definition,
            definition.proof,
            definition.conclusion,
            progress,
        )?;
    }
    for unit in batch.activated_units {
        prepared.push_checked(
            terms,
            original_roots,
            unit.unit,
            unit.proof,
            unit.conclusion,
            progress,
        )?;
    }
    for (&root, sources) in working_roots.iter().zip(source_sets) {
        let mut copied = Vec::new();
        copied.try_reserve_exact(sources.len()).ok()?;
        copied.extend_from_slice(sources);
        prepared.assertions.push(root);
        prepared.source_sets.push(copied);
    }
    if !progress(0, 0) {
        return None;
    }
    Some(prepared)
}
