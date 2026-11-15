// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-driven discovery only: no assertion replacement or solver authority.

use super::*;

mod discovery;
pub(crate) mod install;
#[cfg(test)]
mod tests;
mod units;

/// An exact unit consequence, checked against the batch's complete originals.
/// Replacing its term store or originals requires fresh authentication.
#[derive(Debug)]
pub(crate) struct CheckedActivatedUnit {
    unit: TermId,
    proof: Proof,
    conclusion: ProofId,
}

impl CheckedActivatedUnit {
    pub(crate) fn unit(&self) -> TermId {
        self.unit
    }

    pub(crate) fn proof(&self) -> (&Proof, ProofId) {
        (&self.proof, self.conclusion)
    }
}

/// Immutable additions, never a replacement for the original branch clauses.
/// The retained IDs refer to the supplied term store, not another arena with
/// coincidentally equal numeric IDs. This is proof data, not a SAT permit.
#[derive(Debug)]
pub(crate) struct GuardedStoreBatch {
    original_roots: Vec<TermId>,
    definitions: Vec<GuardedStoreDefinition>,
    activated_units: Vec<CheckedActivatedUnit>,
}

impl GuardedStoreBatch {
    pub(crate) fn original_roots(&self) -> &[TermId] {
        &self.original_roots
    }

    pub(crate) fn definitions(&self) -> &[GuardedStoreDefinition] {
        &self.definitions
    }

    pub(crate) fn activated_units(&self) -> &[CheckedActivatedUnit] {
        &self.activated_units
    }
}

/// Discover exact guarded common-store definitions and activated alias/cover
/// units. Only originally asserted positive Bool variables activate a source;
/// neither derived units nor model assignments become discovery assumptions.
///
/// All discovery, copying, derivation and strict authentication uses the same
/// monotone callback. Any refusal discards the whole batch; harmless interned
/// scratch terms may remain. This function does not mutate assertions.
pub(crate) fn discover(
    terms: &mut TermStore,
    original_roots: &[TermId],
    progress: Progress<'_>,
) -> Option<GuardedStoreBatch> {
    if !progress(
        original_roots.len(),
        original_roots.len().checked_mul(16)?.checked_add(256)?,
    ) {
        return None;
    }
    let roots = original_roots.to_vec();
    let plan = discovery::scan(terms, original_roots, progress)?;
    let mut definitions = Vec::new();
    for request in plan.requests {
        if !progress(1, 512) {
            return None;
        }
        definitions.push(derive(terms, original_roots, request, progress)?);
    }
    let mut activated_units = Vec::new();
    for unit in plan.units {
        if !progress(1, 512) {
            return None;
        }
        activated_units.push(units::derive(terms, original_roots, unit, progress)?);
    }
    if !progress(0, 0) {
        return None;
    }
    Some(GuardedStoreBatch {
        original_roots: roots,
        definitions,
        activated_units,
    })
}
