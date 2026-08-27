// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Epoch- and entry-stamped context-derivation evidence.

use ay_core::term::TermEntryStamp;
use ay_core::{TermData, TermId};
use ay_frontend::SourceContextStamp;

use crate::executor::{DtContextConflictRecord, Executor, QueryAuthorityEpoch};

#[must_use = "checked context-derivation evidence must be consumed or discarded"]
pub(super) struct CheckedContextDerivation {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: SourceContextStamp,
    clause: Vec<TermId>,
    clause_entries: Vec<TermEntryStamp>,
    premises: Vec<TermId>,
    premise_entries: Vec<TermEntryStamp>,
}

impl CheckedContextDerivation {
    /// Seal a producer-recorded context conflict (#dt-context-derivation).
    ///
    /// The record grants no authority: sealing independently re-derives the
    /// entailment by widening the clause with the parity negation of every
    /// premise and requiring the bounded ground refuter to refute the
    /// widened clause's negation against the datatype registries — the SAME
    /// recognizer the fragment lane and the strict checker run, so
    /// acceptance is re-decided identically at every stage. Collisions,
    /// oversized records, and registry absence all decline.
    pub(super) fn seal(executor: &mut Executor, record: &DtContextConflictRecord) -> Option<Self> {
        const MAX_CONTEXT_LITERALS: usize = 64;
        if record.clause.is_empty()
            || record.premises.is_empty()
            || record.clause.len() > MAX_CONTEXT_LITERALS
            || record.premises.len() > MAX_CONTEXT_LITERALS
        {
            return None;
        }
        let registry = crate::theory_inference::dt_funnel_registry_data(&executor.ctx)?;
        let mut widened = record.clause.clone();
        let mut negated: Vec<TermId> = Vec::with_capacity(record.premises.len());
        for &premise in &record.premises {
            let negation = match executor.ctx.terms.get(premise) {
                TermData::Not(inner) => *inner,
                _ => executor.ctx.terms.mk_not(premise),
            };
            if widened.contains(&negation) || negated.contains(&negation) {
                return None;
            }
            negated.push(negation);
            widened.push(negation);
        }
        let view = crate::theory_inference::DatatypeRegistries::from_data(&registry);
        if !ay_proof::recognize_datatype_ground_conflict(
            &executor.ctx.terms,
            &widened,
            view.datatypes,
            view.ctor_selectors,
        ) {
            return None;
        }
        Some(Self {
            query_epoch: executor.query_authority_epoch.clone(),
            source_context_stamp: executor.ctx.source_context_stamp(),
            clause: record.clause.clone(),
            clause_entries: record
                .clause
                .iter()
                .map(|&term| executor.ctx.terms.entry_stamp(term))
                .collect::<Option<Vec<_>>>()?,
            premises: record.premises.clone(),
            premise_entries: record
                .premises
                .iter()
                .map(|&term| executor.ctx.terms.entry_stamp(term))
                .collect::<Option<Vec<_>>>()?,
        })
    }

    /// Re-verify every stamp and yield the normalized-clause key plus this
    /// record's premise set for aggregation.
    pub(super) fn into_current(self, executor: &Executor) -> Option<(Vec<TermId>, Vec<TermId>)> {
        (self
            .query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.clause_entries.iter().copied().map(Some).eq(self
                .clause
                .iter()
                .map(|&term| executor.ctx.terms.entry_stamp(term)))
            && self.premise_entries.iter().copied().map(Some).eq(self
                .premises
                .iter()
                .map(|&term| executor.ctx.terms.entry_stamp(term))))
        .then(|| {
            let mut key = self.clause.clone();
            key.sort_unstable();
            key.dedup();
            (key, self.premises)
        })
    }
}
