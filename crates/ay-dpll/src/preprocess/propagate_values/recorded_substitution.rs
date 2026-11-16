// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Early-ABV substitution provenance, sharing PropagateValues' ordered ledger.
//! Recording is not proof authority and never edits authored source sets.

use std::sync::{Arc, Mutex};

use super::*;
use crate::preprocess::VariableSubstitution;

mod records;
#[cfg(test)]
mod tests;

/// A recording-only wrapper around the actual shared substitution pass.
/// The callback bounds recording; it cannot interrupt VariableSubstitution's
/// existing synchronous traversal. The delegate runs exactly once even when
/// recording refuses, and all hints are withheld after an incomplete round.
pub(crate) struct RecordedVariableSubstitution {
    substitution: Arc<Mutex<VariableSubstitution>>,
    propagation: Arc<Mutex<PropagateValues>>,
    progress: Box<dyn FnMut(usize, usize) -> bool>,
}

impl RecordedVariableSubstitution {
    pub(crate) fn new(
        substitution: Arc<Mutex<VariableSubstitution>>,
        propagation: Arc<Mutex<PropagateValues>>,
        progress: Box<dyn FnMut(usize, usize) -> bool>,
    ) -> Self {
        Self {
            substitution,
            propagation,
            progress,
        }
    }

    fn apply_recorded(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        apply: impl FnOnce(&mut VariableSubstitution, &mut TermStore, &mut Vec<TermId>) -> bool,
    ) -> bool {
        let substitution = Arc::clone(&self.substitution);
        let Ok(mut pass) = substitution.lock() else {
            self.withhold();
            return false;
        };
        let stamp = self.begin();
        let before = stamp.and_then(|_| {
            let bytes = assertions.len().checked_mul(size_of::<TermId>())?;
            (self.progress)(assertions.len(), bytes).then(|| assertions.clone())
        });
        let changed = apply(&mut pass, terms, assertions);
        let records = match (stamp, before) {
            (Some(stamp), Some(before)) => records::round(
                terms,
                &before,
                assertions,
                &pass,
                stamp,
                self.progress.as_mut(),
            )
            .map(|records| (stamp, records)),
            _ => None,
        };
        drop(pass);
        if let Some((stamp, records)) = records {
            self.append(stamp, records);
        } else {
            self.withhold();
        }
        changed
    }

    fn begin(&mut self) -> Option<u32> {
        if !(self.progress)(1, 0) {
            return None;
        }
        let mut pass = self.propagation.lock().ok()?;
        if pass.records_overflowed {
            return None;
        }
        pass.apply_calls = pass.apply_calls.checked_add(1)?;
        Some(pass.apply_calls)
    }

    fn append(&mut self, stamp: u32, records: PropagationRecords) {
        // Existing PV records may have been created outside this wrapper's
        // callback. Pay for the complete destination growth, not just the new
        // suffix. Never invoke the caller callback while holding a PV lock.
        let cost = self.append_cost(stamp, &records);
        let Some((work, bytes)) = cost else {
            self.withhold();
            return;
        };
        if !(self.progress)(work, bytes) {
            self.withhold();
            return;
        }
        let mut pass = match self.propagation.lock() {
            Ok(pass) => pass,
            Err(poisoned) => {
                let mut pass = poisoned.into_inner();
                pass.records_overflowed = true;
                pass.entry_sources.clear();
                pass.rewrite_records.clear();
                return;
            }
        };
        if pass.records_overflowed
            || pass.apply_calls != stamp
            || pass
                .entry_sources
                .len()
                .checked_add(records.entries.len())
                .is_none_or(|count| count > MAX_PROPAGATION_RECORDS)
            || pass
                .rewrite_records
                .len()
                .checked_add(records.rewrites.len())
                .is_none_or(|count| count > MAX_PROPAGATION_RECORDS)
            || pass
                .entry_sources
                .try_reserve_exact(records.entries.len())
                .is_err()
            || pass
                .rewrite_records
                .try_reserve_exact(records.rewrites.len())
                .is_err()
        {
            pass.records_overflowed = true;
            pass.entry_sources.clear();
            pass.rewrite_records.clear();
            return;
        }
        pass.entry_sources.extend(records.entries);
        pass.rewrite_records.extend(records.rewrites);
    }

    fn append_cost(&self, stamp: u32, records: &PropagationRecords) -> Option<(usize, usize)> {
        let pass = self.propagation.lock().ok()?;
        if pass.records_overflowed || pass.apply_calls != stamp {
            return None;
        }
        let entries = pass
            .entry_sources
            .len()
            .checked_add(records.entries.len())?;
        let rewrites = pass
            .rewrite_records
            .len()
            .checked_add(records.rewrites.len())?;
        if entries > MAX_PROPAGATION_RECORDS || rewrites > MAX_PROPAGATION_RECORDS {
            return None;
        }
        let total = entries.checked_add(rewrites)?;
        Some((total, total.checked_mul(32)?))
    }

    fn withhold(&mut self) {
        let mut pass = match self.propagation.lock() {
            Ok(pass) => pass,
            Err(poisoned) => poisoned.into_inner(),
        };
        pass.records_overflowed = true;
        pass.entry_sources.clear();
        pass.rewrite_records.clear();
    }
}

impl PreprocessingPass for RecordedVariableSubstitution {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        self.apply_recorded(terms, assertions, |pass, terms, assertions| {
            pass.apply(terms, assertions)
        })
    }

    fn apply_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> bool {
        self.apply_recorded(terms, assertions, |pass, terms, assertions| {
            pass.apply_with_sources(terms, assertions, source_sets)
        })
    }

    fn reset(&mut self) {
        let substitution = Arc::clone(&self.substitution);
        if let Ok(mut pass) = substitution.lock() {
            pass.reset();
        } else {
            self.withhold();
        };
    }
}
