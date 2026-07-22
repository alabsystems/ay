// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared proof-path caches for incremental solving.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, TermStore, TheoryLit};

/// Tracks SAT-visible terms whose negations are needed for proof construction.
#[derive(Clone, Default)]
pub(crate) struct IncrementalNegationCache {
    enabled: bool,
    negations: HashMap<TermId, TermId>,
    pending_terms: Vec<TermId>,
    pending_set: HashSet<TermId>,
}

impl IncrementalNegationCache {
    /// Build the initial negation map from the current SAT-visible terms.
    pub(crate) fn seed<I>(terms: &mut TermStore, initial_terms: I, enabled: bool) -> Self
    where
        I: IntoIterator<Item = TermId>,
    {
        let mut cache = Self {
            enabled,
            negations: HashMap::default(),
            pending_terms: Vec::new(),
            pending_set: HashSet::default(),
        };
        if enabled {
            for term in initial_terms {
                cache
                    .negations
                    .entry(term)
                    .or_insert_with(|| terms.mk_not(term));
            }
        }
        cache
    }

    /// Record a newly SAT-visible term whose negation may be needed later.
    pub(crate) fn note_fresh_term(&mut self, term: TermId) {
        if !self.enabled || self.negations.contains_key(&term) {
            return;
        }
        if self.pending_set.insert(term) {
            self.pending_terms.push(term);
        }
    }

    /// Materialize negations only for terms added since the last sync.
    pub(crate) fn sync_pending(&mut self, terms: &mut TermStore) {
        if !self.enabled || self.pending_terms.is_empty() {
            return;
        }
        for term in self.pending_terms.drain(..) {
            self.negations
                .entry(term)
                .or_insert_with(|| terms.mk_not(term));
        }
        self.pending_set.clear();
    }

    /// Expose the negation map for proof consumers.
    pub(crate) fn as_map(&self) -> &HashMap<TermId, TermId> {
        &self.negations
    }
}

/// O(1) membership test for replayed theory lemmas.
#[derive(Default)]
pub(crate) struct TheoryLemmaSeenSet {
    seen: HashSet<Vec<TheoryLit>>,
}

impl TheoryLemmaSeenSet {
    fn clause_key(clause: &[TheoryLit]) -> Vec<TheoryLit> {
        let mut key = clause.to_vec();
        key.sort_unstable();
        key.dedup();
        key
    }

    /// Returns `true` only for the first occurrence of a clause.
    pub(crate) fn insert(&mut self, clause: &[TheoryLit]) -> bool {
        self.seen.insert(Self::clause_key(clause))
    }
}

#[cfg(test)]
#[path = "incremental_proof_cache_tests.rs"]
mod tests;
