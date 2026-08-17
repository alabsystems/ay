// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared proof-path caches for incremental solving.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{ClausificationProof, TermId, TermStore, TheoryLemmaProof, TheoryLit, TseitinState};

/// Proof authority captured at the exact original-clause emission site and
/// drained into the clause-ID-indexed ledgers before proof reconstruction.
#[derive(Clone)]
pub(crate) enum PendingOriginalClauseAuthority {
    Clausification {
        original_id: u64,
        proof: ClausificationProof,
    },
    Theory {
        original_id: u64,
        proof: TheoryLemmaProof,
    },
}

/// Tracks SAT-visible terms whose negations are needed for proof construction.
///
/// **Also carries the persistent incremental Tseitin encoder state** (#incr-tseitin-persist).
/// Historically every cache-miss atom encode in `split_incremental` rebuilt the
/// entire accumulated Tseitin state from the local term↔var maps (`local_tseitin_state`)
/// and iterated the whole result map back (`merge_local_mappings_from_tseitin`),
/// making each encode O(total-encoded-terms) and the whole split loop O(n²). The
/// encoder state is threaded to *every* encode helper through this cache (which
/// already rides alongside the local maps), so persisting it here lets each
/// encode touch only its own delta — O(size-of-atom) — without a single new
/// parameter or macro-threading change. The state is seeded lazily from the
/// local maps on first use and re-created fresh (via `seed`) each check-sat.
#[derive(Clone, Default)]
pub(crate) struct IncrementalNegationCache {
    enabled: bool,
    negations: HashMap<TermId, TermId>,
    pending_terms: Vec<TermId>,
    pending_set: HashSet<TermId>,
    /// Persistent Tseitin encoder state (1-indexed DIMACS namespace). `None`
    /// until first use, when it is seeded from the current local maps. Held
    /// out via `take_tseitin_encoder` for the duration of one encode and put
    /// back with `put_tseitin_encoder`.
    tseitin_encoder: Option<TseitinState>,
    pending_original_authorities: Vec<PendingOriginalClauseAuthority>,
}

impl IncrementalNegationCache {
    pub(crate) fn proof_enabled(&self) -> bool {
        self.enabled
    }

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
            tseitin_encoder: None,
            pending_original_authorities: Vec::new(),
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

    /// Take ownership of the persistent Tseitin encoder state for one encode.
    ///
    /// On first use (`None`) the state is seeded from the current local maps,
    /// exactly reproducing the old `local_tseitin_state` seeding: local maps are
    /// 0-indexed SAT vars, the encoder is 1-indexed DIMACS, so `+1` on the way in.
    /// The `encoded` polarity cache is always reset to empty so each assertion is
    /// clausified from scratch — byte-identical to the prior per-call fresh
    /// `TseitinState` — while the term↔var maps and `next_var` persist across
    /// calls (that persistence is the O(n²)→O(n) fix; the maps are no longer
    /// copied per atom).
    ///
    /// `local_next_var` is a 0-indexed high-water mark; the encoder's `next_var`
    /// is raised to `local_next_var + 1` if lower (the old
    /// `next_var: local_next_var + 1` / `ensure_min_next_var` floor) so freshly
    /// minted Tseitin vars never collide with solver-reserved vars.
    pub(crate) fn take_tseitin_encoder(
        &mut self,
        local_term_to_var: &HashMap<TermId, u32>,
        local_var_to_term: &HashMap<u32, TermId>,
        local_next_var: u32,
    ) -> TseitinState {
        match self.tseitin_encoder.take() {
            Some(mut state) => {
                // Reset the polarity cache: each assertion clausifies fresh,
                // matching the historical per-call `encoded: Default::default()`.
                state.encoded = Default::default();
                if state.next_var < local_next_var + 1 {
                    state.next_var = local_next_var + 1;
                }
                state
            }
            None => TseitinState {
                term_to_var: local_term_to_var
                    .iter()
                    .map(|(&term, &var)| (term, var + 1))
                    .collect(),
                var_to_term: local_var_to_term
                    .iter()
                    .map(|(&var, &term)| (var + 1, term))
                    .collect(),
                next_var: local_next_var + 1,
                encoded: Default::default(),
            },
        }
    }

    /// Return the encoder state after an encode so the next atom reuses it.
    pub(crate) fn put_tseitin_encoder(&mut self, state: TseitinState) {
        self.tseitin_encoder = Some(state);
    }

    /// Mirror a direct local-map var allocation into the persistent encoder.
    ///
    /// Some `split_incremental` paths (the opaque-predicate fast path and the
    /// root-alias fallback) allocate/alias a SAT var without going through the
    /// Tseitin encoder. To keep the persistent encoder consistent with the local
    /// maps — so a later encode that references `term` as a subterm reuses this
    /// var instead of minting a fresh, orphaned duplicate (#8786) — record the
    /// same mapping here. `var_0idx` is the 0-indexed SAT var; the encoder stores
    /// it 1-indexed. No-op while the encoder is unseeded (`None`): the eventual
    /// lazy seed reads the local maps, which already carry this entry.
    pub(crate) fn mirror_encoder_var(&mut self, term: TermId, var_0idx: u32) {
        if let Some(ref mut state) = self.tseitin_encoder {
            state.term_to_var.insert(term, var_0idx + 1);
            state.var_to_term.entry(var_0idx + 1).or_insert(term);
            if state.next_var < var_0idx + 2 {
                state.next_var = var_0idx + 2;
            }
        }
    }

    pub(crate) fn note_clausification_authority(
        &mut self,
        original_id: u64,
        proof: ClausificationProof,
    ) {
        if self.enabled {
            self.pending_original_authorities
                .push(PendingOriginalClauseAuthority::Clausification { original_id, proof });
        }
    }

    pub(crate) fn note_theory_authority(&mut self, original_id: u64, proof: TheoryLemmaProof) {
        if self.enabled {
            self.pending_original_authorities
                .push(PendingOriginalClauseAuthority::Theory { original_id, proof });
        }
    }

    pub(crate) fn drain_original_authorities(
        &mut self,
    ) -> impl Iterator<Item = PendingOriginalClauseAuthority> + '_ {
        self.pending_original_authorities.drain(..)
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
