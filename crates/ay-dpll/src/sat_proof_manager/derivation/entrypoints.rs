// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Externally invoked entrypoints into the proof-derivation machinery.

use super::*;

impl SatProofManager<'_> {
    /// Externally-seeded entry to the bounded DPLL(T) empty-clause closer.
    ///
    /// The executor's proof-repair layer uses this when a checked isolated
    /// probe collapses a relaxation-encoded LIA/LRA UNSAT to a whole-problem
    /// `trust` step (no SAT clause trace, no source provenance). It hands in a
    /// clause database it built DIRECTLY from the problem assertions (each
    /// version's `ProofId` proves that clause via an `assume`/`or` step) plus a
    /// `var_to_term` map, and receives the SAME genuine, strict-checkable
    /// `Resolution`-over-Farkas-lemmas derivation the trace-driven path would
    /// produce. Fail-closed: identical contract to
    /// [`Self::derive_empty_via_bounded_dpll_theory`] — any gap truncates the
    /// caller's candidate steps and returns `None`.
    pub(crate) fn close_empty_over_seeded_clauses(
        &mut self,
        clause_versions: &[(Vec<Literal>, ProofId)],
        proof: &mut Proof,
    ) -> Option<ProofId> {
        self.derive_empty_via_bounded_dpll_theory(clause_versions, proof)
    }

    /// Derive a learned clause from its resolution hints.
    ///
    /// Primary strategy (#rank-4 increment 1): RUP/LRAT-style unit-propagation
    /// replay over the *SAT-level* hint clauses — order-insensitive and
    /// complete for any hint set under which the target clause is RUP (this
    /// is exactly the LRAT-check semantics of `ay-sat::lrat_checker`,
    /// extended with fixpoint iteration because trace hints are not
    /// guaranteed to be in propagation order). Falls back to the legacy
    /// left-to-right pairwise term-level resolution (with original-clause
    /// closure) when replay fails.
    ///
    /// The replay runs over raw SAT literals (not SMT terms): distinct SAT
    /// variables can map to identical or complementary terms, which makes
    /// term-level propagation stall on chains that are perfectly valid at
    /// the SAT level (this was the source of the ~10/87 Trust fallbacks on
    /// the rank-4 captured solve).
    ///
    /// On success returns the proof node id *and* the term/SAT clauses that
    /// node actually proves. RUP replay can derive a strict subclause of the
    /// target (a stronger clause); callers must record that subclause so
    /// downstream replays stay exact.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::sat_proof_manager) fn derive_clause_from_hints(
        &mut self,
        target_clause: &[TermId],
        target_sat_clause: &[Literal],
        resolution_hints: &[u64],
        clause_terms: &HashMap<u64, Vec<TermId>>,
        clause_versions: &[SatClauseVersion],
        latest_version_by_id: &HashMap<u64, usize>,
        clause_proofs: &HashMap<u64, ProofId>,
        engine: &mut RupEngine,
        proof: &mut Proof,
    ) -> Result<(ProofId, Vec<TermId>, Vec<Literal>), HintDerivationError> {
        let mut hint_ids = Vec::with_capacity(resolution_hints.len());
        let mut hint_versions = Vec::with_capacity(resolution_hints.len());
        let mut seen_hint_ids: HashSet<u64> = Default::default();
        for &hint_id in resolution_hints {
            if !seen_hint_ids.insert(hint_id) {
                continue;
            }
            if clause_terms.contains_key(&hint_id) && clause_proofs.contains_key(&hint_id) {
                hint_ids.push(hint_id);
            }
            if let Some(&version) = latest_version_by_id.get(&hint_id) {
                hint_versions.push(version);
            }
        }
        if hint_ids.is_empty() && hint_versions.is_empty() {
            return Err(HintDerivationError::NoUsableHints);
        }

        match self.derive_clause_via_rup_replay(
            target_clause,
            target_sat_clause,
            &hint_versions,
            clause_versions,
            engine,
            proof,
        ) {
            Ok(derived) => return Ok(derived),
            Err(rup_error) => {
                tracing::debug!(
                    ?rup_error,
                    ?target_clause,
                    "RUP hint replay failed; falling back to pairwise resolution"
                );
            }
        }

        if hint_ids.is_empty() {
            return Err(HintDerivationError::NoUsableHints);
        }
        self.derive_clause_via_pairwise_resolution(
            target_clause,
            &hint_ids,
            clause_terms,
            clause_proofs,
            proof,
        )
        .map(|(id, derived_terms)| (id, derived_terms, target_sat_clause.to_vec()))
    }
}
