// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Propose the existing bounded word-level derivation over an early raw root.

use super::*;
use ay_core::ProofStep;

impl Executor {
    pub(in crate::executor::proof) fn early_ground_closure_memory_candidate(
        &mut self,
        root: TermId,
    ) -> Option<Proof> {
        if self.should_abort_theory_loop() {
            return None;
        }
        let mut search = GroundSearch::default();
        // Boolean geometry and event-coverage claims need their authored
        // connectives in the same bounded, justified congruence graph.
        self.register_ground_subterms(&mut search.closure, root)?;
        let Some(conflict) = self.saturate_ground_search(&mut search, &[root], &[]) else {
            crate::executor::unsat_cert::probe_cert_reject(|| {
                format!(
                    "early ground memory: word closure declined nodes={} edges={} facts={} probes={}",
                    search.closure.nodes().len(),
                    search.closure.edges().len(),
                    search.facts.facts().len(),
                    search.probes
                )
            });
            return None;
        };
        let candidate = self.emit_ground_closure_refutation(&search, conflict)?;
        // This producer has exactly one authenticated source root. Generated
        // leaves and unrelated context premises receive no assumption authority.
        if candidate
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Assume(premise) if *premise != root))
            || !Self::proof_derives_empty_clause(&candidate)
        {
            return None;
        }
        Some(candidate)
    }
}
