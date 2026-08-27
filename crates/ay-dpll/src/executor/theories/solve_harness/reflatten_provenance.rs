// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof provenance for re-flattened variable-substitution results.

use ay_core::TermId;

use super::{flatten_assertion_with_source, Executor};

impl Executor {
    /// Re-flatten substituted LIA assertions while recording every 1→N split.
    ///
    /// A rewritten `and` becomes per-conjunct assertions. These pairs let proof
    /// replay re-find an `and_pos` path instead of demoting the new unit to a
    /// premise-free `trust`; only proof-producing solves pay for the snapshot.
    pub(super) fn reflatten_substituted_lia_assertions(
        &mut self,
        assertions: &[TermId],
        source_sets: &[Vec<TermId>],
    ) -> (Vec<TermId>, Vec<Vec<TermId>>) {
        let mut flattened = Vec::new();
        let mut provenance = Vec::new();
        let record_provenance = self.produce_proofs_enabled();

        for (&assertion, source_set) in assertions.iter().zip(source_sets) {
            let flatten_start = flattened.len();
            flatten_assertion_with_source(&self.ctx.terms, assertion, source_set, &mut flattened);
            if record_provenance {
                provenance.extend(
                    flattened[flatten_start..]
                        .iter()
                        .map(|(part, _)| *part)
                        .filter(|&part| part != assertion)
                        .map(|part| (assertion, part)),
                );
            }
        }

        self.extend_propagated_value_provenance_from_reflatten(&provenance);
        flattened.into_iter().unzip()
    }
}
