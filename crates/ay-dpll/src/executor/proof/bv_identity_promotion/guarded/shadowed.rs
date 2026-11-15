// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain the dedicated array derivation for a faithfully rebuilt source root.

use super::{Executor, Proof, TermId, TheoryLemmaKind};
use ay_core::TermData;

impl Executor {
    // The caller has expanded only declaration-authenticated source macros,
    // raw-interned the complete authored assertion, and checked its rendering.
    // Keeping that raw root preserves operations erased by elaboration and
    // avoids reintroducing macro aliases into the derived array steps.
    pub(super) fn promote_shadowed_store_source(
        &mut self,
        proof: &mut Proof,
        root: TermId,
    ) -> bool {
        let TermData::Not(equality) = self.ctx.terms.get(root) else {
            return false;
        };
        let equality = *equality;
        if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &[equality])
            != Some(TheoryLemmaKind::ArrayRowChain)
        {
            return false;
        }
        let mut candidate = Proof::new();
        let assumption = candidate.add_assume(root, None);
        let lemma = candidate.add_theory_lemma_with_kind(
            "array",
            vec![equality],
            TheoryLemmaKind::ArrayRowChain,
        );
        candidate.add_resolution(Vec::new(), equality, lemma, assumption);
        if !self
            .check_proof_strict_derivation_with_datatypes(&candidate)
            .is_ok_and(|quality| quality.is_complete())
            || self.should_abort_theory_loop()
        {
            return false;
        }
        self.record_raw_authored_problem_assertion(root);
        self.purge_surface_overrides_for_certified_proof(&candidate);
        *proof = candidate;
        true
    }
}
