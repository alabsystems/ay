// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Keep source capture bounded and publication behind the existing strict gate.

use super::super::*;

impl Executor {
    /// The authored cascade has already established that the current artifact
    /// is not publishable. This member supplies a source-derived replacement;
    /// it never promotes the provisional proof's assumptions into source facts.
    pub(in crate::executor::proof) fn replace_with_exact_authored_activated_equality_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        const MAX_ROOTS: usize = 64;
        if self.term_memory_exceeded() {
            return;
        }
        let mut progress = self.array_preprocessing_progress();
        // Do not call an eager, whole-ledger scope collector before checking
        // cardinality. Missing immutable provenance leaves existing repairs in
        // charge; rewritten working assertions are never a fallback here.
        let Some(provenance) = self.proof_problem_assertion_provenance.as_ref() else {
            return;
        };
        let source = &provenance.original_problem_assertions;
        let assumptions = self.last_assumptions.as_deref().unwrap_or(&[]);
        let Some(count) = source.len().checked_add(assumptions.len()) else {
            return;
        };
        if count == 0 || count > MAX_ROOTS || !progress(count, count * size_of::<TermId>()) {
            return;
        }
        let mut originals = Vec::new();
        if originals.try_reserve_exact(count).is_err() {
            return;
        }
        originals.extend_from_slice(source);
        originals.extend_from_slice(assumptions);
        let Some(candidate) = super::derive(&mut self.ctx.terms, &originals, progress.as_mut())
        else {
            return;
        };
        if self.term_memory_exceeded() || !progress(0, 0) {
            return;
        }
        // The builder's full-source authentication is metered. The established
        // strict commit/optional respelling remains separately checked; this
        // call does not claim a new interruption bound for that older operation.
        self.commit_if_strictly_checked(proof, candidate, &originals);
    }
}
