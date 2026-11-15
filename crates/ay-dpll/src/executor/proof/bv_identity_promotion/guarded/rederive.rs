// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Re-derive an anchored authored root through a named arithmetic lane when
//! that certified document is measurably smaller than the incumbent's.
//!
//! The guarded collapse leaves a publishable proof alone, because re-anchoring
//! one would only trade its derivation for the coarsest lemma in the family
//! (see the loop in `guarded.rs`). That holds for the `BvBitBlast` candidate.
//! An `ArithClauseTautology` lemma over the same root instead prints through
//! the named lanes of `format_bv_structural_arithmetic` (complement, guarded
//! mask, context, interval partition), and those can be far smaller than the
//! complete bit-blast that made the incumbent publishable.
//!
//! Measured on `bv_partition_source`'s exception-coverage fixture. Until
//! 73810d00d the complete blast had no lowering for `bvuge`/`bvule`, so the
//! incumbent `assume root`, `BvBitBlast (not root)` printed a hole, was not
//! publishable, and this planner installed the `ArithClauseTautology`
//! re-anchor: the partition lane's pbblast/la_generic/poly_simp document,
//! 2.27 MB, which carcara checks in 0.1 s. Once 73810d00d lowered those
//! comparisons, the screen admitted the incumbent's 20,481-gate complete blast
//! and the published document became 10.4 MB, which carcara checks in
//! 105-130 s.
//!
//! The choice is made by measurement, not by order: both certified proofs are
//! rendered under the same cap, and the candidate replaces the incumbent only
//! when its clean render is strictly smaller (an incumbent whose render the
//! cap refuses counts as larger). Where no named lane recognizes the root, or
//! the complete blast is the smaller document, the incumbent stays, so every
//! publication 73810d00d gained is kept. The candidate must itself be
//! publishable (`authored_cascade_publishable`: no screened wire gap and a
//! complete strict check) in the presentation view its installation leaves,
//! so a publishable proof is only ever traded for another publishable proof;
//! the mint stays the authority over both.

use super::{proof_already_assumes, Executor, Proof, ProofStep, TermId, TheoryLemmaKind};

#[cfg(test)]
mod tests;

impl Executor {
    /// Returns whether a smaller certified re-derivation replaced `proof`,
    /// which assumes the raw authored `root` and refutes it with a
    /// `BvBitBlast` lemma over `(not root)`.
    pub(super) fn promote_cheaper_named_rederivation(
        &mut self,
        proof: &mut Proof,
        root: TermId,
        negated: TermId,
    ) -> bool {
        // Only a requested or presentation-relevant document has a size to
        // compare; otherwise the screen never asked the complete blast.
        if !self.proof_document_observable()
            || !proof_already_assumes(proof, root)
            || !refutes_by_bit_blast(proof, negated)
            || !ay_proof::recognize_arith_clause_tautology(&self.ctx.terms, &[negated])
        {
            return false;
        }
        let candidate = anchored_refutation(root, negated, TheoryLemmaKind::ArithClauseTautology);
        if !self.rederivation_publishes_smaller(proof, &candidate) {
            return false;
        }
        self.record_raw_authored_problem_assertion(root);
        self.purge_surface_overrides_for_certified_proof(&candidate);
        *proof = candidate;
        true
    }

    /// Whether `candidate`'s clean render is strictly smaller than
    /// `incumbent`'s and `candidate` is publishable. The incumbent is
    /// publishable already, so it needs only its render, and a render the cap
    /// refuses counts as the larger one. The cheapest question goes first:
    /// most candidates that lose do so on their own render.
    fn rederivation_publishes_smaller(&mut self, incumbent: &Proof, candidate: &Proof) -> bool {
        let Some(candidate_len) =
            self.asked_as_installed(candidate, |executor| executor.clean_render_len(candidate))
        else {
            return false;
        };
        if self
            .clean_render_len(incumbent)
            .is_some_and(|incumbent_len| incumbent_len <= candidate_len)
        {
            return false;
        }
        self.asked_as_installed(candidate, |executor| {
            executor.authored_cascade_publishable(candidate)
        })
    }

    /// Answer `question` in the presentation view installing `candidate`
    /// would leave (installation purges the overrides of every term it
    /// prints), then restore the map exactly: this only asks.
    fn asked_as_installed<T>(
        &mut self,
        candidate: &Proof,
        question: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let current = self.last_proof_term_overrides.clone();
        self.purge_surface_overrides_for_certified_proof(candidate);
        let answer = question(self);
        self.last_proof_term_overrides = current;
        answer
    }
}

/// `assume root`, one `kind` lemma `(cl (not root))`, and their resolution:
/// the guarded collapse's single-root shape.
pub(super) fn anchored_refutation(root: TermId, negated: TermId, kind: TheoryLemmaKind) -> Proof {
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![negated], kind);
    proof.add_resolution(Vec::new(), root, assume, lemma);
    proof
}

/// Whether `proof` refutes `(cl negated)` with the generic bit-blast lemma,
/// the one the complete blast certifies on the wire.
fn refutes_by_bit_blast(proof: &Proof, negated: TermId) -> bool {
    proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast,
                clause,
                ..
            } if clause.as_slice() == [negated]
        )
    })
}
