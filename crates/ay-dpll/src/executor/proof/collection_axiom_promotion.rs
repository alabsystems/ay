// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final classification of strict-checkable collection axioms.

use super::*;

impl Executor {
    pub(super) fn promote_final_collection_axioms(&mut self, proof: &mut Proof) {
        self.promote_set_cardinality_axioms(proof);
        self.promote_subset_and_set_card_chain_axioms(proof);
    }

    /// Reclassify the set-cardinality bridge axiom before publication.
    ///
    /// Every route that builds a refutation lands here, which is why the
    /// reclassification lives at this choke point rather than in the individual
    /// re-scoping passes: the axiom reaches publication as a `Step{Trust}` (the
    /// printer renders Trust as `hole`), and the re-scoping passes that rewrite
    /// non-authored ASSUMES never see it.
    ///
    /// This is a hint, not an authority: the strict checker independently
    /// re-validates the exact schema and rejects the lemma if the clause is
    /// anything other than `(<= 0 (set.card s))`.
    fn promote_set_cardinality_axioms(&self, proof: &mut Proof) {
        for step in &mut proof.steps {
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                ..
            } = step
            else {
                continue;
            };
            let [literal] = clause.as_slice() else {
                continue;
            };
            let kind = if Self::is_set_card_non_negative_axiom(&self.ctx.terms, *literal) {
                Some(TheoryLemmaKind::SetCardNonNegative)
            } else if Self::is_set_card_member_lower_bound_axiom(&self.ctx.terms, *literal) {
                Some(TheoryLemmaKind::SetCardMemberLowerBound)
            } else if Self::is_set_card_empty_axiom(&self.ctx.terms, *literal) {
                Some(TheoryLemmaKind::SetCardEmpty)
            } else if Self::is_set_card_member_count_axiom(&self.ctx.terms, *literal) {
                Some(TheoryLemmaKind::SetCardMemberCount)
            } else if Self::is_set_card_zero_axiom(&self.ctx.terms, *literal) {
                Some(TheoryLemmaKind::SetCardEmptyByAssertion)
            } else {
                None
            };
            if let Some(kind) = kind {
                *step = ProofStep::TheoryLemma {
                    theory: "sets".to_string(),
                    clause: vec![*literal],
                    farkas: None,
                    kind,
                    lia: None,
                };
            }
        }
    }

    /// Reclassify collection subset axioms and the set-cardinality store-chain
    /// recurrence before publication, at the same choke point and for the same
    /// reason as the scalar set-cardinality axioms.
    ///
    /// The native set/map/multiset solvers close these refutations with theory
    /// tautologies that previously reached publication as `Step{Trust}` or
    /// `TheoryLemma{Generic}`. The checker's own matchers decide which clauses
    /// qualify, and strict checking independently re-validates every chosen
    /// kind. A `Trust` step carrying premises is derived rather than injected,
    /// so it is left alone.
    fn promote_subset_and_set_card_chain_axioms(&self, proof: &mut Proof) {
        for step in &mut proof.steps {
            let clause = match step {
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    ..
                } if premises.is_empty() => clause.clone(),
                ProofStep::TheoryLemma {
                    clause,
                    kind: TheoryLemmaKind::Generic,
                    ..
                } => clause.clone(),
                _ => continue,
            };
            // The subset schemas and set-cardinality recurrence are disjoint
            // by shape; strict checking re-validates whichever matcher claims
            // the clause.
            let Some((theory, kind)) =
                ay_proof::recognize_subset_theory_lemma(&self.ctx.terms, &clause)
                    .map(|kind| ("subset", kind))
                    .or_else(|| {
                        ay_proof::recognize_set_card_chain_recurrence(&self.ctx.terms, &clause)
                            .map(|kind| ("sets", kind))
                    })
            else {
                continue;
            };
            *step = ProofStep::TheoryLemma {
                theory: theory.to_string(),
                clause,
                farkas: None,
                kind,
                lia: None,
            };
        }
    }
}
