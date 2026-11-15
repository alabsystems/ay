// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy-reason routing shared by normal and early-drain propagation lanes.

use ay_core::{TermId, TheoryPropagation, TheorySolver};
use ay_sat::SolverContext;

use super::propagation::push_term_at_polarity;
use super::*;
use crate::extension::infer_bound_axiom_arith_kind;

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn resolve_lazy_propagation(
        &mut self,
        propagation: TheoryPropagation,
        ctx: &dyn SolverContext,
    ) -> LazyResolution {
        let Some(reason_data) = propagation.reason_data else {
            return LazyResolution::Materialized(propagation);
        };
        let Some(literal) =
            self.term_to_literal(propagation.literal.term, propagation.literal.value)
        else {
            return LazyResolution::Skip;
        };
        if let Some(value) = ctx.value(literal.variable()) {
            if value != propagation.literal.value {
                return self.materialize_lazy_propagation(propagation, reason_data);
            }
            self.feedback_assigned_propagation(
                propagation.literal.term,
                propagation.literal.value,
                FeedbackLane::Deferred,
            );
            return LazyResolution::Skip;
        }
        let guarded_euf_token = reason_data & ay_euf::EUF_LAZY_MAGIC_MASK == ay_euf::EUF_LAZY_MAGIC
            && self.is_ite_guarded_term(propagation.literal.term);
        if guarded_euf_token {
            return self.materialize_lazy_propagation(propagation, reason_data);
        }
        // A proof-tracking solve explains a LEVEL-0 propagation now and
        // delivers it with its reason clause. A lazy reason is a theory-local
        // handle, not a clause, so a level-0 unit carrying one gets no unit
        // proof (`materialize_level0_unit_proofs` skips it); a level-0
        // conflict through it leaves an incomplete terminal chain, the clause
        // trace is marked `proof_work_exhausted`, and the SMT proof collapses
        // to one whole-query `Generic` lemma that mandatory strict
        // certification refuses (the model-checker consumer's BEANS `live_decrease` obligation, QF_LIA
        // and QF_LRA, since the implied-bound delivery of 4a0869ae3).
        //
        // The proof tracker records every public decision, so this runs on
        // every check-sat, not only under `:produce-proofs`. It must
        // therefore leave the level-0 trail exactly as lazy delivery leaves
        // it: a propagation is explained at most once (an assigned literal
        // returns above), and one with no explanation is DELIVERED lazily,
        // never dropped. Dropping it (d2bc57bb2) cost nothing in QF_LRA but
        // dropped every level-0 implied bound in QF_LIA, whose `LiaSolver`
        // had no explanation for its LRA's propagations: the model-checker consumer's k-induction BMC
        // then searched (0 conflicts became 126,943; 0.09 s became 45 s).
        if self.proof.is_some() && ctx.decision_level() == 0 {
            if let Some(reason) = self
                .theory
                .explain_level0_propagation(propagation.literal.term, reason_data)
            {
                self.eager_stats.level0_lazy_explained += 1;
                let mut explained = propagation;
                explained.reason = reason;
                explained.reason_data = None;
                return LazyResolution::Level0Explained {
                    explained,
                    sat_literal: literal,
                    reason_data,
                };
            }
            self.eager_stats.level0_lazy_unexplained += 1;
        }
        LazyResolution::Deliver {
            theory_literal: propagation.literal,
            sat_literal: literal,
            reason_data,
        }
    }

    fn materialize_lazy_propagation(
        &mut self,
        mut propagation: TheoryPropagation,
        reason_data: u64,
    ) -> LazyResolution {
        if let Some(reason) = self
            .theory
            .explain_propagation(propagation.literal.term, reason_data)
        {
            propagation.reason = reason;
            propagation.reason_data = None;
            LazyResolution::Materialized(propagation)
        } else {
            self.theory
                .mark_propagation_rejected(propagation.literal.term, reason_data);
            LazyResolution::Skip
        }
    }

    /// The propagation's clause `(literal \/ ~reason...)` over proof terms, or
    /// `None` without proof tracking or when a polarity has no proof term.
    pub(super) fn level0_proof_clause(
        &self,
        propagation: &TheoryPropagation,
        clause_len: usize,
    ) -> Option<Vec<TermId>> {
        let negations = self.proof.as_ref()?.negations;
        let mut clause = Vec::with_capacity(clause_len);
        let literal = propagation.literal;
        if !push_term_at_polarity(&mut clause, literal.term, literal.value, negations) {
            return None;
        }
        for reason in &propagation.reason {
            if !push_term_at_polarity(&mut clause, reason.term, !reason.value, negations) {
                return None;
            }
        }
        Some(clause)
    }

    /// Give a level-0 lazy explanation delivered with its reason clause a
    /// certified theory lemma, so a proof through it prints no `hole`.
    /// `record_level0_propagation` already recorded the bound-axiom shape; any
    /// other explanation (several reasons, an equality reason) is recorded
    /// only with Farkas coefficients that `try_lra_farkas_reconstruction`
    /// found and re-verified against this exact clause, else not at all.
    /// One small LRA check per such literal, in proof-tracking solves only.
    pub(super) fn certify_level0_explanation(&mut self, propagation: &TheoryPropagation) {
        if bound_axiom_kind(self.terms, propagation).is_some() {
            return;
        }
        let Some(terms) = self.terms else {
            return;
        };
        let clause_len = propagation.reason.len() + 1;
        let Some(clause) = self.level0_proof_clause(propagation, clause_len) else {
            return;
        };
        let mut farkas = None;
        let mut kind = ay_core::TheoryLemmaKind::LraFarkas;
        if !crate::executor::try_lra_farkas_reconstruction(terms, &clause, &mut farkas, &mut kind) {
            return;
        }
        let (Some(farkas), Some(proof)) = (farkas, self.proof.as_mut()) else {
            return;
        };
        self.eager_stats.level0_lazy_certified += 1;
        let _ = proof
            .tracker
            .add_theory_lemma_with_farkas_and_kind(clause, farkas, kind);
    }

    pub(super) fn feedback_assigned_propagation(
        &mut self,
        term: TermId,
        value: bool,
        lane: FeedbackLane,
    ) {
        self.eager_stats.props_already_assigned += 1;
        if Self::prop_feedback_enabled(lane) && self.is_ite_guarded_term(term) {
            self.theory.assert_literal(term, value);
            self.eager_stats.props_fed_back += 1;
        }
    }

    fn prop_feedback_enabled(lane: FeedbackLane) -> bool {
        static MAIN_NO_FEEDBACK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        static SHARED_NO_FEEDBACK: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        let disabled =
            match lane {
                FeedbackLane::MainEager => MAIN_NO_FEEDBACK
                    .get_or_init(|| ay_core::theory_disable_flags().no_prop_feedback),
                FeedbackLane::Deferred => SHARED_NO_FEEDBACK
                    .get_or_init(|| ay_core::theory_disable_flags().no_prop_feedback),
            };
        !*disabled
    }

    pub(super) fn is_ite_guarded_term(&self, term: TermId) -> bool {
        self.term_to_var.get(&term).is_some_and(|&variable| {
            let index = variable as usize;
            let word = index / 64;
            word < self.ite_guarded_bitset.len()
                && (self.ite_guarded_bitset[word] >> (index % 64)) & 1 != 0
        })
    }
}

/// The bound-axiom kind `record_level0_propagation` records a single-reason
/// level-0 implication under, if it has one.
pub(super) fn bound_axiom_kind(
    terms: Option<&ay_core::TermStore>,
    propagation: &TheoryPropagation,
) -> Option<ay_core::TheoryLemmaKind> {
    match (terms, propagation.reason.as_slice()) {
        (Some(terms), [reason]) => infer_bound_axiom_arith_kind(
            terms,
            propagation.literal.term,
            reason.term,
            propagation.literal.value,
            reason.value,
        ),
        _ => None,
    }
}
