// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Faithful reconstruction of bit-vector identities folded during elaboration.

use ay_core::{AletheRule, Proof, Sort, Symbol, TheoryLemmaKind};

use super::{
    add_bvand_commutative_congruence_proof, build_bv_pterm, build_qfbv_pterm, match_eq_negation,
    Executor,
};

impl Executor {
    pub(super) fn promote_bv_identity_collapse(&mut self, proof: &mut Proof) {
        if !Self::proof_needs_schema_collapse_reconstruction(proof) {
            return;
        }
        let parsed = self.ctx.assertions_parsed().to_vec();
        for asrt in &parsed {
            let Some((lhs, rhs)) = match_eq_negation(asrt) else {
                continue;
            };
            // Rebuild the folded sides faithfully. The Boolean layer handles
            // BV-valued `ite` nodes nested below concat/extract operations.
            let (Some(l_id), Some(r_id)) = (
                build_bv_pterm(&mut self.ctx.terms, lhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, lhs)),
                build_bv_pterm(&mut self.ctx.terms, rhs)
                    .or_else(|| build_qfbv_pterm(&mut self.ctx.terms, rhs)),
            ) else {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE rebuild (bv+qfbv both failed on a side)"
                        .to_string()
                });
                continue;
            };
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "bv-identity-collapse: rebuilt both sides OK".to_string()
            });
            // Both sides must share a Boolean/BV sort for `=` to be
            // well-formed. Boolean is load-bearing for direct BV predicate
            // identities such as `(bvult x 1) = (x = 0)`; the recursive
            // congruence builder and the final independent bit-blast replay
            // still authenticate the complete equality before it is used.
            if self.ctx.terms.sort(l_id) != self.ctx.terms.sort(r_id)
                || !matches!(self.ctx.terms.sort(l_id), Sort::Bool | Sort::BitVec(_))
            {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE sort gate".to_string()
                });
                continue;
            }
            let eq_t = self
                .ctx
                .terms
                .mk_app(Symbol::named("="), [l_id, r_id], Sort::Bool);
            let reflexive = l_id == r_id;
            let neg_t = self.ctx.terms.mk_not_raw(eq_t);
            // Export must preserve both rebuilt terms through surface overrides.
            if !self.rebuilt_terms_print_faithfully(&[neg_t, eq_t]) {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE print-faithfulness".to_string()
                });
                continue;
            }

            let mut candidate = Proof::new();
            let assume_id = candidate.add_assume(neg_t, None);
            let lemma_id = if reflexive {
                candidate.add_rule_step(AletheRule::EqReflexive, vec![eq_t], Vec::new(), Vec::new())
            } else if let Some(step) = add_bvand_commutative_congruence_proof(
                &mut self.ctx.terms,
                &mut candidate,
                l_id,
                r_id,
            ) {
                step
            } else if ay_proof::recognize_bv_bitblast(&self.ctx.terms, &[eq_t]) {
                candidate.add_theory_lemma_with_kind("bv", vec![eq_t], TheoryLemmaKind::BvBitBlast)
            } else {
                crate::executor::unsat_cert::probe_cert_reject(|| {
                    "bv-identity-collapse: DECLINE no lemma route (walker None + recognizer refused)"
                        .to_string()
                });
                continue;
            };
            candidate.add_resolution(vec![], eq_t, assume_id, lemma_id);

            self.record_rebuilt_authored_proof_premise(neg_t);
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "bv-identity-collapse: SUCCESS candidate installed".to_string()
            });
            *proof = candidate;
            return;
        }
    }
}
