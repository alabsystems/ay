// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-proof fail-closed acceptance gates before transactional commit.

use super::super::*;
use super::model::{RebuildState, SurgeryPlans};

impl Executor {
    pub(super) fn rebuilt_proof_is_accepted(
        &mut self,
        plans: &SurgeryPlans,
        state: &RebuildState,
    ) -> bool {
        self.rebuilt_terminal_trust_is_authorized(plans, &state.new_proof)
            && self.strict_gate_accepts_rebuild(plans, &state.new_proof)
    }

    fn rebuilt_terminal_trust_is_authorized(&self, plans: &SurgeryPlans, proof: &Proof) -> bool {
        let report = ay_proof::terminal_trust_report(proof);
        if report.trust_rule_on_path == 0 && report.trust_theory_lemma_on_path == 0 {
            return true;
        }
        if plans.deferred_leaves.is_empty() || report.trust_rule_on_path > 0 {
            return false;
        }
        let Some(live) = taut_surface::live_steps(proof) else {
            return false;
        };
        for (index, step) in proof.steps.iter().enumerate() {
            if !live[index] {
                continue;
            }
            let ProofStep::TheoryLemma { kind, clause, .. } = step else {
                continue;
            };
            if kind.is_trust() && !self.trust_leaf_certified_downstream(step, clause) {
                return false;
            }
        }
        true
    }

    fn strict_gate_accepts_rebuild(&mut self, plans: &SurgeryPlans, proof: &Proof) -> bool {
        if !Self::strict_gate_is_required(plans) {
            return true;
        }
        if plans.deferred_leaves.is_empty() {
            // The SAME registry-supplied strict entry the deferred branch and
            // the publication mint-time re-check use: bare
            // `check_proof_strict` rejects registry-validated datatype lemma
            // kinds (`DatatypeExhaustive` et al.) as unsupported, so a
            // rebuild the published gate accepts was refused here. Parity,
            // not widening — every kind is still semantically validated
            // against the executor's declaration registries.
            return self
                .check_proof_strict_derivation_with_datatypes(proof)
                .is_ok();
        }
        // Deferred leaves are still Generic here. Validate a copy after the
        // exact idempotent promotion stages that export will run, so approval
        // applies to the published derivation rather than an intermediate.
        let mut gate_proof = proof.clone();
        let datatype_data = crate::theory_inference::dt_funnel_registry_data(&self.ctx);
        let datatypes = datatype_data
            .as_ref()
            .map(crate::theory_inference::DatatypeRegistries::from_data);
        Self::promote_generic_theory_lemma_kinds_after_rewrite(
            &self.ctx.terms,
            &mut gate_proof,
            datatypes.as_ref(),
        );
        self.promote_array_extensionality_axioms(&mut gate_proof);
        self.check_proof_strict_derivation_with_datatypes(&gate_proof)
            .is_ok()
    }

    fn strict_gate_is_required(plans: &SurgeryPlans) -> bool {
        let has_or_permutation = plans.assume_plans.values().any(|plan| {
            matches!(plan, AssumePlan::AndDistinct { units, .. }
                if units.iter().any(|unit| matches!(unit.kind, AndDistinctKind::OrPerm { .. })))
        });
        !plans.euf_lemmas.is_empty()
            || has_or_permutation
            || !plans.deferred_leaves.is_empty()
            || !plans.subst_eqs.is_empty()
            || !plans.normalized_authored_ors.is_empty()
            || !plans.authored_array_ites.is_empty()
            || plans.has_quant_plans
            || plans.has_ite_lift_plans
            || !plans.exact_provenance_or_assumes.is_empty()
            || !plans.provenance_or_plans.is_empty()
            || !plans.or_units.is_empty()
    }
}
