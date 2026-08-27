// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered recognition of every live trust leaf.

use super::super::*;
use super::model::{SurgeryInput, SurgeryPlans};

enum RecognizedTrustPlan {
    Trichotomy(TrichotomyPlan),
    ProvenanceIte(ProvenanceItePlan),
    Ite(IteLiftPlan),
    NormalizedAuthoredOr(NormalizedAuthoredOrPlan),
    AuthoredArrayIte(AuthoredArrayItePlan),
    ExactProvenanceOrAssume(TermId),
    ProvenanceOr(ProvenanceOrPlan),
    OrUnit(OrUnitPlan),
    Tautology(OrTautologyPlan),
    Euf(EufLemmaPlan),
    QuantNegation(QuantNegationPlan),
    QuantConsequence(QuantConsequencePlan),
    SubstitutedEquality(SubstEqPlan),
    Deferred,
}

impl RecognizedTrustPlan {
    fn record(self, index: usize, plans: &mut SurgeryPlans) {
        match self {
            Self::Trichotomy(plan) => {
                plans.or_split_of.insert(plan.or_split_idx, index);
                plans.trichotomies.insert(index, plan);
            }
            Self::ProvenanceIte(plan) => {
                plans.provenance_ite_lifts.insert(index, plan);
            }
            Self::Ite(plan) => {
                plans.ite_lifts.insert(index, plan);
            }
            Self::NormalizedAuthoredOr(plan) => {
                plans.normalized_authored_ors.insert(index, plan);
            }
            Self::AuthoredArrayIte(plan) => {
                plans.authored_array_ites.insert(index, plan);
            }
            Self::ExactProvenanceOrAssume(term) => {
                plans.exact_provenance_or_assumes.insert(index, term);
            }
            Self::ProvenanceOr(plan) => {
                plans.provenance_or_plans.insert(index, plan);
            }
            Self::OrUnit(plan) => {
                plans.or_units.insert(index, plan);
            }
            Self::Tautology(plan) => {
                plans.taut_units.insert(index, plan);
            }
            Self::Euf(plan) => {
                plans.euf_lemmas.insert(index, plan);
            }
            Self::QuantNegation(plan) => {
                plans.quant_negations.insert(index, plan);
            }
            Self::QuantConsequence(plan) => {
                plans.quant_consequences.insert(index, plan);
            }
            Self::SubstitutedEquality(plan) => {
                plans.subst_eqs.insert(index, plan);
            }
            Self::Deferred => {
                plans.deferred_leaves.insert(index);
            }
        }
    }
}

impl Executor {
    pub(super) fn plan_live_trust_leaves(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        quant_plan_count: &mut usize,
        plans: &mut SurgeryPlans,
    ) -> bool {
        for index in 0..input.step_count() {
            if !input.live[index] {
                continue;
            }
            let clause = match &input.proof.steps[index] {
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    ..
                } => clause.as_slice(),
                ProofStep::TheoryLemma { kind, clause, .. } if kind.is_trust() => clause.as_slice(),
                _ => continue,
            };
            if clause.len() > MAX_PROVENANCE_REPAIR_TERMS
                || !authority
                    .planning_budget()
                    .spend_work(clause.len().saturating_add(1))
                || !self.spend_trust_clause_terms(clause, authority)
            {
                return false;
            }
            let recognized = self
                .recognize_surface_trust_plan(input, authority, index, clause)
                .or_else(|| {
                    self.recognize_certified_trust_plan(
                        input,
                        authority,
                        quant_plan_count,
                        index,
                        clause,
                    )
                });
            let Some(recognized) = recognized else {
                return false;
            };
            recognized.record(index, plans);
        }
        true
    }

    fn recognize_surface_trust_plan(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        index: usize,
        clause: &[TermId],
    ) -> Option<RecognizedTrustPlan> {
        if let Some(plan) =
            self.plan_trichotomy(input.proof, clause, &input.consumers[index], index)
        {
            return Some(RecognizedTrustPlan::Trichotomy(plan));
        }
        let planning = authority.planning_budget();
        if let Some(plan) =
            self.plan_provenance_ite_lift(clause, input.originals, input.source_index, planning)
        {
            return Some(RecognizedTrustPlan::ProvenanceIte(plan));
        }
        if let Some(plan) =
            self.plan_ite_lift(clause, input.originals, input.source_index, planning)
        {
            return Some(RecognizedTrustPlan::Ite(plan));
        }
        if let Some(plan) =
            self.plan_ite_lift_guarded_then(clause, input.originals, input.source_index, planning)
        {
            return Some(RecognizedTrustPlan::Ite(plan));
        }
        if let Some(plan) = self.plan_normalized_authored_or(clause, input.originals) {
            return Some(RecognizedTrustPlan::NormalizedAuthoredOr(plan));
        }
        if let Some(plan) = self.plan_authored_array_ite(clause, input.originals) {
            return Some(RecognizedTrustPlan::AuthoredArrayIte(plan));
        }
        if let Some(term) = self.plan_exact_provenance_or_assume(
            clause,
            input.originals,
            input.source_index,
            planning,
        ) {
            return Some(RecognizedTrustPlan::ExactProvenanceOrAssume(term));
        }
        if let Some(plan) =
            self.plan_provenance_or(clause, input.originals, input.source_index, planning)
        {
            return Some(RecognizedTrustPlan::ProvenanceOr(plan));
        }
        self.plan_or_unit(clause, input.originals, input.source_index, planning)
            .map(RecognizedTrustPlan::OrUnit)
    }

    fn recognize_certified_trust_plan(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        quant_plan_count: &mut usize,
        index: usize,
        clause: &[TermId],
    ) -> Option<RecognizedTrustPlan> {
        if let Some(plan) = self.plan_or_transitivity_tautology(clause) {
            return Some(RecognizedTrustPlan::Tautology(plan));
        }
        if let Some(plan) = self.plan_euf_lemma_with_budget(clause, authority.planning_budget()) {
            return Some(RecognizedTrustPlan::Euf(plan));
        }
        if let Some(plan) =
            self.plan_ematching_quant_negation(clause, input.originals, authority, quant_plan_count)
        {
            return Some(RecognizedTrustPlan::QuantNegation(plan));
        }
        if let Some(plan) =
            self.plan_quant_consequence(clause, input.originals, authority, quant_plan_count)
        {
            return Some(RecognizedTrustPlan::QuantConsequence(plan));
        }
        if let Some(plan) = self.plan_substituted_equality(
            clause,
            input.originals,
            input.source_index,
            authority.planning_budget(),
        ) {
            return Some(RecognizedTrustPlan::SubstitutedEquality(plan));
        }
        self.trust_leaf_certified_downstream(&input.proof.steps[index], clause)
            .then_some(RecognizedTrustPlan::Deferred)
    }
}
