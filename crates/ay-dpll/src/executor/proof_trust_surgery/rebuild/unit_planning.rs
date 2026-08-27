// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Certified unit-extraction, quantifier-chain, and volume preflight.

use super::super::*;
use super::model::{SurgeryInput, SurgeryPlans};

enum UnitCandidate {
    NotApplicable,
    Pattern {
        assume_index: usize,
        and_pos_index: usize,
        position: usize,
    },
    Reject,
}

impl Executor {
    pub(super) fn plan_units_and_volume(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        plans: &mut SurgeryPlans,
    ) -> bool {
        if !self.plan_unit_patterns(input, plans)
            || !Self::unit_consumers_are_closed(input, plans)
            || !self.prepare_quant_chains(input, authority, plans)
            || !Self::dropped_and_pos_consumers_are_closed(input, plans)
            || !self.prepare_quant_overrides(input, authority, plans)
        {
            return false;
        }
        self.planned_volume_is_bounded(input, plans)
    }

    fn plan_unit_patterns(&mut self, input: &SurgeryInput<'_>, plans: &mut SurgeryPlans) -> bool {
        plans.dropped_and_pos = vec![false; input.step_count()];
        for (index, step) in input.proof.steps.iter().enumerate() {
            if !input.live[index] {
                continue;
            }
            match self.recognize_unit_candidate(input, plans, step) {
                UnitCandidate::NotApplicable => {}
                UnitCandidate::Reject => return false,
                UnitCandidate::Pattern {
                    assume_index,
                    and_pos_index,
                    position,
                } => {
                    plans.unit_patterns.insert(index, (assume_index, position));
                    plans.dropped_and_pos[and_pos_index] = true;
                }
            }
        }
        true
    }

    fn recognize_unit_candidate(
        &self,
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
        step: &ProofStep,
    ) -> UnitCandidate {
        let (clause, first, second) = match step {
            ProofStep::Resolution {
                clause,
                clause1,
                clause2,
                ..
            } => (clause, clause1.0 as usize, clause2.0 as usize),
            ProofStep::Step {
                rule: AletheRule::ThResolution | AletheRule::Resolution,
                clause,
                premises,
                ..
            } if premises.len() == 2 => (clause, premises[0].0 as usize, premises[1].0 as usize),
            _ => return UnitCandidate::NotApplicable,
        };
        if clause.len() != 1 {
            return UnitCandidate::NotApplicable;
        }
        let (assume_index, and_pos_index) = if plans.assume_plans.contains_key(&first) {
            (first, second)
        } else if plans.assume_plans.contains_key(&second) {
            (second, first)
        } else {
            return UnitCandidate::NotApplicable;
        };
        let Some(ProofStep::Step {
            rule: AletheRule::AndPos(position),
            premises,
            ..
        }) = input.proof.steps.get(and_pos_index)
        else {
            return UnitCandidate::NotApplicable;
        };
        if !premises.is_empty() {
            return UnitCandidate::NotApplicable;
        }
        let position = *position as usize;
        let conjs = match &plans.assume_plans[&assume_index] {
            AssumePlan::Distinct { conjs, .. }
            | AssumePlan::AndBounds { conjs, .. }
            | AssumePlan::QuantExpansion { conjs, .. }
            | AssumePlan::AndDistinct { conjs, .. } => conjs,
            AssumePlan::Literal { .. } => return UnitCandidate::NotApplicable,
        };
        if position >= conjs.len() || conjs[position] != clause[0] {
            return UnitCandidate::Reject;
        }
        UnitCandidate::Pattern {
            assume_index,
            and_pos_index,
            position,
        }
    }

    fn unit_consumers_are_closed(input: &SurgeryInput<'_>, plans: &SurgeryPlans) -> bool {
        plans.assume_plans.iter().all(|(&index, plan)| {
            !matches!(
                plan,
                AssumePlan::AndBounds { .. } | AssumePlan::QuantExpansion { .. }
            ) || input.consumers[index]
                .iter()
                .all(|consumer| plans.unit_patterns.contains_key(consumer))
        })
    }

    fn prepare_quant_chains(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        plans: &mut SurgeryPlans,
    ) -> bool {
        let mut targets = Vec::new();
        let mut seen = HashSet::default();
        for &(assume_index, position) in plans.unit_patterns.values() {
            if !matches!(
                plans.assume_plans.get(&assume_index),
                Some(AssumePlan::QuantExpansion { .. })
            ) || !seen.insert((assume_index, position))
            {
                continue;
            }
            if targets.len() >= quant_surface::MAX_QUANT_SURFACE_CHAINS {
                return false;
            }
            targets.push((assume_index, position));
        }
        targets.sort_unstable();
        for (assume_index, position) in targets {
            let Some(AssumePlan::QuantExpansion {
                forall_term,
                assertion_index,
                conjs,
                instances,
            }) = plans.assume_plans.get(&assume_index)
            else {
                continue;
            };
            let Some((source, parsed)) = input.originals.get(*assertion_index) else {
                return false;
            };
            let target = conjs[position];
            let Some(values) = instances.get(&target).cloned() else {
                return false;
            };
            if source != forall_term
                || !authority.spend_chain_source(*forall_term, parsed)
                || !authority.spend_solver_attempt(&self.ctx.terms, &values)
            {
                return false;
            }
            let Some(chain) = self.build_quant_instance_chain(parsed, &values, target) else {
                return false;
            };
            plans.quant_chains.insert((assume_index, position), chain);
        }
        true
    }

    fn dropped_and_pos_consumers_are_closed(
        input: &SurgeryInput<'_>,
        plans: &SurgeryPlans,
    ) -> bool {
        plans
            .dropped_and_pos
            .iter()
            .enumerate()
            .all(|(index, &dropped)| {
                !dropped
                    || input.consumers[index]
                        .iter()
                        .all(|consumer| plans.unit_patterns.contains_key(consumer))
            })
    }

    fn prepare_quant_overrides(
        &mut self,
        input: &SurgeryInput<'_>,
        authority: &mut quant_surface::QuantSurfaceAuthority<'_>,
        plans: &mut SurgeryPlans,
    ) -> bool {
        if !plans.has_quant_plans {
            return true;
        }
        let Some(overrides) = self.prepare_quant_surface_overrides(
            authority,
            input.proof,
            input.live,
            input.originals,
            quant_surface::QuantSurfacePlans {
                assumes: &plans.assume_plans,
                chains: &plans.quant_chains,
                consequences: &plans.quant_consequences,
                negations: &plans.quant_negations,
            },
        ) else {
            return false;
        };
        plans.prepared_quant_surface_overrides = Some(overrides);
        true
    }

    fn planned_volume_is_bounded(&self, input: &SurgeryInput<'_>, plans: &SurgeryPlans) -> bool {
        volume::emitted_proof_volume_is_bounded(
            input.proof,
            input.live,
            &self.ctx.terms,
            volume::EmittedVolumePlans {
                trichotomies: &plans.trichotomies,
                ite_lifts: &plans.ite_lifts,
                provenance_ite_lifts: &plans.provenance_ite_lifts,
                exact_or_assumes: &plans.exact_provenance_or_assumes,
                provenance_or_plans: &plans.provenance_or_plans,
                or_units: &plans.or_units,
                taut_units: &plans.taut_units,
                euf_lemmas: &plans.euf_lemmas,
                subst_eqs: &plans.subst_eqs,
                quant_negations: &plans.quant_negations,
                quant_consequences: &plans.quant_consequences,
                assume_plans: &plans.assume_plans,
                unit_patterns: &plans.unit_patterns,
                quant_chains: &plans.quant_chains,
            },
        )
    }
}
