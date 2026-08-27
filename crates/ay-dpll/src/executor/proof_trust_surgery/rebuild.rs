// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered fail-closed planning, rebuilding, acceptance, and commit pipeline.

use super::*;

#[path = "rebuild/acceptance.rs"]
mod acceptance;
#[path = "rebuild/commit.rs"]
mod commit;
#[path = "rebuild/copy_steps.rs"]
mod copy_steps;
#[path = "rebuild/emit_assumes.rs"]
mod emit_assumes;
#[path = "rebuild/emit_leaf_plans.rs"]
mod emit_leaf_plans;
#[path = "rebuild/emit_lifts.rs"]
mod emit_lifts;
#[path = "rebuild/emit_units.rs"]
mod emit_units;
#[path = "rebuild/model.rs"]
mod model;
#[path = "rebuild/prologue.rs"]
mod prologue;
#[path = "rebuild/surface_planning.rs"]
mod surface_planning;
#[path = "rebuild/trust_planning.rs"]
mod trust_planning;
#[path = "rebuild/unit_planning.rs"]
mod unit_planning;
#[path = "rebuild/walk.rs"]
mod walk;

use model::{SurgeryInput, SurgeryPlans};

impl Executor {
    /// See the parent module docs. The old proof and executor export state are
    /// changed only after every authority, volume, and strict-check gate passes.
    pub(in crate::executor) fn try_rebuild_with_trust_surgery(
        &mut self,
        proof: &mut Proof,
        originals: &[(TermId, FrontendTerm)],
    ) -> bool {
        let source_index = OriginalSourceIndex::new(originals);
        if !source_index.is_valid() || !surgery_sources_are_bounded(&self.ctx.terms, originals) {
            return false;
        }
        let step_count = proof.steps.len();
        if step_count == 0
            || step_count > 100_000
            || proof
                .steps
                .iter()
                .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return false;
        }
        let Some(live) = taut_surface::live_steps(proof) else {
            return false;
        };
        let Some(consumers) = Self::build_live_consumer_map(proof, &live) else {
            return false;
        };
        let (mut plans, state) = {
            let input = SurgeryInput {
                proof,
                originals,
                source_index: &source_index,
                live: &live,
                consumers: &consumers,
            };
            let mut authority = quant_surface::QuantSurfaceAuthority::new(&source_index);
            let mut quant_plan_count = 0usize;
            let mut plans = SurgeryPlans::default();
            if !self.plan_live_trust_leaves(
                &input,
                &mut authority,
                &mut quant_plan_count,
                &mut plans,
            ) || !self.plan_assumes_and_surface_policy(
                &input,
                &mut authority,
                &mut quant_plan_count,
                &mut plans,
            ) || !self.plan_units_and_volume(&input, &mut authority, &mut plans)
            {
                return false;
            }
            let mut state = self.build_assumption_prologue(&input, &plans);
            if !self.emit_ordered_rebuild(&input, &plans, &mut state)
                || !self.rebuilt_proof_is_accepted(&plans, &state)
            {
                return false;
            }
            (plans, state)
        };
        self.commit_trust_surgery(proof, originals, &mut plans, state)
    }

    /// Consumer order is the original forward scan order; planners rely on
    /// that deterministic order and only dead steps are omitted.
    fn build_live_consumer_map(proof: &Proof, live: &[bool]) -> Option<Vec<Vec<usize>>> {
        let step_count = proof.steps.len();
        let mut consumers = vec![Vec::new(); step_count];
        for (index, step) in proof.steps.iter().enumerate() {
            if !live[index] {
                continue;
            }
            match step {
                ProofStep::Step { premises, .. } => {
                    for premise in premises {
                        let source = premise.0 as usize;
                        if source >= step_count {
                            return None;
                        }
                        consumers[source].push(index);
                    }
                }
                ProofStep::Resolution {
                    clause1, clause2, ..
                } => {
                    for premise in [clause1, clause2] {
                        let source = premise.0 as usize;
                        if source >= step_count {
                            return None;
                        }
                        consumers[source].push(index);
                    }
                }
                _ => {}
            }
        }
        Some(consumers)
    }
}
