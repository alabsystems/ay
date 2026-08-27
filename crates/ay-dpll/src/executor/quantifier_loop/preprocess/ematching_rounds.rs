// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Multi-round preprocessing E-matching campaign state and orchestration.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::TermId;

use super::super::super::Executor;
use super::EmatchingSummary;
use crate::ematching::{EMatchingResult, ForallInstantiationProvenance};
use crate::quantifier_manager::QuantifierManager;

enum RoundProgress {
    Advanced,
    Fixpoint,
}

struct EmatchingCampaign {
    assertions: Vec<TermId>,
    seen: HashSet<TermId>,
    instantiations: Vec<TermId>,
    instantiated_quantifiers: HashSet<TermId>,
    forall_instantiations: Vec<ForallInstantiationProvenance>,
    seen_forall_instantiations: HashSet<(TermId, Vec<TermId>, TermId)>,
    has_uninstantiated: bool,
    uninstantiated_quantifiers: HashSet<TermId>,
    reached_limit: bool,
    rounds_completed: u64,
    instances_created: u64,
    support_roots: HashSet<TermId>,
}

impl EmatchingCampaign {
    fn new(assertions: &[TermId]) -> Self {
        Self {
            assertions: assertions.to_vec(),
            seen: assertions.iter().copied().collect(),
            instantiations: Vec::new(),
            instantiated_quantifiers: HashSet::default(),
            forall_instantiations: Vec::new(),
            seen_forall_instantiations: HashSet::default(),
            has_uninstantiated: false,
            uninstantiated_quantifiers: HashSet::default(),
            reached_limit: false,
            rounds_completed: 0,
            instances_created: 0,
            support_roots: HashSet::default(),
        }
    }

    fn absorb(
        &mut self,
        executor: &mut Executor,
        result: EMatchingResult,
        relevance_watermark: u32,
    ) -> RoundProgress {
        self.rounds_completed += 1;
        self.instances_created += result.instantiations.len() as u64;
        self.instantiated_quantifiers
            .extend(result.instantiated_quantifiers);
        self.support_roots.extend(result.unconditional_forall_roots);

        let novel = result
            .instantiations
            .into_iter()
            .filter(|instance| !self.seen.contains(instance))
            .collect();
        let admission =
            executor.relevance_admit_round(novel, &self.support_roots, relevance_watermark);
        if admission.withheld > 0 {
            // The carry queue also raises `has_deferred`; keep the round-limit
            // signal aligned so an incomplete campaign cannot finalize SAT.
            self.reached_limit = true;
        }
        let mut added = 0;
        for entry in admission.admitted {
            if self.seen.insert(entry.inst) {
                self.assertions.push(entry.inst);
                self.instantiations.push(entry.inst);
                added += 1;
            }
        }

        for record in result.unconditional_forall_instantiations {
            let key = (record.quantifier, record.binding.clone(), record.instance);
            if self.seen_forall_instantiations.insert(key) {
                self.forall_instantiations.push(record);
            }
        }
        self.has_uninstantiated = result.has_uninstantiated;
        self.uninstantiated_quantifiers = result.uninstantiated_quantifiers;
        self.reached_limit |= result.reached_limit;

        if result.reached_limit || added == 0 {
            RoundProgress::Fixpoint
        } else {
            RoundProgress::Advanced
        }
    }

    fn finish(self, executor: &Executor, gated_families: usize) -> EmatchingSummary {
        if gated_families > 0 && ay_core::misc_cli_flags().demand_debug {
            if let Some(manager) = executor.quantifier_manager.as_ref() {
                eprintln!(
                    "c demand-lane batch_instances={} gated_families={} frontier={} has_parked={}",
                    self.instantiations.len(),
                    gated_families,
                    manager.demand_frontier(),
                    manager.demand_has_parked(),
                );
            }
        }
        debug_assert!(
            self.instantiations.len() <= self.assertions.len() - executor.ctx.assertions.len(),
            "E-matching: more unique instantiations ({}) than new assertions ({})",
            self.instantiations.len(),
            self.assertions.len() - executor.ctx.assertions.len()
        );
        EmatchingSummary {
            instantiations: self.instantiations,
            instantiated_quantifiers: self.instantiated_quantifiers,
            unconditional_forall_instantiations: self.forall_instantiations,
            has_uninstantiated: self.has_uninstantiated,
            uninstantiated_quantifiers: self.uninstantiated_quantifiers,
            reached_limit: self.reached_limit,
            rounds_completed: self.rounds_completed,
            instances_created: self.instances_created,
            unconditional_forall_roots: self.support_roots,
        }
    }
}

impl Executor {
    fn classified_demand_gate(&self) -> HashSet<u32> {
        if !self.demand_lane_eligible() {
            return HashSet::default();
        }
        let foralls = self.collect_classifiable_foralls();
        self.classify_quantifier_families(&foralls)
            .iter()
            .filter(|(_, class)| {
                matches!(
                    class,
                    super::super::family_classifier::FamilyClass::SelfChainingDefinitional
                        | super::super::family_classifier::FamilyClass::BridgeCycle
                )
            })
            .map(|(term, _)| term.0)
            .collect()
    }

    fn begin_ematching_epoch(&mut self, gated: HashSet<u32>) -> usize {
        let gated_count = gated.len();
        let manager = self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        // Reset the persistent match memo to the scope baseline once per solve.
        // Interleaved and post-CEGQI rounds intentionally share this epoch.
        manager.begin_epoch();
        if !gated.is_empty() {
            manager.demand_arm(gated, crate::executor::dt_axioms::DT_WARM_START_DEPTH);
        }
        gated_count
    }

    /// Run multi-round E-matching, collecting instantiations across rounds.
    pub(in crate::executor::quantifier_loop) fn run_ematching_rounds(
        &mut self,
    ) -> EmatchingSummary {
        let max_rounds = self.ematching_round_limit();
        let gated = self.classified_demand_gate();
        // The closure owns its deadline/interrupt snapshots and does not borrow self.
        let should_stop = self.make_should_stop();
        let gated_families = self.begin_ematching_epoch(gated);
        let mut campaign = EmatchingCampaign::new(&self.ctx.assertions);

        for round_index in 0..max_rounds {
            if should_stop() {
                campaign.reached_limit = true;
                break;
            }
            let watermark = u32::try_from(self.ctx.terms.len()).unwrap_or(u32::MAX);
            let started_at = std::time::Instant::now();
            let result = {
                let euf_model = self
                    .last_model
                    .as_ref()
                    .and_then(|model| model.euf_model.as_ref());
                let manager = self
                    .quantifier_manager
                    .get_or_insert_with(QuantifierManager::new);
                manager.run_ematching_round(
                    &mut self.ctx.terms,
                    &campaign.assertions,
                    euf_model,
                    &should_stop,
                )
            };
            self.add_phase_seconds(
                "time.quantifier.ematching_seconds",
                started_at.elapsed().as_secs_f64(),
            );
            if matches!(
                campaign.absorb(self, result, watermark),
                RoundProgress::Fixpoint
            ) {
                break;
            }
            if round_index + 1 == max_rounds {
                // Progress on the final allowed round means more work may remain.
                campaign.reached_limit = true;
            }
        }
        campaign.finish(self, gated_families)
    }
}
