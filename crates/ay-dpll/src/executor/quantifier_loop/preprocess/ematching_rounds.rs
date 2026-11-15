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
    /// (#quantifier-guarded-instances) Instances of unentailed universals,
    /// deduplicated across rounds. Deliberately NOT added to
    /// `assertions`/`seen`: nothing here is asserted, so nothing here may be
    /// read as a fact — not by the entailed-universal walk, not by the unit
    /// harvest, not by the equality classes — or filtered as an
    /// already-derived fact.
    guarded_instantiations: Vec<ForallInstantiationProvenance>,
    seen_guarded: HashSet<(TermId, Vec<TermId>, TermId)>,
    /// (#guarded-instance-match-terms) The quantifier-free guarded instances,
    /// offered to later rounds as MATCH-ONLY roots: their ground terms may
    /// bind a trigger, and that is all they may do.
    ///
    /// Without them a guarded instance was a dead end. Verus states each
    /// fuel-controlled definition as `(=> (fuel_bool f) (forall …))`; when the
    /// guard is derived during search rather than asserted, the definition is
    /// not entailed, its instance `(= (f x) (Add (%I x) 1))` becomes a guarded
    /// clause, and the prelude axiom for `Add` never met `(Add (%I x) 1)`,
    /// because that term occurs nowhere else. z3 matches on every term of an
    /// instance it has asserted as `(or (not q) body)`; this is the same
    /// discipline. Instances found this way are conjoined only when their own
    /// universal is entailed, and `∀x̄.B ⊨ B[t̄]` for every ground `t̄`, so
    /// where a binding's terms came from cannot make one unsound.
    ///
    /// Bounded like every other instance: the terms of a guarded instance
    /// carry its generation, so the cost gate and the round limit apply to
    /// what they trigger. With `--no-quantifier-guarded-instances` there is no
    /// guarded record, hence no root, and the campaign is what it was.
    guarded_match_roots: Vec<TermId>,
    /// (#guarded-nested-quantifiers) The closed quantifiers of the exact
    /// guarded instances, offered to later rounds as guarded-only
    /// quantifiers: their instances are guarded records too, and the guarded
    /// pass gives each one a proxy of its own (`nested_guarded`).
    guarded_nested_quantifiers: Vec<TermId>,
    /// The nested quantifiers and skeleton roots already offered.
    seen_nested: HashSet<TermId>,
    /// The maximal quantifiers of the campaign's input assertions: with the
    /// nested ones offered, the only universals the guarded pass can give a
    /// proxy. The quantifiers nested in an instance of any other universal
    /// are not offered; its record gets no clause, and offering them would
    /// only change what the rounds match.
    proxiable: HashSet<TermId>,
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
            guarded_instantiations: Vec::new(),
            seen_guarded: HashSet::default(),
            guarded_match_roots: Vec::new(),
            guarded_nested_quantifiers: Vec::new(),
            seen_nested: HashSet::default(),
            proxiable: HashSet::default(),
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
        // (#degrade277-narrow) Record what THIS round was licensed to conjoin.
        // Per round, not once for the campaign: round `k` runs against
        // `self.assertions`, which already carries rounds `0..k`'s instances,
        // so the entailed set can differ round to round.
        executor.record_entailed_forall_authority(&result.entailed_foralls);
        executor.record_matched_instances(&result.conditional_forall_instantiations);
        executor.record_matched_instances(&result.guarded_instantiations);
        executor.record_matched_instances(&result.unconditional_forall_instantiations);

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

        let mut new_match_roots = 0usize;
        for record in result.guarded_instantiations {
            let key = (record.quantifier, record.binding.clone(), record.instance);
            if self.seen_guarded.insert(key) {
                // An instance that still carries a quantifier is not a root:
                // its bound variables are not ground terms, and a match-only
                // root is never searched for quantifiers anyway. Its ground
                // skeleton is, and its quantifiers join the next round.
                if !crate::ematching::contains_quantifier(&executor.ctx.terms, record.instance) {
                    if !self.seen.contains(&record.instance) {
                        self.guarded_match_roots.push(record.instance);
                        new_match_roots += 1;
                    }
                } else {
                    new_match_roots += self.absorb_nested(executor, &record);
                }
                self.guarded_instantiations.push(record);
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

        // A round that only found new guarded instances still advanced: their
        // terms are new match candidates for the next round.
        if result.reached_limit || (added == 0 && new_match_roots == 0) {
            RoundProgress::Fixpoint
        } else {
            RoundProgress::Advanced
        }
    }

    /// Offer the quantifiers nested in `record`'s EXACT instance (the term
    /// the guarded pass will proxy, so the records of each name the same
    /// `TermId`) to later rounds, and its ground skeleton as a match-only
    /// root. Returns how many new roots and quantifiers it added.
    fn absorb_nested(
        &mut self,
        executor: &mut Executor,
        record: &ForallInstantiationProvenance,
    ) -> usize {
        if !self.proxiable.contains(&record.quantifier)
            && !self.seen_nested.contains(&record.quantifier)
        {
            return 0;
        }
        let Some(exact) = executor.exact_forall_instance(record.quantifier, &record.binding) else {
            return 0;
        };
        let Some((nested, skeleton)) =
            super::nested_guarded::nested_parts(&mut executor.ctx.terms, exact)
        else {
            return 0;
        };
        let mut added = 0;
        for quantifier in nested {
            if self.guarded_nested_quantifiers.len()
                >= super::nested_guarded::MAX_NESTED_QUANTIFIERS
            {
                break;
            }
            // A nested existential is matched through its dual, whose
            // records its proxy guards (`nested_guarded`).
            let universal = match executor.ctx.terms.get(quantifier) {
                ay_core::TermData::Forall(..) => Some(quantifier),
                ay_core::TermData::Exists(..) => {
                    super::nested_guarded::existential_dual(&mut executor.ctx.terms, quantifier)
                }
                _ => None,
            };
            if let Some(universal) = universal {
                if self.seen_nested.insert(universal) {
                    self.guarded_nested_quantifiers.push(universal);
                    added += 1;
                }
            }
        }
        if !self.seen.contains(&skeleton) && self.seen_nested.insert(skeleton) {
            self.guarded_match_roots.push(skeleton);
            added += 1;
        }
        added
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
            guarded_instantiations: self.guarded_instantiations,
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
        for &assertion in &self.ctx.assertions {
            if let Some(maximal) =
                super::quantifier_proxy::maximal_quantifiers_of(&self.ctx.terms, assertion)
            {
                campaign.proxiable.extend(maximal);
            }
        }

        for round_index in 0..max_rounds {
            if should_stop() || self.ematching_check_budget.exhausted() {
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
                manager.run_ematching_round_with_match_roots(
                    &mut self.ctx.terms,
                    &campaign.assertions,
                    &campaign.guarded_match_roots,
                    &campaign.guarded_nested_quantifiers,
                    euf_model,
                    &should_stop,
                )
            };
            self.add_phase_seconds(
                "time.quantifier.ematching_seconds",
                started_at.elapsed().as_secs_f64(),
            );
            let new_terms = self.ctx.terms.len().saturating_sub(watermark as usize);
            let budget_spent = self
                .ematching_check_budget
                .charge(result.instantiations.len(), new_terms);
            if matches!(
                campaign.absorb(self, result, watermark),
                RoundProgress::Fixpoint
            ) {
                break;
            }
            if budget_spent {
                campaign.reached_limit = true;
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
