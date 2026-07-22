// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Gas assigned to a fresh MAY pob: 5 units per cluster member, mirroring
/// GSpacer's `pob gas = 5 x cluster size` discipline (spacer_cluster.h).
pub(in crate::pdr::solver) const MAY_POB_GAS_PER_MEMBER: u32 = 5;

impl PdrSolver {
    /// Whether GSpacer-style may-pob global guidance is active (agenda #6).
    /// `AY_CHC_MAY_POB=0` is the runtime kill switch; `use_may_pobs` gates
    /// per-config (portfolio variants / tests).
    pub(in crate::pdr::solver) fn may_pobs_enabled(&self) -> bool {
        self.config.use_may_pobs && crate::pdr::obligation::may_pob_env_enabled()
    }

    /// Queue a global-guidance candidate cube as a MAY proof obligation
    /// (GSpacer SUBSUME/CONJECTURE rules, CAV'20 "Global Guidance of
    /// Induction in Model Checking" completion of AY's inline versions).
    ///
    /// The candidate could not be accepted inline (not immediately
    /// inductive), so the full PDR engine gets to prove it unreachable:
    /// posted at `min(cluster min level, origin level)` clamped to >= 1,
    /// with `desired_level` = the origin pob's level and gas =
    /// `MAY_POB_GAS_PER_MEMBER x cluster size`.
    ///
    /// SOUNDNESS (G2): a may-pob only ever *adds lemmas* through the
    /// standard inductiveness-checked blocking path; if it turns out
    /// reachable or undecidable it is dropped silently and never enters
    /// counterexample reconstruction (guards in `strengthen.rs`).
    ///
    /// Returns true when a may-pob was actually enqueued.
    pub(in crate::pdr::solver) fn spawn_may_pob(
        &mut self,
        origin: &ProofObligation,
        candidate: ChcExpr,
        kind: PobKind,
        cluster_min_level: Option<usize>,
        cluster_size: usize,
    ) -> bool {
        if !self.may_pobs_enabled() {
            return false;
        }
        // Gas discipline: may-pobs never spawn further may-pobs (also
        // enforced by the early return in try_global_generalization).
        if origin.is_may() {
            return false;
        }
        if cluster_size == 0 {
            return false;
        }
        // Level 0 is the init frame: blocking there is an init-intersection
        // check, not a lemma opportunity — clamp to >= 1.
        let level = cluster_min_level
            .map_or(origin.level, |min_lvl| min_lvl.min(origin.level))
            .max(1);
        let key = (origin.predicate, kind, candidate.structural_hash());
        if !self.obligations.spawned_may_pobs.insert(key) {
            return false;
        }
        let gas =
            MAY_POB_GAS_PER_MEMBER.saturating_mul(u32::try_from(cluster_size).unwrap_or(u32::MAX));
        let may_pob = ProofObligation::new(origin.predicate, candidate, level).with_may(
            kind,
            gas,
            origin.level,
        );
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Spawning {:?} may-pob for pred {} at level {} (desired {}, gas {}): {}",
                kind,
                origin.predicate.index(),
                level,
                origin.level,
                gas,
                may_pob.state,
            );
        }
        self.push_obligation(may_pob);
        true
    }

    pub(in crate::pdr::solver) fn try_global_generalization(
        &mut self,
        blocking_formula: &ChcExpr,
        pob: &mut ProofObligation,
        is_on_counterexample_path: bool,
    ) -> ChcExpr {
        // MAY pobs are themselves products of global guidance: skip cluster
        // bookkeeping and further global generalization for them so the
        // conjectured cube stays intact (GSpacer's disable_local_gen analog)
        // and may-pobs can never recursively spawn more may-pobs.
        if pob.is_may() {
            return blocking_formula.clone();
        }
        let mut final_blocking_formula = blocking_formula.clone();
        if self.config.use_convex_closure && !is_on_counterexample_path {
            if let Some(idx) = self.caches.cluster_store.add_blocking_cube(
                pob.predicate,
                blocking_formula,
                pob.level,
            ) {
                let extracted_state_values = if pob.smt_model.is_some() {
                    None
                } else {
                    Some(self.extract_point_values_from_state(&pob.state))
                };
                let state_values = match pob.smt_model.as_ref() {
                    Some(model) => model,
                    None => extracted_state_values
                        .as_ref()
                        .expect("extracted when smt_model is None"),
                };

                let (min_max_candidates, eligible_for_subsume) = self
                    .caches
                    .cluster_store
                    .get_clusters(pob.predicate)
                    .and_then(|cs| cs.get(idx))
                    .map_or((Vec::new(), false), |cluster| {
                        (
                            cluster.propose_min_max_blocking_cubes(),
                            cluster.is_eligible(),
                        )
                    });

                for candidate in min_max_candidates {
                    if !self.point_values_satisfy_cube(&candidate, state_values) {
                        continue;
                    }
                    if self.predicate_has_facts(pob.predicate)
                        && !self.blocks_initial_states(pob.predicate, &candidate)
                    {
                        continue;
                    }
                    if self.is_safety_path_point_blocking_acceptable(
                        &candidate,
                        pob.predicate,
                        pob.level,
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Cluster min/max generalized blocking cube: {} -> {}",
                                blocking_formula,
                                candidate
                            );
                        }
                        final_blocking_formula = candidate;
                        self.caches.cluster_store.add_blocking_cube(
                            pob.predicate,
                            &final_blocking_formula,
                            pob.level,
                        );
                        break;
                    }
                }

                if final_blocking_formula == *blocking_formula && eligible_for_subsume {
                    let cluster = self
                        .caches
                        .cluster_store
                        .get_clusters(pob.predicate)
                        .and_then(|cs| cs.get(idx))
                        .cloned();

                    if let Some(cluster) = cluster {
                        let cluster_min_level = cluster.min_level();
                        let cluster_size = cluster.size();
                        let generalized = self.try_cluster_subsume(&cluster, pob.level);
                        if let Some(clusters_mut) =
                            self.caches.cluster_store.get_clusters_mut(pob.predicate)
                        {
                            if let Some(cluster_mut) = clusters_mut.get_mut(idx) {
                                cluster_mut.dec_gas();
                            }
                        }

                        if let Some(generalized) = generalized {
                            let covers_pob_state =
                                self.point_values_satisfy_cube(&generalized, state_values);
                            let blocks_init = !self.predicate_has_facts(pob.predicate)
                                || self.blocks_initial_states(pob.predicate, &generalized);
                            if covers_pob_state
                                && blocks_init
                                && self.is_safety_path_point_blocking_acceptable(
                                    &generalized,
                                    pob.predicate,
                                    pob.level,
                                )
                            {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Global generalizer produced: {} (was: {})",
                                        generalized,
                                        blocking_formula
                                    );
                                }
                                final_blocking_formula = generalized;
                                self.caches.cluster_store.add_blocking_cube(
                                    pob.predicate,
                                    &final_blocking_formula,
                                    pob.level,
                                );
                            } else if blocks_init {
                                // MAY-POB (agenda #6, GSpacer SUBSUME): the
                                // candidate is not immediately inductive —
                                // exactly the case where recursive
                                // strengthening by the full engine can still
                                // prove it. Queue it as a gas-budgeted may
                                // proof obligation instead of discarding.
                                // Candidates that intersect init are skipped:
                                // they are unblockable by construction.
                                self.spawn_may_pob(
                                    pob,
                                    generalized,
                                    PobKind::MaySubsume,
                                    cluster_min_level,
                                    cluster_size,
                                );
                            }
                        }
                    }
                }

                if final_blocking_formula == *blocking_formula {
                    let conjecture_info = self
                        .caches
                        .cluster_store
                        .get_clusters(pob.predicate)
                        .and_then(|cs| cs.get(idx))
                        .and_then(|cluster| {
                            if !cluster.is_eligible() || cluster.gas == 0 {
                                return None;
                            }
                            let mono_var_lit = cluster.find_mono_var_literal()?;
                            let pattern_var = cluster.pattern_vars.first()?.clone();
                            Some((
                                mono_var_lit,
                                pattern_var,
                                cluster.min_level(),
                                cluster.size(),
                            ))
                        });

                    if let Some((mono_var_lit, pattern_var, cluster_min_level, cluster_size)) =
                        conjecture_info
                    {
                        let mut pob_conjuncts = Vec::new();
                        pob.state.collect_conjuncts_into(&mut pob_conjuncts);

                        let conjecture_formula = filter_out_lit_with_eq_retry(
                            &pob_conjuncts,
                            &mono_var_lit,
                            &pattern_var,
                        )
                        .or_else(|| {
                            let mut lemma_conjuncts = Vec::new();
                            blocking_formula.collect_conjuncts_into(&mut lemma_conjuncts);
                            filter_out_lit(&lemma_conjuncts, &mono_var_lit, &pattern_var)
                        });

                        if let Some(clusters_mut) =
                            self.caches.cluster_store.get_clusters_mut(pob.predicate)
                        {
                            if let Some(cluster_mut) = clusters_mut.get_mut(idx) {
                                cluster_mut.dec_gas();
                            }
                        }

                        if let Some(remaining) = conjecture_formula {
                            if !remaining.is_empty() {
                                let conj_formula = ChcExpr::and_all(remaining);
                                let covers_pob_state =
                                    self.point_values_satisfy_cube(&conj_formula, state_values);
                                let blocks_init = !self.predicate_has_facts(pob.predicate)
                                    || self.blocks_initial_states(pob.predicate, &conj_formula);
                                if covers_pob_state
                                    && blocks_init
                                    && self.is_safety_path_point_blocking_acceptable(
                                        &conj_formula,
                                        pob.predicate,
                                        pob.level,
                                    )
                                {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Conjecture generalized blocking cube: {} -> {}",
                                            blocking_formula,
                                            conj_formula
                                        );
                                    }
                                    final_blocking_formula = conj_formula;
                                    self.caches.cluster_store.add_blocking_cube(
                                        pob.predicate,
                                        &final_blocking_formula,
                                        pob.level,
                                    );
                                } else {
                                    if blocks_init {
                                        // MAY-POB (agenda #6, GSpacer
                                        // CONJECTURE): not immediately
                                        // inductive — post as a gas-budgeted
                                        // may proof obligation.
                                        self.spawn_may_pob(
                                            pob,
                                            conj_formula.clone(),
                                            PobKind::MayConjecture,
                                            cluster_min_level,
                                            cluster_size,
                                        );
                                    }
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Conjecture {} failed inductiveness/init check",
                                            conj_formula
                                        );
                                    }
                                }
                            } else if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Conjecture empty after filtering mono-var from {}",
                                    blocking_formula
                                );
                            }
                        } else if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Conjecture filtering failed for mono-var lit {} in {}",
                                mono_var_lit,
                                blocking_formula
                            );
                        }
                    }
                }

                if final_blocking_formula == *blocking_formula {
                    let cluster_for_concretize = self
                        .caches
                        .cluster_store
                        .get_clusters(pob.predicate)
                        .and_then(|cs| cs.get(idx))
                        .map(|cluster| (cluster.pattern.clone(), cluster.pattern_vars.clone()));

                    if let Some((pattern, pattern_vars)) = cluster_for_concretize {
                        if crate::pdr::pob_concretize::has_nonlinear_pattern_vars(
                            &pattern,
                            &pattern_vars,
                        ) {
                            if let Some(model) = pob.smt_model.as_ref() {
                                let model_map: ay_core::kani_compat::DetHashMap<String, SmtValue> =
                                    model.iter().map(|(k, v)| (k.clone(), v.clone())).collect();

                                let mut pob_literals = Vec::new();
                                pob.state.collect_conjuncts_into(&mut pob_literals);

                                let mut concretizer =
                                    crate::pdr::pob_concretize::PobConcretizer::new(
                                        &pattern,
                                        &pattern_vars,
                                        &model_map,
                                    );

                                if let Some(concretized_lits) = concretizer.apply(&pob_literals) {
                                    if concretized_lits != pob_literals
                                        && !concretized_lits.is_empty()
                                    {
                                        let conc_formula = ChcExpr::and_all(concretized_lits);
                                        if self
                                            .point_values_satisfy_cube(&conc_formula, state_values)
                                            && (!self.predicate_has_facts(pob.predicate)
                                                || self.blocks_initial_states(
                                                    pob.predicate,
                                                    &conc_formula,
                                                ))
                                            && self.is_safety_path_point_blocking_acceptable(
                                                &conc_formula,
                                                pob.predicate,
                                                pob.level,
                                            )
                                        {
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: Concretization generalized blocking cube: {} -> {}",
                                                    blocking_formula,
                                                    conc_formula
                                                );
                                            }
                                            final_blocking_formula = conc_formula;
                                            self.caches.cluster_store.add_blocking_cube(
                                                pob.predicate,
                                                &final_blocking_formula,
                                                pob.level,
                                            );
                                        } else if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: Concretized formula {} failed validation",
                                                conc_formula
                                            );
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        final_blocking_formula
    }
}
