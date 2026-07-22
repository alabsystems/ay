// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver statistics extraction for failure analysis.
//!
//! Part of #1870 - Failure-guided learning for retry attempts.

use super::PdrSolver;
use crate::failure_analysis::SolverStats;
use crate::lemma_hints::LemmaHint;
use crate::lemma_pool::{LemmaPool, SharedLemma};
use crate::pdr::config::{PdrConfig, LIA_FARKAS_PROFILE_NAME};
use crate::pdr::PdrResult;
use crate::{ChcExpr, ChcProblem, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    fn learned_lemma_count(&self) -> usize {
        self.frames.iter().map(|frame| frame.lemmas.len()).sum()
    }

    /// Export all learned lemmas as a LemmaPool for cross-engine transfer (#7919).
    ///
    /// Extracts non-trivial lemmas from all frames, preferring higher-frame lemmas
    /// (which survived more pushing rounds). Used after non-inlined PDR returns
    /// Unknown to seed portfolio engines and failure-guided retry.
    pub(crate) fn export_lemmas(&self) -> LemmaPool {
        let mut pool = LemmaPool::new();
        let mut seen = FxHashSet::default();
        for (level, frame) in self.frames.iter().enumerate().rev() {
            for lemma in &frame.lemmas {
                if lemma.formula.simplify_constants() == ChcExpr::Bool(true) {
                    continue;
                }
                if !seen.insert((lemma.predicate, lemma.formula.clone())) {
                    continue;
                }
                pool.lemmas.push(SharedLemma {
                    formula: lemma.formula.clone(),
                    predicate: lemma.predicate,
                    source_frame: level,
                });
            }
        }
        pool
    }

    /// Extract learned frame lemmas as runtime hints for retry configurations.
    pub(crate) fn extract_learned_lemmas(&self) -> Vec<LemmaHint> {
        const MAX_TRANSFER_LEMMAS: usize = 100;
        const TRANSFER_PRIORITY: u16 = 0;
        const TRANSFER_SOURCE: &str = "portfolio_transfer";

        let mut candidates = self
            .frames
            .iter()
            .enumerate()
            .skip(1)
            .flat_map(|(level, frame)| {
                frame.lemmas.iter().filter_map(move |lemma| {
                    if lemma.formula.simplify_constants() == ChcExpr::Bool(true) {
                        return None;
                    }
                    Some((level, lemma.predicate, lemma.formula.clone()))
                })
            })
            .collect::<Vec<_>>();

        // Prefer higher-frame lemmas first: they survived more pushing and are
        // more likely to be useful when we cap the transferred hint set.
        candidates.sort_by(|a, b| {
            b.0.cmp(&a.0)
                .then_with(|| a.1.cmp(&b.1))
                .then_with(|| a.2.cmp(&b.2))
        });

        let mut learned_lemmas = Vec::with_capacity(candidates.len().min(MAX_TRANSFER_LEMMAS));
        let mut seen = FxHashSet::default();
        for (_, predicate, formula) in candidates {
            if !seen.insert((predicate, formula.clone())) {
                continue;
            }
            learned_lemmas.push(LemmaHint::new(
                predicate,
                formula,
                TRANSFER_PRIORITY,
                TRANSFER_SOURCE,
            ));
            if learned_lemmas.len() == MAX_TRANSFER_LEMMAS {
                break;
            }
        }

        learned_lemmas
    }

    /// Publish current learned lemmas to the cooperative blackboard (#7910).
    ///
    /// Called at restarts and periodically during the main loop. Only
    /// publishes when a blackboard is configured (portfolio parallel mode).
    /// Skips trivial-true lemmas and prefers higher-frame lemmas.
    pub(crate) fn publish_to_blackboard(&self) {
        let Some(ref bb) = self.config.blackboard else {
            return;
        };

        let lemmas = self
            .frames
            .iter()
            .enumerate()
            .skip(1)
            .flat_map(|(level, frame)| {
                frame.lemmas.iter().filter_map(move |lemma| {
                    if lemma.formula.simplify_constants() == ChcExpr::Bool(true) {
                        return None;
                    }
                    Some((lemma.predicate, lemma.formula.clone(), level))
                })
            });

        bb.publish(self.config.engine_idx, lemmas);
    }

    /// Extract statistics from the solver's current state.
    ///
    /// This is used for failure analysis when the solver returns Unknown,
    /// allowing the adaptive portfolio to make informed decisions about
    /// retry attempts.
    pub(crate) fn extract_stats(&self) -> SolverStats {
        // Count total lemmas across all frames.
        let total_lemmas = self.learned_lemma_count();
        let mut lemmas_per_predicate = FxHashMap::default();

        for frame in &self.frames {
            for lemma in &frame.lemmas {
                *lemmas_per_predicate.entry(lemma.predicate).or_insert(0) += 1;
            }
        }

        // Detect predicate coupling: if multiple predicates have similar lemma counts
        // and the problem has inter-predicate clauses, they may be coupled
        let has_predicate_coupling = self.detect_predicate_coupling(&lemmas_per_predicate);

        // Estimate max CEX depth from obligations queue size and frame depth
        // This is a heuristic: deep CEX exploration tends to create deep obligation chains
        let estimated_cex_depth =
            if self.obligations.deque.is_empty() && self.obligations.heap.is_empty() {
                // If queue is empty, use frame count as baseline
                self.frames.len().saturating_sub(1)
            } else {
                // Use a proxy: iterations without lemma learning suggests deep CEX exploration
                // The actual tracking would require instrumenting the solve loop (#1870 follow-up)
                self.frames
                    .len()
                    .saturating_sub(1)
                    .max(self.verification.consecutive_unlearnable.saturating_mul(2))
            };
        let entry_inductive_failure_counts = self
            .telemetry
            .entry_inductive_failure_counts
            .iter()
            .map(|(reason, count)| (reason.as_str().to_string(), *count))
            .collect();

        let native_helper_stats = self
            .caches
            .implication_cache
            .native_code_helper_statistics();
        let (symbolic_scalarization_projected_cells, symbolic_scalarization_multi_cell_args) =
            self.symbolic_scalarization_projection_counts();

        SolverStats {
            iterations: self.iterations,
            lemmas_learned: total_lemmas,
            max_frame: self.frames.len().saturating_sub(1),
            restart_count: self.restart.restart_count,
            consecutive_unlearnable: self.verification.consecutive_unlearnable,
            smt_unknowns: self.verification.total_unknowns,
            lemmas_per_predicate,
            // Estimate max CEX depth from unlearnable failures as a proxy
            // Proper tracking requires instrumenting the solve loop (#1870 follow-up)
            max_cex_depth: estimated_cex_depth,
            has_predicate_coupling,
            // ImplicationCache statistics (#2126, #2262)
            implication_cache_hits: self.caches.implication_cache.cache_hits,
            implication_model_rejections: self.caches.implication_cache.model_rejections,
            implication_solver_calls: self.caches.implication_cache.solver_calls,
            chc_native_code_helper_compile_attempts: native_helper_stats.compile_attempts as usize,
            chc_native_code_helper_compile_successes: native_helper_stats.compile_successes
                as usize,
            chc_native_code_helper_compile_failures: native_helper_stats.compile_failures as usize,
            chc_native_code_helper_evaluations: native_helper_stats.evaluations as usize,
            chc_native_code_helper_deopts: native_helper_stats.deopts as usize,
            chc_native_code_helper_fallbacks: native_helper_stats.fallbacks as usize,
            chc_native_code_helper_missing_var_fallbacks: native_helper_stats.missing_var_fallbacks
                as usize,
            chc_native_code_helper_interpreter_confirmations: native_helper_stats
                .interpreter_confirmations
                as usize,
            chc_native_code_helper_trusted_true_results: native_helper_stats.trusted_true_results
                as usize,
            chc_native_code_helper_applications: native_helper_stats.applications as usize,
            chc_tla_transition_cluster_applications: 0,
            symbolic_scalarization_projected_cells,
            symbolic_scalarization_multi_cell_args,
            sat_no_cube_events: self.telemetry.sat_no_cube_events,
            entry_inductive_failure_counts,
            // Convergence monitoring data
            elapsed_secs: self.convergence.elapsed().as_secs_f64(),
            secs_since_frame_advance: self.convergence.time_since_frame_advance().as_secs_f64(),
            consecutive_stagnant_windows: self.convergence.consecutive_stagnant_windows,
            terminated_by_stagnation: self.terminated_by_stagnation,
        }
    }

    /// Detect if predicates appear to be coupled (progress on one affects others)
    fn detect_predicate_coupling(
        &self,
        lemmas_per_predicate: &FxHashMap<PredicateId, usize>,
    ) -> bool {
        // Simple heuristic: if we have multiple predicates with similar lemma counts
        // and they're in the same SCC, they're likely coupled
        if lemmas_per_predicate.len() < 2 {
            return false;
        }

        // Check if any multi-predicate SCC has all its members with lemmas
        for scc in &self.scc_info.sccs {
            if scc.predicates.len() > 1 && scc.is_cyclic {
                let scc_preds_with_lemmas = scc
                    .predicates
                    .iter()
                    .filter(|p| lemmas_per_predicate.contains_key(*p))
                    .count();

                // If all or most predicates in an SCC have lemmas, they're likely coupled
                if scc_preds_with_lemmas >= scc.predicates.len() / 2 {
                    return true;
                }
            }
        }

        false
    }
}

/// Derived Lane 4 route counters built from PDR's existing telemetry.
///
/// These counters are intentionally internal: they document whether the
/// arithmetic profile exercised the expected template/Farkas/validation surface
/// without adding another user-facing configuration knob.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct LiaFarkasRouteStats {
    pub(crate) profile_name: &'static str,
    pub(crate) profile_enabled: bool,
    pub(crate) enabled_template_surfaces: usize,
    pub(crate) template_generation_surfaces: usize,
    pub(crate) templates_generated: usize,
    pub(crate) template_generation_checks: usize,
    pub(crate) farkas_checks: usize,
    pub(crate) accepted_lemmas: usize,
    pub(crate) rejected_lemmas: usize,
    pub(crate) validation_checks: usize,
    pub(crate) validation_failures: usize,
    pub(crate) original_validation_required: bool,
}

impl PdrSolver {
    /// Extract LIA/Farkas route evidence from the solver's current state.
    pub(crate) fn extract_lia_farkas_route_stats(&self) -> LiaFarkasRouteStats {
        let template_stats = self.telemetry.lia_farkas_templates;

        LiaFarkasRouteStats {
            profile_name: LIA_FARKAS_PROFILE_NAME,
            profile_enabled: self.config.is_lia_farkas_profile(),
            enabled_template_surfaces: self.config.lia_farkas_template_surface().enabled_count(),
            template_generation_surfaces: template_stats.observed_surface_count(),
            templates_generated: template_stats.templates_generated,
            template_generation_checks: template_stats.template_checks,
            farkas_checks: template_stats.farkas_checks,
            accepted_lemmas: template_stats.accepted_lemmas,
            rejected_lemmas: template_stats.rejected_lemmas,
            validation_checks: self.telemetry.verification_queries,
            validation_failures: template_stats.validation_failures,
            original_validation_required: self.config.strict_proofs
                && self.config.preserve_original_clauses,
        }
    }
}

/// Combined result with statistics for failure analysis
#[derive(Debug, Clone)]
pub(crate) struct PdrResultWithStats {
    /// The solving result
    pub result: PdrResult,
    /// Statistics from the solving attempt
    pub stats: SolverStats,
    /// Lane 4 arithmetic route diagnostics derived from PDR telemetry.
    pub(crate) lia_farkas_route_stats: LiaFarkasRouteStats,
    /// Learned lemmas extracted from the solver frames for retry seeding.
    pub(crate) learned_lemmas: Vec<LemmaHint>,
}

impl PdrSolver {
    /// Solve the CHC problem and return both result and statistics.
    ///
    /// This is useful for failure-guided retry where we need to analyze
    /// why a solve attempt returned Unknown.
    pub(crate) fn solve_with_stats(&mut self) -> PdrResultWithStats {
        let result = self.solve();
        let stats = self.extract_stats();
        let lia_farkas_route_stats = self.extract_lia_farkas_route_stats();
        let learned_lemmas = self.extract_learned_lemmas();

        // Print ImplicationCache statistics in verbose mode (#2262)
        if self.config.verbose {
            let total_queries = stats.implication_cache_hits
                + stats.implication_model_rejections
                + stats.implication_solver_calls;
            // Saved calls = queries that didn't require an SMT solver call
            let saved_calls = stats.implication_cache_hits + stats.implication_model_rejections;
            let savings_pct = if total_queries > 0 {
                (saved_calls as f64 / total_queries as f64) * 100.0
            } else {
                0.0
            };
            safe_eprintln!(
                "PDR: ImplicationCache stats: hits={}, model_rejections={}, solver_calls={}, savings={:.1}%",
                stats.implication_cache_hits,
                stats.implication_model_rejections,
                stats.implication_solver_calls,
                savings_pct
            );

            // Print interpolation telemetry (#2450)
            safe_eprintln!(
                "PDR: Interpolation stats: {}",
                self.telemetry.interpolation_stats.summary()
            );
            safe_eprintln!("PDR: SAT-no-cube events: {}", stats.sat_no_cube_events);
        }

        PdrResultWithStats {
            result,
            stats,
            lia_farkas_route_stats,
            learned_lemmas,
        }
    }

    /// Solve a pre-parsed problem with stats for failure analysis.
    pub(crate) fn solve_problem_with_stats(
        problem: &ChcProblem,
        mut config: PdrConfig,
    ) -> PdrResultWithStats {
        // Try case-split for unconstrained constant arguments.
        // Skip when running under a cancellation token (portfolio engine) since
        // the Adaptive strategy already runs case-split as Stage 0 (#5399).
        // Also skip under trace mode so the top-level PDR run owns the JSONL.
        if config.cancellation_token.is_none() && config.tla_trace_path.is_none() {
            let case_split_start = ay_core::time::Instant::now();
            if let Some(case_split_result) = Self::try_case_split_solve(problem, config.clone()) {
                return PdrResultWithStats {
                    result: case_split_result,
                    stats: SolverStats::default(),
                    lia_farkas_route_stats: LiaFarkasRouteStats::default(),
                    learned_lemmas: Vec::new(),
                };
            }
            let Some(fallback_config) =
                Self::case_split_fallback_config(config, case_split_start.elapsed())
            else {
                return PdrResultWithStats {
                    result: PdrResult::Unknown,
                    stats: SolverStats::default(),
                    lia_farkas_route_stats: LiaFarkasRouteStats::default(),
                    learned_lemmas: Vec::new(),
                };
            };
            config = fallback_config;
        }

        let trace_path = config.tla_trace_path.clone();
        let mut solver = Self::new(problem.clone(), config);
        if let Some(path) = trace_path.as_deref() {
            solver.enable_tla_trace_from_path(path);
        }
        solver.solve_with_stats()
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
