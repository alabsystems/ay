// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA2 trace integration for PDR solver transitions.
//!
//! Emits compact runtime snapshots for validating PDR action sequences against
//! `specs/pdr_test.tla`.

use super::PdrSolver;
use crate::pdr::frame::PdrResult;
use crate::pdr::obligation::ProofObligation;
use crate::pdr::InvariantModel;
use ay_sat::{TlaTraceWriter, TlaTraceable};

const PDR_TRACE_MODULE: &str = "pdr_test";
const PDR_TRACE_VARIABLES: [&str; 8] = [
    "frames",
    "obligations",
    "currentLevel",
    "result",
    "lemmaCount",
    "activePredicate",
    "activeLevel",
    "obligationDepth",
];

impl TlaTraceable for PdrSolver {
    fn tla_module() -> &'static str {
        PDR_TRACE_MODULE
    }

    fn tla_variables() -> &'static [&'static str] {
        &PDR_TRACE_VARIABLES
    }

    /// Enable TLA2 JSONL trace emission for this solver instance.
    ///
    /// Writes an initial step (index 0) immediately with action = None.
    fn enable_tla_trace(&mut self, path: &str, module: &str, variables: &[&str]) {
        ay_core::claim_trace_file();
        self.tracing.tla_trace = Some(TlaTraceWriter::new(path, module, variables));
        self.pdr_trace_step("Running", None, None);
    }
}

impl PdrSolver {
    /// Enable trace output on an explicit path.
    pub(in crate::pdr::solver) fn enable_tla_trace_from_path(&mut self, path: &str) {
        <Self as TlaTraceable>::enable_tla_trace(
            self,
            path,
            PDR_TRACE_MODULE,
            &PDR_TRACE_VARIABLES,
        );
    }

    /// Enable trace output from the path captured in the solver config.
    ///
    /// This is intended for top-level PDR solve entry points that already
    /// captured `AY_TRACE_FILE` in `PdrConfig` and must not re-read the
    /// environment. If tracing is already enabled, leave the active writer
    /// untouched to avoid clobbering the JSONL file.
    pub(crate) fn enable_tla_trace_from_config(&mut self) {
        if self.tracing.tla_trace.is_some() {
            return;
        }
        if let Some(path) = self.config.tla_trace_path.clone() {
            self.enable_tla_trace_from_path(&path);
        }
    }

    fn obligations_len(&self) -> usize {
        if self.config.use_level_priority {
            self.obligations.heap.len()
        } else {
            self.obligations.deque.len()
        }
    }

    fn usize_to_i64(value: usize) -> i64 {
        i64::try_from(value).unwrap_or(i64::MAX)
    }

    /// Build a TLA2 state snapshot aligned with `specs/pdr_test.tla`.
    ///
    /// `active_pob` provides obligation context when processing an obligation.
    /// Pass `None` for non-obligation actions (Init, ExpandLevel, PropagateLemmas, terminal).
    fn pdr_trace_snapshot(
        &self,
        result: &str,
        active_pob: Option<&ProofObligation>,
    ) -> serde_json::Value {
        let frame_count = Self::usize_to_i64(self.frames.len());
        let obligations = Self::usize_to_i64(self.obligations_len());
        // Use the independently-tracked query level instead of computing from frames.len().
        // This makes `FrameMonotonicity` (currentLevel = frames - 1) non-vacuous:
        // the invariant can now detect bugs where the query level falls out of sync
        // with the frame count (e.g., missing push_frame update, stale level after restart).
        let current_level = match self.tracing.query_level {
            Some(level) => Self::usize_to_i64(level),
            None => Self::usize_to_i64(self.frames.len().saturating_sub(1)),
        };
        let lemma_count: usize = self.frames.iter().map(|f| f.lemmas.len()).sum();

        let (active_pred, active_lvl, ob_depth) = match active_pob {
            Some(pob) => (
                pob.predicate.index() as i64,
                pob.level as i64,
                pob.depth as i64,
            ),
            None => match self.tracing.active_pob {
                Some((pred_idx, level, depth)) => (pred_idx as i64, level as i64, depth as i64),
                None => (-1_i64, -1_i64, 0_i64),
            },
        };

        serde_json::json!({
            "frames": {"type": "int", "value": frame_count},
            "obligations": {"type": "int", "value": obligations},
            "currentLevel": {"type": "int", "value": current_level},
            "result": {"type": "string", "value": result},
            "lemmaCount": {"type": "int", "value": Self::usize_to_i64(lemma_count)},
            "activePredicate": {"type": "int", "value": active_pred},
            "activeLevel": {"type": "int", "value": active_lvl},
            "obligationDepth": {"type": "int", "value": ob_depth},
        })
    }

    /// Build a snapshot with no active obligation context.
    fn pdr_trace_snapshot_without_active(&self, result: &str) -> serde_json::Value {
        let frame_count = Self::usize_to_i64(self.frames.len());
        let obligations = Self::usize_to_i64(self.obligations_len());
        let current_level = match self.tracing.query_level {
            Some(level) => Self::usize_to_i64(level),
            None => Self::usize_to_i64(self.frames.len().saturating_sub(1)),
        };
        let lemma_count: usize = self.frames.iter().map(|f| f.lemmas.len()).sum();

        serde_json::json!({
            "frames": {"type": "int", "value": frame_count},
            "obligations": {"type": "int", "value": obligations},
            "currentLevel": {"type": "int", "value": current_level},
            "result": {"type": "string", "value": result},
            "lemmaCount": {"type": "int", "value": Self::usize_to_i64(lemma_count)},
            "activePredicate": {"type": "int", "value": -1_i64},
            "activeLevel": {"type": "int", "value": -1_i64},
            "obligationDepth": {"type": "int", "value": 0_i64},
        })
    }

    fn lia_farkas_route_telemetry(&self) -> serde_json::Value {
        let stats = self.extract_lia_farkas_route_stats();
        let surface = self.config.lia_farkas_template_surface();

        serde_json::json!({
            "profile_name": stats.profile_name,
            "profile_enabled": stats.profile_enabled,
            "template_surfaces": {
                "affine_equalities": surface.affine_equalities,
                "intervals": surface.intervals,
                "difference_bounds": surface.difference_bounds,
                "scaled_linear_combinations": surface.scaled_linear_combinations,
            },
            "enabled_template_surfaces": stats.enabled_template_surfaces,
            "template_generation_surfaces": stats.template_generation_surfaces,
            "templates_generated": stats.templates_generated,
            "template_generation_checks": stats.template_generation_checks,
            "farkas_checks": stats.farkas_checks,
            "accepted_lemmas": stats.accepted_lemmas,
            "rejected_lemmas": stats.rejected_lemmas,
            "validation_checks": stats.validation_checks,
            "validation_failures": stats.validation_failures,
            "original_validation_required": stats.original_validation_required,
        })
    }

    /// Emit a single PDR trace step when trace output is enabled.
    ///
    /// `active_pob` provides obligation context for BlockObligation and LearnLemma actions.
    /// Pass `None` for non-obligation actions.
    pub(in crate::pdr::solver) fn pdr_trace_step(
        &self,
        result: &str,
        action: Option<&str>,
        active_pob: Option<&ProofObligation>,
    ) {
        if let Some(ref writer) = self.tracing.tla_trace {
            writer.write_step(self.pdr_trace_snapshot(result, active_pob), action);
        }
    }

    /// Emit a reason-bearing conservative-failure trace step.
    ///
    /// Uses a spec-compatible action name and attaches failure telemetry so Unknown
    /// exits can be triaged without parsing stderr.
    pub(in crate::pdr::solver) fn pdr_trace_conservative_fail(
        &self,
        reason: &'static str,
        detail: serde_json::Value,
        active_pob: Option<&ProofObligation>,
    ) {
        let Some(ref writer) = self.tracing.tla_trace else {
            return;
        };

        let has_active_obligation = active_pob.is_some() || self.tracing.active_pob.is_some();
        let (action, state) = if has_active_obligation {
            (
                "BlockObligation",
                self.pdr_trace_snapshot("Running", active_pob),
            )
        } else {
            (
                "PropagateLemmas",
                self.pdr_trace_snapshot_without_active("Running"),
            )
        };

        let entry_failure_total: usize = self
            .telemetry
            .entry_inductive_failure_counts
            .values()
            .copied()
            .sum();
        let cegar_total: usize = self.telemetry.entry_cegar_discharge_outcomes.iter().sum();
        let telemetry = serde_json::json!({
            "failure": {
                "reason": reason,
                "detail": detail,
            },
            "counters": {
                "iterations": self.iterations,
                "sat_no_cube_events": self.telemetry.sat_no_cube_events,
                "interpolation_attempts": self.telemetry.interpolation_stats.attempts,
                "interpolation_all_failed": self.telemetry.interpolation_stats.all_failed,
                "entry_inductive_failure_total": entry_failure_total,
                "entry_cegar_discharge_total": cegar_total,
                "consecutive_unlearnable_failures": self.verification.consecutive_unlearnable,
                "total_verification_unknowns": self.verification.total_unknowns,
                "total_model_verification_failures": self.verification.total_model_failures,
                "lia_farkas_route": self.lia_farkas_route_telemetry(),
            },
        });
        writer.write_step_with_telemetry(state, Some(action), Some(telemetry));
    }

    /// Flush the trace file (no-op when trace output is disabled).
    pub(in crate::pdr::solver) fn finish_pdr_tla_trace(&self) {
        if let Some(ref writer) = self.tracing.tla_trace {
            let _ = writer.finish();
        }
    }

    /// Build a telemetry payload from accumulated solver diagnostics.
    ///
    /// Captures interpolation cascade stats, SAT-no-cube events, and
    /// entry-inductiveness failure reasons as structured JSON for offline
    /// triage (#4697).
    fn build_telemetry_payload(&self) -> serde_json::Value {
        // Interpolation cascade stats (#2450).
        let interp = &self.telemetry.interpolation_stats;
        let interpolation = serde_json::json!({
            "attempts": interp.attempts,
            "golem_sat_successes": interp.golem_sat_successes,
            "n1_per_clause_successes": interp.n1_per_clause_successes,
            "lia_farkas_successes": interp.lia_farkas_successes,
            "syntactic_farkas_successes": interp.syntactic_farkas_successes,
            "iuc_farkas_successes": interp.iuc_farkas_successes,
            "golem_a_unsat_skips": interp.golem_a_unsat_skips,
            "all_failed": interp.all_failed,
        });

        // Entry-inductiveness failure histogram (#4695).
        let entry_failures: serde_json::Map<String, serde_json::Value> = self
            .telemetry
            .entry_inductive_failure_counts
            .iter()
            .map(|(reason, &count)| (reason.to_string(), serde_json::json!(count)))
            .collect();

        // Entry-CEGAR discharge outcome histogram (#4697).
        let [reachable, unreachable, unknown] = self.telemetry.entry_cegar_discharge_outcomes;
        let cegar_discharges = serde_json::json!({
            "reachable": reachable,
            "unreachable": unreachable,
            "unknown": unknown,
        });
        let (symbolic_scalarization_projected_cells, symbolic_scalarization_multi_cell_args) =
            self.symbolic_scalarization_projection_counts();
        let array_scalarization_transform_memory = self.array_scalarization_memory_diagnostic();

        serde_json::json!({
            "interpolation": interpolation,
            "sat_no_cube_events": self.telemetry.sat_no_cube_events,
            "entry_inductive_failures": entry_failures,
            "entry_cegar_discharges": cegar_discharges,
            "symbolic_scalarization_projected_cells": symbolic_scalarization_projected_cells,
            "symbolic_scalarization_multi_cell_args": symbolic_scalarization_multi_cell_args,
            "array_scalarization_transform_memory": array_scalarization_transform_memory,
            "lia_farkas_route": self.lia_farkas_route_telemetry(),
        })
    }

    /// Strictly validate a Safe model before it leaves direct PDR.
    ///
    /// #9227: PDR may use `individually_inductive` / `convergence_proven`
    /// evidence internally while searching, but those flags must not replace
    /// final init + transition + query validation at a public Safe boundary.
    pub(in crate::pdr::solver) fn finish_safe_with_result_trace(
        &mut self,
        model: InvariantModel,
        stage: &'static str,
    ) -> PdrResult {
        let Some(model) = self.try_translate_array_scalarized_model(model) else {
            let memory = self
                .array_scalarization_memory_report()
                .diagnostic_summary();
            tracing::warn!(
                stage,
                transform_memory = %memory,
                "PDR Safe result failed array-scalarized model backtranslation; demoting to Unknown"
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: {stage} Safe result failed array-scalarized model backtranslation; demoting to Unknown; {memory}"
                );
            }
            return self.finish_with_result_trace(PdrResult::Unknown);
        };

        let verified = if self.array_scalarization_maps.is_empty() {
            let previous_strict_proofs = self.config.strict_proofs;
            self.config.strict_proofs = true;
            let verified = self.verify_model_fresh(&model);
            self.config.strict_proofs = previous_strict_proofs;
            verified
        } else {
            let config = crate::pdr::PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                cancellation_token: self.config.cancellation_token.clone(),
                solve_timeout: self.config.solve_timeout,
                disable_array_scalarization: true,
                ..crate::pdr::PdrConfig::default()
            };
            let mut verifier = Self::new(self.model_problem.clone(), config);
            verifier.solve_deadline = self.solve_deadline.or_else(|| {
                verifier
                    .config
                    .solve_timeout
                    .map(|timeout| ay_core::time::Instant::now() + timeout)
            });
            verifier.verify_model_fresh(&model)
        };

        if verified {
            self.finish_with_result_trace(PdrResult::Safe(model))
        } else {
            let memory = self
                .array_scalarization_memory_report()
                .diagnostic_summary();
            tracing::warn!(
                stage,
                transform_memory = %memory,
                "PDR Safe result failed strict final validation; demoting to Unknown"
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: {stage} Safe result failed strict final validation; demoting to Unknown (#9227); {memory}"
                );
            }
            self.finish_with_result_trace(PdrResult::Unknown)
        }
    }

    /// Finish a startup Safe candidate, but treat a strict-validation demotion
    /// as non-terminal.
    ///
    /// #4751: startup "direct safety" claims are optimistic (e.g. the
    /// backward-chain check can accept a model whose query-predicate
    /// interpretation is not inductive). When strict final validation demotes
    /// such a claim to Unknown, the demotion must NOT abort the whole solve:
    /// the frame lemmas discovered so far are sound, and the remaining startup
    /// passes (bound floods, kernel equalities like dillig12_m's D=2C,
    /// derived-predicate propagation) plus the main PDR loop still have the
    /// entire budget available. Returning the demoted Unknown from
    /// `run_fixpoint_discovery` was additionally misread by
    /// `run_startup_discovery` as a cancellation, aborting the solve at ~0.1s
    /// of a 60s budget.
    ///
    /// Returns `Some(result)` when the model survived strict validation (the
    /// caller should return it), and `None` when it was demoted (the caller
    /// should continue discovery).
    pub(in crate::pdr::solver) fn finish_safe_or_continue(
        &mut self,
        model: InvariantModel,
        stage: &'static str,
    ) -> Option<PdrResult> {
        // Non-scalarized candidates can preserve the strict gate's concrete
        // failure for candidate repair. This avoids repeating the expensive
        // failed verification before the first weakening round and leaves the
        // existing deadline for the mandatory repaired-candidate recheck.
        if self.array_scalarization_maps.is_empty() {
            let previous_strict_proofs = self.config.strict_proofs;
            self.config.strict_proofs = true;
            let failure = self.verify_model_fresh_with_failure(&model);
            self.config.strict_proofs = previous_strict_proofs;

            let Some(failure) = failure else {
                return Some(self.finish_with_result_trace(PdrResult::Safe(model)));
            };

            let memory = self
                .array_scalarization_memory_report()
                .diagnostic_summary();
            tracing::warn!(
                stage,
                transform_memory = %memory,
                "PDR Safe result failed strict final validation; demoting to Unknown"
            );
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: {stage} Safe result failed strict final validation; demoting to Unknown (#9227); {memory}"
                );
            }
            let _ = self.finish_with_result_trace(PdrResult::Unknown);
            self.strict_validation_demotions = self.strict_validation_demotions.saturating_add(1);
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: {stage} demoted by strict validation; continuing discovery (#4751)"
                );
            }

            // The returned wrapper is constructible only after the modified
            // model has passed the same fresh-context strict verifier. Publish
            // that already-verified model directly: a third redundant check
            // could lose a completed proof to a cancellation race.
            if let Some(repaired) = self.repair_demoted_candidate_after_failure(model, failure) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: {stage}: repaired demoted candidate passed strict re-verification; finalizing (#4751 L4)"
                    );
                }
                return Some(self.finish_with_result_trace(PdrResult::Safe(repaired.into_model())));
            }
            return None;
        }

        // Array-scalarized models require translation and a verifier over the
        // original problem, so keep their existing fail-closed path.
        match self.finish_safe_with_result_trace(model.clone(), stage) {
            PdrResult::Unknown => {
                self.strict_validation_demotions =
                    self.strict_validation_demotions.saturating_add(1);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: {stage} demoted by strict validation; continuing discovery (#4751)"
                    );
                }
                None
            }
            result => Some(result),
        }
    }

    /// Emit the terminal action for a solver result and flush the trace.
    ///
    /// The terminal step includes a `telemetry` payload with accumulated
    /// interpolation stats, SAT-no-cube counts, and entry-inductiveness
    /// failure reasons for offline Unknown-outcome triage (#4697).
    pub(in crate::pdr::solver) fn finish_with_result_trace(&self, result: PdrResult) -> PdrResult {
        let (result_str, action) = match &result {
            PdrResult::Safe(_) => ("Safe", "DeclareSafe"),
            PdrResult::Unsafe(_) => ("Unsafe", "DeclareUnsafe"),
            PdrResult::Unknown | PdrResult::NotApplicable => ("Unknown", "DeclareUnknown"),
        };
        // Emit terminal step with telemetry payload.
        if let Some(ref writer) = self.tracing.tla_trace {
            let state = self.pdr_trace_snapshot(result_str, None);
            let telemetry = self.build_telemetry_payload();
            writer.write_step_with_telemetry(state, Some(action), Some(telemetry));
        }
        tracing::info!(
            action,
            result = result_str,
            frames = self.frames.len(),
            "PDR solver terminated"
        );
        // Print interpolation telemetry at solve end (#2450)
        if self.config.verbose && self.telemetry.interpolation_stats.attempts > 0 {
            safe_eprintln!(
                "PDR: Interpolation stats: {}",
                self.telemetry.interpolation_stats.summary()
            );
        }
        // Export learned lemmas to the sequential lemma cache (#7919).
        if matches!(result, PdrResult::Unknown) {
            if let Some(ref cache) = self.config.lemma_cache {
                let pool = self.export_lemmas();
                if !pool.is_empty() {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Exported {} lemmas to sequential LemmaCache (#7919)",
                            pool.len()
                        );
                    }
                    cache.merge(&pool);
                }
            }
        }

        self.finish_pdr_tla_trace();
        result
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
