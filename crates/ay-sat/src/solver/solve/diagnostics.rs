// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TLA tracing, diagnostic emission, and solve-time telemetry.
//!
//! All methods here are thin wrappers around the `TlaTraceWriter` and
//! `SatDiagnosticWriter` infrastructure. They are no-ops when the
//! corresponding trace/diagnostic writer is `None`.

use super::super::*;

impl Solver {
    /// Build a TLA2-format state snapshot of the current CDCL state.
    ///
    /// Uses TLA2's `JsonValue` encoding: `{"type":"str","value":"..."}` etc.
    /// Only called when `self.cold.tla_trace` is `Some`.
    fn tla_cdcl_snapshot(&self, state: CdclTraceState) -> serde_json::Value {
        // Build assignment as a TLA2 function: domain is var indices, mapping is TRUE/FALSE/UNDEF
        let assignment_pairs: Vec<serde_json::Value> = (0..self.num_vars)
            .map(|i| {
                let val = match self.var_value_from_vals(i) {
                    Some(true) => "TRUE",
                    Some(false) => "FALSE",
                    None => "UNDEF",
                };
                serde_json::json!([
                    {"type": "int", "value": i},
                    {"type": "string", "value": val}
                ])
            })
            .collect();

        let domain: Vec<serde_json::Value> = (0..self.num_vars)
            .map(|i| serde_json::json!({"type": "int", "value": i}))
            .collect();

        // Build trail as a TLA2 sequence of literal indices
        let trail_elems: Vec<serde_json::Value> = self
            .trail
            .iter()
            .map(|lit| {
                let var_idx = lit.variable().index() as i64;
                let sign = if lit.is_positive() { "pos" } else { "neg" };
                serde_json::json!({"type": "tuple", "value": [
                    {"type": "int", "value": var_idx},
                    {"type": "string", "value": sign}
                ]})
            })
            .collect();

        serde_json::json!({
            "assignment": {
                "type": "function",
                "value": {
                    "domain": domain,
                    "mapping": assignment_pairs
                }
            },
            "trail": {"type": "seq", "value": trail_elems},
            "state": {"type": "string", "value": state.as_str()},
            "decisionLevel": {"type": "int", "value": i64::from(self.decision_level)},
            "learnedClauses": {"type": "int", "value": self.num_conflicts as i64}
        })
    }

    /// Write a TLA trace step if tracing is enabled.
    pub(in crate::solver) fn tla_trace_step(
        &self,
        state: CdclTraceState,
        action: Option<CdclTraceAction>,
    ) {
        if let Some(ref writer) = self.cold.tla_trace {
            let snapshot = self.tla_cdcl_snapshot(state);
            writer.write_step(snapshot, action.map(CdclTraceAction::as_str));
        }
    }

    /// Record final SAT outcome to deterministic trace.
    pub(in crate::solver) fn trace_sat_result(&mut self, result: &SatResult) {
        match result {
            SatResult::Sat(_) => self.trace_result(SolveOutcome::Sat),
            SatResult::Unsat(_) => self.trace_result(SolveOutcome::Unsat),
            SatResult::Unknown => self.trace_result(SolveOutcome::Unknown),
        }
    }

    /// Flush buffered TLA trace output if tracing is enabled.
    /// Also flushes the diagnostic trace if active.
    pub(in crate::solver) fn finish_tla_trace(&mut self) {
        if let Some(ref writer) = self.cold.tla_trace {
            writer.finish();
        }
        self.finish_diagnostic_trace();
        self.finish_decision_trace();
    }

    /// Emit a diagnostic result summary for a SAT result (Wave 4).
    ///
    /// `model_size` is the user-visible model length (after truncation).
    /// No-op when diagnostic tracing is disabled.
    pub(in crate::solver) fn emit_diagnostic_sat_summary(&self, model_size: usize) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_result_summary(serde_json::json!({
                "result": "sat",
                "model_size": model_size,
                "num_original_clauses": self.num_original_clauses,
                "num_clauses": self.num_clauses(),
                "reconstruction_steps": self.inproc.reconstruction.len(),
                "num_conflicts": self.num_conflicts,
                "num_decisions": self.num_decisions,
            }));
        }
    }

    /// Emit a diagnostic result summary for an UNSAT result (Wave 4).
    ///
    /// Reports proof steps, empty-clause status, and enabled passes.
    /// No-op when diagnostic tracing is disabled.
    pub(in crate::solver) fn emit_diagnostic_unsat_summary(&self) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            let proof_steps = self
                .proof_manager
                .as_ref()
                .map_or(0, ProofManager::added_count);
            let enabled_passes = self.collect_enabled_passes();
            writer.emit_result_summary(serde_json::json!({
                "result": "unsat",
                "proof_steps_added": proof_steps,
                "empty_clause_written": self.cold.empty_clause_in_proof,
                "num_original_clauses": self.num_original_clauses,
                "num_conflicts": self.num_conflicts,
                "num_decisions": self.num_decisions,
                "enabled_passes": enabled_passes,
            }));
        }
    }

    /// Emit a diagnostic result summary for an UNKNOWN result.
    ///
    /// Until #4622 lands per-path reason plumbing, callers use
    /// `"unspecified"` as the reason payload.
    pub(in crate::solver) fn emit_diagnostic_unknown_summary(&self, reason: &'static str) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_result_summary(serde_json::json!({
                "result": "unknown",
                "reason": reason,
                "num_original_clauses": self.num_original_clauses,
                "num_conflicts": self.num_conflicts,
                "num_decisions": self.num_decisions,
            }));
        }
    }

    /// Emit a diagnostic restart event (#4172).
    ///
    /// Records the solver's conflict count and trail length at restart time.
    /// Restarts reset the search tree and directly affect clause learning
    /// behavior, making them essential for understanding solve dynamics.
    /// No-op when diagnostic tracing is disabled.
    pub(in crate::solver) fn emit_diagnostic_restart(&self) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_restart(self.num_conflicts, self.trail.len());
        }
    }

    /// Emit a diagnostic event when chronological backtracking is used (#4172).
    ///
    /// Called from `compute_chrono_backtrack_level` when the actual backtrack
    /// level differs from the jump level (i.e., chrono BT was selected over NCB).
    /// No-op when diagnostic tracing is disabled.
    pub(in crate::solver) fn emit_diagnostic_chrono_backtrack(
        &self,
        decision_level: u32,
        jump_level: u32,
        actual_level: u32,
    ) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_chrono_backtrack(decision_level, jump_level, actual_level);
        }
    }

    /// Emit a diagnostic event when stable/focused mode switches (#4674).
    ///
    /// Called from `should_restart` when the solver toggles between stable mode
    /// (VSIDS + reluctant doubling) and focused mode (VMTF + glucose restarts).
    /// No-op when diagnostic tracing is disabled.
    pub(in crate::solver) fn emit_diagnostic_mode_switch(
        &self,
        entering_stable: bool,
        phase_length: u64,
    ) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_mode_switch(entering_stable, self.num_conflicts, phase_length);
        }
    }

    /// Emit a diagnostic event when entering a new incremental scope.
    pub(in crate::solver) fn emit_diagnostic_scope_push(
        &self,
        selector: Variable,
        restored_clause_count: usize,
    ) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_scope_push(
                self.cold.scope_selectors.len(),
                selector.index() as u32,
                restored_clause_count,
                self.num_conflicts,
            );
        }
    }

    /// Emit a diagnostic event when leaving an incremental scope.
    pub(in crate::solver) fn emit_diagnostic_scope_pop(
        &self,
        scope_depth_before: usize,
        selector: Variable,
        retracted_empty_clause: bool,
    ) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.emit_scope_pop(
                scope_depth_before,
                self.cold.scope_selectors.len(),
                selector.index() as u32,
                retracted_empty_clause,
                self.num_conflicts,
            );
        }
    }

    /// Emit the composed assumption batch for one solve call.
    pub(in crate::solver) fn emit_diagnostic_assumption_batch(
        &self,
        assumptions: &[Literal],
        composed_with_scope: bool,
    ) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            let lits: Vec<i64> = assumptions
                .iter()
                .map(|lit| i64::from(lit.to_dimacs()))
                .collect();
            writer.emit_assumption_batch(
                lits.len(),
                &lits,
                composed_with_scope,
                self.num_conflicts,
            );
        }
    }

    /// Emit the terminal result for one assumption solve call.
    pub(in crate::solver) fn emit_diagnostic_assumption_result(&self, result: &AssumeResult) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            match result {
                AssumeResult::Sat(_) => {
                    writer.emit_assumption_result("sat", None, None, self.num_conflicts);
                }
                AssumeResult::Unsat(core, _) => {
                    writer.emit_assumption_result(
                        "unsat",
                        Some(core.len()),
                        None,
                        self.num_conflicts,
                    );
                }
                AssumeResult::Unknown => {
                    let reason = self
                        .last_unknown_reason()
                        .map(SatUnknownReason::diagnostic_label)
                        .unwrap_or(SatUnknownReason::Unspecified.diagnostic_label());
                    writer.emit_assumption_result(
                        "unknown",
                        None,
                        Some(reason),
                        self.num_conflicts,
                    );
                }
            }
        }
    }

    /// Emit a per-inprocessing-round statistics summary (#4674).
    ///
    /// Called at the end of `run_restart_inprocessing` with before/after clause
    /// counts and the list of passes that actually executed in this round.
    /// No-op when diagnostic tracing is disabled.
    pub(in crate::solver) fn emit_diagnostic_inprocessing_round(
        &self,
        clauses_before: usize,
        clauses_after: usize,
        passes_run: &[&str],
        telemetry: &crate::diagnostic_trace::InprocessingRoundTelemetry,
    ) {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            let vars_active = self.num_vars - self.var_lifecycle.count_removed();
            writer.emit_inprocessing_round(
                self.num_conflicts,
                clauses_before,
                clauses_after,
                vars_active,
                passes_run,
                telemetry,
            );
        }
    }

    /// Collect the names of currently enabled inprocessing passes.
    pub(in crate::solver) fn collect_enabled_passes(&self) -> Vec<&'static str> {
        let ctrl = &self.inproc_ctrl;
        let mut passes = Vec::new();
        if ctrl.vivify.enabled {
            passes.push("vivify");
        }
        if ctrl.vivify_irred.enabled {
            passes.push("vivify_irred");
        }
        if ctrl.subsume.enabled {
            passes.push("subsume");
        }
        if ctrl.probe.enabled {
            passes.push("probe");
        }
        if ctrl.bve.enabled {
            passes.push("bve");
        }
        if ctrl.bce.enabled {
            passes.push("bce");
        }
        if ctrl.condition.enabled {
            passes.push("condition");
        }
        if ctrl.decompose.enabled {
            passes.push("decompose");
        }
        if ctrl.factor.enabled {
            passes.push("factor");
        }
        if ctrl.transred.enabled {
            passes.push("transred");
        }
        if ctrl.htr.enabled {
            passes.push("htr");
        }
        if ctrl.gate.enabled {
            passes.push("gate");
        }
        if ctrl.congruence.enabled {
            passes.push("congruence");
        }
        if ctrl.sweep.enabled {
            passes.push("sweep");
        }
        passes
    }
}
