// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) diagnostic and TLA+ tracing methods.
//!
//! Extracted from `lib.rs` — pure observability `impl` block on [`DpllT`].
//! These methods read solver state and emit to trace writers; they do not
//! modify solver logic or search state.

use std::time::Duration;

use ay_core::TheorySolver;
use ay_sat::{TlaTraceWriter, TlaTraceable};

use crate::diagnostic_trace::{duration_to_micros, DpllDiagnosticWriter};
use crate::DpllT;

/// TLA+ trace module name for DPLL(T) round-trip traces.
pub(crate) const DPLL_TRACE_MODULE: &str = "dpll_t_test";

/// TLA+ variable names emitted in DPLL(T) trace snapshots.
pub(crate) const DPLL_TRACE_VARIABLES: [&str; 7] = [
    "round",
    "satResult",
    "theoryResult",
    "satConflicts",
    "satDecisions",
    "theoryConflicts",
    "theoryPropagations",
];

#[inline]
pub(crate) fn u64_to_i64(value: u64) -> i64 {
    i64::try_from(value).unwrap_or(i64::MAX)
}

impl<T: TheorySolver> DpllT<'_, T> {
    /// Enable TLA2 trace emission on the internal SAT solver from `AY_TRACE_FILE`.
    pub fn maybe_enable_tla_trace_from_env(&mut self) {
        self.sat.maybe_enable_tla_trace_from_env();
        self.maybe_enable_dpll_tla_trace_from_env();
    }

    /// Enable SAT diagnostic trace from `AY_DIAGNOSTIC`/`AY_DIAGNOSTIC_FILE` env vars.
    pub fn maybe_enable_diagnostic_trace_from_env(&mut self) {
        self.sat.maybe_enable_diagnostic_trace_from_env();
    }

    /// Enable DPLL(T) diagnostic trace from env vars.
    ///
    /// Activation:
    /// - `AY_DPLL_DIAGNOSTIC_FILE=<path>`
    /// - `AY_DPLL_DIAGNOSTIC=1` (auto temp path)
    pub fn maybe_enable_dpll_diagnostic_trace_from_env(&mut self) {
        let Some(path) = crate::diagnostic_trace::diagnostic_path_from_env() else {
            return;
        };

        if let Err(err) = self.enable_dpll_diagnostic_trace(&path) {
            tracing::warn!(
                error = %err,
                path = %path,
                "failed to enable DPLL diagnostic trace"
            );
        }
    }

    /// Enable DPLL(T) diagnostic trace on an explicit path.
    pub fn enable_dpll_diagnostic_trace(&mut self, path: &str) -> std::io::Result<()> {
        self.diagnostic_trace = Some(DpllDiagnosticWriter::new(path, std::any::type_name::<T>())?);
        Ok(())
    }

    /// Enable DPLL(T) TLA2 trace from `AY_DPLL_TRACE_FILE`.
    pub fn maybe_enable_dpll_tla_trace_from_env(&mut self) {
        let Some(path) = crate::theory_debug_flags::dpll_trace_file_path() else {
            return;
        };
        self.enable_dpll_tla_trace(&path, DPLL_TRACE_MODULE, &DPLL_TRACE_VARIABLES);
    }

    /// Enable DPLL(T) TLA2 trace writer.
    pub fn enable_dpll_tla_trace(&mut self, path: &str, module: &str, variables: &[&str]) {
        self.dpll_tla_trace = Some(TlaTraceWriter::new(path, module, variables));
        self.dpll_tla_step(0, "init", "init", None);
    }

    /// Enable SAT deterministic trace recording from `AY_DECISION_TRACE_FILE`.
    pub fn maybe_enable_decision_trace_from_env(&mut self) {
        self.sat.maybe_enable_decision_trace_from_env();
    }

    /// Enable SAT deterministic replay checking from `AY_REPLAY_TRACE_FILE`.
    pub fn maybe_enable_replay_trace_from_env(&mut self) {
        self.sat.maybe_enable_replay_trace_from_env();
    }

    /// Load a solution witness from `AY_SOLUTION_FILE` for Sam Buss trick debugging.
    pub fn maybe_load_solution_from_env(&mut self) {
        self.sat.maybe_load_solution_from_env();
    }

    #[allow(clippy::cast_possible_truncation, clippy::cast_sign_loss)]
    pub(crate) fn dpll_tla_snapshot(
        &self,
        round: u64,
        sat_result: &str,
        theory_result: &str,
    ) -> serde_json::Value {
        serde_json::json!({
            "round": {"type": "int", "value": u64_to_i64(round)},
            "satResult": {"type": "string", "value": sat_result},
            "theoryResult": {"type": "string", "value": theory_result},
            "satConflicts": {"type": "int", "value": u64_to_i64(self.sat.num_conflicts())},
            "satDecisions": {"type": "int", "value": u64_to_i64(self.sat.num_decisions())},
            "theoryConflicts": {"type": "int", "value": u64_to_i64(self.theory_conflict_count)},
            "theoryPropagations": {"type": "int", "value": u64_to_i64(self.theory_propagation_count)},
        })
    }

    pub(crate) fn dpll_tla_step(
        &self,
        round: u64,
        sat_result: &str,
        theory_result: &str,
        action: Option<&str>,
    ) {
        if let Some(ref writer) = self.dpll_tla_trace {
            writer.write_step(
                self.dpll_tla_snapshot(round, sat_result, theory_result),
                action,
            );
        }
    }

    pub(crate) fn finish_dpll_tla_trace(&mut self) {
        if let Some(ref writer) = self.dpll_tla_trace {
            let _ = writer.finish();
        }
    }

    pub(crate) fn emit_theory_check_event(
        &self,
        phase: &str,
        result: &str,
        count: Option<usize>,
        conflict_size: Option<usize>,
        duration: Option<Duration>,
    ) {
        if let Some(ref diag) = self.diagnostic_trace {
            diag.emit_theory_check(
                phase,
                result,
                count,
                conflict_size,
                duration.map_or(0, duration_to_micros),
            );
        }
    }

    pub(crate) fn emit_theory_split_event(&self, kind: &str, round: u64) {
        if let Some(ref diag) = self.diagnostic_trace {
            diag.emit_theory_split(kind, round);
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn emit_dpll_round_event(
        &self,
        round: u64,
        sat_result: &str,
        sat_duration: Duration,
        sync_duration: Duration,
        check_result: &str,
        check_duration: Duration,
        propagations_added: usize,
        conflict_size: usize,
        action: Option<&str>,
    ) {
        if let Some(ref diag) = self.diagnostic_trace {
            diag.emit_dpll_round(
                round,
                sat_result,
                duration_to_micros(sat_duration),
                duration_to_micros(sync_duration),
                check_result,
                duration_to_micros(check_duration),
                propagations_added,
                conflict_size,
                self.sat.num_conflicts(),
                self.sat.num_decisions(),
            );
        }
        self.dpll_tla_step(round, sat_result, check_result, action);
    }

    pub(crate) fn emit_solve_summary_event(&self, result: &str) {
        if let Some(ref diag) = self.diagnostic_trace {
            diag.emit_solve_summary(
                result,
                self.timings.round_trips,
                duration_to_micros(self.timings.sat_solve),
                duration_to_micros(self.timings.theory_sync),
                duration_to_micros(self.timings.theory_check),
                self.theory_conflict_count,
                self.theory_propagation_count,
                self.sat.num_conflicts(),
                self.sat.num_decisions(),
            );
            let _ = diag.finish();
        }
    }
}
