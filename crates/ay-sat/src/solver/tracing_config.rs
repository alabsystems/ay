// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver tracing, diagnostics, and configuration methods.
//!
//! Includes: logging (fmt_lit), forward checker config, LRAT/clause-trace
//! config, diagnostic/decision/replay trace config, and diagnostic pass
//! management.

use super::*;

include!("solution_witness.rs");

impl Solver {
    /// Format a literal with CaDiCaL-style rich display: `42@3+=1`.
    ///
    /// Format: `<dimacs_lit>@<level><reason><value>`
    /// - level: decision level of the variable
    /// - reason: `+` for decisions, empty for propagated
    /// - value: `1`/`0` for assigned, `?` for unassigned
    ///
    /// Only compiled when `ay_logging` is active (#4293).
    #[cfg(ay_logging)]
    pub(crate) fn fmt_lit(&self, lit: Literal) -> String {
        let var = lit.variable();
        let idx = var.index();
        let level = if idx < self.var_data.len() {
            self.var_data[idx].level
        } else {
            0
        };
        let val = if idx < self.num_vars {
            match self.var_value_from_vals(idx) {
                Some(true) => {
                    if lit.is_positive() {
                        "1"
                    } else {
                        "0"
                    }
                }
                Some(false) => {
                    if lit.is_positive() {
                        "0"
                    } else {
                        "1"
                    }
                }
                None => "?",
            }
        } else {
            "?"
        };
        let reason = if idx < self.var_data.len()
            && self.var_data[idx].reason == NO_REASON
            && self.var_is_assigned(idx)
        {
            "+"
        } else {
            ""
        };
        format!("{}@{}{}{}", lit.to_dimacs(), level, reason, val)
    }

    /// Enable online forward DRUP checking (CaDiCaL `--check --checkproof`).
    ///
    /// When enabled, every derived clause is verified via reverse unit
    /// propagation (RUP) at derivation time. If a learned clause is not
    /// implied by existing clauses, the solver panics immediately.
    ///
    /// Overhead: ~3x slowdown. Call before adding any clauses.
    pub fn enable_forward_checker(&mut self) {
        self.cold.forward_checker =
            Some(crate::forward_checker::ForwardChecker::new(self.num_vars));
    }

    /// Enable sampled forward DRUP checking (#5625).
    ///
    /// Only every `sample_period`th derived clause undergoes full RUP
    /// verification. Non-sampled clauses are added to the checker DB as
    /// trusted (no BCP cost) to maintain state consistency.
    ///
    /// A `sample_period` of 10 checks ~10% of clauses (~1.24x overhead).
    /// Systematic bugs (affecting most derived clauses) are caught with
    /// >99.99% probability over a typical solve.
    pub fn enable_forward_checker_sampled(&mut self, sample_period: u64) {
        self.cold.forward_checker = Some(crate::forward_checker::ForwardChecker::new_sampled(
            self.num_vars,
            sample_period,
        ));
    }

    /// Set the deterministic search-time proof bookkeeping work budget
    /// (#A2b construction budget; `None` = unbudgeted).
    ///
    /// Only set for SYNTHESIZED-DEFAULT certificates: explicit `--proof`,
    /// `--strict-proofs`, `--self-check`, and `:produce-proofs` runs stay
    /// eager and unbudgeted. On exhaustion, level-0 LRAT unit
    /// materialization becomes a no-op and the clause trace is marked
    /// `proof_work_exhausted`, so downstream reconstruction fails closed
    /// (verdict kept, honest "no proof certificate emitted" warning).
    pub fn set_proof_bookkeeping_budget(&mut self, budget: Option<u64>) {
        self.cold.proof_bookkeeping_budget = budget;
    }

    /// Enable LRAT proof support (track clause IDs and resolution chains)
    ///
    /// # Panics
    ///
    /// Panics if called after clauses have been added. Late enabling creates
    /// unstable clause IDs because existing clauses have no LRAT IDs while
    /// new clauses start allocation from 1, causing ID collisions.
    pub fn enable_lrat(&mut self) {
        assert!(
            self.arena.is_empty(),
            "BUG: enable_lrat() called after {} clauses were added — \
             must be called before adding any clauses",
            self.arena.num_clauses(),
        );
        self.cold.lrat_enabled = true;
        self.cold.lrat_level0_unit_materialize_cursor = 0;
        self.cold.lrat_level0_unit_materialize_pinned.clear();
        self.enforce_inprocessing_proof_overrides();
        // unit_proof_id, level0_proof_id, and clause_ids are now allocated
        // unconditionally at construction (#8069: Phase 2a). No resizing needed.
    }

    /// Enable in-memory clause trace for SMT proof reconstruction
    ///
    /// This records all clause additions (original and learned) in memory
    /// for consumption by the SMT layer's `SatProofManager`. Unlike LRAT,
    /// this does not write to an external file and is designed for Alethe
    /// `resolution` proof reconstruction.
    ///
    /// # Panics
    ///
    /// Panics if called after clauses have been added. Late enabling creates
    /// unstable clause IDs because existing clauses have no LRAT IDs while
    /// new clauses start allocation from 1, causing ID collisions.
    pub fn enable_clause_trace(&mut self) {
        assert!(
            self.arena.is_empty(),
            "BUG: enable_clause_trace() called after {} clauses were added — \
             must be called before adding any clauses",
            self.arena.num_clauses(),
        );
        // Enable LRAT mode for clause ID tracking
        self.cold.lrat_enabled = true;
        self.enforce_inprocessing_proof_overrides();
        // unit_proof_id, level0_proof_id, and clause_ids are now allocated
        // unconditionally at construction (#8069: Phase 2a). No resizing needed.
        // Allocate clause trace
        let capacity = self.num_vars.saturating_mul(4).min(100_000);
        self.cold.clause_trace = Some(ClauseTrace::with_capacity(capacity));
    }

    /// Enable or disable UNSAT proof-certificate construction.
    ///
    /// Backward LRAT reconstruction runs on every UNSAT result to build the
    /// `ProofCertificate` returned in `SatResult::Unsat` /
    /// `AssumeResult::Unsat`. Internal queries that enable clause tracing
    /// (for clause-ID tracking and #5384 UNSAT replay verification) but never
    /// consume the certificate can disable it to skip the full-arena backward
    /// reconstruction pass.
    ///
    /// When disabled, consumers of these solvers get
    /// `ProofCertificate::empty()` in UNSAT results (and `None` certificate
    /// from `solve_with_assumptions`). The in-memory `ClauseTrace` and LRAT
    /// clause-ID tracking are unaffected.
    ///
    /// Defaults to enabled.
    pub fn set_unsat_certificate_enabled(&mut self, enabled: bool) {
        self.cold.unsat_certificate_enabled = enabled;
    }

    /// Disable encoding-dump, Fmla authority/artifact, solver-start JIT hooks,
    /// and startup walk, and do not retain a second copy of emitted backward
    /// LRAT steps in the result.
    ///
    /// Startup walk is only a phase-selection heuristic. On tiny proof-routed
    /// formulas its fixed work can dominate the complete CDCL search; periodic
    /// rephase walk remains enabled and available to longer solves.
    ///
    /// This is crate-internal because ordinary solver callers retain the
    /// historical artifact and certificate behavior.
    pub(crate) fn set_bounded_in_memory_proof_posture(&mut self) {
        self.cold.ambient_artifacts_enabled = false;
        self.cold.retain_unsat_certificate = false;
        // Solver-start native/JIT installation is process-global and may
        // compile or load artifacts selected by the ambient environment.
        self.cold.jit_disabled = true;
        self.set_startup_walk_enabled(false);
    }

    /// Check if clause trace is enabled
    pub fn clause_trace_enabled(&self) -> bool {
        self.cold.clause_trace.is_some()
    }

    /// Highest clause ID ever issued to an original (non-derived) clause.
    ///
    /// This is an ID high-water mark, not a count: derived IDs may occupy
    /// holes below it, and tautological originals may consume IDs without a
    /// retained trace row. Proof-annotation ledgers use this value to preserve
    /// their `clause_id - 1` indexing across both kinds of hole.
    #[must_use]
    pub fn issued_original_clause_id_max(&self) -> u64 {
        self.cold.issued_original_clause_id_max
    }

    /// Whether `id` was actually issued to an original (non-derived) clause.
    ///
    /// Range membership alone is insufficient because late original clauses
    /// share the monotonic namespace with derived clauses.
    #[must_use]
    pub fn is_issued_original_clause_id(&self, id: u64) -> bool {
        self.is_original_clause_id(id)
    }

    /// Take the clause trace, consuming it from the solver
    ///
    /// Returns `None` if clause trace was not enabled.
    pub fn take_clause_trace(&mut self) -> Option<ClauseTrace> {
        let solver_num_vars = self.total_num_vars();
        let scope_assumptions = self.active_scope_assumptions();
        let mut trace = self.cold.clause_trace.take();
        if let Some(t) = trace.as_mut() {
            t.stamp_solver_provenance(solver_num_vars, &scope_assumptions);
            // #A2b observability: the two search-time proof bookkeeping
            // meters (trace bytes recorded, root-trail entries rescanned by
            // level-0 LRAT materialization) that calibrate the construction
            // work budget.
            tracing::debug!(
                trace_used_bytes = t.used_bytes(),
                trace_entries = t.len(),
                materialize_root_trail_entries =
                    self.stats.lrat_materialize_root_trail_entries
                        + self.stats.lrat_materialize_minimize_root_trail_entries,
                budget_remaining = ?self.cold.proof_bookkeeping_budget,
                "clause trace taken (#A2b bookkeeping meters)"
            );
        }
        trace
    }

    /// Clone the clause trace and bind the snapshot to this solver's exact
    /// variable namespace.
    ///
    /// Unlike [`Self::clause_trace`], the returned value is an immutable proof
    /// candidate with bundled namespace provenance. Mutating its proof content
    /// through a public [`ClauseTrace`] mutator clears that provenance.
    pub fn snapshot_clause_trace(&self) -> Option<ClauseTrace> {
        let mut trace = self.cold.clause_trace.clone()?;
        trace.stamp_solver_provenance(self.total_num_vars(), &self.active_scope_assumptions());
        Some(trace)
    }

    /// Get a reference to the clause trace
    pub fn clause_trace(&self) -> Option<&ClauseTrace> {
        self.cold.clause_trace.as_ref()
    }

    /// Return the structured Extended Resolution extension-variable proof log.
    #[must_use]
    pub fn er_extension_proof_log(&self) -> &crate::er_proof::ErProofLog {
        &self.cold.er_proof_log
    }

    /// Number of extension-variable definitions recorded for ER replay.
    #[must_use]
    pub fn er_extension_definition_count(&self) -> usize {
        self.cold.er_proof_log.len()
    }

    /// Emit the ER extension-variable proof log as a Lean-style replay artifact.
    ///
    /// This writer is side-effect free and does not alter the SAT proof stream.
    /// It emits definition clauses, derived replacement clauses, source clause
    /// IDs, and replay obligations; heuristic candidate-selection details are
    /// intentionally omitted from the artifact.
    pub fn write_er_extension_log_proof_replay(
        &self,
        writer: &mut dyn Write,
    ) -> std::io::Result<()> {
        self.cold.er_proof_log.write_proof_replay(writer)
    }

    /// Get the clause ID for a given clause reference
    ///
    /// Returns 0 if the clause doesn't have an assigned ID.
    #[inline]
    pub fn clause_id(&self, clause_ref: ClauseRef) -> u64 {
        let idx = clause_ref.0 as usize;
        if idx < self.cold.clause_ids.len() {
            self.cold.clause_ids[idx]
        } else {
            0
        }
    }

    /// Enable SAT diagnostic tracing to the given file path.
    ///
    /// Creates the diagnostic writer and writes the JSONL header immediately.
    /// Can be called at any point before solving; events emitted before this
    /// call are lost.
    ///
    /// Returns an I/O error if the file cannot be created or the header
    /// cannot be written.
    pub fn enable_diagnostic_trace(&mut self, path: &str) -> std::io::Result<()> {
        self.cold.diagnostic_trace = Some(SatDiagnosticWriter::new(path)?);
        Ok(())
    }

    /// Enable SAT diagnostic tracing from environment variables.
    ///
    /// Checks `AY_DIAGNOSTIC_FILE` and `AY_DIAGNOSTIC` env vars.
    /// No-op if neither is set. Logs a warning and continues if
    /// the diagnostic file cannot be created.
    pub fn maybe_enable_diagnostic_trace_from_env(&mut self) {
        if let Some(path) = crate::diagnostic_trace::diagnostic_path_from_env() {
            if let Err(e) = self.enable_diagnostic_trace(&path) {
                eprintln!("warning: failed to enable SAT diagnostic trace to {path}: {e}");
            }
        }
    }

    /// Enable deterministic SAT decision tracing to a binary file.
    ///
    /// # Errors
    ///
    /// Returns an I/O error if the trace file cannot be created.
    pub fn enable_decision_trace(&mut self, path: &str) -> std::io::Result<()> {
        self.cold.decision_trace = Some(DecisionTraceWriter::new(path)?);
        Ok(())
    }

    /// Close and detach the active decision-trace writer, if any.
    ///
    /// Call this before deleting or replacing the trace path. Merely opening
    /// the path again is unsafe while the old buffered file descriptor remains
    /// live: later events could append at its stale offset and corrupt or
    /// re-expose a result that the public boundary rejected.
    pub fn disable_decision_trace(&mut self) -> bool {
        self.cold.decision_trace.take().is_some()
    }

    /// Enable deterministic SAT decision tracing from `AY_DECISION_TRACE_FILE`.
    ///
    /// No-op if the env var is not set. A configured trace is an explicit
    /// artifact contract, so initialization failure terminates before the SAT
    /// solver can publish a verdict.
    pub fn maybe_enable_decision_trace_from_env(&mut self) {
        if let Some(path) = decision_trace::decision_trace_path_from_env() {
            if let Err(e) = self.enable_decision_trace(&path) {
                eprintln!("Error: failed to initialize SAT decision trace {path}: {e}");
                std::process::exit(1);
            }
        }
    }

    /// Enable deterministic replay checking from a binary trace file.
    ///
    /// The solver still executes normally, but every replay-relevant event is
    /// matched against the expected stream and divergence panics immediately.
    ///
    /// # Errors
    ///
    /// Returns an I/O error if the replay trace file cannot be loaded.
    pub fn enable_replay_trace(&mut self, path: &str) -> std::io::Result<()> {
        self.cold.replay_trace = Some(ReplayTrace::from_file(path)?);
        Ok(())
    }

    /// Enable deterministic replay checking from `AY_REPLAY_TRACE_FILE`.
    ///
    /// No-op if the env var is not set. Logs a warning and continues if the
    /// replay trace file cannot be loaded.
    pub fn maybe_enable_replay_trace_from_env(&mut self) {
        if let Some(path) = decision_trace::replay_trace_path_from_env() {
            if let Err(e) = self.enable_replay_trace(&path) {
                eprintln!("warning: failed to enable SAT replay trace from {path}: {e}");
            }
        }
    }

    /// Returns `true` if diagnostic tracing is active (used in tests).
    #[inline]
    #[cfg(test)]
    pub(super) fn diagnostic_enabled(&self) -> bool {
        self.cold.diagnostic_trace.is_some()
    }

    /// Set the current diagnostic pass (technique attribution context).
    #[inline]
    pub(super) fn set_diagnostic_pass(&mut self, pass: DiagnosticPass) {
        self.cold.diagnostic_pass = pass;
        if pass != DiagnosticPass::None {
            self.trace_event(TraceEvent::Inprocess {
                pass_code: Self::diagnostic_pass_code(pass),
            });
        }
    }

    /// Clear the diagnostic pass back to `None`.
    #[inline]
    pub(super) fn clear_diagnostic_pass(&mut self) {
        self.cold.diagnostic_pass = DiagnosticPass::None;
    }

    /// Flush the diagnostic trace and return the event count.
    /// No-op if diagnostics are disabled.
    pub(super) fn finish_diagnostic_trace(&mut self) -> u64 {
        if let Some(ref writer) = self.cold.diagnostic_trace {
            writer.finish()
        } else {
            0
        }
    }

    /// Emit an event to trace writer and/or replay checker.
    #[inline]
    pub(super) fn trace_event(&mut self, event: TraceEvent) {
        if let Some(ref mut replay) = self.cold.replay_trace {
            if let Err(mismatch) = replay.expect(&event) {
                panic!("{}", mismatch.describe());
            }
        }
        if let Some(writer) = self.cold.decision_trace.as_mut() {
            writer
                .write_event(&event)
                .expect("failed to write decision trace event");
        }
    }

    #[inline]
    pub(super) fn trace_decide(&mut self, lit: Literal) {
        self.trace_event(TraceEvent::Decide {
            lit_dimacs: lit.to_dimacs(),
        });
    }

    // trace_propagate removed: propagation is deterministic (same decisions +
    // clause set → same propagations), so recording it wastes ~10x the trace
    // bytes for no replay benefit. The Propagate variant remains in the binary
    // format for backward-compatible reading of old traces.

    #[inline]
    pub(super) fn trace_conflict(&mut self, clause_id: u64) {
        self.trace_event(TraceEvent::Conflict { clause_id });
    }

    #[inline]
    pub(super) fn trace_learn(&mut self, clause_id: u64) {
        self.trace_event(TraceEvent::Learn { clause_id });
    }

    #[inline]
    pub(super) fn trace_restart(&mut self) {
        self.trace_event(TraceEvent::Restart);
    }

    #[inline]
    pub(super) fn trace_reduce(&mut self, clause_ids: Vec<u64>) {
        self.trace_event(TraceEvent::Reduce { clause_ids });
    }

    #[inline]
    pub(super) fn trace_result(&mut self, outcome: SolveOutcome) {
        self.trace_event(TraceEvent::Result { outcome });
    }

    #[inline]
    fn diagnostic_pass_code(pass: DiagnosticPass) -> u8 {
        match pass {
            DiagnosticPass::None => 0,
            DiagnosticPass::Input => 1,
            DiagnosticPass::Learning => 2,
            DiagnosticPass::BVE => 3,
            DiagnosticPass::BCE => 4,
            DiagnosticPass::Vivify => 5,
            DiagnosticPass::Subsume => 6,
            DiagnosticPass::Probe => 7,
            DiagnosticPass::Backbone => 8,
            DiagnosticPass::Congruence => 9,
            DiagnosticPass::Decompose => 10,
            DiagnosticPass::HTR => 11,
            DiagnosticPass::Factor => 12,
            DiagnosticPass::Sbva => 20,
            DiagnosticPass::Condition => 13,
            DiagnosticPass::TransRed => 14,
            DiagnosticPass::Sweep => 15,
            DiagnosticPass::Reduce => 16,
            DiagnosticPass::Flush => 17,
            DiagnosticPass::CCE => 18,
            DiagnosticPass::Reorder => 19,
        }
    }

    /// Flush deterministic trace outputs and enforce replay completeness.
    pub(super) fn finish_decision_trace(&mut self) {
        if let Some(writer) = self.cold.decision_trace.as_mut() {
            writer
                .finish()
                .expect("failed to flush deterministic decision trace");
        }
        if let Some(ref replay) = self.cold.replay_trace {
            if let Err(mismatch) = replay.finish() {
                panic!("{}", mismatch.describe());
            }
        }
    }
}

#[cfg(test)]
mod bounded_posture_tests {
    use super::*;

    #[test]
    fn bounded_in_memory_posture_disables_ambient_hooks_and_retention() {
        let mut solver = Solver::new(1);
        solver.set_bounded_in_memory_proof_posture();
        assert!(!solver.cold.ambient_artifacts_enabled);
        assert!(!solver.cold.retain_unsat_certificate);
        assert!(solver.cold.jit_disabled);
    }
}
