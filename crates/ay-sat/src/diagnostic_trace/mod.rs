// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT diagnostic JSONL writer for clause mutation provenance and result explanation.
//!
//! Emits structured JSONL events that explain *why* each SAT/UNSAT result is correct:
//! clause additions/deletions with pass attribution, variable lifecycle transitions,
//! and post-solve summaries with verification evidence.
//!
//! Activated via `AY_DIAGNOSTIC=1` (or `AY_DIAGNOSTIC_FILE=<path>`).
//! Zero overhead when disabled: the solver stores `Option<SatDiagnosticWriter>`,
//! and all emit methods early-return on `None`.
//!
//! See the development design notes for the
//! full schema and execution plan.

// SAT solvers use domain acronyms (BVE, BCE, HTR) — consistent with crate convention.
#![allow(clippy::upper_case_acronyms)]

use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::Mutex;

/// Per-round BCP and preprocessing telemetry, bundled to avoid parameter bloat.
#[derive(Debug, Clone, Copy, Default)]
pub(crate) struct InprocessingRoundTelemetry {
    /// BCP: blocker-fastpath hits (`blocker_val > 0`).
    pub bcp_blocker_fastpath_hits: u64,
    /// BCP: binary watcher path hits.
    pub bcp_binary_path_hits: u64,
    /// BCP: binary reason chains compressed (jumped reasons, #8034).
    pub jumped_reasons: u64,
    /// BCP: literals examined in replacement scans.
    pub bcp_replacement_scan_steps: u64,
    /// Level-0 preprocess: root-false literals removed.
    pub preprocess_level0_literals_removed: u64,
    /// Level-0 preprocess: satisfied clauses deleted.
    pub preprocess_level0_satisfied_deleted: u64,
}

/// The inprocessing/preprocessing technique that triggered a clause mutation or
/// variable transition. Stored on the solver and read by emit helpers so that
/// individual mutation call-sites don't need to pass a pass argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DiagnosticPass {
    /// No active pass (e.g., during CDCL search).
    None,
    /// Input clause loading.
    Input,
    /// Conflict-driven clause learning.
    Learning,
    /// Bounded variable elimination.
    BVE,
    /// Blocked clause elimination.
    BCE,
    /// Covered clause elimination (ACCE).
    CCE,
    /// Vivification (clause strengthening).
    Vivify,
    /// Subsumption / self-subsumption.
    Subsume,
    /// Failed literal probing.
    Probe,
    /// Backbone literal computation.
    Backbone,
    /// Congruence closure.
    Congruence,
    /// SCC decomposition.
    Decompose,
    /// Hyper-ternary resolution.
    HTR,
    /// Factorization.
    Factor,
    /// Structured BVA (SBVA).
    Sbva,
    /// Conditioning.
    Condition,
    /// Transitive reduction.
    TransRed,
    /// SAT sweeping.
    Sweep,
    /// Clause database reduction.
    Reduce,
    /// Aggressive clause flush (CaDiCaL reduce.cpp flush path).
    Flush,
    /// Variable reorder by clause weight (Kissat reorder.c).
    Reorder,
}

impl DiagnosticPass {
    fn as_str(self) -> &'static str {
        match self {
            Self::None => "none",
            Self::Input => "input",
            Self::Learning => "learning",
            Self::BVE => "bve",
            Self::BCE => "bce",
            Self::CCE => "cce",
            Self::Vivify => "vivify",
            Self::Subsume => "subsume",
            Self::Probe => "probe",
            Self::Backbone => "backbone",
            Self::Congruence => "congruence",
            Self::Decompose => "decompose",
            Self::HTR => "htr",
            Self::Factor => "factor",
            Self::Sbva => "sbva",
            Self::Condition => "condition",
            Self::TransRed => "transred",
            Self::Sweep => "sweep",
            Self::Reduce => "reduce",
            Self::Flush => "flush",
            Self::Reorder => "reorder",
        }
    }
}

/// Kind of clause being added.
#[derive(Debug, Clone, Copy)]
pub(crate) enum ClauseKind {
    /// Original input clause.
    Original,
    /// Learned from conflict analysis.
    Learned,
    /// Theory-propagated clause (from DPLL(T)).
    Theory,
    /// BVE resolvent.
    Resolvent,
    /// Strengthened (replacement) clause.
    Strengthened,
}

impl ClauseKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::Original => "original",
            Self::Learned => "learned",
            Self::Theory => "theory",
            Self::Resolvent => "resolvent",
            Self::Strengthened => "strengthened",
        }
    }
}

/// Reason a clause was deleted.
#[derive(Debug, Clone, Copy)]
pub(crate) enum DeleteReason {
    /// Clause database reduction (LBD-based tier eviction).
    Reduce,
    /// Subsumed by another clause.
    Subsumed,
    /// Eliminated via BVE.
    Eliminated,
    /// Blocked clause elimination.
    Blocked,
    /// Replaced by a strengthened version.
    Replaced,
    /// Other inprocessing technique.
    Inprocessing,
}

impl DeleteReason {
    fn as_str(self) -> &'static str {
        match self {
            Self::Reduce => "reduce",
            Self::Subsumed => "subsumed",
            Self::Eliminated => "eliminated",
            Self::Blocked => "blocked",
            Self::Replaced => "replaced",
            Self::Inprocessing => "inprocessing",
        }
    }
}

/// Variable lifecycle state.
#[derive(Debug, Clone, Copy)]
pub(crate) enum VarState {
    /// Variable is active in the formula.
    Active,
    /// Variable has been eliminated (BVE/BCE).
    Eliminated,
    /// Variable has been substituted (SCC decompose).
    Substituted,
}

impl VarState {
    fn as_str(self) -> &'static str {
        match self {
            Self::Active => "active",
            Self::Eliminated => "eliminated",
            Self::Substituted => "substituted",
        }
    }
}

/// JSONL diagnostic writer for SAT solver events.
///
/// Patterned after [`TlaTraceWriter`](crate::tla_trace::TlaTraceWriter):
/// `Mutex<BufWriter<File>>`, append-only, flush on finish.
pub(crate) struct SatDiagnosticWriter {
    inner: Mutex<DiagnosticInner>,
}

struct DiagnosticInner {
    writer: BufWriter<File>,
    event_count: u64,
    /// Latched on the first write failure; further writes are skipped so a
    /// transient I/O error (disk full, broken pipe) degrades diagnostics
    /// instead of aborting the solve.
    io_failed: bool,
}

impl SatDiagnosticWriter {
    /// Create a new diagnostic writer. Writes the JSONL header immediately.
    ///
    /// Returns an I/O error if the file cannot be created or the header
    /// cannot be written (bad path, permissions, disk full, etc.).
    pub(crate) fn new(path: &str) -> std::io::Result<Self> {
        let file = File::create(path)?;
        let mut writer = BufWriter::new(file);

        let is_debug = cfg!(debug_assertions);
        let header = serde_json::json!({
            "type": "header",
            "version": "1",
            "tool": "ay-sat-diagnostic",
            "pid": std::process::id(),
            "build": if is_debug { "debug" } else { "release" },
        });
        writeln!(writer, "{header}")?;
        writer.flush()?;

        Ok(Self {
            inner: Mutex::new(DiagnosticInner {
                writer,
                event_count: 0,
                io_failed: false,
            }),
        })
    }

    /// Emit a clause addition event.
    pub(crate) fn emit_clause_add(
        &self,
        clause_id: u64,
        lits: &[i64],
        pass: DiagnosticPass,
        kind: ClauseKind,
        parents: &[u64],
    ) {
        let event = serde_json::json!({
            "type": "clause_add",
            "clause_id": clause_id,
            "lits": lits,
            "pass": pass.as_str(),
            "kind": kind.as_str(),
            "parents": parents,
        });
        self.write_event(&event);
    }

    /// Emit a clause deletion event.
    pub(crate) fn emit_clause_delete(
        &self,
        clause_id: u64,
        pass: DiagnosticPass,
        reason: DeleteReason,
    ) {
        let event = serde_json::json!({
            "type": "clause_delete",
            "clause_id": clause_id,
            "pass": pass.as_str(),
            "reason_policy": reason.as_str(),
        });
        self.write_event(&event);
    }

    /// Emit a clause replacement event.
    pub(crate) fn emit_clause_replace(
        &self,
        old_clause_id: u64,
        new_lits: &[i64],
        pass: DiagnosticPass,
    ) {
        let event = serde_json::json!({
            "type": "clause_replace",
            "old_clause_id": old_clause_id,
            "new_lits": new_lits,
            "pass": pass.as_str(),
            "parents": [old_clause_id],
        });
        self.write_event(&event);
    }

    /// Emit a variable state transition event.
    pub(crate) fn emit_var_transition(
        &self,
        var: u32,
        from: VarState,
        to: VarState,
        pass: DiagnosticPass,
    ) {
        let event = serde_json::json!({
            "type": "var_transition",
            "var": var,
            "from": from.as_str(),
            "to": to.as_str(),
            "pass": pass.as_str(),
        });
        self.write_event(&event);
    }

    /// Emit a restart event.
    ///
    /// Records that the solver restarted at this point, including the trail
    /// depth (number of assigned variables) and conflict count at restart time.
    /// Restarts are critical solver events that affect clause learning and
    /// search behavior — invisible restarts make CDCL traces hard to interpret.
    pub(crate) fn emit_restart(&self, num_conflicts: u64, trail_len: usize) {
        let event = serde_json::json!({
            "type": "restart",
            "num_conflicts": num_conflicts,
            "trail_len": trail_len,
        });
        self.write_event(&event);
    }

    /// Emit a chronological backtracking decision event.
    ///
    /// Records when the solver chooses chronological backtracking over standard
    /// non-chronological backtracking. The `jump_level` is the asserting level
    /// from conflict analysis; `actual_level` is the level the solver actually
    /// backtracks to. When `actual_level > jump_level`, chrono BT was used.
    pub(crate) fn emit_chrono_backtrack(
        &self,
        decision_level: u32,
        jump_level: u32,
        actual_level: u32,
    ) {
        let event = serde_json::json!({
            "type": "chrono_backtrack",
            "decision_level": decision_level,
            "jump_level": jump_level,
            "actual_level": actual_level,
        });
        self.write_event(&event);
    }

    /// Emit a stable/focused mode switch event.
    ///
    /// Records when the solver switches between stable mode (VSIDS + reluctant
    /// doubling restarts) and focused mode (VMTF + glucose restarts). The
    /// `entering_stable` flag indicates the new mode; `num_conflicts` is the
    /// conflict count at the switch point.
    pub(crate) fn emit_mode_switch(
        &self,
        entering_stable: bool,
        num_conflicts: u64,
        phase_length: u64,
    ) {
        let event = serde_json::json!({
            "type": "mode_switch",
            "mode": if entering_stable { "stable" } else { "focused" },
            "num_conflicts": num_conflicts,
            "phase_length": phase_length,
        });
        self.write_event(&event);
    }

    /// Emit a per-inprocessing-round statistics summary.
    ///
    /// Records the net effect of one inprocessing round: how many clauses were
    /// added/deleted and how many variables remain. Paired with restart/mode
    /// events, this makes the solver's simplification trajectory visible.
    pub(crate) fn emit_inprocessing_round(
        &self,
        num_conflicts: u64,
        clauses_before: usize,
        clauses_after: usize,
        vars_active: usize,
        passes_run: &[&str],
        telemetry: &InprocessingRoundTelemetry,
    ) {
        let event = serde_json::json!({
            "type": "inprocessing_round",
            "num_conflicts": num_conflicts,
            "clauses_before": clauses_before,
            "clauses_after": clauses_after,
            "clause_delta": clauses_after as i64 - clauses_before as i64,
            "vars_active": vars_active,
            "passes": passes_run,
            "bcp_blocker_fastpath_hits": telemetry.bcp_blocker_fastpath_hits,
            "bcp_binary_path_hits": telemetry.bcp_binary_path_hits,
            "jumped_reasons": telemetry.jumped_reasons,
            "bcp_replacement_scan_steps": telemetry.bcp_replacement_scan_steps,
            "preprocess_level0_literals_removed": telemetry.preprocess_level0_literals_removed,
            "preprocess_level0_satisfied_deleted": telemetry.preprocess_level0_satisfied_deleted,
        });
        self.write_event(&event);
    }

    /// Emit a post-solve result summary.
    pub(crate) fn emit_result_summary(&self, summary: serde_json::Value) {
        let mut event = summary;
        event["type"] = serde_json::json!("result_summary");
        self.write_event(&event);
    }

    /// Flush buffered output and return the number of events written.
    pub(crate) fn finish(&self) -> u64 {
        let mut inner = self.inner.lock().expect("diagnostic writer mutex poisoned");
        let _ = inner.writer.flush();
        inner.event_count
    }

    fn write_event(&self, event: &serde_json::Value) {
        let mut inner = self.inner.lock().expect("diagnostic writer mutex poisoned");
        if inner.io_failed {
            return;
        }
        if writeln!(inner.writer, "{event}").is_err() {
            inner.io_failed = true;
            eprintln!("warning: SAT diagnostic trace write failed; disabling diagnostic output");
            return;
        }
        inner.event_count += 1;
        // Flush periodically to avoid data loss on crash
        if inner.event_count.is_multiple_of(256) && inner.writer.flush().is_err() {
            inner.io_failed = true;
            eprintln!("warning: SAT diagnostic trace flush failed; disabling diagnostic output");
        }
    }
}

/// Check environment variables and return the diagnostic file path if enabled.
///
/// Activation rules:
/// - `AY_DIAGNOSTIC_FILE=<path>` → use that path
/// - `AY_DIAGNOSTIC=1` → use `<tmp>/ay_sat_diagnostic_<pid>.jsonl`
/// - Neither set → `None` (disabled)
pub(crate) fn diagnostic_path_from_env() -> Option<String> {
    // Delegates to ay-core's centralized TraceConfig (#8495).
    ay_core::trace_config().diagnostic_path.clone()
}

mod incremental;

#[cfg(test)]
mod tests;
