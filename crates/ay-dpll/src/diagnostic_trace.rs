// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DPLL(T) diagnostic JSONL writer for theory-SAT interaction visibility.
//!
//! Activated via `AY_DPLL_DIAGNOSTIC=1` or `AY_DPLL_DIAGNOSTIC_FILE=<path>`.
//! This complements SAT diagnostic logging by making the DPLL(T) round-trip
//! and theory interaction surface observable.

use std::fs::File;
use std::io::{BufWriter, Write};
use std::sync::Mutex;
use std::time::Duration;

/// JSONL diagnostic writer for DPLL(T) events.
pub(crate) struct DpllDiagnosticWriter {
    inner: Mutex<DiagnosticInner>,
}

struct DiagnosticInner {
    writer: BufWriter<File>,
    event_count: u64,
}

impl DpllDiagnosticWriter {
    /// Create a new diagnostic writer and emit a header event.
    pub(crate) fn new(path: &str, theory_name: &str) -> std::io::Result<Self> {
        let file = File::create(path)?;
        let mut writer = BufWriter::new(file);

        let header = serde_json::json!({
            "type": "header",
            "version": "1",
            "tool": "ay-dpll-diagnostic",
            "pid": std::process::id(),
            "build": if cfg!(debug_assertions) { "debug" } else { "release" },
            "theory": theory_name,
        });
        writeln!(writer, "{header}")?;
        writer.flush()?;

        Ok(Self {
            inner: Mutex::new(DiagnosticInner {
                writer,
                event_count: 0,
            }),
        })
    }

    /// Emit one DPLL(T) round-trip event.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn emit_dpll_round(
        &self,
        round: u64,
        sat_result: &str,
        sat_duration_us: u64,
        sync_duration_us: u64,
        check_result: &str,
        check_duration_us: u64,
        propagations_added: usize,
        conflict_size: usize,
        sat_conflicts: u64,
        sat_decisions: u64,
    ) {
        let event = serde_json::json!({
            "type": "dpll_round",
            "round": round,
            "sat_result": sat_result,
            "sat_duration_us": sat_duration_us,
            "sync_duration_us": sync_duration_us,
            "check_result": check_result,
            "check_duration_us": check_duration_us,
            "propagations_added": propagations_added,
            "conflict_size": conflict_size,
            "sat_conflicts": sat_conflicts,
            "sat_decisions": sat_decisions,
        });
        self.write_event(&event);
    }

    /// Emit one theory-check phase event.
    pub(crate) fn emit_theory_check(
        &self,
        phase: &str,
        result: &str,
        count: Option<usize>,
        conflict_size: Option<usize>,
        duration_us: u64,
    ) {
        let event = serde_json::json!({
            "type": "theory_check",
            "phase": phase,
            "result": result,
            "count": count,
            "conflict_size": conflict_size,
            "duration_us": duration_us,
        });
        self.write_event(&event);
    }

    /// Emit an eager extension propagation event.
    pub(crate) fn emit_eager_propagate(
        &self,
        sat_level: u32,
        new_assertions: usize,
        check_result: &str,
        propagations: usize,
        duration_us: u64,
    ) {
        let event = serde_json::json!({
            "type": "eager_propagate",
            "sat_level": sat_level,
            "new_assertions": new_assertions,
            "check_result": check_result,
            "propagations": propagations,
            "duration_us": duration_us,
        });
        self.write_event(&event);
    }

    /// Emit a theory split request event.
    pub(crate) fn emit_theory_split(&self, kind: &str, round: u64) {
        let event = serde_json::json!({
            "type": "theory_split",
            "kind": kind,
            "round": round,
        });
        self.write_event(&event);
    }

    /// Emit a push event for incremental theory scope changes.
    pub(crate) fn emit_push(&self, level: u32) {
        let event = serde_json::json!({
            "type": "push",
            "level": level,
        });
        self.write_event(&event);
    }

    /// Emit a pop event for incremental theory scope changes.
    pub(crate) fn emit_pop(&self, from_level: u32, to_level: u32) {
        let event = serde_json::json!({
            "type": "pop",
            "from_level": from_level,
            "to_level": to_level,
        });
        self.write_event(&event);
    }

    /// Emit a solve summary event.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn emit_solve_summary(
        &self,
        result: &str,
        round_trips: u64,
        total_sat_us: u64,
        total_theory_sync_us: u64,
        total_theory_check_us: u64,
        theory_conflicts: u64,
        theory_propagations: u64,
        sat_conflicts: u64,
        sat_decisions: u64,
    ) {
        let event = serde_json::json!({
            "type": "solve_summary",
            "result": result,
            "round_trips": round_trips,
            "total_sat_us": total_sat_us,
            "total_theory_sync_us": total_theory_sync_us,
            "total_theory_check_us": total_theory_check_us,
            "theory_conflicts": theory_conflicts,
            "theory_propagations": theory_propagations,
            "sat_conflicts": sat_conflicts,
            "sat_decisions": sat_decisions,
        });
        self.write_event(&event);
    }

    /// Flush buffered output and return number of non-header events written.
    pub(crate) fn finish(&self) -> u64 {
        let mut inner = self.inner.lock().expect("diagnostic writer mutex poisoned");
        let _ = inner.writer.flush();
        inner.event_count
    }

    fn write_event(&self, event: &serde_json::Value) {
        let mut inner = self.inner.lock().expect("diagnostic writer mutex poisoned");
        writeln!(inner.writer, "{event}").expect("failed to write DPLL diagnostic event");
        inner.event_count += 1;
        if inner.event_count.is_multiple_of(256) {
            let _ = inner.writer.flush();
        }
    }
}

/// Convert a duration to microseconds, saturating to `u64::MAX`.
#[must_use]
pub(crate) fn duration_to_micros(duration: Duration) -> u64 {
    u64::try_from(duration.as_micros()).unwrap_or(u64::MAX)
}

/// Return the diagnostic output path from environment variables.
///
/// Activation rules:
/// - `AY_DPLL_DIAGNOSTIC_FILE=<path>`: explicit output path
/// - `AY_DPLL_DIAGNOSTIC=1`: auto path in temp dir
/// - Otherwise: disabled
#[must_use]
pub(crate) fn diagnostic_path_from_env() -> Option<String> {
    crate::theory_debug_flags::dpll_diagnostic_path()
}

#[cfg(test)]
#[path = "diagnostic_trace_tests.rs"]
mod tests;
