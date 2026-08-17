// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JSONL progress stream observer for `--progress-json <file>`.
//!
//! Implements `SolveObserver` to write one JSON object per event to a file,
//! producing a unified JSONL (JSON Lines) stream. Each line is a self-contained
//! JSON object with a stable versioned schema.
//!
//! # Schema
//!
//! Every event object contains:
//! - `schema_version`: `1` (integer, for forward compatibility)
//! - `event`: event type string (`"conflict"`, `"restart"`, `"progress"`, `"inprocessing"`)
//! - `timestamp_ms`: wall-clock milliseconds since observer creation
//! - Event-specific fields (see individual methods)
//!
//! # Example JSONL output
//!
//! ```text
//! {"schema_version":1,"event":"conflict","timestamp_ms":42,"conflicts":100,"decisions":50,"propagations":200,"restarts":3,"stable_mode":true,"decision_level":12}
//! {"schema_version":1,"event":"restart","timestamp_ms":43,"conflicts":101,"decisions":51,"propagations":205,"restarts":4,"stable_mode":false,"decision_level":0}
//! {"schema_version":1,"event":"inprocessing","timestamp_ms":500,"technique":"vivify","simplifications":15}
//! {"schema_version":1,"event":"progress","timestamp_ms":5000,"conflicts":10000,"decisions":5000,"propagations":20000,"restarts":50,"stable_mode":true,"decision_level":8}
//! ```

use ay_core::time::Instant;
use std::io::{BufWriter, Write};

use crate::observer::{InprocessingTechnique, ProgressStats, SolveObserver, TheoryId};

/// Schema version for the JSONL output format.
///
/// Bump this when adding new fields or changing semantics.
const SCHEMA_VERSION: u32 = 1;

/// A `SolveObserver` that writes JSONL (one JSON object per line) to a file.
///
/// Created via [`JsonProgressObserver::new`] with a file path. The observer
/// opens the file eagerly and buffers writes for performance.
///
/// # Conflict throttling
///
/// Conflict events fire at thousands per second. To avoid overwhelming the
/// output file, conflicts are throttled: only every Nth conflict is written,
/// where N is controlled by [`JsonProgressObserver::set_conflict_interval`]
/// (default: 1000). Set to 1 for full granularity.
pub struct JsonProgressObserver {
    writer: BufWriter<std::fs::File>,
    start: Instant,
    conflict_interval: u64,
    conflict_counter: u64,
    learn_counter: u64,
}

impl JsonProgressObserver {
    /// Create a new JSONL observer writing to the given file path.
    ///
    /// The file is created (or truncated) immediately. Returns `Err` if the
    /// file cannot be opened.
    pub fn new(path: &str) -> std::io::Result<Self> {
        let file = std::fs::File::create(path)?;
        Ok(Self {
            writer: BufWriter::new(file),
            start: Instant::now(),
            conflict_interval: 1000,
            conflict_counter: 0,
            learn_counter: 0,
        })
    }

    /// Create a new JSONL observer that appends to an existing file.
    ///
    /// The file is created if it does not exist, or appended to if it does.
    /// This is used when multiple SAT solver instances write to the same
    /// progress file over the course of a single solve session.
    pub fn new_append(path: &str) -> std::io::Result<Self> {
        let file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(path)?;
        Ok(Self {
            writer: BufWriter::new(file),
            start: Instant::now(),
            conflict_interval: 1000,
            conflict_counter: 0,
            learn_counter: 0,
        })
    }

    /// Set the conflict sampling interval.
    ///
    /// Only every `interval`th conflict event is written to the file.
    /// Default is 1000 (write one event per 1000 conflicts).
    /// Set to 1 for full granularity.
    pub fn set_conflict_interval(&mut self, interval: u64) {
        self.conflict_interval = interval.max(1);
    }

    fn elapsed_ms(&self) -> u64 {
        self.start.elapsed().as_millis() as u64
    }

    fn write_stats_event(&mut self, event: &str, stats: &ProgressStats) {
        // Build JSON manually to avoid serde derive dependency on ProgressStats.
        // This keeps ProgressStats in ay-sat free of serde.
        let line = format!(
            "{{\"schema_version\":{},\"event\":\"{}\",\"timestamp_ms\":{},\"conflicts\":{},\"decisions\":{},\"propagations\":{},\"restarts\":{},\"stable_mode\":{},\"decision_level\":{}}}",
            SCHEMA_VERSION,
            event,
            self.elapsed_ms(),
            stats.conflicts,
            stats.decisions,
            stats.propagations,
            stats.restarts,
            stats.stable_mode,
            stats.decision_level,
        );
        let _ = writeln!(self.writer, "{line}");
    }

    fn write_inprocessing_event(&mut self, technique: InprocessingTechnique, simplifications: u64) {
        let technique_name = technique_to_str(technique);
        let line = format!(
            "{{\"schema_version\":{},\"event\":\"inprocessing\",\"timestamp_ms\":{},\"technique\":\"{}\",\"simplifications\":{}}}",
            SCHEMA_VERSION,
            self.elapsed_ms(),
            technique_name,
            simplifications,
        );
        let _ = writeln!(self.writer, "{line}");
    }

    fn write_learn_event(&mut self, clause_len: u32, lbd: u32) {
        let line = format!(
            "{{\"schema_version\":{},\"event\":\"learn\",\"timestamp_ms\":{},\"clause_len\":{},\"lbd\":{}}}",
            SCHEMA_VERSION,
            self.elapsed_ms(),
            clause_len,
            lbd,
        );
        let _ = writeln!(self.writer, "{line}");
    }

    fn write_theory_conflict_event(&mut self, theory: TheoryId) {
        let theory_name = theory_id_to_str(theory);
        let line = format!(
            "{{\"schema_version\":{},\"event\":\"theory_conflict\",\"timestamp_ms\":{},\"theory\":\"{}\"}}",
            SCHEMA_VERSION,
            self.elapsed_ms(),
            theory_name,
        );
        let _ = writeln!(self.writer, "{line}");
    }
}

impl SolveObserver for JsonProgressObserver {
    fn on_conflict(&mut self, stats: &ProgressStats) {
        self.conflict_counter += 1;
        if self.conflict_counter.is_multiple_of(self.conflict_interval) {
            self.write_stats_event("conflict", stats);
        }
    }

    fn on_restart(&mut self, stats: &ProgressStats) {
        self.write_stats_event("restart", stats);
    }

    fn on_progress(&mut self, stats: &ProgressStats) {
        self.write_stats_event("progress", stats);
        // Flush on progress events (periodic, ~5s) to ensure consumers
        // can tail the file and see updates.
        let _ = self.writer.flush();
    }

    fn on_inprocessing(&mut self, technique: InprocessingTechnique, simplifications: u64) {
        self.write_inprocessing_event(technique, simplifications);
    }

    fn on_learn(&mut self, clause_len: u32, lbd: u32) {
        // Throttle learn events at the same rate as conflicts to avoid
        // overwhelming the output (learn fires once per conflict).
        self.learn_counter += 1;
        if self.learn_counter.is_multiple_of(self.conflict_interval) {
            self.write_learn_event(clause_len, lbd);
        }
    }

    fn on_theory_conflict(&mut self, theory: TheoryId) {
        self.write_theory_conflict_event(theory);
    }
}

impl Drop for JsonProgressObserver {
    fn drop(&mut self) {
        let _ = self.writer.flush();
    }
}

/// Convert a theory identifier to its stable string name for JSONL output.
fn theory_id_to_str(theory: TheoryId) -> &'static str {
    match theory {
        TheoryId::Lia => "lia",
        TheoryId::Lra => "lra",
        TheoryId::Bv => "bv",
        TheoryId::Euf => "euf",
        TheoryId::Arrays => "arrays",
        TheoryId::Strings => "strings",
        TheoryId::Datatypes => "datatypes",
        TheoryId::Fp => "fp",
        TheoryId::Combined => "combined",
        TheoryId::Other => "other",
    }
}

/// Convert an inprocessing technique to its stable string name for JSONL output.
fn technique_to_str(technique: InprocessingTechnique) -> &'static str {
    match technique {
        InprocessingTechnique::Vivify => "vivify",
        InprocessingTechnique::Subsume => "subsume",
        InprocessingTechnique::Bve => "bve",
        InprocessingTechnique::Bce => "bce",
        InprocessingTechnique::Probe => "probe",
        InprocessingTechnique::Htr => "htr",
        InprocessingTechnique::Congruence => "congruence",
        InprocessingTechnique::Sweep => "sweep",
        InprocessingTechnique::Backbone => "backbone",
        InprocessingTechnique::TransRed => "transred",
        InprocessingTechnique::Decompose => "decompose",
        InprocessingTechnique::Factor => "factor",
        InprocessingTechnique::Condition => "condition",
        InprocessingTechnique::Cce => "cce",
        InprocessingTechnique::Reorder => "reorder",
    }
}

#[cfg(test)]
mod tests;
