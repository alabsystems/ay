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
mod tests {
    use super::*;
    use std::io::Read;

    #[test]
    fn test_json_observer_writes_valid_jsonl() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("progress.jsonl");
        let path_str = path.to_str().expect("path");

        {
            let mut obs = JsonProgressObserver::new(path_str).expect("create observer");
            obs.set_conflict_interval(1); // write every conflict

            let stats = ProgressStats {
                conflicts: 100,
                decisions: 50,
                propagations: 200,
                restarts: 3,
                stable_mode: true,
                decision_level: 12,
            };

            obs.on_conflict(&stats);
            obs.on_restart(&stats);
            obs.on_progress(&stats);
            obs.on_inprocessing(InprocessingTechnique::Vivify, 15);
            obs.on_learn(7, 4);
            obs.on_theory_conflict(TheoryId::Lia);
        } // drop flushes

        let mut content = String::new();
        std::fs::File::open(&path)
            .expect("open")
            .read_to_string(&mut content)
            .expect("read");

        let lines: Vec<&str> = content.lines().collect();
        assert_eq!(lines.len(), 6, "should have 6 events");

        for line in &lines {
            let parsed: serde_json::Value =
                serde_json::from_str(line).expect("each line should be valid JSON");
            assert_eq!(parsed["schema_version"], 1);
            assert!(
                parsed["timestamp_ms"].as_u64().is_some(),
                "timestamp_ms should be present"
            );
        }

        // Verify event types
        let e0: serde_json::Value = serde_json::from_str(lines[0]).expect("parse");
        assert_eq!(e0["event"], "conflict");
        assert_eq!(e0["conflicts"], 100);
        assert_eq!(e0["decisions"], 50);
        assert_eq!(e0["stable_mode"], true);
        assert_eq!(e0["decision_level"], 12);

        let e1: serde_json::Value = serde_json::from_str(lines[1]).expect("parse");
        assert_eq!(e1["event"], "restart");

        let e2: serde_json::Value = serde_json::from_str(lines[2]).expect("parse");
        assert_eq!(e2["event"], "progress");

        let e3: serde_json::Value = serde_json::from_str(lines[3]).expect("parse");
        assert_eq!(e3["event"], "inprocessing");
        assert_eq!(e3["technique"], "vivify");
        assert_eq!(e3["simplifications"], 15);

        let e4: serde_json::Value = serde_json::from_str(lines[4]).expect("parse");
        assert_eq!(e4["event"], "learn");
        assert_eq!(e4["clause_len"], 7);
        assert_eq!(e4["lbd"], 4);

        let e5: serde_json::Value = serde_json::from_str(lines[5]).expect("parse");
        assert_eq!(e5["event"], "theory_conflict");
        assert_eq!(e5["theory"], "lia");
    }

    #[test]
    fn test_json_observer_conflict_throttling() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("throttle.jsonl");
        let path_str = path.to_str().expect("path");

        {
            let mut obs = JsonProgressObserver::new(path_str).expect("create observer");
            // Default interval is 1000, set to 10 for test.
            obs.set_conflict_interval(10);

            let stats = ProgressStats {
                conflicts: 0,
                decisions: 0,
                propagations: 0,
                restarts: 0,
                stable_mode: false,
                decision_level: 0,
            };

            // Fire 25 conflicts, only conflicts 10 and 20 should be written.
            for _ in 0..25 {
                obs.on_conflict(&stats);
            }
        }

        let content = std::fs::read_to_string(&path).expect("read");
        let lines: Vec<&str> = content.lines().filter(|l| !l.is_empty()).collect();
        assert_eq!(
            lines.len(),
            2,
            "25 conflicts at interval 10 should produce 2 events (at 10 and 20)"
        );
    }

    #[test]
    fn test_json_observer_append_mode() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("append.jsonl");
        let path_str = path.to_str().expect("path");

        let stats = ProgressStats {
            conflicts: 1,
            decisions: 1,
            propagations: 1,
            restarts: 0,
            stable_mode: false,
            decision_level: 0,
        };

        // Write first event with truncate mode.
        {
            let mut obs = JsonProgressObserver::new(path_str).expect("create observer");
            obs.on_restart(&stats);
        }

        // Append second event.
        {
            let mut obs = JsonProgressObserver::new_append(path_str).expect("append observer");
            obs.on_restart(&stats);
        }

        let content = std::fs::read_to_string(&path).expect("read");
        let lines: Vec<&str> = content.lines().filter(|l| !l.is_empty()).collect();
        assert_eq!(lines.len(), 2, "should have 2 events after append");
    }

    #[test]
    fn test_json_observer_schema_version_stable() {
        assert_eq!(
            SCHEMA_VERSION, 1,
            "schema version must be bumped deliberately"
        );
    }

    #[test]
    fn test_technique_to_str_all_variants() {
        // Verify all known variants produce non-"unknown" strings.
        let known = [
            (InprocessingTechnique::Vivify, "vivify"),
            (InprocessingTechnique::Subsume, "subsume"),
            (InprocessingTechnique::Bve, "bve"),
            (InprocessingTechnique::Bce, "bce"),
            (InprocessingTechnique::Probe, "probe"),
            (InprocessingTechnique::Htr, "htr"),
            (InprocessingTechnique::Congruence, "congruence"),
            (InprocessingTechnique::Sweep, "sweep"),
            (InprocessingTechnique::Backbone, "backbone"),
            (InprocessingTechnique::TransRed, "transred"),
            (InprocessingTechnique::Decompose, "decompose"),
            (InprocessingTechnique::Factor, "factor"),
            (InprocessingTechnique::Condition, "condition"),
            (InprocessingTechnique::Cce, "cce"),
            (InprocessingTechnique::Reorder, "reorder"),
        ];
        for (technique, expected) in known {
            assert_eq!(technique_to_str(technique), expected);
        }
    }

    #[test]
    fn test_json_observer_learn_event() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("learn.jsonl");
        let path_str = path.to_str().expect("path");

        {
            let mut obs = JsonProgressObserver::new(path_str).expect("create observer");
            obs.set_conflict_interval(1); // write every learn event

            obs.on_learn(5, 3);
        }

        let content = std::fs::read_to_string(&path).expect("read");
        let lines: Vec<&str> = content.lines().filter(|l| !l.is_empty()).collect();
        assert_eq!(lines.len(), 1, "should have 1 learn event");

        let parsed: serde_json::Value =
            serde_json::from_str(lines[0]).expect("should be valid JSON");
        assert_eq!(parsed["schema_version"], 1);
        assert_eq!(parsed["event"], "learn");
        assert_eq!(parsed["clause_len"], 5);
        assert_eq!(parsed["lbd"], 3);
    }

    #[test]
    fn test_json_observer_theory_conflict_event() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("theory.jsonl");
        let path_str = path.to_str().expect("path");

        {
            let mut obs = JsonProgressObserver::new(path_str).expect("create observer");
            obs.on_theory_conflict(TheoryId::Lia);
            obs.on_theory_conflict(TheoryId::Bv);
            obs.on_theory_conflict(TheoryId::Other);
        }

        let content = std::fs::read_to_string(&path).expect("read");
        let lines: Vec<&str> = content.lines().filter(|l| !l.is_empty()).collect();
        assert_eq!(lines.len(), 3, "should have 3 theory conflict events");

        let e0: serde_json::Value = serde_json::from_str(lines[0]).expect("parse");
        assert_eq!(e0["event"], "theory_conflict");
        assert_eq!(e0["theory"], "lia");

        let e1: serde_json::Value = serde_json::from_str(lines[1]).expect("parse");
        assert_eq!(e1["theory"], "bv");

        let e2: serde_json::Value = serde_json::from_str(lines[2]).expect("parse");
        assert_eq!(e2["theory"], "other");
    }

    #[test]
    fn test_theory_id_to_str_all_variants() {
        let known = [
            (TheoryId::Lia, "lia"),
            (TheoryId::Lra, "lra"),
            (TheoryId::Bv, "bv"),
            (TheoryId::Euf, "euf"),
            (TheoryId::Arrays, "arrays"),
            (TheoryId::Strings, "strings"),
            (TheoryId::Datatypes, "datatypes"),
            (TheoryId::Fp, "fp"),
            (TheoryId::Combined, "combined"),
            (TheoryId::Other, "other"),
        ];
        for (theory, expected) in known {
            assert_eq!(theory_id_to_str(theory), expected);
        }
    }

    #[test]
    fn test_json_observer_learn_throttling() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("learn_throttle.jsonl");
        let path_str = path.to_str().expect("path");

        {
            let mut obs = JsonProgressObserver::new(path_str).expect("create observer");
            obs.set_conflict_interval(5);

            // Fire 12 learn events, only 5 and 10 should be written.
            for _ in 0..12 {
                obs.on_learn(3, 2);
            }
        }

        let content = std::fs::read_to_string(&path).expect("read");
        let lines: Vec<&str> = content.lines().filter(|l| !l.is_empty()).collect();
        assert_eq!(
            lines.len(),
            2,
            "12 learns at interval 5 should produce 2 events (at 5 and 10)"
        );
    }
}
