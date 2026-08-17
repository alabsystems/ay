// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical statistics output for the AY binary.
//!
//! All solve paths (SMT, DIMACS SAT, CHC, PB) populate a [`RunStatistics`] envelope
//! with a common key namespace, then render through one shared function. This
//! ensures `--stats` emits a stable schema regardless of mode.
//!
//! Part of #4723 — cross-mode stats schema contract.

use std::collections::BTreeMap;
use std::time::Duration;

/// Structured build provenance for the active ay binary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BuildProvenance {
    pub(crate) version: &'static str,
    pub(crate) commit: &'static str,
    pub(crate) datetime_utc: &'static str,
    pub(crate) stamp: &'static str,
}

impl BuildProvenance {
    pub(crate) fn human_banner(self) -> String {
        format!("ay build: {}", self.stamp)
    }

    pub(crate) fn comment_line(self) -> String {
        format!("c ay.build.stamp: {}", self.stamp)
    }

    pub(crate) fn json_value(self) -> serde_json::Value {
        serde_json::json!({
            "version": self.version,
            "commit": self.commit,
            "datetime_utc": self.datetime_utc,
            "stamp": self.stamp,
        })
    }
}

pub(crate) const BUILD_PROVENANCE: BuildProvenance = BuildProvenance {
    version: env!("CARGO_PKG_VERSION"),
    commit: env!("AY_BUILD_COMMIT"),
    datetime_utc: env!("AY_BUILD_DATETIME_UTC"),
    stamp: env!("AY_BUILD_STAMP"),
};

/// Controls which stats format(s) to emit.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct StatsConfig {
    /// Human-readable stats (--stats / -st).
    pub(crate) human: bool,
    /// JSON stats to stderr (--stats-json).
    pub(crate) json: bool,
}

impl StatsConfig {
    /// True if any stats output is requested.
    pub(crate) fn any(&self) -> bool {
        self.human || self.json
    }
}

/// Solve mode tag included in every stats envelope.
#[derive(Debug, Clone, Copy)]
pub(crate) enum SolveMode {
    Smt,
    DimacsSat,
    Chc,
    Portfolio,
    Pb,
}

impl SolveMode {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Smt => "smt",
            Self::DimacsSat => "dimacs-sat",
            Self::Chc => "chc",
            Self::Portfolio => "portfolio",
            Self::Pb => "pb",
        }
    }
}

/// Optional competition JIT application counter metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompetitionJitApplicationCounter {
    pub(crate) key: String,
    pub(crate) value: u64,
}

impl CompetitionJitApplicationCounter {
    fn json_value(&self) -> serde_json::Value {
        serde_json::json!({
            "key": self.key,
            "value": self.value,
        })
    }
}

/// Optional metadata envelope for competition JIT evidence in stats JSON.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CompetitionJitEvidence {
    pub(crate) track: String,
    pub(crate) artifact_id: String,
    pub(crate) candidate_mode: String,
    pub(crate) application_counter: Option<CompetitionJitApplicationCounter>,
}

impl CompetitionJitEvidence {
    fn requested_mode(&self) -> &str {
        self.candidate_mode.as_str()
    }

    fn native_dispatch(&self) -> bool {
        self.candidate_mode == "current"
            && self
                .application_counter
                .as_ref()
                .is_some_and(|counter| counter.value > 0)
    }

    fn fail_closed(&self) -> bool {
        self.candidate_mode == "current" && !self.native_dispatch()
    }

    fn json_value(&self) -> serde_json::Value {
        let mut map = serde_json::Map::new();
        map.insert("schema_version".to_string(), serde_json::json!(1));
        map.insert(
            "track".to_string(),
            serde_json::Value::String(self.track.clone()),
        );
        map.insert(
            "artifact_id".to_string(),
            serde_json::Value::String(self.artifact_id.clone()),
        );
        map.insert(
            "artifact".to_string(),
            serde_json::Value::String(self.artifact_id.clone()),
        );
        map.insert(
            "candidate_mode".to_string(),
            serde_json::Value::String(self.candidate_mode.clone()),
        );
        map.insert(
            "requested_mode".to_string(),
            serde_json::Value::String(self.requested_mode().to_string()),
        );
        map.insert(
            "native_dispatch".to_string(),
            serde_json::json!(self.native_dispatch()),
        );
        map.insert(
            "fail_closed".to_string(),
            serde_json::json!(self.fail_closed()),
        );
        if let Some(application_counter) = &self.application_counter {
            map.insert(
                "application_counter".to_string(),
                application_counter.json_value(),
            );
        }
        serde_json::Value::Object(map)
    }
}

/// Canonical statistics envelope populated by every solve path.
///
/// The `counters` map uses a stable key namespace:
/// - Common keys: `conflicts`, `decisions`, `propagations`, `restarts`
/// - SAT-specific: `sat.chrono_bt`, `sat.learned_cls`, `sat.bve_eliminated`, etc.
/// - CHC-specific: `chc.iterations`, `chc.lemmas_learned`, `chc.max_frame`, etc.
/// - SMT-specific: `smt.theory_conflicts`, `smt.theory_propagations`,
///   `smt.no_rounds`, `smt.unknown_returns`, `smt.diseq_propagations`,
///   `smt.conflicts.{lia,lra,euf,arrays}`, `smt.checks.{lia,lra,euf,arrays}`,
///   `smt.props.{lia,lra,euf}`, `smt.partial_clauses`
/// - PB-specific: `pb_pbo_candidate_applications`,
///   `pb_native_code_helper_applications`
pub(crate) struct RunStatistics {
    pub(crate) mode: SolveMode,
    pub(crate) result: String,
    pub(crate) wall_time_ms: u64,
    pub(crate) counters: BTreeMap<String, u64>,
    /// String-valued machine telemetry that does not belong in the numeric
    /// counter namespace. These fields are emitted only in JSON; human routes
    /// retain their purpose-built comment rows.
    pub(crate) text_fields: BTreeMap<String, String>,
    pub(crate) competition_jit: Option<CompetitionJitEvidence>,
}

impl RunStatistics {
    pub(crate) fn new(mode: SolveMode, result: &str, elapsed: Duration) -> Self {
        Self {
            mode,
            result: result.to_string(),
            wall_time_ms: elapsed.as_millis() as u64,
            counters: BTreeMap::new(),
            text_fields: BTreeMap::new(),
            competition_jit: None,
        }
    }

    /// Insert a counter value. Key should use the stable namespace (e.g., `"conflicts"`).
    pub(crate) fn insert(&mut self, key: &str, value: u64) {
        self.counters.insert(key.to_string(), value);
    }

    /// Insert a string-valued machine telemetry field.
    pub(crate) fn insert_text(&mut self, key: &str, value: impl Into<String>) {
        self.text_fields.insert(key.to_string(), value.into());
    }

    fn should_emit_counter(key: &str) -> bool {
        !is_retired_sat_propagation_counter(key)
    }

    /// Print statistics to stderr in the canonical format.
    ///
    /// Format:
    /// ```text
    /// c
    /// c --- AY statistics ---
    /// c ay.mode:          dimacs-sat
    /// c ay.result:               sat
    /// c ay.wall_time_ms:          42
    /// c conflicts:              1234
    /// c decisions:              5678
    /// ...
    /// c
    /// ```
    pub(crate) fn print_to_stderr(&self) {
        safe_eprintln!("c");
        safe_eprintln!("c --- AY statistics ---");
        safe_eprintln!("c ay.mode:          {:>12}", self.mode.as_str());
        safe_eprintln!("c ay.result:        {:>12}", self.result);
        safe_eprintln!("c ay.wall_time_ms:  {:>12}", self.wall_time_ms);
        safe_eprintln!("{}", BUILD_PROVENANCE.comment_line());
        for (key, value) in &self.counters {
            if !Self::should_emit_counter(key) {
                continue;
            }
            // Pad key to align values
            let padded = format!("c {key}:");
            safe_eprintln!("{padded:<20} {value:>12}");
        }
        safe_eprintln!("c");
    }

    /// Serialize statistics as a single-line JSON object.
    ///
    /// The output includes `mode`, `result`, `wall_time_ms`, and all counters
    /// as a flat object. Designed for machine consumption (CI pipelines,
    /// benchmarking scripts, LLM tool-use).
    pub(crate) fn to_json(&self) -> String {
        let mut map = serde_json::Map::new();
        map.insert(
            "mode".to_string(),
            serde_json::Value::String(self.mode.as_str().to_string()),
        );
        map.insert(
            "result".to_string(),
            serde_json::Value::String(self.result.clone()),
        );
        map.insert(
            "wall_time_ms".to_string(),
            serde_json::json!(self.wall_time_ms),
        );
        map.insert("ay_build".to_string(), BUILD_PROVENANCE.json_value());
        if let Some(competition_jit) = &self.competition_jit {
            map.insert("competition_jit".to_string(), competition_jit.json_value());
        }
        for (key, value) in &self.counters {
            if !Self::should_emit_counter(key) {
                continue;
            }
            map.insert(key.clone(), serde_json::json!(value));
        }
        for (key, value) in &self.text_fields {
            map.insert(key.clone(), serde_json::Value::String(value.clone()));
        }
        serde_json::Value::Object(map).to_string()
    }

    /// Print JSON statistics to stderr.
    pub(crate) fn print_json_to_stderr(&self) {
        safe_eprintln!("{}", self.to_json());
    }

    /// Emit stats according to the given config.
    pub(crate) fn emit(&self, config: StatsConfig) {
        if config.human {
            self.print_to_stderr();
        }
        if config.json {
            self.print_json_to_stderr();
        }
    }
}

fn is_retired_sat_propagation_counter(key: &str) -> bool {
    key.starts_with("sat.retired_propagation_compiler_")
        || key.starts_with("sat.propagation_native_")
}

#[cfg(test)]
mod tests;
