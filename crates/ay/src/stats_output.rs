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
    pub(crate) competition_jit: Option<CompetitionJitEvidence>,
}

impl RunStatistics {
    pub(crate) fn new(mode: SolveMode, result: &str, elapsed: Duration) -> Self {
        Self {
            mode,
            result: result.to_string(),
            wall_time_ms: elapsed.as_millis() as u64,
            counters: BTreeMap::new(),
            competition_jit: None,
        }
    }

    /// Insert a counter value. Key should use the stable namespace (e.g., `"conflicts"`).
    pub(crate) fn insert(&mut self, key: &str, value: u64) {
        self.counters.insert(key.to_string(), value);
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
mod tests {
    use super::*;

    #[test]
    fn test_to_json_contains_required_fields() {
        let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::from_millis(42));
        stats.insert("conflicts", 1234);
        stats.insert("decisions", 5678);

        let json_str = stats.to_json();
        let parsed: serde_json::Value =
            serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

        assert_eq!(parsed["mode"], "dimacs-sat");
        assert_eq!(parsed["result"], "sat");
        assert_eq!(parsed["wall_time_ms"], 42);
        assert_eq!(parsed["ay_build"]["stamp"], BUILD_PROVENANCE.stamp);
        assert_eq!(parsed["conflicts"], 1234);
        assert_eq!(parsed["decisions"], 5678);
        assert!(
            parsed.get("competition_jit").is_none(),
            "competition JIT metadata should only appear when attached"
        );
    }

    #[test]
    fn test_to_json_suppresses_retired_sat_propagation_counters() {
        let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::ZERO);
        stats.insert("sat.native_code_helpers_enabled", 1);
        stats.insert("sat.retired_propagation_compiler_rounds", 2);
        stats.insert("sat.propagation_native_active", 1);
        stats.insert("sat.propagation_native_propagations", 3);

        let json_str = stats.to_json();
        let parsed: serde_json::Value =
            serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

        assert_eq!(parsed["sat.native_code_helpers_enabled"], 1);
        assert!(
            parsed
                .as_object()
                .expect("stats JSON should be an object")
                .keys()
                .all(|key| !is_retired_sat_propagation_counter(key)),
            "retired SAT propagation counters must not appear in stats JSON: {parsed}"
        );
    }

    #[test]
    fn test_to_json_contains_competition_jit_evidence_with_counter() {
        let mut stats = RunStatistics::new(SolveMode::Pb, "sat", Duration::from_millis(7));
        stats.insert("pb_pbo_candidate_applications", 9);
        stats.competition_jit = Some(CompetitionJitEvidence {
            track: "pb".to_string(),
            artifact_id: "pb-pbo-candidates".to_string(),
            candidate_mode: "solver-program".to_string(),
            application_counter: Some(CompetitionJitApplicationCounter {
                key: "pb_pbo_candidate_applications".to_string(),
                value: 9,
            }),
        });

        let json_str = stats.to_json();
        let parsed: serde_json::Value =
            serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

        let evidence = &parsed["competition_jit"];
        assert_eq!(evidence["schema_version"], 1);
        assert_eq!(evidence["track"], "pb");
        assert_eq!(evidence["artifact_id"], "pb-pbo-candidates");
        assert_eq!(evidence["artifact"], "pb-pbo-candidates");
        assert_eq!(evidence["candidate_mode"], "solver-program");
        assert_eq!(evidence["requested_mode"], "solver-program");
        assert_eq!(evidence["native_dispatch"], false);
        assert_eq!(evidence["fail_closed"], false);
        assert_eq!(
            evidence["application_counter"]["key"],
            "pb_pbo_candidate_applications"
        );
        assert_eq!(evidence["application_counter"]["value"], 9);
        assert_eq!(parsed["pb_pbo_candidate_applications"], 9);
    }

    #[test]
    fn test_to_json_contains_competition_jit_evidence_without_counter() {
        let mut stats = RunStatistics::new(SolveMode::DimacsSat, "unknown", Duration::ZERO);
        stats.competition_jit = Some(CompetitionJitEvidence {
            track: "sat".to_string(),
            artifact_id: "sat-native-code-helpers".to_string(),
            candidate_mode: "current".to_string(),
            application_counter: None,
        });

        let json_str = stats.to_json();
        let parsed: serde_json::Value =
            serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

        let evidence = &parsed["competition_jit"];
        assert_eq!(evidence["schema_version"], 1);
        assert_eq!(evidence["track"], "sat");
        assert_eq!(evidence["artifact_id"], "sat-native-code-helpers");
        assert_eq!(evidence["artifact"], "sat-native-code-helpers");
        assert_eq!(evidence["candidate_mode"], "current");
        assert_eq!(evidence["requested_mode"], "current");
        assert_eq!(evidence["native_dispatch"], false);
        assert_eq!(evidence["fail_closed"], true);
        assert!(
            evidence.get("application_counter").is_none(),
            "application counter should be omitted when not applicable"
        );
    }

    #[test]
    fn test_to_json_competition_jit_current_mode_with_applications_dispatches_native() {
        let mut stats = RunStatistics::new(SolveMode::DimacsSat, "sat", Duration::ZERO);
        stats.competition_jit = Some(CompetitionJitEvidence {
            track: "sat".to_string(),
            artifact_id: "sat-native-code-helpers".to_string(),
            candidate_mode: "current".to_string(),
            application_counter: Some(CompetitionJitApplicationCounter {
                key: "sat.native_code_helper_applications".to_string(),
                value: 3,
            }),
        });

        let json_str = stats.to_json();
        let parsed: serde_json::Value =
            serde_json::from_str(&json_str).expect("to_json output should be valid JSON");

        let evidence = &parsed["competition_jit"];
        assert_eq!(evidence["requested_mode"], "current");
        assert_eq!(evidence["candidate_mode"], "current");
        assert_eq!(evidence["native_dispatch"], true);
        assert_eq!(evidence["fail_closed"], false);
    }

    #[test]
    fn test_build_provenance_helpers_include_build_stamp() {
        assert_eq!(
            BUILD_PROVENANCE.json_value()["stamp"],
            serde_json::Value::String(BUILD_PROVENANCE.stamp.to_string())
        );
        assert!(
            BUILD_PROVENANCE
                .human_banner()
                .contains(BUILD_PROVENANCE.stamp),
            "human banner should expose the active build stamp"
        );
        assert!(
            BUILD_PROVENANCE
                .comment_line()
                .contains(BUILD_PROVENANCE.stamp),
            "comment line should expose the active build stamp"
        );
    }

    #[test]
    fn test_to_json_single_line() {
        let stats = RunStatistics::new(SolveMode::Smt, "done", Duration::from_millis(100));
        let json_str = stats.to_json();
        assert!(
            !json_str.contains('\n'),
            "JSON stats should be a single line for easy grep/parse"
        );
    }

    #[test]
    fn test_to_json_all_modes() {
        for (mode, expected) in [
            (SolveMode::Smt, "smt"),
            (SolveMode::DimacsSat, "dimacs-sat"),
            (SolveMode::Chc, "chc"),
            (SolveMode::Portfolio, "portfolio"),
            (SolveMode::Pb, "pb"),
        ] {
            let stats = RunStatistics::new(mode, "unknown", Duration::ZERO);
            let json_str = stats.to_json();
            let parsed: serde_json::Value = serde_json::from_str(&json_str).unwrap();
            assert_eq!(parsed["mode"], expected);
        }
    }

    #[test]
    fn test_stats_config_any() {
        assert!(!StatsConfig {
            human: false,
            json: false
        }
        .any());
        assert!(StatsConfig {
            human: true,
            json: false
        }
        .any());
        assert!(StatsConfig {
            human: false,
            json: true
        }
        .any());
        assert!(StatsConfig {
            human: true,
            json: true
        }
        .any());
    }
}
