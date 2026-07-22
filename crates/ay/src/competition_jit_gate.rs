// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Product-owned competition external code generation JIT gate data model.
//!
//! This module owns the fail-closed gate contract for the product CLI. It is
//! intentionally side-effect light: callers load a checked-in mode matrix,
//! normalize baseline/candidate JSON summaries into [`GateMetrics`], then call
//! [`evaluate_gate`] to obtain a deterministic [`GateDecision`].

#![allow(dead_code, unreachable_pub)]

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use serde_json::{Map as JsonMap, Value};

/// Matrix schema version understood by the competition JIT gate.
pub const COMPETITION_JIT_SCHEMA_VERSION: i64 = 1;

/// Canonical competition JIT mode values.
pub const JIT_MODES: [&str; 4] = ["off", "current", "solver-program", "profile-only"];

/// Modes that may dispatch native external code generation code after the gate passes.
pub const NATIVE_JIT_MODES: [&str; 2] = ["current", "solver-program"];

/// Evidence kind used by profile-only artifacts.
pub const EVIDENCE_PROFILE_ONLY: &str = "profile-only";

/// Evidence kind used by already-integrated native helper artifacts.
pub const EVIDENCE_INTEGRATED_NATIVE_HELPER: &str = "integrated-native-helper";

/// Evidence kind used by solver-program native artifacts.
pub const EVIDENCE_SOLVER_PROGRAM_NATIVE: &str = "solver-program-native";

const SOLVE_CONTROL_VOCABULARY: [&str; 5] = [
    "mode",
    "guidance",
    "guidance-out",
    "runtime-summary",
    "telemetry",
];

const REQUIRED_TRACKS: [&str; 4] = ["sat", "smt", "pb", "chc"];

const GATE_RULES: [&str; 7] = [
    "wrong_answer",
    "proof_failure",
    "witness_failure",
    "crash",
    "solved_count_loss",
    "par2_loss",
    "application_count",
];

const INTEGRITY_RULE_NAMES: [&str; 4] =
    ["wrong_answer", "proof_failure", "witness_failure", "crash"];

const INTEGRITY_FAILURES: [&str; 4] = ["wrong-answer", "proof-failure", "witness-failure", "crash"];

const FAILURE_MODES: [&str; 2] = ["off", "profile-only"];
const EPSILON: f64 = 1e-9;

const CANDIDATE_MODE_FIELDS: [&str; 4] = [
    "candidate_mode",
    "competition_jit_candidate_mode",
    "competition_jit_mode",
    "jit_mode",
];

/// Error type returned by matrix loading, invariant validation, and evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompetitionJitGateError {
    message: String,
}

impl CompetitionJitGateError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }

    /// Human-readable error message.
    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for CompetitionJitGateError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.message)
    }
}

impl Error for CompetitionJitGateError {}

/// Result alias for competition JIT gate helpers.
pub type GateResult<T> = Result<T, CompetitionJitGateError>;

/// Top-level checked-in competition JIT mode matrix.
#[derive(Debug, Clone, PartialEq)]
pub struct CompetitionJitMatrix {
    /// Matrix schema version.
    pub version: i64,
    /// Supported runtime modes keyed by mode name.
    pub modes: BTreeMap<String, JitModeConfig>,
    /// Solve-control plane vocabulary and track telemetry mapping.
    pub solve_control_plane: SolveControlPlane,
    /// Global gate thresholds used when artifacts do not override them.
    pub gate_defaults: GateDefaults,
    /// Competition tracks keyed by track name.
    pub tracks: BTreeMap<String, CompetitionTrack>,
}

impl CompetitionJitMatrix {
    /// Find an artifact by track and artifact id.
    pub fn find_artifact(&self, track: &str, artifact_id: &str) -> GateResult<&JitArtifact> {
        let track_cfg = self.tracks.get(track).ok_or_else(|| {
            CompetitionJitGateError::new(format!("unknown competition JIT track: {track}"))
        })?;
        track_cfg
            .artifacts
            .iter()
            .find(|artifact| artifact.id == artifact_id)
            .ok_or_else(|| {
                let known = track_cfg
                    .artifacts
                    .iter()
                    .map(|artifact| artifact.id.as_str())
                    .collect::<Vec<_>>()
                    .join(", ");
                CompetitionJitGateError::new(format!(
                    "unknown artifact {artifact_id:?} for track {track:?}; known: {known}"
                ))
            })
    }
}

/// One entry from the matrix `modes` object.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JitModeConfig {
    /// True if this mode may dispatch native code after gate evaluation.
    pub native_dispatch: bool,
    /// Human-readable matrix description.
    pub description: String,
}

/// Solve-control plane section of the matrix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolveControlPlane {
    /// Solve-control plane version.
    pub version: i64,
    /// Vocabulary entries keyed by stable term.
    pub vocabulary: BTreeMap<String, ControlPlaneVocabularyEntry>,
    /// Track-level control-plane mappings keyed by track name.
    pub tracks: BTreeMap<String, ControlPlaneTrack>,
}

/// One solve-control vocabulary entry.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneVocabularyEntry {
    /// Human-readable description.
    pub description: String,
    /// Optional mode values for the `mode` vocabulary term.
    pub mode_values: Vec<String>,
    /// Stable decision field names emitted under the vocabulary term.
    pub decision_fields: Vec<String>,
}

/// Solve-control mapping for one competition track.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ControlPlaneTrack {
    /// Runtime solve modes covered by the competition track.
    pub runtime_modes: Vec<String>,
    /// Matrix path expression describing where mode candidates come from.
    pub mode_source: String,
    /// Artifact ids surfaced in guidance output.
    pub guidance_artifacts: Vec<String>,
    /// Telemetry counters exported for this track.
    pub telemetry_counters: Vec<String>,
}

/// Global default gate thresholds and fail-closed modes.
#[derive(Debug, Clone, PartialEq)]
pub struct GateDefaults {
    /// Maximum allowed candidate wrong answers.
    pub wrong_answers_max: i64,
    /// Maximum allowed candidate proof failures.
    pub proof_failures_max: i64,
    /// Maximum allowed candidate witness failures.
    pub witness_failures_max: i64,
    /// Maximum allowed candidate crashes.
    pub crashes_max: i64,
    /// Maximum allowed solved-count loss against baseline.
    pub solved_count_loss_max: i64,
    /// Maximum allowed PAR-2 regression in seconds.
    pub par2_loss_max_sec: f64,
    /// Default minimum useful application count.
    pub min_useful_applications: i64,
    /// Recommended fail-closed mode for integrity failures.
    pub integrity_failure_mode: String,
    /// Recommended fail-closed mode for performance failures.
    pub performance_failure_mode: String,
}

/// Competition track section of the matrix.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CompetitionTrack {
    /// Competition name, such as SAT-COMP.
    pub competition: String,
    /// Evaluation names tied to this track.
    pub evals: Vec<String>,
    /// Gateable artifacts for the track.
    pub artifacts: Vec<JitArtifact>,
}

/// Gateable external code generation JIT artifact.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JitArtifact {
    /// Stable artifact id.
    pub id: String,
    /// Human-readable artifact description.
    pub description: String,
    /// Default mode when the caller does not pass a candidate mode.
    pub default_mode: String,
    /// Candidate modes legal for this artifact.
    pub candidate_modes: Vec<String>,
    /// Evidence class required before native dispatch may be enabled.
    pub evidence_kind: String,
    /// Artifact-specific minimum useful application threshold.
    pub min_useful_applications: i64,
    /// Counter key used as useful application evidence.
    pub application_counter: String,
    /// Optional native dispatch install/apply counters keyed by native mode.
    pub native_dispatch_counters: BTreeMap<String, NativeDispatchCounters>,
    /// Fail-closed gate rules keyed by rule name.
    pub gate: BTreeMap<String, GateRule>,
}

/// Install/apply counters that must be positive for native dispatch.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NativeDispatchCounters {
    /// Counter recording native artifact installation.
    pub install_counter: String,
    /// Counter recording native artifact application.
    pub apply_counter: String,
}

/// One fail-closed gate rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateRule {
    /// Whether the rule participates in non-integrity gate failures.
    pub enabled: bool,
    /// Fail-closed mode used when the rule fires.
    pub failure_mode: String,
    /// Optional human-readable rule description.
    pub description: Option<String>,
}

/// Normalized metrics consumed by the competition JIT gate.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct GateMetrics {
    /// Candidate wrong answers or comparison disagreements.
    pub wrong_answers: i64,
    /// UNSAT proof failures.
    pub proof_failures: i64,
    /// SAT/PB witness failures.
    pub witness_failures: i64,
    /// Crashes or fatal runner errors.
    pub crashes: i64,
    /// Solved or definitive result count.
    pub solved: Option<i64>,
    /// PAR-2 total in seconds.
    pub par2: Option<f64>,
    /// Artifact useful application count.
    pub application_count: Option<i64>,
    /// Native dispatch install count for solver-program artifacts.
    pub native_install_count: Option<i64>,
    /// Native dispatch apply count for solver-program artifacts.
    pub native_apply_count: Option<i64>,
    /// CHC native helper compile-attempt count.
    pub native_helper_compile_attempt_count: Option<i64>,
    /// CHC native helper compile-success count.
    pub native_helper_compile_success_count: Option<i64>,
    /// CHC native helper evaluation count.
    pub native_helper_evaluation_count: Option<i64>,
    /// CHC native helper interpreter-confirmation count.
    pub native_helper_interpreter_confirmation_count: Option<i64>,
    /// CHC native helper trusted-true count.
    pub native_helper_trusted_true_count: Option<i64>,
    /// CHC native helper deopt count.
    pub native_helper_deopt_count: Option<i64>,
    /// CHC native helper fallback count.
    pub native_helper_fallback_count: Option<i64>,
    /// CHC native helper missing-var fallback count.
    pub native_helper_missing_var_fallback_count: Option<i64>,
}

/// One reason a gate failed and the mode it fails closed to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateFailure {
    /// Stable failure kind.
    pub kind: String,
    /// Fail-closed mode for this failure.
    pub failure_mode: String,
    /// Human-readable failure detail.
    pub detail: String,
}

/// Deterministic fail-closed gate decision.
#[derive(Debug, Clone, PartialEq)]
pub struct GateDecision {
    /// `pass` or `fail`.
    pub status: String,
    /// Competition track.
    pub track: String,
    /// Artifact id.
    pub artifact: String,
    /// Candidate mode evaluated by the gate.
    pub candidate_mode: String,
    /// Recommended mode after fail-closed evaluation.
    pub recommended_mode: String,
    /// True only when the gate passed and the recommended mode has native evidence.
    pub native_dispatch: bool,
    /// Ordered gate failures.
    pub failures: Vec<GateFailure>,
    /// Baseline metrics used by the gate.
    pub baseline: GateMetrics,
    /// Candidate metrics used by the gate.
    pub candidate: GateMetrics,
}

/// Options for extracting metrics from a JSON summary or comparison payload.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MetricNormalizationOptions<'a> {
    /// Optional role inside a comparison payload, usually `baseline` or `candidate`.
    pub role: Option<&'a str>,
    /// Artifact-specific useful application counter.
    pub application_counter_key: Option<&'a str>,
    /// Native dispatch install counter for the candidate mode.
    pub native_install_counter_key: Option<&'a str>,
    /// Native dispatch apply counter for the candidate mode.
    pub native_apply_counter_key: Option<&'a str>,
}

/// Return the canonical matrix path under a repository root.
pub fn default_matrix_path(repo_root: impl AsRef<Path>) -> PathBuf {
    repo_root
        .as_ref()
        .join("competition")
        .join("jit_mode_matrix.json")
}

/// Return the sibling schema path for a matrix path.
pub fn matrix_schema_path(matrix_path: impl AsRef<Path>) -> PathBuf {
    let path = matrix_path.as_ref();
    match path.file_name().and_then(|name| name.to_str()) {
        Some(name)
            if Path::new(name)
                .extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("json")) =>
        {
            path.with_file_name(format!(
                "{}.schema.json",
                &name[..name.len() - ".json".len()]
            ))
        }
        _ => path.with_extension(format!(
            "{}schema.json",
            path.extension()
                .and_then(|extension| extension.to_str())
                .map(|extension| format!("{extension}."))
                .unwrap_or_default()
        )),
    }
}

/// Load an arbitrary JSON file as an object value.
pub fn load_json_object(path: impl AsRef<Path>) -> GateResult<Value> {
    let path = path.as_ref();
    let text = fs::read_to_string(path)
        .map_err(|err| CompetitionJitGateError::new(format!("{}: {err}", path.display())))?;
    let value: Value = serde_json::from_str(&text)
        .map_err(|err| CompetitionJitGateError::new(format!("{}: {err}", path.display())))?;
    if !value.is_object() {
        return Err(CompetitionJitGateError::new(format!(
            "{}: expected a JSON object",
            path.display()
        )));
    }
    Ok(value)
}

/// Load and validate a competition JIT mode matrix.
pub fn load_matrix(path: impl AsRef<Path>) -> GateResult<CompetitionJitMatrix> {
    let path = path.as_ref();
    let value = load_json_object(path)?;
    let matrix = parse_matrix_value(&value)?;
    validate_matrix_invariants(&matrix).map_err(|err| {
        CompetitionJitGateError::new(format!("{}: {}", path.display(), err.message()))
    })?;
    Ok(matrix)
}

/// Parse a matrix from a JSON value. Call [`validate_matrix_invariants`] before use
/// if the value did not come from [`load_matrix`].
pub fn parse_matrix_value(value: &Value) -> GateResult<CompetitionJitMatrix> {
    let root = value.as_object().ok_or_else(|| {
        CompetitionJitGateError::new("competition JIT matrix must be a JSON object")
    })?;
    let version = required_i64(root, "version", "matrix")?;
    let modes = parse_modes(required_object(root, "modes", "matrix")?)?;
    let solve_control_plane =
        parse_solve_control_plane(required_object(root, "solve_control_plane", "matrix")?)?;
    let gate_defaults = parse_gate_defaults(required_object(root, "gate_defaults", "matrix")?)?;
    let tracks = parse_tracks(required_object(root, "tracks", "matrix")?)?;

    Ok(CompetitionJitMatrix {
        version,
        modes,
        solve_control_plane,
        gate_defaults,
        tracks,
    })
}

/// Validate semantic invariants that are stronger than JSON shape.
pub fn validate_matrix_invariants(matrix: &CompetitionJitMatrix) -> GateResult<()> {
    let mut errors = Vec::new();

    let mode_names = matrix.modes.keys().cloned().collect::<BTreeSet<_>>();
    let expected_modes = JIT_MODES
        .iter()
        .map(|mode| (*mode).to_string())
        .collect::<BTreeSet<_>>();
    for mode in expected_modes.difference(&mode_names) {
        errors.push(format!("missing mode: {mode}"));
    }
    for mode in mode_names.difference(&expected_modes) {
        errors.push(format!("unknown mode: {mode}"));
    }

    for mode in ["integrity_failure_mode", "performance_failure_mode"] {
        let value = if mode == "integrity_failure_mode" {
            &matrix.gate_defaults.integrity_failure_mode
        } else {
            &matrix.gate_defaults.performance_failure_mode
        };
        if !is_failure_mode(value) {
            errors.push(format!(
                "{mode} must be one of {{{}}}, got {value:?}",
                FAILURE_MODES.join(", ")
            ));
        }
    }

    for term in SOLVE_CONTROL_VOCABULARY {
        if !matrix.solve_control_plane.vocabulary.contains_key(term) {
            errors.push(format!("missing solve-control vocabulary term: {term}"));
        }
    }
    if let Some(mode_entry) = matrix.solve_control_plane.vocabulary.get("mode") {
        let values = mode_entry
            .mode_values
            .iter()
            .cloned()
            .collect::<BTreeSet<_>>();
        if values != mode_names {
            errors.push("solve-control mode values must match modes object".to_string());
        }
    }

    for track in REQUIRED_TRACKS {
        if !matrix.tracks.contains_key(track) {
            errors.push(format!("missing track: {track}"));
        }
        if !matrix.solve_control_plane.tracks.contains_key(track) {
            errors.push(format!("missing solve-control track: {track}"));
        }
    }

    for (track_name, track_cfg) in &matrix.tracks {
        if track_cfg.artifacts.is_empty() {
            errors.push(format!("track {track_name:?} must define artifacts"));
            continue;
        }

        let mut artifact_ids = Vec::new();
        let mut seen_artifacts = BTreeSet::new();
        let mut expected_telemetry_counters = Vec::new();

        for artifact in &track_cfg.artifacts {
            artifact_ids.push(artifact.id.clone());
            if !seen_artifacts.insert(artifact.id.clone()) {
                errors.push(format!(
                    "{track_name}/{} artifact id is duplicated",
                    artifact.id
                ));
            }
            if artifact.application_counter.is_empty() {
                errors.push(format!(
                    "{track_name}/{} application_counter is required",
                    artifact.id
                ));
            } else {
                expected_telemetry_counters.push(artifact.application_counter.clone());
            }
            if !is_mode(&artifact.default_mode) {
                errors.push(format!(
                    "{track_name}/{} default_mode must be one of {{{}}}, got {:?}",
                    artifact.id,
                    JIT_MODES.join(", "),
                    artifact.default_mode
                ));
            }
            if artifact.candidate_modes.is_empty() {
                errors.push(format!(
                    "{track_name}/{} candidate_modes must not be empty",
                    artifact.id
                ));
            }
            for mode in &artifact.candidate_modes {
                if !is_mode(mode) {
                    errors.push(format!(
                        "{track_name}/{} candidate mode must be one of {{{}}}, got {mode:?}",
                        artifact.id,
                        JIT_MODES.join(", ")
                    ));
                }
            }
            if !artifact.candidate_modes.contains(&artifact.default_mode) {
                errors.push(format!(
                    "{track_name}/{} default_mode {:?} must be listed in candidate_modes",
                    artifact.id, artifact.default_mode
                ));
            }

            if !is_evidence_kind(&artifact.evidence_kind) {
                errors.push(format!(
                    "{track_name}/{} evidence_kind must be one of {{{}}}, got {:?}",
                    artifact.id,
                    [
                        EVIDENCE_PROFILE_ONLY,
                        EVIDENCE_INTEGRATED_NATIVE_HELPER,
                        EVIDENCE_SOLVER_PROGRAM_NATIVE,
                    ]
                    .join(", "),
                    artifact.evidence_kind
                ));
            }
            if artifact
                .candidate_modes
                .iter()
                .any(|mode| mode == "current")
                && (artifact.evidence_kind != EVIDENCE_INTEGRATED_NATIVE_HELPER
                    || !artifact.id.ends_with("-native-code-helpers"))
            {
                errors.push(format!(
                    "{track_name}/{} may expose `current` only for integrated native-code helper artifacts",
                    artifact.id
                ));
            }

            for (native_mode, counters) in &artifact.native_dispatch_counters {
                if !is_native_mode(native_mode) {
                    errors.push(format!(
                        "{track_name}/{} native_dispatch_counters mode must be one of {{{}}}, got {native_mode:?}",
                        artifact.id,
                        NATIVE_JIT_MODES.join(", ")
                    ));
                }
                if counters.install_counter.is_empty() {
                    errors.push(format!(
                        "{track_name}/{} native_dispatch_counters[{native_mode:?}].install_counter is required",
                        artifact.id
                    ));
                } else {
                    expected_telemetry_counters.push(counters.install_counter.clone());
                }
                if counters.apply_counter.is_empty() {
                    errors.push(format!(
                        "{track_name}/{} native_dispatch_counters[{native_mode:?}].apply_counter is required",
                        artifact.id
                    ));
                } else {
                    expected_telemetry_counters.push(counters.apply_counter.clone());
                }
            }

            for rule_name in GATE_RULES {
                let Some(rule) = artifact.gate.get(rule_name) else {
                    errors.push(format!(
                        "{track_name}/{} missing {rule_name} gate rule",
                        artifact.id
                    ));
                    continue;
                };
                if !is_failure_mode(&rule.failure_mode) {
                    errors.push(format!(
                        "{track_name}/{} {rule_name} failure_mode must be one of {{{}}}, got {:?}",
                        artifact.id,
                        FAILURE_MODES.join(", "),
                        rule.failure_mode
                    ));
                }
                if INTEGRITY_RULE_NAMES.contains(&rule_name) {
                    if !rule.enabled {
                        errors.push(format!(
                            "{track_name}/{} {rule_name} must be enabled",
                            artifact.id
                        ));
                    }
                    if rule.failure_mode != "off" {
                        errors.push(format!(
                            "{track_name}/{} {rule_name} must fail closed to 'off'",
                            artifact.id
                        ));
                    }
                }
            }
        }

        let Some(control_track) = matrix.solve_control_plane.tracks.get(track_name) else {
            continue;
        };
        let expected_mode_source = format!("tracks.{track_name}.artifacts[].candidate_modes");
        if control_track.mode_source != expected_mode_source {
            errors.push(format!(
                "solve-control track {track_name:?} mode_source must be {expected_mode_source:?}, got {:?}",
                control_track.mode_source
            ));
        }
        if control_track.guidance_artifacts != artifact_ids {
            errors.push(format!(
                "solve-control track {track_name:?} guidance_artifacts must match artifact ids {artifact_ids:?}, got {:?}",
                control_track.guidance_artifacts
            ));
        }
        let mut seen_counters = BTreeSet::new();
        for counter in &control_track.telemetry_counters {
            if !seen_counters.insert(counter) {
                errors.push(format!(
                    "solve-control track {track_name:?} telemetry_counters must not contain duplicates, got {:?}",
                    control_track.telemetry_counters
                ));
                break;
            }
        }
        let missing_counters = expected_telemetry_counters
            .iter()
            .filter(|counter| !control_track.telemetry_counters.contains(counter))
            .cloned()
            .collect::<Vec<_>>();
        if !missing_counters.is_empty() {
            errors.push(format!(
                "solve-control track {track_name:?} telemetry_counters must include artifact application counters {expected_telemetry_counters:?}, missing {missing_counters:?} from {:?}",
                control_track.telemetry_counters
            ));
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(CompetitionJitGateError::new(errors.join("; ")))
    }
}

/// Find an artifact by track and artifact id.
pub fn find_artifact<'a>(
    matrix: &'a CompetitionJitMatrix,
    track: &str,
    artifact_id: &str,
) -> GateResult<&'a JitArtifact> {
    matrix.find_artifact(track, artifact_id)
}

/// Return native dispatch install/apply counter keys for an artifact mode.
pub fn native_dispatch_counter_keys<'a>(
    artifact: &'a JitArtifact,
    mode: &str,
) -> (Option<&'a str>, Option<&'a str>) {
    artifact
        .native_dispatch_counters
        .get(mode)
        .map(|counters| {
            (
                Some(counters.install_counter.as_str()),
                Some(counters.apply_counter.as_str()),
            )
        })
        .unwrap_or((None, None))
}

/// Extract the candidate mode from summary metadata aliases.
pub fn summary_candidate_mode(data: &Value) -> Option<String> {
    find_metadata_field(data, &CANDIDATE_MODE_FIELDS).and_then(|value| match value {
        Value::String(mode) if !mode.is_empty() => Some(mode.clone()),
        _ => None,
    })
}

/// Normalize one JSON summary or one role from a comparison payload into gate metrics.
pub fn normalize_gate_metrics(
    data: &Value,
    options: MetricNormalizationOptions<'_>,
) -> GateMetrics {
    let Some(source) = selected_source(data, options.role) else {
        return GateMetrics::default();
    };
    let flattened = flattened_summary_source(source);

    let application_count = if let Some(application_counter_key) = options.application_counter_key {
        first_int(&flattened, &[application_counter_key]).or_else(|| {
            summary_application_counter_value(&flattened, application_counter_key)
                .and_then(|value| as_int(&value))
        })
    } else {
        first_int(&flattened, &["application_count"])
    };

    let direct = GateMetrics {
        wrong_answers: first_int(
            &flattened,
            &[
                "wrong_answers",
                "wrong",
                "errors",
                "disagree",
                "disagreements",
                "soundness_failures",
            ],
        )
        .unwrap_or(0),
        proof_failures: first_int(
            &flattened,
            &[
                "proof_failures",
                "proof_failure_count",
                "proof_invalid",
                "proof_errors",
            ],
        )
        .unwrap_or(0),
        witness_failures: first_int(
            &flattened,
            &[
                "witness_failures",
                "witness_invalid",
                "witness_broken",
                "candidate_witness_failures",
            ],
        )
        .unwrap_or(0),
        crashes: first_int(
            &flattened,
            &["crashes", "crash_count", "segfaults", "signals"],
        )
        .unwrap_or(0),
        solved: first_int(
            &flattened,
            &["solved", "definitive", "correct", "solved_count"],
        ),
        par2: first_float(
            &flattened,
            &["par2", "par2_total", "par2_sum_s", "par2_sec"],
        ),
        application_count,
        native_install_count: options
            .native_install_counter_key
            .and_then(|key| first_int(&flattened, &[key])),
        native_apply_count: options
            .native_apply_counter_key
            .and_then(|key| first_int(&flattened, &[key])),
        native_helper_compile_attempt_count: first_int(
            &flattened,
            &["chc.native_code_helper_compile_attempts"],
        ),
        native_helper_compile_success_count: first_int(
            &flattened,
            &["chc.native_code_helper_compile_successes"],
        ),
        native_helper_evaluation_count: first_int(
            &flattened,
            &["chc.native_code_helper_evaluations"],
        ),
        native_helper_interpreter_confirmation_count: first_int(
            &flattened,
            &["chc.native_code_helper_interpreter_confirmations"],
        ),
        native_helper_trusted_true_count: first_int(
            &flattened,
            &["chc.native_code_helper_trusted_true_results"],
        ),
        native_helper_deopt_count: first_int(&flattened, &["chc.native_code_helper_deopts"]),
        native_helper_fallback_count: first_int(&flattened, &["chc.native_code_helper_fallbacks"]),
        native_helper_missing_var_fallback_count: first_int(
            &flattened,
            &["chc.native_code_helper_missing_var_fallbacks"],
        ),
    };

    merge_metrics(
        &merge_metrics(&direct, &metrics_from_comparisons(&flattened)),
        &metrics_from_items(&flattened),
    )
}

/// Normalize baseline and candidate metrics from a comparison payload.
pub fn normalize_ab_metrics(
    data: &Value,
    artifact: &JitArtifact,
    candidate_mode: &str,
) -> (GateMetrics, GateMetrics) {
    let (native_install_counter_key, native_apply_counter_key) =
        native_dispatch_counter_keys(artifact, candidate_mode);
    let baseline = normalize_gate_metrics(
        data,
        MetricNormalizationOptions {
            role: Some("baseline"),
            application_counter_key: Some(&artifact.application_counter),
            native_install_counter_key,
            native_apply_counter_key,
        },
    );
    let candidate = normalize_gate_metrics(
        data,
        MetricNormalizationOptions {
            role: Some("candidate"),
            application_counter_key: Some(&artifact.application_counter),
            native_install_counter_key,
            native_apply_counter_key,
        },
    );
    (baseline, candidate)
}

/// Evaluate the fail-closed competition JIT gate.
pub fn evaluate_gate(
    matrix: &CompetitionJitMatrix,
    track: &str,
    artifact_id: &str,
    baseline: GateMetrics,
    candidate: GateMetrics,
    candidate_mode: Option<&str>,
) -> GateResult<GateDecision> {
    let artifact = matrix.find_artifact(track, artifact_id)?;
    let mode = candidate_mode.unwrap_or(&artifact.default_mode).to_string();
    if !is_mode(&mode) {
        return Err(CompetitionJitGateError::new(format!(
            "unknown JIT mode: {mode}"
        )));
    }
    if !artifact.candidate_modes.contains(&mode) {
        return Err(CompetitionJitGateError::new(format!(
            "mode {mode:?} is not allowed for {artifact_id:?}; allowed: {}",
            artifact.candidate_modes.join(", ")
        )));
    }

    let defaults = &matrix.gate_defaults;
    let min_applications = artifact.min_useful_applications;
    let required_applications = required_application_minimum(&mode, artifact, min_applications);

    let mut failures = Vec::new();
    if candidate.wrong_answers > defaults.wrong_answers_max {
        add_failure(
            &mut failures,
            artifact,
            "wrong_answer",
            "wrong-answer",
            format!(
                "candidate wrong answers {} > allowed {}",
                candidate.wrong_answers, defaults.wrong_answers_max
            ),
        );
    }
    if candidate.proof_failures > defaults.proof_failures_max {
        add_failure(
            &mut failures,
            artifact,
            "proof_failure",
            "proof-failure",
            format!(
                "candidate proof failures {} > allowed {}",
                candidate.proof_failures, defaults.proof_failures_max
            ),
        );
    }
    if candidate.witness_failures > defaults.witness_failures_max {
        add_failure(
            &mut failures,
            artifact,
            "witness_failure",
            "witness-failure",
            format!(
                "candidate witness failures {} > allowed {}",
                candidate.witness_failures, defaults.witness_failures_max
            ),
        );
    }
    if candidate.crashes > defaults.crashes_max {
        add_failure(
            &mut failures,
            artifact,
            "crash",
            "crash",
            format!(
                "candidate crashes {} > allowed {}",
                candidate.crashes, defaults.crashes_max
            ),
        );
    }

    match (baseline.solved, candidate.solved) {
        (Some(baseline_solved), Some(candidate_solved)) => {
            let solved_loss = baseline_solved - candidate_solved;
            if solved_loss > defaults.solved_count_loss_max {
                add_failure(
                    &mut failures,
                    artifact,
                    "solved_count_loss",
                    "solved-count-loss",
                    format!(
                        "candidate solved count lost {solved_loss} ({baseline_solved}->{candidate_solved})"
                    ),
                );
            }
        }
        _ => add_failure(
            &mut failures,
            artifact,
            "solved_count_loss",
            "solved-count-loss",
            "baseline and candidate solved counts are required for the A/B gate".to_string(),
        ),
    }

    match (baseline.par2, candidate.par2) {
        (Some(baseline_par2), Some(candidate_par2)) => {
            let par2_loss = candidate_par2 - baseline_par2;
            if par2_loss > defaults.par2_loss_max_sec + EPSILON {
                add_failure(
                    &mut failures,
                    artifact,
                    "par2_loss",
                    "par2-loss",
                    format!(
                        "candidate PAR-2 regressed by {par2_loss:.3}s ({baseline_par2}->{candidate_par2})"
                    ),
                );
            }
        }
        _ => add_failure(
            &mut failures,
            artifact,
            "par2_loss",
            "par2-loss",
            "baseline and candidate PAR-2 totals are required for the A/B gate".to_string(),
        ),
    }

    if mode != "off" && required_applications > 0 {
        if candidate
            .application_count
            .is_none_or(|applications| applications < required_applications)
        {
            let actual = candidate
                .application_count
                .map(|applications| applications.to_string())
                .unwrap_or_else(|| "missing".to_string());
            add_failure(
                &mut failures,
                artifact,
                "application_count",
                "application-count",
                format!(
                    "candidate useful applications {actual} < required {required_applications}"
                ),
            );
        }
    }

    if is_native_mode(&mode) {
        let required_evidence = native_evidence_kind_for_mode(&mode);
        if artifact.evidence_kind != required_evidence {
            failures.push(GateFailure {
                kind: "native-dispatch-evidence".to_string(),
                failure_mode: "profile-only".to_string(),
                detail: format!(
                    "{} counter evidence is {:?}; {:?} requires {:?} evidence",
                    artifact.id, artifact.evidence_kind, mode, required_evidence
                ),
            });
        }
        if let Some(counters) = artifact.native_dispatch_counters.get(&mode) {
            if candidate
                .native_install_count
                .is_none_or(|count| count <= 0)
            {
                failures.push(native_dispatch_counter_failure(
                    "native-install-evidence",
                    &mode,
                    &counters.install_counter,
                    candidate.native_install_count,
                ));
            }
            if candidate.native_apply_count.is_none_or(|count| count <= 0) {
                failures.push(native_dispatch_counter_failure(
                    "native-apply-evidence",
                    &mode,
                    &counters.apply_counter,
                    candidate.native_apply_count,
                ));
            }
        }
    }

    if track == "chc"
        && artifact_id == "chc-native-code-helpers"
        && mode == "current"
        && !failures
            .iter()
            .any(|failure| is_integrity_failure(&failure.kind))
    {
        validate_chc_native_helper_current_gate(&mut failures, &candidate);
    }

    let (status, recommended_mode) = if failures.is_empty() {
        ("pass".to_string(), mode.clone())
    } else {
        let relevant_failures = if failures
            .iter()
            .any(|failure| is_integrity_failure(&failure.kind))
        {
            failures
                .iter()
                .filter(|failure| is_integrity_failure(&failure.kind))
                .collect::<Vec<_>>()
        } else {
            failures.iter().collect::<Vec<_>>()
        };
        let recommended = relevant_failures
            .iter()
            .map(|failure| failure.failure_mode.as_str())
            .min_by_key(|mode| if *mode == "off" { 0 } else { 1 })
            .unwrap_or("profile-only")
            .to_string();
        ("fail".to_string(), recommended)
    };

    let native_dispatch = status == "pass" && native_dispatch_allowed(&recommended_mode, artifact);

    Ok(GateDecision {
        status,
        track: track.to_string(),
        artifact: artifact_id.to_string(),
        candidate_mode: mode,
        recommended_mode,
        native_dispatch,
        failures,
        baseline,
        candidate,
    })
}

/// Convert normalized metrics to the JSON shape used by gate reports.
pub fn gate_metrics_to_json_value(metrics: &GateMetrics) -> Value {
    serde_json::json!({
        "wrong_answers": metrics.wrong_answers,
        "proof_failures": metrics.proof_failures,
        "witness_failures": metrics.witness_failures,
        "crashes": metrics.crashes,
        "solved": metrics.solved,
        "par2": metrics.par2,
        "application_count": metrics.application_count,
        "native_install_count": metrics.native_install_count,
        "native_apply_count": metrics.native_apply_count,
        "native_helper_compile_attempt_count": metrics.native_helper_compile_attempt_count,
        "native_helper_compile_success_count": metrics.native_helper_compile_success_count,
        "native_helper_evaluation_count": metrics.native_helper_evaluation_count,
        "native_helper_interpreter_confirmation_count": metrics.native_helper_interpreter_confirmation_count,
        "native_helper_trusted_true_count": metrics.native_helper_trusted_true_count,
        "native_helper_deopt_count": metrics.native_helper_deopt_count,
        "native_helper_fallback_count": metrics.native_helper_fallback_count,
        "native_helper_missing_var_fallback_count": metrics.native_helper_missing_var_fallback_count,
    })
}

/// Convert a gate failure to the JSON shape used by gate reports.
pub fn gate_failure_to_json_value(failure: &GateFailure) -> Value {
    serde_json::json!({
        "kind": failure.kind,
        "failure_mode": failure.failure_mode,
        "detail": failure.detail,
    })
}

/// Convert a gate decision to the JSON shape used by gate reports.
pub fn gate_decision_to_json_value(decision: &GateDecision) -> Value {
    serde_json::json!({
        "status": decision.status,
        "track": decision.track,
        "artifact": decision.artifact,
        "candidate_mode": decision.candidate_mode,
        "recommended_mode": decision.recommended_mode,
        "native_dispatch": decision.native_dispatch,
        "failures": decision.failures.iter().map(gate_failure_to_json_value).collect::<Vec<_>>(),
        "baseline": gate_metrics_to_json_value(&decision.baseline),
        "candidate": gate_metrics_to_json_value(&decision.candidate),
    })
}

/// Convert a gate decision to stable pretty-printed JSON.
pub fn gate_decision_to_json_string(decision: &GateDecision) -> GateResult<String> {
    serde_json::to_string_pretty(&gate_decision_to_json_value(decision))
        .map(|mut text| {
            text.push('\n');
            text
        })
        .map_err(|err| CompetitionJitGateError::new(err.to_string()))
}

fn parse_modes(raw: &JsonMap<String, Value>) -> GateResult<BTreeMap<String, JitModeConfig>> {
    let mut modes = BTreeMap::new();
    for (name, value) in raw {
        let context = format!("modes.{name}");
        let object = value
            .as_object()
            .ok_or_else(|| CompetitionJitGateError::new(format!("{context} must be an object")))?;
        modes.insert(
            name.clone(),
            JitModeConfig {
                native_dispatch: required_bool(object, "native_dispatch", &context)?,
                description: required_string(object, "description", &context)?,
            },
        );
    }
    Ok(modes)
}

fn parse_solve_control_plane(raw: &JsonMap<String, Value>) -> GateResult<SolveControlPlane> {
    let version = required_i64(raw, "version", "solve_control_plane")?;
    let vocabulary = parse_vocabulary(required_object(raw, "vocabulary", "solve_control_plane")?)?;
    let tracks = parse_control_tracks(required_object(raw, "tracks", "solve_control_plane")?)?;
    Ok(SolveControlPlane {
        version,
        vocabulary,
        tracks,
    })
}

fn parse_vocabulary(
    raw: &JsonMap<String, Value>,
) -> GateResult<BTreeMap<String, ControlPlaneVocabularyEntry>> {
    let mut vocabulary = BTreeMap::new();
    for (name, value) in raw {
        let context = format!("solve_control_plane.vocabulary.{name}");
        let object = value
            .as_object()
            .ok_or_else(|| CompetitionJitGateError::new(format!("{context} must be an object")))?;
        vocabulary.insert(
            name.clone(),
            ControlPlaneVocabularyEntry {
                description: required_string(object, "description", &context)?,
                mode_values: optional_string_array(object, "mode_values", &context)?,
                decision_fields: required_string_array(object, "decision_fields", &context)?,
            },
        );
    }
    Ok(vocabulary)
}

fn parse_control_tracks(
    raw: &JsonMap<String, Value>,
) -> GateResult<BTreeMap<String, ControlPlaneTrack>> {
    let mut tracks = BTreeMap::new();
    for (name, value) in raw {
        let context = format!("solve_control_plane.tracks.{name}");
        let object = value
            .as_object()
            .ok_or_else(|| CompetitionJitGateError::new(format!("{context} must be an object")))?;
        tracks.insert(
            name.clone(),
            ControlPlaneTrack {
                runtime_modes: required_string_array(object, "runtime_modes", &context)?,
                mode_source: required_string(object, "mode_source", &context)?,
                guidance_artifacts: required_string_array(object, "guidance_artifacts", &context)?,
                telemetry_counters: required_string_array(object, "telemetry_counters", &context)?,
            },
        );
    }
    Ok(tracks)
}

fn parse_gate_defaults(raw: &JsonMap<String, Value>) -> GateResult<GateDefaults> {
    Ok(GateDefaults {
        wrong_answers_max: required_i64(raw, "wrong_answers_max", "gate_defaults")?,
        proof_failures_max: required_i64(raw, "proof_failures_max", "gate_defaults")?,
        witness_failures_max: required_i64(raw, "witness_failures_max", "gate_defaults")?,
        crashes_max: required_i64(raw, "crashes_max", "gate_defaults")?,
        solved_count_loss_max: required_i64(raw, "solved_count_loss_max", "gate_defaults")?,
        par2_loss_max_sec: required_f64(raw, "par2_loss_max_sec", "gate_defaults")?,
        min_useful_applications: required_i64(raw, "min_useful_applications", "gate_defaults")?,
        integrity_failure_mode: optional_string(raw, "integrity_failure_mode")
            .unwrap_or_else(|| "off".to_string()),
        performance_failure_mode: optional_string(raw, "performance_failure_mode")
            .unwrap_or_else(|| "profile-only".to_string()),
    })
}

fn parse_tracks(raw: &JsonMap<String, Value>) -> GateResult<BTreeMap<String, CompetitionTrack>> {
    let mut tracks = BTreeMap::new();
    for (name, value) in raw {
        let context = format!("tracks.{name}");
        let object = value
            .as_object()
            .ok_or_else(|| CompetitionJitGateError::new(format!("{context} must be an object")))?;
        tracks.insert(
            name.clone(),
            CompetitionTrack {
                competition: required_string(object, "competition", &context)?,
                evals: required_string_array(object, "evals", &context)?,
                artifacts: parse_artifacts(required_array(object, "artifacts", &context)?, name)?,
            },
        );
    }
    Ok(tracks)
}

fn parse_artifacts(raw: &[Value], track_name: &str) -> GateResult<Vec<JitArtifact>> {
    let mut artifacts = Vec::new();
    for (index, value) in raw.iter().enumerate() {
        let object = value.as_object().ok_or_else(|| {
            CompetitionJitGateError::new(format!(
                "tracks.{track_name}.artifacts[{index}] must be an object"
            ))
        })?;
        let id = required_string(
            object,
            "id",
            &format!("tracks.{track_name}.artifacts[{index}]"),
        )?;
        let context = format!("tracks.{track_name}.artifacts[{id}]");
        artifacts.push(JitArtifact {
            id,
            description: required_string(object, "description", &context)?,
            default_mode: required_string(object, "default_mode", &context)?,
            candidate_modes: required_string_array(object, "candidate_modes", &context)?,
            evidence_kind: required_string(object, "evidence_kind", &context)?,
            min_useful_applications: required_i64(object, "min_useful_applications", &context)?,
            application_counter: required_string(object, "application_counter", &context)?,
            native_dispatch_counters: parse_native_dispatch_counters(
                optional_object(object, "native_dispatch_counters"),
                &context,
            )?,
            gate: parse_gate_rules(required_object(object, "gate", &context)?, &context)?,
        });
    }
    Ok(artifacts)
}

fn parse_native_dispatch_counters(
    raw: Option<&JsonMap<String, Value>>,
    context: &str,
) -> GateResult<BTreeMap<String, NativeDispatchCounters>> {
    let mut counters = BTreeMap::new();
    let Some(raw) = raw else {
        return Ok(counters);
    };
    for (mode, value) in raw {
        let counter_context = format!("{context}.native_dispatch_counters[{mode:?}]");
        let object = value.as_object().ok_or_else(|| {
            CompetitionJitGateError::new(format!("{counter_context} must be an object"))
        })?;
        counters.insert(
            mode.clone(),
            NativeDispatchCounters {
                install_counter: required_string(object, "install_counter", &counter_context)?,
                apply_counter: required_string(object, "apply_counter", &counter_context)?,
            },
        );
    }
    Ok(counters)
}

fn parse_gate_rules(
    raw: &JsonMap<String, Value>,
    context: &str,
) -> GateResult<BTreeMap<String, GateRule>> {
    let mut rules = BTreeMap::new();
    for (name, value) in raw {
        let rule_context = format!("{context}.gate.{name}");
        let object = value.as_object().ok_or_else(|| {
            CompetitionJitGateError::new(format!("{rule_context} must be an object"))
        })?;
        rules.insert(
            name.clone(),
            GateRule {
                enabled: required_bool(object, "enabled", &rule_context)?,
                failure_mode: required_string(object, "failure_mode", &rule_context)?,
                description: optional_string(object, "description"),
            },
        );
    }
    Ok(rules)
}

fn required_object<'a>(
    object: &'a JsonMap<String, Value>,
    key: &str,
    context: &str,
) -> GateResult<&'a JsonMap<String, Value>> {
    object
        .get(key)
        .and_then(Value::as_object)
        .ok_or_else(|| CompetitionJitGateError::new(format!("{context}.{key} must be an object")))
}

fn optional_object<'a>(
    object: &'a JsonMap<String, Value>,
    key: &str,
) -> Option<&'a JsonMap<String, Value>> {
    object.get(key).and_then(Value::as_object)
}

fn required_array<'a>(
    object: &'a JsonMap<String, Value>,
    key: &str,
    context: &str,
) -> GateResult<&'a Vec<Value>> {
    object
        .get(key)
        .and_then(Value::as_array)
        .ok_or_else(|| CompetitionJitGateError::new(format!("{context}.{key} must be an array")))
}

fn required_string(
    object: &JsonMap<String, Value>,
    key: &str,
    context: &str,
) -> GateResult<String> {
    object
        .get(key)
        .and_then(Value::as_str)
        .map(ToString::to_string)
        .filter(|value| !value.is_empty())
        .ok_or_else(|| {
            CompetitionJitGateError::new(format!("{context}.{key} must be a non-empty string"))
        })
}

fn optional_string(object: &JsonMap<String, Value>, key: &str) -> Option<String> {
    object
        .get(key)
        .and_then(Value::as_str)
        .map(ToString::to_string)
}

fn required_string_array(
    object: &JsonMap<String, Value>,
    key: &str,
    context: &str,
) -> GateResult<Vec<String>> {
    let array = required_array(object, key, context)?;
    let mut values = Vec::with_capacity(array.len());
    for (index, value) in array.iter().enumerate() {
        let Some(text) = value.as_str() else {
            return Err(CompetitionJitGateError::new(format!(
                "{context}.{key}[{index}] must be a string"
            )));
        };
        values.push(text.to_string());
    }
    Ok(values)
}

fn optional_string_array(
    object: &JsonMap<String, Value>,
    key: &str,
    context: &str,
) -> GateResult<Vec<String>> {
    if object.get(key).is_none() {
        return Ok(Vec::new());
    }
    required_string_array(object, key, context)
}

fn required_bool(object: &JsonMap<String, Value>, key: &str, context: &str) -> GateResult<bool> {
    object
        .get(key)
        .and_then(Value::as_bool)
        .ok_or_else(|| CompetitionJitGateError::new(format!("{context}.{key} must be a boolean")))
}

fn required_i64(object: &JsonMap<String, Value>, key: &str, context: &str) -> GateResult<i64> {
    object
        .get(key)
        .and_then(as_int)
        .ok_or_else(|| CompetitionJitGateError::new(format!("{context}.{key} must be an integer")))
}

fn required_f64(object: &JsonMap<String, Value>, key: &str, context: &str) -> GateResult<f64> {
    object
        .get(key)
        .and_then(as_number)
        .ok_or_else(|| CompetitionJitGateError::new(format!("{context}.{key} must be numeric")))
}

fn is_mode(mode: &str) -> bool {
    JIT_MODES.contains(&mode)
}

fn is_native_mode(mode: &str) -> bool {
    NATIVE_JIT_MODES.contains(&mode)
}

fn is_failure_mode(mode: &str) -> bool {
    FAILURE_MODES.contains(&mode)
}

fn is_evidence_kind(kind: &str) -> bool {
    matches!(
        kind,
        EVIDENCE_PROFILE_ONLY | EVIDENCE_INTEGRATED_NATIVE_HELPER | EVIDENCE_SOLVER_PROGRAM_NATIVE
    )
}

fn native_evidence_kind_for_mode(mode: &str) -> &'static str {
    match mode {
        "current" => EVIDENCE_INTEGRATED_NATIVE_HELPER,
        "solver-program" => EVIDENCE_SOLVER_PROGRAM_NATIVE,
        _ => EVIDENCE_PROFILE_ONLY,
    }
}

fn selected_source<'a>(data: &'a Value, role: Option<&str>) -> Option<&'a JsonMap<String, Value>> {
    let root = data.as_object()?;
    if let Some(role) = role {
        if let Some(source) = root.get(role).and_then(Value::as_object) {
            return Some(source);
        }
    }
    Some(root)
}

fn flattened_summary_source(source: &JsonMap<String, Value>) -> JsonMap<String, Value> {
    let mut flattened = source.clone();
    for name in ["metrics", "totals", "counters"] {
        if let Some(nested) = source.get(name).and_then(Value::as_object) {
            for (key, value) in nested {
                flattened.insert(key.clone(), value.clone());
            }
        }
    }
    flattened
}

fn as_number(value: &Value) -> Option<f64> {
    match value {
        Value::Null => None,
        Value::String(text) if text.is_empty() => None,
        Value::String(text) => text.parse::<f64>().ok(),
        Value::Bool(flag) => Some(i32::from(*flag).into()),
        Value::Number(number) => number.as_f64(),
        _ => None,
    }
}

fn as_int(value: &Value) -> Option<i64> {
    as_number(value).map(|number| number as i64)
}

fn first_int(object: &JsonMap<String, Value>, names: &[&str]) -> Option<i64> {
    names
        .iter()
        .find_map(|name| object.get(*name).and_then(as_int))
}

fn first_float(object: &JsonMap<String, Value>, names: &[&str]) -> Option<f64> {
    names
        .iter()
        .find_map(|name| object.get(*name).and_then(as_number))
}

fn normalize_verdict(value: Option<&Value>) -> String {
    let token = value
        .and_then(|value| match value {
            Value::String(text) => Some(text.clone()),
            Value::Null => None,
            other => Some(other.to_string()),
        })
        .unwrap_or_default()
        .trim()
        .to_ascii_lowercase();
    match token.as_str() {
        "s satisfiable" | "satisfiable" => "sat".to_string(),
        "s unsatisfiable" | "unsatisfiable" => "unsat".to_string(),
        "optimum" | "optimum found" | "s optimum found" => "optimum".to_string(),
        "timeout" | "timed out" => "timeout".to_string(),
        "crash" | "crashed" | "segfault" | "sigbus" | "error" => "error".to_string(),
        _ => token,
    }
}

fn is_definitive(verdict: &str) -> bool {
    matches!(verdict, "sat" | "unsat" | "optimum")
}

fn looks_like_crash(item: &JsonMap<String, Value>, verdict: &str) -> bool {
    if matches!(verdict, "error" | "crash" | "segfault" | "sigbus") {
        return true;
    }
    item.get("exit_code")
        .and_then(as_int)
        .is_some_and(|exit_code| !matches!(exit_code, 0 | 10 | 20 | 30 | 124))
}

fn reports_invalid(item: &JsonMap<String, Value>, names: &[&str]) -> bool {
    for name in names {
        let Some(value) = item.get(*name) else {
            continue;
        };
        match value {
            Value::Bool(flag) => return !flag,
            Value::Number(_) => {
                if as_number(value).is_some_and(|number| number > 0.0) {
                    return true;
                }
            }
            _ => {
                let token = value_to_string(value)
                    .trim()
                    .to_ascii_lowercase()
                    .replace('-', "_");
                if matches!(
                    token.as_str(),
                    "bad"
                        | "broken"
                        | "error"
                        | "fail"
                        | "failed"
                        | "failure"
                        | "false"
                        | "invalid"
                        | "invalid_state"
                        | "missing"
                        | "missing_field"
                        | "missing_required"
                        | "mismatch"
                        | "rejected"
                        | "unexpected_present"
                        | "wrong"
                ) || token.starts_with("invalid")
                    || token.starts_with("fail")
                    || token.starts_with("reject")
                {
                    return true;
                }
            }
        }
    }
    false
}

fn metrics_from_comparisons(data: &JsonMap<String, Value>) -> GateMetrics {
    if let Some(comparison) = data.get("comparison").and_then(Value::as_object) {
        if let Some(disagreements) = first_int(
            comparison,
            &[
                "disagree",
                "disagreements",
                "wrong_answers",
                "soundness_failures",
            ],
        ) {
            return GateMetrics {
                wrong_answers: disagreements,
                ..GateMetrics::default()
            };
        }
    }

    let wrong_answers = data
        .get("comparisons")
        .and_then(Value::as_array)
        .map(|comparisons| {
            comparisons
                .iter()
                .filter_map(Value::as_object)
                .filter(|entry| comparison_entry_disagrees(entry))
                .count() as i64
        })
        .unwrap_or(0);

    GateMetrics {
        wrong_answers,
        ..GateMetrics::default()
    }
}

fn comparison_entry_disagrees(entry: &JsonMap<String, Value>) -> bool {
    if first_int(entry, &["disagree", "disagreements"]).is_some_and(|value| value != 0) {
        return true;
    }
    match entry.get("agreement") {
        Some(Value::Bool(flag)) => !flag,
        Some(value) => matches!(
            value_to_string(value)
                .trim()
                .to_ascii_lowercase()
                .replace('-', "_")
                .as_str(),
            "disagree" | "mismatch" | "different" | "wrong" | "false"
        ),
        None => false,
    }
}

fn metrics_from_items(data: &JsonMap<String, Value>) -> GateMetrics {
    let Some(items) = data
        .get("items")
        .or_else(|| data.get("benchmarks"))
        .and_then(Value::as_array)
    else {
        return GateMetrics::default();
    };

    let settings = data.get("settings").and_then(Value::as_object);
    let timeout_sec = settings
        .and_then(|settings| settings.get("timeout_sec"))
        .and_then(as_number)
        .or_else(|| data.get("timeout_sec").and_then(as_number));

    let mut wrong_answers = 0;
    let mut proof_failures = 0;
    let mut witness_failures = 0;
    let mut crashes = 0;
    let mut solved = 0;
    let mut par2 = timeout_sec.map(|_| 0.0);

    for item in items.iter().filter_map(Value::as_object) {
        let actual = normalize_verdict(
            item.get("result")
                .or_else(|| item.get("actual"))
                .or_else(|| item.get("ay_result"))
                .or_else(|| item.get("ay_actual"))
                .or_else(|| item.get("status")),
        );
        let expected = item
            .get("expected")
            .map(|expected| normalize_verdict(Some(expected)))
            .unwrap_or_default();
        let definitive = is_definitive(&actual);
        let is_wrong = definitive && !expected.is_empty() && expected != actual;
        if is_wrong {
            wrong_answers += 1;
        } else if definitive {
            solved += 1;
        }
        if looks_like_crash(item, &actual) {
            crashes += 1;
        }
        if reports_invalid(
            item,
            &[
                "proof_validity",
                "proof_status",
                "proof_result",
                "proof_valid",
                "proof_verified",
            ],
        ) {
            proof_failures += 1;
        }
        if reports_invalid(
            item,
            &[
                "witness_validity",
                "witness_status",
                "witness_result",
                "witness_valid",
                "witness_verified",
            ],
        ) {
            witness_failures += 1;
        }

        if let Some(timeout_sec) = timeout_sec {
            let elapsed = first_truthy_number(item, &["time_sec", "wall_time_sec", "elapsed_sec"])
                .unwrap_or(0.0);
            let par2_ref = par2.get_or_insert(0.0);
            if definitive && !is_wrong {
                *par2_ref += elapsed;
            } else {
                *par2_ref += 2.0 * timeout_sec;
            }
        }
    }

    GateMetrics {
        wrong_answers,
        proof_failures,
        witness_failures,
        crashes,
        solved: Some(solved),
        par2: par2.map(|value| (value * 1000.0).round() / 1000.0),
        ..GateMetrics::default()
    }
}

fn first_truthy_number(object: &JsonMap<String, Value>, names: &[&str]) -> Option<f64> {
    names
        .iter()
        .filter_map(|name| object.get(*name).and_then(as_number))
        .find(|value| *value != 0.0)
}

fn merge_metrics(primary: &GateMetrics, fallback: &GateMetrics) -> GateMetrics {
    GateMetrics {
        wrong_answers: if primary.wrong_answers != 0 {
            primary.wrong_answers
        } else {
            fallback.wrong_answers
        },
        proof_failures: if primary.proof_failures != 0 {
            primary.proof_failures
        } else {
            fallback.proof_failures
        },
        witness_failures: if primary.witness_failures != 0 {
            primary.witness_failures
        } else {
            fallback.witness_failures
        },
        crashes: if primary.crashes != 0 {
            primary.crashes
        } else {
            fallback.crashes
        },
        solved: primary.solved.or(fallback.solved),
        par2: primary.par2.or(fallback.par2),
        application_count: primary.application_count.or(fallback.application_count),
        native_install_count: primary
            .native_install_count
            .or(fallback.native_install_count),
        native_apply_count: primary.native_apply_count.or(fallback.native_apply_count),
        native_helper_compile_attempt_count: primary
            .native_helper_compile_attempt_count
            .or(fallback.native_helper_compile_attempt_count),
        native_helper_compile_success_count: primary
            .native_helper_compile_success_count
            .or(fallback.native_helper_compile_success_count),
        native_helper_evaluation_count: primary
            .native_helper_evaluation_count
            .or(fallback.native_helper_evaluation_count),
        native_helper_interpreter_confirmation_count: primary
            .native_helper_interpreter_confirmation_count
            .or(fallback.native_helper_interpreter_confirmation_count),
        native_helper_trusted_true_count: primary
            .native_helper_trusted_true_count
            .or(fallback.native_helper_trusted_true_count),
        native_helper_deopt_count: primary
            .native_helper_deopt_count
            .or(fallback.native_helper_deopt_count),
        native_helper_fallback_count: primary
            .native_helper_fallback_count
            .or(fallback.native_helper_fallback_count),
        native_helper_missing_var_fallback_count: primary
            .native_helper_missing_var_fallback_count
            .or(fallback.native_helper_missing_var_fallback_count),
    }
}

fn summary_application_counter_value(data: &JsonMap<String, Value>, name: &str) -> Option<Value> {
    if data
        .get("competition_jit_application_counter")
        .and_then(application_counter_metadata_key)
        .is_some_and(|key| key == name)
    {
        return data.get("competition_jit_application_count").cloned();
    }

    let envelope = data.get("competition_jit").and_then(Value::as_object)?;
    let value = envelope.get("application_counter")?;
    if application_counter_metadata_key(value).is_some_and(|key| key == name) {
        return application_counter_metadata_value(value);
    }
    None
}

fn application_counter_metadata_key(value: &Value) -> Option<&str> {
    match value {
        Value::Object(object) => object.get("key").and_then(Value::as_str),
        Value::String(text) => Some(text),
        _ => None,
    }
}

fn application_counter_metadata_value(value: &Value) -> Option<Value> {
    match value {
        Value::Object(object) => object.get("value").cloned(),
        _ => None,
    }
}

fn metadata_sources(data: &Value) -> Vec<&JsonMap<String, Value>> {
    let mut sources = Vec::new();
    let Some(root) = data.as_object() else {
        return sources;
    };
    sources.push(root);
    for name in [
        "competition_jit",
        "jit_metadata",
        "runtime-summary",
        "runtime_summary",
    ] {
        if let Some(object) = root.get(name).and_then(Value::as_object) {
            sources.push(object);
        }
    }
    if let Some(object) = root.get("mode").and_then(Value::as_object) {
        sources.push(object);
    }
    sources
}

fn find_metadata_field<'a>(data: &'a Value, names: &[&str]) -> Option<&'a Value> {
    metadata_sources(data)
        .into_iter()
        .find_map(|source| names.iter().find_map(|name| source.get(*name)))
}

fn value_to_string(value: &Value) -> String {
    match value {
        Value::String(text) => text.clone(),
        Value::Null => String::new(),
        other => other.to_string(),
    }
}

fn rule<'a>(artifact: &'a JitArtifact, name: &str) -> Option<&'a GateRule> {
    artifact.gate.get(name)
}

fn add_failure(
    failures: &mut Vec<GateFailure>,
    artifact: &JitArtifact,
    rule_name: &str,
    kind: &str,
    detail: String,
) {
    let Some(rule) = rule(artifact, rule_name) else {
        return;
    };
    if !rule.enabled && !is_integrity_failure(kind) {
        return;
    }
    failures.push(GateFailure {
        kind: kind.to_string(),
        failure_mode: safe_failure_mode(rule, kind),
        detail,
    });
}

fn safe_failure_mode(rule: &GateRule, kind: &str) -> String {
    if is_integrity_failure(kind) {
        return "off".to_string();
    }
    if is_failure_mode(&rule.failure_mode) {
        rule.failure_mode.clone()
    } else {
        "profile-only".to_string()
    }
}

fn is_integrity_failure(kind: &str) -> bool {
    INTEGRITY_FAILURES.contains(&kind)
}

fn native_dispatch_allowed(mode: &str, artifact: &JitArtifact) -> bool {
    is_native_mode(mode) && artifact.evidence_kind == native_evidence_kind_for_mode(mode)
}

fn required_application_minimum(
    mode: &str,
    artifact: &JitArtifact,
    configured_minimum: i64,
) -> i64 {
    if native_dispatch_allowed(mode, artifact) {
        configured_minimum.max(1)
    } else {
        configured_minimum
    }
}

fn native_dispatch_counter_failure(
    kind: &str,
    mode: &str,
    counter: &str,
    value: Option<i64>,
) -> GateFailure {
    let actual = value
        .map(|value| value.to_string())
        .unwrap_or_else(|| "missing".to_string());
    GateFailure {
        kind: kind.to_string(),
        failure_mode: "profile-only".to_string(),
        detail: format!(
            "{mode:?} native dispatch requires positive {counter:?} evidence, got {actual}"
        ),
    }
}

fn profile_only_failure(kind: &str, detail: String) -> GateFailure {
    GateFailure {
        kind: kind.to_string(),
        failure_mode: "profile-only".to_string(),
        detail,
    }
}

fn positive_counter_gate_failure(kind: &str, label: &str, value: Option<i64>) -> GateFailure {
    let actual = value
        .map(|value| value.to_string())
        .unwrap_or_else(|| "missing".to_string());
    profile_only_failure(
        kind,
        format!("candidate {label} evidence must be > 0, got {actual}"),
    )
}

fn zero_counter_gate_failure(kind: &str, label: &str, value: Option<i64>) -> GateFailure {
    let actual = value
        .map(|value| value.to_string())
        .unwrap_or_else(|| "missing".to_string());
    profile_only_failure(
        kind,
        format!("candidate {label} evidence must be 0, got {actual}"),
    )
}

fn validate_chc_native_helper_current_gate(
    failures: &mut Vec<GateFailure>,
    candidate: &GateMetrics,
) {
    let Some(applications) = candidate.application_count else {
        return;
    };
    if applications <= 0 {
        return;
    }

    for (kind, label, value) in [
        (
            "native-helper-compile-attempt",
            "CHC native-helper compile attempt",
            candidate.native_helper_compile_attempt_count,
        ),
        (
            "native-helper-compile-success",
            "CHC native-helper compile success",
            candidate.native_helper_compile_success_count,
        ),
        (
            "native-helper-evaluation-evidence",
            "CHC native-helper evaluation",
            candidate.native_helper_evaluation_count,
        ),
    ] {
        if value.is_none_or(|value| value <= 0) {
            failures.push(positive_counter_gate_failure(kind, label, value));
        }
    }

    let confirmations = candidate
        .native_helper_interpreter_confirmation_count
        .unwrap_or(0);
    let trusted_true = candidate.native_helper_trusted_true_count.unwrap_or(0);
    let accepted_true_results = confirmations + trusted_true;
    if accepted_true_results <= 0 {
        failures.push(profile_only_failure(
            "native-helper-accepted-true",
            format!(
                "candidate CHC native-helper accepted true evidence must be > 0, got interpreter_confirmations={confirmations}, trusted_true={trusted_true}"
            ),
        ));
    }
    if accepted_true_results != applications {
        failures.push(profile_only_failure(
            "native-helper-accepted-true",
            format!(
                "candidate CHC native-helper interpreter confirmations plus trusted true results must equal useful applications {applications}, got {accepted_true_results}"
            ),
        ));
    }

    for (kind, label, value) in [
        (
            "native-helper-deopt",
            "CHC native-helper deopt",
            candidate.native_helper_deopt_count,
        ),
        (
            "native-helper-fallback",
            "CHC native-helper fallback",
            candidate.native_helper_fallback_count,
        ),
        (
            "native-helper-missing-var-fallback",
            "CHC native-helper missing-var fallback",
            candidate.native_helper_missing_var_fallback_count,
        ),
    ] {
        if value != Some(0) {
            failures.push(zero_counter_gate_failure(kind, label, value));
        }
    }
}
