// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Competition JIT release report validation and generation support.
//!
//! This module intentionally contains no CLI wiring. It mirrors the
//! machine-checkable release-report invariants and provenance checks for the
//! product CLI, while leaving gate-decision recomputation behind an explicit
//! hook API.

#![allow(dead_code, unreachable_pub)]

use crate::competition_jit_gate;

use serde_json::{Map, Value};
use sha2::{Digest, Sha256};
use std::error::Error;
use std::fmt;
use std::fs;
use std::io::{self, Read};
use std::path::{Path, PathBuf};
use std::process::Command;

#[cfg(unix)]
use std::ffi::OsString;
#[cfg(unix)]
use std::os::unix::ffi::{OsStrExt, OsStringExt};
#[cfg(unix)]
use std::os::unix::fs::PermissionsExt;

const CHUNK_SIZE: usize = 1024 * 1024;

/// Release-report schema string used by the competition JIT gate.
pub const RELEASE_REPORT_SCHEMA: &str = "ay.competition-jit-release-report/v1";

/// Tracks accepted by competition JIT release reports.
pub const RELEASE_REPORT_TRACKS: &[&str] = &["sat", "smt", "pb", "chc"];

/// Release status values accepted by the report validator.
pub const RELEASE_REPORT_STATUSES: &[&str] = &["ready", "profile-only", "fail-closed"];

/// JIT modes accepted by the gate matrix.
pub const MODES: &[&str] = &["off", "current", "solver-program", "profile-only"];

const FAILURE_MODES: &[&str] = &["off", "profile-only"];
const RELEASE_REPORT_STEP_STATUSES: &[&str] = &["pass"];
const RELEASE_REPORT_BLOCKING_FAILURES: &[&str] = &[
    "wrong-answer",
    "proof-failure",
    "witness-failure",
    "crash",
    "solved-count-loss",
    "par2-loss",
];

/// Errors produced while generating or validating a release report.
#[derive(Debug)]
pub enum ReleaseReportError {
    /// An I/O operation failed.
    Io {
        /// Human-readable operation context.
        context: String,
        /// Underlying I/O error.
        source: io::Error,
    },
    /// JSON parsing or serialization failed.
    Json {
        /// Human-readable operation context.
        context: String,
        /// Underlying JSON error.
        source: serde_json::Error,
    },
    /// A git command needed for provenance failed.
    Git {
        /// The git command arguments, excluding the leading `git`.
        args: Vec<String>,
        /// The stderr detail, if git provided one.
        detail: String,
    },
    /// The report was well-formed JSON but failed release validation.
    Validation {
        /// Optional report path attached to diagnostics.
        path: Option<PathBuf>,
        /// Individual validation failures.
        errors: Vec<String>,
    },
}

impl ReleaseReportError {
    fn io(context: impl Into<String>, source: io::Error) -> Self {
        Self::Io {
            context: context.into(),
            source,
        }
    }

    fn json(context: impl Into<String>, source: serde_json::Error) -> Self {
        Self::Json {
            context: context.into(),
            source,
        }
    }

    fn validation(path: Option<PathBuf>, errors: Vec<String>) -> Self {
        Self::Validation { path, errors }
    }
}

impl fmt::Display for ReleaseReportError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io { context, source } => write!(formatter, "{context}: {source}"),
            Self::Json { context, source } => write!(formatter, "{context}: {source}"),
            Self::Git { args, detail } => {
                if detail.is_empty() {
                    write!(formatter, "git {} failed", args.join(" "))
                } else {
                    write!(formatter, "git {} failed: {detail}", args.join(" "))
                }
            }
            Self::Validation { path, errors } => {
                if let Some(path) = path {
                    write!(
                        formatter,
                        "{} release report validation failed: {}",
                        path.display(),
                        errors.join("; ")
                    )
                } else {
                    write!(
                        formatter,
                        "release report validation failed: {}",
                        errors.join("; ")
                    )
                }
            }
        }
    }
}

impl Error for ReleaseReportError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Io { source, .. } => Some(source),
            Self::Json { source, .. } => Some(source),
            Self::Git { .. } | Self::Validation { .. } => None,
        }
    }
}

/// Options shared by release-report generation and validation.
#[derive(Debug, Clone)]
pub struct ReleaseReportOptions {
    /// Repository root used for relative path display and git provenance.
    pub repo_root: PathBuf,
    /// Checked-in JIT mode matrix path.
    pub matrix_path: PathBuf,
    /// Optional checked-in schema path. If absent, it is derived from `matrix_path`.
    pub matrix_schema_path: Option<PathBuf>,
    /// Whether validation recomputes and checks current git worktree provenance.
    pub verify_source: bool,
}

impl ReleaseReportOptions {
    /// Build options for a repository root and JIT matrix path.
    pub fn new(repo_root: impl Into<PathBuf>, matrix_path: impl Into<PathBuf>) -> Self {
        Self {
            repo_root: repo_root.into(),
            matrix_path: matrix_path.into(),
            matrix_schema_path: None,
            verify_source: true,
        }
    }

    /// Return the configured or derived matrix schema path.
    pub fn effective_matrix_schema_path(&self) -> PathBuf {
        self.matrix_schema_path
            .clone()
            .unwrap_or_else(|| matrix_schema_path(&self.matrix_path))
    }
}

/// Git worktree provenance embedded in generated release reports.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceProvenance {
    /// Provenance kind. Release reports use `git-worktree`.
    pub kind: String,
    /// Current `HEAD` commit.
    pub git_commit: String,
    /// Current branch name.
    pub git_branch: String,
    /// Whether `git status --porcelain=v1 --untracked-files=all` is non-empty.
    pub git_dirty: bool,
    /// SHA-256 of raw porcelain status bytes.
    pub git_status_sha256: String,
    /// SHA-256 binding commit, status, diffs, and untracked file contents.
    pub source_tree_sha256: String,
}

impl SourceProvenance {
    /// Convert this provenance object into the report JSON shape.
    pub fn to_json(&self) -> Value {
        let mut object = Map::new();
        object.insert("kind".to_string(), Value::String(self.kind.clone()));
        object.insert(
            "git_commit".to_string(),
            Value::String(self.git_commit.clone()),
        );
        object.insert(
            "git_branch".to_string(),
            Value::String(self.git_branch.clone()),
        );
        object.insert("git_dirty".to_string(), Value::Bool(self.git_dirty));
        object.insert(
            "git_status_sha256".to_string(),
            Value::String(self.git_status_sha256.clone()),
        );
        object.insert(
            "source_tree_sha256".to_string(),
            Value::String(self.source_tree_sha256.clone()),
        );
        Value::Object(object)
    }
}

/// A completed package or replay step to embed in a release report.
#[derive(Debug, Clone)]
pub struct ReleaseStepInput {
    /// Shell-display command string.
    pub command: String,
    /// Step status. Release reports accept only `pass`.
    pub status: String,
    /// Process exit code. Release reports require zero.
    pub exit_code: i64,
    /// Path to the captured step log.
    pub log_path: PathBuf,
    /// Optional package artifact path; required for the package step.
    pub artifact_path: Option<PathBuf>,
}

impl ReleaseStepInput {
    /// Construct a passing step from a command string, exit code, and log path.
    pub fn new(command: impl Into<String>, exit_code: i64, log_path: impl Into<PathBuf>) -> Self {
        Self {
            command: command.into(),
            status: "pass".to_string(),
            exit_code,
            log_path: log_path.into(),
            artifact_path: None,
        }
    }

    /// Attach a package artifact path to this step.
    pub fn with_artifact(mut self, artifact_path: impl Into<PathBuf>) -> Self {
        self.artifact_path = Some(artifact_path.into());
        self
    }
}

/// Inputs needed to build a release report JSON object.
#[derive(Debug, Clone)]
pub struct ReleaseReportBuildInput {
    /// Shared report options.
    pub options: ReleaseReportOptions,
    /// UTC timestamp string to place in `generated_at_utc`.
    pub generated_at_utc: String,
    /// Track name: `sat`, `smt`, `pb`, or `chc`.
    pub track: String,
    /// Optional explicit release status. If absent, it is derived from the gate payload.
    pub release_status: Option<String>,
    /// Package step evidence.
    pub package: ReleaseStepInput,
    /// Replay step evidence.
    pub replay: ReleaseStepInput,
    /// Gate decision payload generated by the competition JIT gate.
    pub gate: Value,
}

/// Summary returned after successful release-report validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ReleaseReportSummary {
    /// Release-report schema string.
    pub schema: String,
    /// Validation status. Successful validation returns `pass`.
    pub status: String,
    /// Reported release status.
    pub release_status: String,
    /// Competition track.
    pub track: String,
    /// JIT artifact id.
    pub artifact: String,
    /// Candidate mode evaluated by the gate.
    pub candidate_mode: String,
    /// Recomputed recommended mode.
    pub recommended_mode: String,
    /// Recomputed native dispatch decision.
    pub native_dispatch: bool,
    /// Package step status.
    pub package: String,
    /// Replay step status.
    pub replay: String,
}

/// Snapshot returned by the gate hook after recomputing a report's gate payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateDecisionSnapshot {
    /// Recomputed gate status.
    pub status: String,
    /// Recomputed track.
    pub track: String,
    /// Recomputed artifact id.
    pub artifact: String,
    /// Candidate mode evaluated by the gate.
    pub candidate_mode: String,
    /// Recomputed recommended mode.
    pub recommended_mode: String,
    /// Recomputed native dispatch decision.
    pub native_dispatch: bool,
    /// Recomputed failure kinds, in report order.
    pub failure_kinds: Vec<String>,
    /// Candidate useful application count, if present in the gate evidence.
    pub candidate_application_count: Option<i64>,
}

impl GateDecisionSnapshot {
    /// Parse a snapshot directly from a reported gate payload.
    ///
    /// This is useful for tests and for wiring an external gate module into the
    /// release validator. Production readiness gates should recompute this
    /// snapshot from matrix rules and metrics before returning it.
    pub fn from_gate_payload(gate: &Value) -> Result<Self, Vec<String>> {
        let Some(raw_gate) = gate.as_object() else {
            return Err(vec!["gate must be an object".to_string()]);
        };

        let mut errors = Vec::new();
        let status = required_string(raw_gate, "status", "gate.status", &mut errors);
        let track = required_string(raw_gate, "track", "gate.track", &mut errors);
        let artifact = required_string(raw_gate, "artifact", "gate.artifact", &mut errors);
        let candidate_mode = required_string(
            raw_gate,
            "candidate_mode",
            "gate.candidate_mode",
            &mut errors,
        );
        let recommended_mode = required_string(
            raw_gate,
            "recommended_mode",
            "gate.recommended_mode",
            &mut errors,
        );
        let native_dispatch = required_bool(
            raw_gate,
            "native_dispatch",
            "gate.native_dispatch",
            &mut errors,
        );
        let (failure_kinds, failure_errors) = gate_failure_kinds(raw_gate.get("failures"), "gate");
        errors.extend(failure_errors);

        let candidate_application_count = raw_gate
            .get("candidate")
            .and_then(Value::as_object)
            .and_then(|candidate| as_i64_like(candidate.get("application_count")));

        if errors.is_empty() {
            Ok(Self {
                status,
                track,
                artifact,
                candidate_mode,
                recommended_mode,
                native_dispatch,
                failure_kinds,
                candidate_application_count,
            })
        } else {
            Err(errors)
        }
    }
}

/// Gate hook used by release-report validation.
///
/// The release module owns schema, provenance, hash, step, and status checks.
/// The gate module owns recomputing the JIT gate decision from the matrix and
/// reported metrics, then returning the fields that must match the report.
pub trait GateModule {
    /// Recompute or validate the gate payload embedded in `report`.
    fn evaluate_release_gate(
        &self,
        report: &Map<String, Value>,
        matrix: &Map<String, Value>,
    ) -> Result<GateDecisionSnapshot, Vec<String>>;
}

/// Structural gate hook that trusts the report's own gate payload.
///
/// This hook is intentionally weaker than the Python gate evaluator because it
/// does not recompute matrix policy. It is useful for exercising the release
/// validator around a separately recomputed payload.
#[derive(Debug, Default, Clone, Copy)]
pub struct ReportedGateModule;

impl GateModule for ReportedGateModule {
    fn evaluate_release_gate(
        &self,
        report: &Map<String, Value>,
        _matrix: &Map<String, Value>,
    ) -> Result<GateDecisionSnapshot, Vec<String>> {
        match report.get("gate") {
            Some(gate) => GateDecisionSnapshot::from_gate_payload(gate),
            None => Err(vec!["gate must be an object".to_string()]),
        }
    }
}

/// Gate hook that recomputes release readiness through the Rust matrix gate.
#[derive(Debug, Default, Clone, Copy)]
pub struct RecomputedGateModule;

impl GateModule for RecomputedGateModule {
    fn evaluate_release_gate(
        &self,
        report: &Map<String, Value>,
        matrix: &Map<String, Value>,
    ) -> Result<GateDecisionSnapshot, Vec<String>> {
        let raw_gate = report
            .get("gate")
            .and_then(Value::as_object)
            .ok_or_else(|| vec!["gate must be an object".to_string()])?;
        let track = report
            .get("track")
            .and_then(Value::as_str)
            .or_else(|| raw_gate.get("track").and_then(Value::as_str))
            .ok_or_else(|| vec!["track must be a non-empty string".to_string()])?;
        let artifact = raw_gate
            .get("artifact")
            .and_then(Value::as_str)
            .ok_or_else(|| vec!["gate.artifact must be a non-empty string".to_string()])?;
        let candidate_mode = raw_gate
            .get("candidate_mode")
            .and_then(Value::as_str)
            .ok_or_else(|| vec!["gate.candidate_mode must be a non-empty string".to_string()])?;
        let matrix_value = Value::Object(matrix.clone());
        let typed_matrix = competition_jit_gate::parse_matrix_value(&matrix_value)
            .and_then(|matrix| {
                competition_jit_gate::validate_matrix_invariants(&matrix).map(|()| matrix)
            })
            .map_err(|error| vec![format!("matrix could not be parsed: {error}")])?;
        let baseline = gate_metrics_from_release_payload(raw_gate, "baseline")?;
        let candidate = gate_metrics_from_release_payload(raw_gate, "candidate")?;
        let decision = competition_jit_gate::evaluate_gate(
            &typed_matrix,
            track,
            artifact,
            baseline,
            candidate,
            Some(candidate_mode),
        )
        .map_err(|error| vec![format!("gate could not be recomputed: {error}")])?;
        Ok(GateDecisionSnapshot {
            status: decision.status,
            track: decision.track,
            artifact: decision.artifact,
            candidate_mode: decision.candidate_mode,
            recommended_mode: decision.recommended_mode,
            native_dispatch: decision.native_dispatch,
            failure_kinds: decision
                .failures
                .iter()
                .map(|failure| failure.kind.clone())
                .collect(),
            candidate_application_count: decision.candidate.application_count,
        })
    }
}

fn gate_metrics_from_release_payload(
    raw_gate: &Map<String, Value>,
    role: &str,
) -> Result<competition_jit_gate::GateMetrics, Vec<String>> {
    let metrics = raw_gate
        .get(role)
        .and_then(Value::as_object)
        .ok_or_else(|| vec![format!("gate.{role} must be an object")])?;
    Ok(competition_jit_gate::GateMetrics {
        wrong_answers: gate_metric_i64(metrics, "wrong_answers").unwrap_or(0),
        proof_failures: gate_metric_i64(metrics, "proof_failures").unwrap_or(0),
        witness_failures: gate_metric_i64(metrics, "witness_failures").unwrap_or(0),
        crashes: gate_metric_i64(metrics, "crashes").unwrap_or(0),
        solved: gate_metric_i64(metrics, "solved"),
        par2: gate_metric_f64(metrics, "par2"),
        application_count: gate_metric_i64(metrics, "application_count"),
        native_install_count: gate_metric_i64(metrics, "native_install_count"),
        native_apply_count: gate_metric_i64(metrics, "native_apply_count"),
        native_helper_compile_attempt_count: gate_metric_i64(
            metrics,
            "native_helper_compile_attempt_count",
        ),
        native_helper_compile_success_count: gate_metric_i64(
            metrics,
            "native_helper_compile_success_count",
        ),
        native_helper_evaluation_count: gate_metric_i64(metrics, "native_helper_evaluation_count"),
        native_helper_interpreter_confirmation_count: gate_metric_i64(
            metrics,
            "native_helper_interpreter_confirmation_count",
        ),
        native_helper_trusted_true_count: gate_metric_i64(
            metrics,
            "native_helper_trusted_true_count",
        ),
        native_helper_deopt_count: gate_metric_i64(metrics, "native_helper_deopt_count"),
        native_helper_fallback_count: gate_metric_i64(metrics, "native_helper_fallback_count"),
        native_helper_missing_var_fallback_count: gate_metric_i64(
            metrics,
            "native_helper_missing_var_fallback_count",
        ),
    })
}

fn gate_metric_i64(metrics: &Map<String, Value>, field: &str) -> Option<i64> {
    as_i64_like(gate_metric_value(metrics, field))
}

fn gate_metric_f64(metrics: &Map<String, Value>, field: &str) -> Option<f64> {
    as_f64_like(gate_metric_value(metrics, field))
}

fn gate_metric_value<'a>(metrics: &'a Map<String, Value>, field: &str) -> Option<&'a Value> {
    metrics
        .get(field)
        .or_else(|| {
            metrics
                .get("metrics")
                .and_then(Value::as_object)
                .and_then(|nested| nested.get(field))
        })
        .or_else(|| {
            metrics
                .get("totals")
                .and_then(Value::as_object)
                .and_then(|nested| nested.get(field))
        })
}

/// Return the matrix schema path corresponding to a matrix path.
pub fn matrix_schema_path(matrix_path: &Path) -> PathBuf {
    let Some(name) = matrix_path.file_name().and_then(|name| name.to_str()) else {
        return matrix_path.with_extension("schema.json");
    };
    if let Some(prefix) = name.strip_suffix(".json") {
        matrix_path.with_file_name(format!("{prefix}.schema.json"))
    } else {
        let suffix = matrix_path
            .extension()
            .and_then(|extension| extension.to_str())
            .map(|extension| format!("{extension}.schema.json"))
            .unwrap_or_else(|| "schema.json".to_string());
        matrix_path.with_extension(suffix)
    }
}

/// Display a path relative to `repo_root` when possible.
pub fn display_path(repo_root: &Path, path: &Path) -> String {
    let root = absolute_path(Path::new("."), repo_root);
    let absolute = absolute_path(&root, path);
    match absolute.strip_prefix(&root) {
        Ok(relative) if !relative.as_os_str().is_empty() => path_to_posix_lossy(relative),
        _ => path_to_posix_lossy(path),
    }
}

/// Compute a lowercase SHA-256 hex digest for a file.
pub fn sha256_file(path: &Path) -> Result<String, ReleaseReportError> {
    let mut file = fs::File::open(path)
        .map_err(|source| ReleaseReportError::io(format!("open {}", path.display()), source))?;
    let mut digest = Sha256::new();
    let mut buffer = vec![0; CHUNK_SIZE];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|source| ReleaseReportError::io(format!("read {}", path.display()), source))?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    let bytes = digest.finalize();
    Ok(hex_digest(&bytes))
}

/// Compute the release-report SHA-256 for a file or directory.
///
/// Directory hashes match the Python gate: sorted relative entries, explicit
/// record tags for symlink/directory/file, file mode bits, file contents, and
/// NUL separators.
pub fn sha256_path(path: &Path) -> Result<String, ReleaseReportError> {
    if path.is_file() {
        return sha256_file(path);
    }
    if !path.is_dir() {
        return Err(ReleaseReportError::validation(
            None,
            vec![format!(
                "artifact path is not a file or directory: {}",
                path.display()
            )],
        ));
    }

    let mut entries = Vec::new();
    collect_descendants(path, path, &mut entries)?;
    entries.sort_by(|left, right| {
        relative_posix(path, left)
            .unwrap_or_else(|_| path_to_posix_lossy(left))
            .cmp(&relative_posix(path, right).unwrap_or_else(|_| path_to_posix_lossy(right)))
    });

    let mut digest = Sha256::new();
    for entry in entries {
        let relative = relative_posix(path, &entry)?;
        let relative_bytes = relative.as_bytes();
        let metadata = fs::symlink_metadata(&entry).map_err(|source| {
            ReleaseReportError::io(format!("stat {}", entry.display()), source)
        })?;
        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            digest.update(b"L\0");
            digest.update(relative_bytes);
            digest.update(b"\0");
            let target = fs::read_link(&entry).map_err(|source| {
                ReleaseReportError::io(format!("readlink {}", entry.display()), source)
            })?;
            digest.update(path_os_bytes(&target));
            digest.update(b"\0");
        } else if file_type.is_dir() {
            digest.update(b"D\0");
            digest.update(relative_bytes);
            digest.update(b"\0");
        } else if file_type.is_file() {
            digest.update(b"F\0");
            digest.update(relative_bytes);
            digest.update(b"\0");
            digest.update(format!("0o{:o}", file_mode_bits(&metadata)).as_bytes());
            digest.update(b"\0");
            update_digest_from_file(&mut digest, &entry)?;
            digest.update(b"\0");
        }
    }

    let bytes = digest.finalize();
    Ok(hex_digest(&bytes))
}

/// Run git and return stdout bytes from `repo_root`.
pub fn git_bytes(repo_root: &Path, args: &[&str]) -> Result<Vec<u8>, ReleaseReportError> {
    let completed = Command::new("git")
        .args(args)
        .current_dir(repo_root)
        .output()
        .map_err(|source| ReleaseReportError::io("spawn git", source))?;
    if completed.status.success() {
        return Ok(completed.stdout);
    }

    let detail = String::from_utf8_lossy(&completed.stderr)
        .trim()
        .to_string();
    Err(ReleaseReportError::Git {
        args: args.iter().map(|arg| (*arg).to_string()).collect(),
        detail,
    })
}

/// Compute the git worktree source-tree SHA-256 used in release reports.
pub fn source_tree_sha256(
    repo_root: &Path,
    commit: &str,
    status: &[u8],
) -> Result<String, ReleaseReportError> {
    let mut digest = Sha256::new();
    digest.update(b"commit\0");
    digest.update(commit.as_bytes());
    digest.update(b"\0status\0");
    digest.update(status);
    digest.update(b"\0diff-head\0");
    digest.update(git_bytes(
        repo_root,
        &["diff", "--binary", "--no-ext-diff", "HEAD", "--"],
    )?);
    digest.update(b"\0diff-cached\0");
    digest.update(git_bytes(
        repo_root,
        &["diff", "--binary", "--cached", "--no-ext-diff", "--"],
    )?);
    digest.update(b"\0untracked\0");

    let mut untracked = git_bytes(
        repo_root,
        &["ls-files", "--others", "--exclude-standard", "-z"],
    )?
    .split(|byte| *byte == 0)
    .filter(|item| !item.is_empty())
    .map(<[u8]>::to_vec)
    .collect::<Vec<_>>();
    untracked.sort();

    for relative in untracked {
        let path = repo_root.join(path_from_git_bytes(&relative));
        let metadata = match fs::symlink_metadata(&path) {
            Ok(metadata) => metadata,
            Err(source) if source.kind() == io::ErrorKind::NotFound => continue,
            Err(source) => {
                return Err(ReleaseReportError::io(
                    format!("stat {}", path.display()),
                    source,
                ));
            }
        };
        let file_type = metadata.file_type();
        if file_type.is_symlink() {
            digest.update(b"L\0");
            digest.update(&relative);
            digest.update(b"\0");
            let target = fs::read_link(&path).map_err(|source| {
                ReleaseReportError::io(format!("readlink {}", path.display()), source)
            })?;
            digest.update(path_os_bytes(&target));
            digest.update(b"\0");
        } else if file_type.is_dir() {
            digest.update(b"D\0");
            digest.update(&relative);
            digest.update(b"\0");
        } else if file_type.is_file() {
            digest.update(b"F\0");
            digest.update(&relative);
            digest.update(b"\0");
            digest.update(format!("0o{:o}", file_mode_bits(&metadata)).as_bytes());
            digest.update(b"\0");
            update_digest_from_file(&mut digest, &path)?;
            digest.update(b"\0");
        }
    }

    let bytes = digest.finalize();
    Ok(hex_digest(&bytes))
}

/// Recompute current git worktree provenance for a release report.
pub fn current_source_provenance(repo_root: &Path) -> Result<SourceProvenance, ReleaseReportError> {
    let commit = String::from_utf8_lossy(&git_bytes(repo_root, &["rev-parse", "HEAD"])?)
        .trim()
        .to_string();
    let branch = String::from_utf8_lossy(&git_bytes(
        repo_root,
        &["rev-parse", "--abbrev-ref", "HEAD"],
    )?)
    .trim()
    .to_string();
    let status = git_bytes(
        repo_root,
        &["status", "--porcelain=v1", "--untracked-files=all"],
    )?;
    Ok(SourceProvenance {
        kind: "git-worktree".to_string(),
        git_commit: commit.clone(),
        git_branch: branch,
        git_dirty: !status.is_empty(),
        git_status_sha256: sha256_bytes(&status),
        source_tree_sha256: source_tree_sha256(repo_root, &commit, &status)?,
    })
}

/// Build the JSON object for one package or replay step.
pub fn build_report_step(
    repo_root: &Path,
    step: &ReleaseStepInput,
) -> Result<Value, ReleaseReportError> {
    let mut object = Map::new();
    object.insert("command".to_string(), Value::String(step.command.clone()));
    object.insert("status".to_string(), Value::String(step.status.clone()));
    object.insert(
        "exit_code".to_string(),
        Value::Number(serde_json::Number::from(step.exit_code)),
    );
    object.insert(
        "log".to_string(),
        Value::String(display_path(repo_root, &step.log_path)),
    );
    object.insert(
        "log_sha256".to_string(),
        Value::String(sha256_file(&step.log_path)?),
    );
    if let Some(artifact_path) = &step.artifact_path {
        object.insert(
            "artifact_path".to_string(),
            Value::String(display_path(repo_root, artifact_path)),
        );
        object.insert(
            "artifact_sha256".to_string(),
            Value::String(sha256_path(artifact_path)?),
        );
    }
    Ok(Value::Object(object))
}

/// Build a full release report JSON object from package/replay evidence.
pub fn build_release_report(input: &ReleaseReportBuildInput) -> Result<Value, ReleaseReportError> {
    let root = &input.options.repo_root;
    let matrix_path = absolute_path(root, &input.options.matrix_path);
    let schema_path = absolute_path(root, &input.options.effective_matrix_schema_path());
    let release_status = input
        .release_status
        .clone()
        .unwrap_or_else(|| release_status_from_gate_payload(&input.gate).to_string());

    let mut object = Map::new();
    object.insert(
        "schema".to_string(),
        Value::String(RELEASE_REPORT_SCHEMA.to_string()),
    );
    object.insert(
        "generated_at_utc".to_string(),
        Value::String(input.generated_at_utc.clone()),
    );
    object.insert("release_status".to_string(), Value::String(release_status));
    object.insert("track".to_string(), Value::String(input.track.clone()));
    object.insert(
        "source".to_string(),
        current_source_provenance(root)?.to_json(),
    );
    object.insert(
        "matrix".to_string(),
        Value::String(display_path(root, &matrix_path)),
    );
    object.insert(
        "matrix_sha256".to_string(),
        Value::String(sha256_file(&matrix_path)?),
    );
    object.insert(
        "matrix_schema".to_string(),
        Value::String(display_path(root, &schema_path)),
    );
    object.insert(
        "matrix_schema_sha256".to_string(),
        Value::String(sha256_file(&schema_path)?),
    );
    object.insert(
        "package".to_string(),
        build_report_step(root, &input.package)?,
    );
    object.insert(
        "replay".to_string(),
        build_report_step(root, &input.replay)?,
    );
    object.insert("gate".to_string(), input.gate.clone());
    Ok(Value::Object(object))
}

/// Write a JSON report with sorted keys and a trailing newline.
pub fn write_json(path: &Path, payload: &Value) -> Result<(), ReleaseReportError> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).map_err(|source| {
            ReleaseReportError::io(format!("create directory {}", parent.display()), source)
        })?;
    }
    let text = serde_json::to_string_pretty(payload)
        .map_err(|source| ReleaseReportError::json("serialize release report", source))?;
    fs::write(path, format!("{text}\n"))
        .map_err(|source| ReleaseReportError::io(format!("write {}", path.display()), source))
}

/// Load and validate a release report from disk.
pub fn validate_release_report(
    options: &ReleaseReportOptions,
    report_path: &Path,
    gate_module: &impl GateModule,
) -> Result<ReleaseReportSummary, ReleaseReportError> {
    let report = load_json_object(report_path)?;
    let matrix_path = absolute_path(&options.repo_root, &options.matrix_path);
    let matrix = load_json_object(&matrix_path)?;
    validate_release_report_value(options, Some(report_path), &report, &matrix, gate_module)
}

/// Validate an already-loaded release report and matrix.
pub fn validate_release_report_value(
    options: &ReleaseReportOptions,
    report_path: Option<&Path>,
    report: &Map<String, Value>,
    matrix: &Map<String, Value>,
    gate_module: &impl GateModule,
) -> Result<ReleaseReportSummary, ReleaseReportError> {
    let mut errors = Vec::new();

    let schema = report.get("schema");
    if schema.and_then(Value::as_str) != Some(RELEASE_REPORT_SCHEMA) {
        errors.push(format!(
            "schema must be {RELEASE_REPORT_SCHEMA:?}, got {}",
            value_repr(schema)
        ));
    }

    let track = report.get("track").and_then(Value::as_str);
    if !track.is_some_and(|track| RELEASE_REPORT_TRACKS.contains(&track)) {
        errors.push(format!(
            "track must be one of {{{}}}, got {}",
            sorted_join(RELEASE_REPORT_TRACKS),
            value_repr(report.get("track"))
        ));
    }

    let root = &options.repo_root;
    let matrix_path = absolute_path(root, &options.matrix_path);
    let schema_path = absolute_path(root, &options.effective_matrix_schema_path());
    let expected_fields = [
        (
            "matrix",
            display_path(root, &matrix_path),
            "matrix".to_string(),
        ),
        (
            "matrix_sha256",
            sha256_file(&matrix_path)?,
            "matrix_sha256".to_string(),
        ),
        (
            "matrix_schema",
            display_path(root, &schema_path),
            "matrix_schema".to_string(),
        ),
        (
            "matrix_schema_sha256",
            sha256_file(&schema_path)?,
            "matrix_schema_sha256".to_string(),
        ),
    ];
    for (field, expected, label) in expected_fields {
        let actual = report_field(report, field);
        if actual.and_then(Value::as_str) != Some(expected.as_str()) {
            errors.push(format!(
                "{label} must be {expected:?}, got {}",
                value_repr(actual)
            ));
        }
    }

    if options.verify_source {
        errors.extend(release_report_source_errors(root, report));
    }
    errors.extend(release_step_errors(root, report, "package"));
    errors.extend(release_step_errors(root, report, "replay"));

    let mut decision = None;
    if track.is_some_and(|track| RELEASE_REPORT_TRACKS.contains(&track)) {
        match validate_release_report_gate(report, matrix, gate_module) {
            Ok(snapshot) => decision = Some(snapshot),
            Err(gate_errors) => errors.extend(gate_errors),
        }
    }

    if !errors.is_empty() {
        return Err(ReleaseReportError::validation(
            report_path.map(Path::to_path_buf),
            errors,
        ));
    }

    let decision = decision.expect("valid report has a gate decision");
    Ok(ReleaseReportSummary {
        schema: RELEASE_REPORT_SCHEMA.to_string(),
        status: "pass".to_string(),
        release_status: report
            .get("release_status")
            .and_then(Value::as_str)
            .unwrap_or("ready")
            .to_string(),
        track: decision.track,
        artifact: decision.artifact,
        candidate_mode: decision.candidate_mode,
        recommended_mode: decision.recommended_mode,
        native_dispatch: decision.native_dispatch,
        package: "pass".to_string(),
        replay: "pass".to_string(),
    })
}

/// Derive release status from a gate payload using the Python report generator policy.
pub fn release_status_from_gate_payload(gate: &Value) -> &'static str {
    let Some(gate) = gate.as_object() else {
        return "fail-closed";
    };
    if gate.get("status").and_then(Value::as_str) == Some("pass")
        && gate.get("native_dispatch").and_then(Value::as_bool) == Some(true)
    {
        return "ready";
    }
    if gate.get("recommended_mode").and_then(Value::as_str) == Some("profile-only") {
        return "profile-only";
    }
    "fail-closed"
}

/// Derive release status from a recomputed gate decision snapshot.
pub fn release_status_from_gate_decision(decision: &GateDecisionSnapshot) -> &'static str {
    if decision.status == "pass" && decision.native_dispatch {
        "ready"
    } else if decision.recommended_mode == "profile-only" {
        "profile-only"
    } else {
        "fail-closed"
    }
}

fn validate_release_report_gate(
    report: &Map<String, Value>,
    matrix: &Map<String, Value>,
    gate_module: &impl GateModule,
) -> Result<GateDecisionSnapshot, Vec<String>> {
    let Some(raw_gate) = report.get("gate").and_then(Value::as_object) else {
        return Err(vec!["gate must be an object".to_string()]);
    };

    let mut errors = Vec::new();
    let track = report.get("track").and_then(Value::as_str).unwrap_or("");
    let gate_track = raw_gate.get("track").and_then(Value::as_str);
    if gate_track != Some(track) {
        errors.push(format!(
            "gate.track must be {track:?}, got {}",
            value_repr(raw_gate.get("track"))
        ));
    }

    let artifact_id = raw_gate.get("artifact").and_then(Value::as_str);
    match artifact_id {
        Some(artifact_id) if !artifact_id.is_empty() => {
            if let Err(error) = find_artifact(matrix, track, artifact_id) {
                errors.push(error);
            }
        }
        _ => errors.push(format!(
            "gate.artifact must be a non-empty string, got {}",
            value_repr(raw_gate.get("artifact"))
        )),
    }

    let candidate_mode = raw_gate.get("candidate_mode").and_then(Value::as_str);
    if !candidate_mode.is_some_and(|mode| MODES.contains(&mode)) {
        errors.push(format!(
            "gate.candidate_mode must be one of {{{}}}, got {}",
            sorted_join(MODES),
            value_repr(raw_gate.get("candidate_mode"))
        ));
    }

    if !errors.is_empty() {
        return Err(errors);
    }

    let decision = gate_module.evaluate_release_gate(report, matrix)?;

    for (field, expected) in [
        ("status", Value::String(decision.status.clone())),
        (
            "recommended_mode",
            Value::String(decision.recommended_mode.clone()),
        ),
        ("native_dispatch", Value::Bool(decision.native_dispatch)),
    ] {
        if raw_gate.get(field) != Some(&expected) {
            errors.push(format!(
                "gate.{field} must match recomputed value {}, got {}",
                value_repr(Some(&expected)),
                value_repr(raw_gate.get(field))
            ));
        }
    }

    let (reported_failure_kinds, failure_errors) =
        gate_failure_kinds(raw_gate.get("failures"), "gate");
    errors.extend(failure_errors);
    if reported_failure_kinds != decision.failure_kinds {
        errors.push(format!(
            "gate.failures must match recomputed fail-closed decision, got {:?}, expected {:?}",
            reported_failure_kinds, decision.failure_kinds
        ));
    }

    let mut blocking_failures = decision
        .failure_kinds
        .iter()
        .filter(|kind| RELEASE_REPORT_BLOCKING_FAILURES.contains(&kind.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    blocking_failures.sort();
    if !blocking_failures.is_empty() {
        errors.push(format!(
            "release report cannot clear readiness with blocking failure(s): {}",
            blocking_failures.join(", ")
        ));
    }

    if decision.native_dispatch {
        match decision.candidate_application_count {
            Some(count) if count > 0 => {}
            Some(count) => errors.push(format!(
                "native dispatch release evidence requires positive useful applications, got {count}"
            )),
            None => errors.push(
                "native dispatch release evidence requires positive useful applications, got missing"
                    .to_string(),
            ),
        }
    }

    errors.extend(release_report_status_errors(
        report.get("release_status"),
        &decision,
    ));

    if errors.is_empty() {
        Ok(decision)
    } else {
        Err(errors)
    }
}

fn release_report_source_errors(repo_root: &Path, report: &Map<String, Value>) -> Vec<String> {
    let Some(source) = report.get("source").and_then(Value::as_object) else {
        return vec!["source must be an object".to_string()];
    };

    let current = match current_source_provenance(repo_root) {
        Ok(current) => current,
        Err(error) => {
            return vec![format!(
                "source provenance could not be recomputed: {error}"
            )];
        }
    };

    let mut errors = Vec::new();
    if source.get("kind").and_then(Value::as_str) != Some("git-worktree") {
        errors.push(format!(
            "source.kind must be 'git-worktree', got {}",
            value_repr(source.get("kind"))
        ));
    }

    let branch = source.get("git_branch").and_then(Value::as_str);
    if branch.is_none_or(str::is_empty) {
        errors.push(format!(
            "source.git_branch must be a non-empty string, got {}",
            value_repr(source.get("git_branch"))
        ));
    }

    let commit = source.get("git_commit").and_then(Value::as_str);
    if !commit.is_some_and(is_git_commit) {
        errors.push(format!(
            "source.git_commit must be a 40-hex git commit, got {}",
            value_repr(source.get("git_commit"))
        ));
    } else if commit != Some(current.git_commit.as_str()) {
        errors.push(format!(
            "source.git_commit must match current HEAD {:?}, got {}",
            current.git_commit,
            value_repr(source.get("git_commit"))
        ));
    }

    let dirty = source.get("git_dirty").and_then(Value::as_bool);
    if dirty.is_none() {
        errors.push(format!(
            "source.git_dirty must be a boolean, got {}",
            value_repr(source.get("git_dirty"))
        ));
    } else if dirty != Some(current.git_dirty) {
        errors.push(format!(
            "source.git_dirty must match current worktree {:?}, got {}",
            current.git_dirty,
            value_repr(source.get("git_dirty"))
        ));
    }

    for (field, expected) in [
        ("git_status_sha256", current.git_status_sha256.as_str()),
        ("source_tree_sha256", current.source_tree_sha256.as_str()),
    ] {
        let actual = source.get(field).and_then(Value::as_str);
        if !actual.is_some_and(is_sha256) {
            errors.push(format!("source.{field} must be a SHA-256 hex digest"));
        } else if actual != Some(expected) {
            errors.push(format!(
                "source.{field} must be {expected:?}, got {}",
                value_repr(source.get(field))
            ));
        }
    }

    errors
}

fn release_step_errors(
    repo_root: &Path,
    report: &Map<String, Value>,
    step_name: &str,
) -> Vec<String> {
    let Some(raw_step) = report.get(step_name).and_then(Value::as_object) else {
        return vec![format!("{step_name} must be an object")];
    };

    let mut errors = Vec::new();
    let command = raw_step.get("command").and_then(Value::as_str);
    if command.is_none_or(|command| command.trim().is_empty()) {
        errors.push(format!("{step_name}.command must be a non-empty string"));
    }

    let status = raw_step.get("status").and_then(Value::as_str);
    if !status.is_some_and(|status| RELEASE_REPORT_STEP_STATUSES.contains(&status)) {
        errors.push(format!(
            "{step_name}.status must be one of {{{}}}, got {}",
            sorted_join(RELEASE_REPORT_STEP_STATUSES),
            value_repr(raw_step.get("status"))
        ));
    }

    let exit_code = as_i64_like(raw_step.get("exit_code"));
    if exit_code != Some(0) {
        errors.push(format!(
            "{step_name}.exit_code must be 0, got {}",
            value_repr(raw_step.get("exit_code"))
        ));
    }

    errors.extend(release_file_sha_errors(
        repo_root,
        raw_step,
        "log",
        "log_sha256",
        &format!("{step_name}.log"),
        &format!("{step_name}.log_sha256"),
        false,
    ));

    if step_name == "package" {
        errors.extend(release_file_sha_errors(
            repo_root,
            raw_step,
            "artifact_path",
            "artifact_sha256",
            "package.artifact_path",
            "package.artifact_sha256",
            true,
        ));
    }

    if let Some(summary_sha256) = raw_step.get("summary_sha256") {
        if !summary_sha256.as_str().is_some_and(is_sha256) {
            errors.push(format!(
                "{step_name}.summary_sha256 must be a SHA-256 hex digest"
            ));
        }
    }

    errors
}

fn release_file_sha_errors(
    repo_root: &Path,
    raw_step: &Map<String, Value>,
    path_field: &str,
    digest_field: &str,
    path_label: &str,
    digest_label: &str,
    directory_ok: bool,
) -> Vec<String> {
    let mut errors = Vec::new();
    let Some(raw_path) = raw_step.get(path_field).and_then(Value::as_str) else {
        errors.push(format!("{path_label} must be a non-empty string"));
        return errors;
    };
    if raw_path.trim().is_empty() {
        errors.push(format!("{path_label} must be a non-empty string"));
        return errors;
    }

    let raw_digest = raw_step.get(digest_field).and_then(Value::as_str);
    if !raw_digest.is_some_and(is_sha256) {
        errors.push(format!("{digest_label} must be a SHA-256 hex digest"));
        return errors;
    }

    let path = repo_path(repo_root, raw_path);
    if !path.exists() {
        errors.push(format!("{path_label} does not exist: {raw_path}"));
        return errors;
    }

    let actual = if directory_ok {
        if !path.is_file() && !path.is_dir() {
            errors.push(format!(
                "{path_label} must be a file or directory: {raw_path}"
            ));
            return errors;
        }
        sha256_path(&path)
    } else {
        if !path.is_file() {
            errors.push(format!("{path_label} must be a file: {raw_path}"));
            return errors;
        }
        sha256_file(&path)
    };

    match actual {
        Ok(actual) if Some(actual.as_str()) == raw_digest => {}
        Ok(actual) => errors.push(format!(
            "{digest_label} must match {raw_path}: expected {actual}, got {}",
            raw_digest.unwrap_or("")
        )),
        Err(error) => errors.push(format!("{digest_label} could not be recomputed: {error}")),
    }

    errors
}

fn release_report_status_errors(
    release_status: Option<&Value>,
    decision: &GateDecisionSnapshot,
) -> Vec<String> {
    let Some(release_status) = release_status.and_then(Value::as_str) else {
        return vec!["release_status is required".to_string()];
    };
    if !RELEASE_REPORT_STATUSES.contains(&release_status) {
        return vec![format!(
            "release_status must be one of {{{}}}, got {release_status:?}",
            sorted_join(RELEASE_REPORT_STATUSES)
        )];
    }

    let mut errors = Vec::new();
    if release_status == "ready" && decision.status != "pass" {
        errors.push("release_status 'ready' requires a passing recomputed gate".to_string());
    }
    if release_status == "profile-only"
        && (decision.recommended_mode != "profile-only" || decision.native_dispatch)
    {
        errors.push(
            "release_status 'profile-only' requires recommended_mode 'profile-only' with native_dispatch=false"
                .to_string(),
        );
    }
    if release_status == "fail-closed"
        && (decision.native_dispatch
            || !FAILURE_MODES.contains(&decision.recommended_mode.as_str()))
    {
        errors.push(
            "release_status 'fail-closed' requires native_dispatch=false and recommended_mode off/profile-only"
                .to_string(),
        );
    }
    errors
}

fn find_artifact<'a>(
    matrix: &'a Map<String, Value>,
    track: &str,
    artifact_id: &str,
) -> Result<&'a Map<String, Value>, String> {
    let Some(tracks) = matrix.get("tracks").and_then(Value::as_object) else {
        return Err("matrix.tracks must be an object".to_string());
    };
    let Some(track_cfg) = tracks.get(track).and_then(Value::as_object) else {
        return Err(format!("unknown competition JIT track: {track}"));
    };
    let Some(artifacts) = track_cfg.get("artifacts").and_then(Value::as_array) else {
        return Err(format!("track {track:?} must define artifacts"));
    };

    for artifact in artifacts {
        if let Some(artifact) = artifact.as_object() {
            if artifact.get("id").and_then(Value::as_str) == Some(artifact_id) {
                return Ok(artifact);
            }
        }
    }

    let known = artifacts
        .iter()
        .filter_map(Value::as_object)
        .filter_map(|artifact| artifact.get("id").and_then(Value::as_str))
        .collect::<Vec<_>>()
        .join(", ");
    Err(format!(
        "unknown artifact {artifact_id:?} for track {track:?}; known: {known}"
    ))
}

fn gate_failure_kinds(raw_failures: Option<&Value>, label: &str) -> (Vec<String>, Vec<String>) {
    let Some(raw_failures) = raw_failures.and_then(Value::as_array) else {
        return (Vec::new(), vec![format!("{label}.failures must be a list")]);
    };

    let mut kinds = Vec::new();
    let mut errors = Vec::new();
    for (index, failure) in raw_failures.iter().enumerate() {
        let Some(failure) = failure.as_object() else {
            errors.push(format!("{label}.failures[{index}] must be an object"));
            continue;
        };
        let Some(kind) = failure.get("kind").and_then(Value::as_str) else {
            errors.push(format!(
                "{label}.failures[{index}].kind must be a non-empty string"
            ));
            continue;
        };
        if kind.is_empty() {
            errors.push(format!(
                "{label}.failures[{index}].kind must be a non-empty string"
            ));
            continue;
        }
        kinds.push(kind.to_string());
    }
    (kinds, errors)
}

fn load_json_object(path: &Path) -> Result<Map<String, Value>, ReleaseReportError> {
    let text = fs::read_to_string(path)
        .map_err(|source| ReleaseReportError::io(format!("read {}", path.display()), source))?;
    let value = serde_json::from_str::<Value>(&text)
        .map_err(|source| ReleaseReportError::json(format!("parse {}", path.display()), source))?;
    match value {
        Value::Object(object) => Ok(object),
        other => Err(ReleaseReportError::validation(
            Some(path.to_path_buf()),
            vec![format!(
                "expected a JSON object, got {}",
                value_repr(Some(&other))
            )],
        )),
    }
}

fn collect_descendants(
    root: &Path,
    current: &Path,
    entries: &mut Vec<PathBuf>,
) -> Result<(), ReleaseReportError> {
    for entry in fs::read_dir(current).map_err(|source| {
        ReleaseReportError::io(format!("read directory {}", current.display()), source)
    })? {
        let entry = entry.map_err(|source| {
            ReleaseReportError::io(format!("read directory {}", current.display()), source)
        })?;
        let path = entry.path();
        entries.push(path.clone());
        let metadata = fs::symlink_metadata(&path)
            .map_err(|source| ReleaseReportError::io(format!("stat {}", path.display()), source))?;
        if metadata.file_type().is_dir() {
            let relative = path.strip_prefix(root).map_err(|_| {
                ReleaseReportError::validation(
                    None,
                    vec![format!("{} is outside {}", path.display(), root.display())],
                )
            })?;
            if !relative.as_os_str().is_empty() {
                collect_descendants(root, &path, entries)?;
            }
        }
    }
    Ok(())
}

fn update_digest_from_file(digest: &mut Sha256, path: &Path) -> Result<(), ReleaseReportError> {
    let mut file = fs::File::open(path)
        .map_err(|source| ReleaseReportError::io(format!("open {}", path.display()), source))?;
    let mut buffer = vec![0; CHUNK_SIZE];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|source| ReleaseReportError::io(format!("read {}", path.display()), source))?;
        if read == 0 {
            return Ok(());
        }
        digest.update(&buffer[..read]);
    }
}

fn relative_posix(root: &Path, path: &Path) -> Result<String, ReleaseReportError> {
    let relative = path.strip_prefix(root).map_err(|_| {
        ReleaseReportError::validation(
            None,
            vec![format!("{} is outside {}", path.display(), root.display())],
        )
    })?;
    relative
        .to_str()
        .map(|value| value.replace('\\', "/"))
        .ok_or_else(|| {
            ReleaseReportError::validation(
                None,
                vec![format!("{} is not valid UTF-8", relative.display())],
            )
        })
}

fn path_to_posix_lossy(path: &Path) -> String {
    path.to_string_lossy().replace('\\', "/")
}

fn absolute_path(base: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        base.join(path)
    }
}

fn repo_path(repo_root: &Path, path: &str) -> PathBuf {
    let path = Path::new(path);
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    }
}

fn path_from_git_bytes(bytes: &[u8]) -> PathBuf {
    #[cfg(unix)]
    {
        PathBuf::from(OsString::from_vec(bytes.to_vec()))
    }
    #[cfg(not(unix))]
    {
        PathBuf::from(String::from_utf8_lossy(bytes).into_owned())
    }
}

fn path_os_bytes(path: &Path) -> Vec<u8> {
    #[cfg(unix)]
    {
        path.as_os_str().as_bytes().to_vec()
    }
    #[cfg(not(unix))]
    {
        path.to_string_lossy().as_bytes().to_vec()
    }
}

fn file_mode_bits(metadata: &fs::Metadata) -> u32 {
    #[cfg(unix)]
    {
        metadata.permissions().mode() & 0o777
    }
    #[cfg(not(unix))]
    {
        let _ = metadata;
        0
    }
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut digest = Sha256::new();
    digest.update(bytes);
    let bytes = digest.finalize();
    hex_digest(&bytes)
}

fn hex_digest(bytes: &[u8]) -> String {
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        use std::fmt::Write as _;
        let _ = write!(&mut text, "{byte:02x}");
    }
    text
}

fn is_sha256(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn is_git_commit(value: &str) -> bool {
    value.len() == 40 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn as_i64_like(value: Option<&Value>) -> Option<i64> {
    match value? {
        Value::Number(number) => number
            .as_i64()
            .or_else(|| number.as_u64().and_then(|value| i64::try_from(value).ok()))
            .or_else(|| number.as_f64().map(|value| value as i64)),
        Value::Bool(value) => Some(i64::from(*value)),
        Value::String(value) => value.parse::<f64>().ok().map(|value| value as i64),
        Value::Null | Value::Array(_) | Value::Object(_) => None,
    }
}

fn as_f64_like(value: Option<&Value>) -> Option<f64> {
    match value? {
        Value::Number(number) => number.as_f64(),
        Value::Bool(value) => Some(f64::from(u8::from(*value))),
        Value::String(value) => value.parse::<f64>().ok(),
        Value::Null | Value::Array(_) | Value::Object(_) => None,
    }
}

fn report_field<'a>(report: &'a Map<String, Value>, name: &str) -> Option<&'a Value> {
    report.get(name).or_else(|| {
        report
            .get("provenance")
            .and_then(Value::as_object)
            .and_then(|provenance| provenance.get(name))
    })
}

fn required_string(
    object: &Map<String, Value>,
    field: &str,
    label: &str,
    errors: &mut Vec<String>,
) -> String {
    match object.get(field).and_then(Value::as_str) {
        Some(value) if !value.is_empty() => value.to_string(),
        _ => {
            errors.push(format!("{label} must be a non-empty string"));
            String::new()
        }
    }
}

fn required_bool(
    object: &Map<String, Value>,
    field: &str,
    label: &str,
    errors: &mut Vec<String>,
) -> bool {
    match object.get(field).and_then(Value::as_bool) {
        Some(value) => value,
        None => {
            errors.push(format!("{label} must be a boolean"));
            false
        }
    }
}

fn sorted_join(values: &[&str]) -> String {
    let mut sorted = values.to_vec();
    sorted.sort_unstable();
    sorted.join(", ")
}

fn value_repr(value: Option<&Value>) -> String {
    match value {
        Some(Value::String(value)) => format!("{value:?}"),
        Some(value) => value.to_string(),
        None => "missing".to_string(),
    }
}
