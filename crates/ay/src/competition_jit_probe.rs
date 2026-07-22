// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(dead_code, missing_docs, unreachable_pub, unused_qualifications)]

//! Rust support for bounded external code generation ROI probes.
//!
//! This keeps bounded ROI probes inside the product.  It builds per-track ay
//! commands, handles missing probes as skipped records, parses `--stats-json`
//! output, aggregates summaries, and emits JSON/human reports for higher-level
//! callers.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

use serde_json::{json, Value};

pub const SCHEMA: &str = "ay.jit-roi-probe/v1";
pub const SUMMARY_SCHEMA: &str = "ay.jit-roi-probe-summary/v1";
pub const COMPARISON_SCHEMA: &str = "ay.jit-roi-probe-comparison/v1";
pub const BASELINE_MODE: &str = "off";
pub const DEFAULT_MAX_PROBES: usize = 8;
pub const DEFAULT_TIMEOUT_MS: u64 = 1000;
pub const DEFAULT_WALL_TIMEOUT_SEC: f64 = 2.0;
pub const DEFAULT_OVERALL_TIMEOUT_SEC: f64 = 30.0;
pub const OUTPUT_CAPTURE_LIMIT: usize = 200_000;
pub const VALID_TRACKS: &[&str] = &["sat", "smt", "pb", "chc"];

const MODES: &[&str] = &["off", "current", "solver-program", "profile-only"];
const NATIVE_MODES: &[&str] = &["current", "solver-program"];
const INTEGRITY_FAILURES: &[&str] = &["wrong-answer", "proof-failure", "witness-failure", "crash"];
const EPSILON: f64 = 1e-9;

const SAT_DEFAULT_PROBES: &[&str] = &[
    "benchmarks/sat/canary/tiny_sat.cnf",
    "benchmarks/sat/canary/tiny_unsat.cnf",
];
const SMT_DEFAULT_PROBES: &[&str] = &[
    "benchmarks/smtcomp/QF_LRA/synched.base.smt2",
    "benchmarks/smtcomp/QF_LRA/constraints-tempo-width-10.smt2",
];
const PB_DEFAULT_PROBES: &[&str] = &[
    "benchmarks/pb-comp/test-instances/trivial-sat.opb",
    "benchmarks/pb-comp/test-instances/trivial-unsat.opb",
];
const CHC_DEFAULT_PROBES: &[&str] = &[
    "tests/chc/regression/false_proof_array_selfloop.smt2",
    "tests/chc/regression/false_proof_array_chain.smt2",
];

#[derive(Debug)]
pub enum ProbeError {
    InvalidArgument(String),
    Matrix(String),
    Process(String),
    Io(std::io::Error),
    Json(serde_json::Error),
}

impl fmt::Display for ProbeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidArgument(message) | Self::Matrix(message) | Self::Process(message) => {
                f.write_str(message)
            }
            Self::Io(err) => err.fmt(f),
            Self::Json(err) => err.fmt(f),
        }
    }
}

impl Error for ProbeError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidArgument(_) | Self::Matrix(_) | Self::Process(_) => None,
            Self::Io(err) => Some(err),
            Self::Json(err) => Some(err),
        }
    }
}

impl From<std::io::Error> for ProbeError {
    fn from(err: std::io::Error) -> Self {
        Self::Io(err)
    }
}

impl From<serde_json::Error> for ProbeError {
    fn from(err: serde_json::Error) -> Self {
        Self::Json(err)
    }
}

pub type ProbeResult<T> = std::result::Result<T, ProbeError>;

#[derive(Clone, Debug, PartialEq)]
pub struct RoiProbeOptions {
    pub root: PathBuf,
    pub track: String,
    pub artifact: Option<String>,
    pub matrix: PathBuf,
    pub ay: Option<PathBuf>,
    pub probes: Vec<PathBuf>,
    pub max_probes: usize,
    pub timeout_ms: u64,
    pub wall_timeout_s: f64,
    pub kill_grace_s: f64,
    pub overall_timeout_s: f64,
    pub baseline_mode: String,
    pub candidate_mode: Option<String>,
    pub sat_variant: String,
    pub pb_native: bool,
    pub ay_args: Vec<String>,
    pub dry_run: bool,
}

impl Default for RoiProbeOptions {
    fn default() -> Self {
        let root = default_repo_root();
        Self {
            matrix: default_matrix_path(&root),
            root,
            track: "sat".to_string(),
            artifact: None,
            ay: None,
            probes: Vec::new(),
            max_probes: DEFAULT_MAX_PROBES,
            timeout_ms: DEFAULT_TIMEOUT_MS,
            wall_timeout_s: DEFAULT_WALL_TIMEOUT_SEC,
            kill_grace_s: 0.5,
            overall_timeout_s: DEFAULT_OVERALL_TIMEOUT_SEC,
            baseline_mode: BASELINE_MODE.to_string(),
            candidate_mode: None,
            sat_variant: "default".to_string(),
            pb_native: false,
            ay_args: Vec::new(),
            dry_run: false,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct RunRecord {
    pub role: String,
    pub mode: String,
    pub probe: PathBuf,
    pub command: Vec<String>,
    pub status: String,
    pub expected: Option<String>,
    pub actual: String,
    pub elapsed_sec: f64,
    pub par2_sec: f64,
    pub returncode: Option<i32>,
    pub timed_out: bool,
    pub crash: bool,
    pub wrong_answer: bool,
    pub stats_json_found: bool,
    pub application_count: i64,
    pub counters: BTreeMap<String, i64>,
    pub reason: Option<String>,
}

impl RunRecord {
    pub fn to_json(&self, root: &Path) -> Value {
        let mut payload = serde_json::Map::new();
        payload.insert("role".to_string(), json!(self.role));
        payload.insert("mode".to_string(), json!(self.mode));
        payload.insert("probe".to_string(), json!(display_path(&self.probe, root)));
        payload.insert("command".to_string(), json!(shell_join(&self.command)));
        payload.insert("status".to_string(), json!(self.status));
        payload.insert("expected".to_string(), json!(self.expected));
        payload.insert("actual".to_string(), json!(self.actual));
        payload.insert("elapsed_sec".to_string(), json!(round6(self.elapsed_sec)));
        payload.insert("par2_sec".to_string(), json!(round6(self.par2_sec)));
        payload.insert("returncode".to_string(), json!(self.returncode));
        payload.insert("timed_out".to_string(), json!(self.timed_out));
        payload.insert("crash".to_string(), json!(self.crash));
        payload.insert("wrong_answer".to_string(), json!(self.wrong_answer));
        payload.insert("stats_json_found".to_string(), json!(self.stats_json_found));
        payload.insert(
            "application_count".to_string(),
            json!(self.application_count),
        );
        payload.insert("counters".to_string(), json!(self.counters));
        if let Some(reason) = &self.reason {
            payload.insert("reason".to_string(), json!(reason));
        }
        Value::Object(payload)
    }
}

#[derive(Clone, Debug)]
pub struct RunInvocation<'a> {
    pub root: &'a Path,
    pub track: &'a str,
    pub artifact: &'a Value,
    pub role: &'a str,
    pub mode: &'a str,
    pub probe: &'a Path,
    pub ay: &'a Path,
    pub timeout_ms: u64,
    pub wall_timeout_sec: f64,
    pub kill_grace_sec: f64,
    pub sat_variant: &'a str,
    pub pb_native: bool,
    pub extra_args: &'a [String],
    pub dry_run: bool,
    pub telemetry_counters: &'a [String],
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct ProcessOutput {
    pub returncode: i32,
    pub timed_out: bool,
    pub elapsed_sec: f64,
    pub stdout: String,
    pub stderr: String,
}

#[derive(Clone, Debug, Default, PartialEq)]
pub struct GateMetrics {
    pub wrong_answers: i64,
    pub proof_failures: i64,
    pub witness_failures: i64,
    pub crashes: i64,
    pub solved: Option<i64>,
    pub par2: Option<f64>,
    pub application_count: Option<i64>,
    pub native_install_count: Option<i64>,
    pub native_apply_count: Option<i64>,
    pub native_helper_compile_attempt_count: Option<i64>,
    pub native_helper_compile_success_count: Option<i64>,
    pub native_helper_evaluation_count: Option<i64>,
    pub native_helper_interpreter_confirmation_count: Option<i64>,
    pub native_helper_trusted_true_count: Option<i64>,
    pub native_helper_deopt_count: Option<i64>,
    pub native_helper_fallback_count: Option<i64>,
    pub native_helper_missing_var_fallback_count: Option<i64>,
}

impl GateMetrics {
    pub fn to_json(&self) -> Value {
        json!({
            "wrong_answers": self.wrong_answers,
            "proof_failures": self.proof_failures,
            "witness_failures": self.witness_failures,
            "crashes": self.crashes,
            "solved": self.solved,
            "par2": self.par2,
            "application_count": self.application_count,
            "native_install_count": self.native_install_count,
            "native_apply_count": self.native_apply_count,
            "native_helper_compile_attempt_count": self.native_helper_compile_attempt_count,
            "native_helper_compile_success_count": self.native_helper_compile_success_count,
            "native_helper_evaluation_count": self.native_helper_evaluation_count,
            "native_helper_interpreter_confirmation_count": self.native_helper_interpreter_confirmation_count,
            "native_helper_trusted_true_count": self.native_helper_trusted_true_count,
            "native_helper_deopt_count": self.native_helper_deopt_count,
            "native_helper_fallback_count": self.native_helper_fallback_count,
            "native_helper_missing_var_fallback_count": self.native_helper_missing_var_fallback_count,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GateFailure {
    pub kind: String,
    pub failure_mode: String,
    pub detail: String,
}

impl GateFailure {
    pub fn to_json(&self) -> Value {
        json!({
            "kind": self.kind,
            "failure_mode": self.failure_mode,
            "detail": self.detail,
        })
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct GateDecision {
    pub status: String,
    pub track: String,
    pub artifact: String,
    pub candidate_mode: String,
    pub recommended_mode: String,
    pub native_dispatch: bool,
    pub failures: Vec<GateFailure>,
    pub baseline: GateMetrics,
    pub candidate: GateMetrics,
}

impl GateDecision {
    pub fn to_json(&self) -> Value {
        json!({
            "status": self.status,
            "track": self.track,
            "artifact": self.artifact,
            "candidate_mode": self.candidate_mode,
            "recommended_mode": self.recommended_mode,
            "native_dispatch": self.native_dispatch,
            "failures": self.failures.iter().map(GateFailure::to_json).collect::<Vec<_>>(),
            "baseline": self.baseline.to_json(),
            "candidate": self.candidate.to_json(),
        })
    }
}

pub fn default_repo_root() -> PathBuf {
    if let Some(manifest_dir) = option_env!("CARGO_MANIFEST_DIR") {
        let manifest = PathBuf::from(manifest_dir);
        if manifest.ends_with(Path::new("crates/ay")) {
            if let Some(root) = manifest.parent().and_then(Path::parent) {
                return root.to_path_buf();
            }
        }
    }
    std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."))
}

pub fn default_matrix_path(root: &Path) -> PathBuf {
    root.join("competition").join("jit_mode_matrix.json")
}

pub fn display_path(path: impl AsRef<Path>, root: impl AsRef<Path>) -> String {
    let path = path.as_ref();
    path.strip_prefix(root.as_ref())
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

pub fn truncate_text(text: &str, limit: usize) -> String {
    if text.len() <= limit {
        return text.to_string();
    }
    let mut end = limit;
    while !text.is_char_boundary(end) {
        end -= 1;
    }
    format!("{}\n...<truncated>...\n", &text[..end])
}

pub fn normalize_result(value: impl AsRef<str>) -> String {
    let token = value
        .as_ref()
        .trim()
        .to_ascii_lowercase()
        .replace(['_', '-'], " ");
    match token.as_str() {
        "s satisfiable" | "s sat" | "satisfiable" | "sat" => "sat".to_string(),
        "s unsatisfiable" | "s unsat" | "unsatisfiable" | "unsat" => "unsat".to_string(),
        "s optimum found" | "optimum found" | "optimum" => "optimum".to_string(),
        "s unknown" | "unknown" | "timeout" | "timed out" => "unknown".to_string(),
        _ => token,
    }
}

pub fn expected_from_probe(path: &Path) -> Option<String> {
    let name = path.file_name()?.to_string_lossy().to_ascii_lowercase();
    if name.contains("unsat") {
        return Some("unsat".to_string());
    }
    if name.contains("sat") {
        return Some("sat".to_string());
    }
    if path.extension().and_then(|ext| ext.to_str()) == Some("smt2") {
        let mut file = fs::File::open(path).ok()?;
        let mut text = String::new();
        let _ = file
            .by_ref()
            .take(1024 * 1024)
            .read_to_string(&mut text)
            .ok()?;
        return status_from_smt2_prefix(&text);
    }
    None
}

pub fn parse_stats_json(stdout: &str, stderr: &str) -> Value {
    for stream in [stderr, stdout] {
        for line in stream.lines() {
            let line = line.trim();
            if !(line.starts_with('{') && line.ends_with('}')) {
                continue;
            }
            let Ok(parsed) = serde_json::from_str::<Value>(line) else {
                continue;
            };
            if !parsed.is_object() {
                continue;
            }
            if parsed.get("schema").and_then(Value::as_str) == Some("ay.stats-json/v1")
                || parsed.get("result").is_some()
                || parsed.get("counters").is_some()
            {
                return parsed;
            }
        }
    }
    json!({})
}

pub fn parse_solver_result(stdout: &str, stderr: &str, stats: &Value) -> String {
    let result = stats
        .get("result")
        .map(value_to_string)
        .map(normalize_result)
        .unwrap_or_default();
    if is_definitive_result(&result) || result == "unknown" {
        return result;
    }
    for line in stdout.lines().chain(stderr.lines()) {
        let normalized = normalize_result(line);
        if is_definitive_result(&normalized) || normalized == "unknown" {
            return normalized;
        }
    }
    "unknown".to_string()
}

pub fn as_int(value: &Value) -> Option<i64> {
    match value {
        Value::Null => None,
        Value::Bool(value) => Some(i64::from(*value)),
        Value::Number(value) => value
            .as_i64()
            .or_else(|| value.as_u64().and_then(|value| i64::try_from(value).ok()))
            .or_else(|| value.as_f64().map(|value| value as i64)),
        Value::String(value) if value.is_empty() => None,
        Value::String(value) => value.parse::<f64>().ok().map(|value| value as i64),
        Value::Object(object) => object.get("value").and_then(as_int),
        Value::Array(_) => None,
    }
}

pub fn as_float(value: &Value) -> Option<f64> {
    match value {
        Value::Null => None,
        Value::Bool(value) => Some(f64::from(u8::from(*value))),
        Value::Number(value) => value.as_f64(),
        Value::String(value) if value.is_empty() => None,
        Value::String(value) => value.parse::<f64>().ok(),
        Value::Object(_) | Value::Array(_) => None,
    }
}

pub fn counter_value(stats: &Value, key: &str) -> Option<i64> {
    let value = stats.get(key).and_then(as_int);
    if value.is_some() {
        return value;
    }
    let value = stats
        .get("counters")
        .and_then(Value::as_object)
        .and_then(|counters| counters.get(key))
        .and_then(as_int);
    if value.is_some() {
        return value;
    }
    let competition_jit = stats.get("competition_jit").and_then(Value::as_object)?;
    let application_counter = competition_jit.get("application_counter")?;
    if let Some(counter_object) = application_counter.as_object() {
        if counter_object.get("key").and_then(Value::as_str) == Some(key) {
            return counter_object.get("value").and_then(as_int);
        }
    } else if application_counter.as_str() == Some(key) {
        return competition_jit.get("application_count").and_then(as_int);
    }
    None
}

pub fn stats_elapsed_sec(stats: &Value) -> Option<f64> {
    for key in ["time.total_ms", "wall_time_ms", "solve_time_ms", "time_ms"] {
        if let Some(value) = counter_value(stats, key) {
            return Some((value as f64 / 1000.0).max(0.0));
        }
    }
    for key in ["time.total_s", "solve_time_s", "elapsed_sec"] {
        if let Some(value) = stats.get(key).and_then(as_float) {
            return Some(value.max(0.0));
        }
    }
    None
}

pub fn load_matrix(path: &Path) -> ProbeResult<Value> {
    let text = fs::read_to_string(path)?;
    let matrix = serde_json::from_str::<Value>(&text)?;
    if !matrix.is_object() {
        return Err(ProbeError::Matrix(format!(
            "{}: expected a JSON object",
            path.display()
        )));
    }
    if !matrix.get("tracks").is_some_and(Value::is_object) {
        return Err(ProbeError::Matrix(format!(
            "{}: missing tracks object",
            path.display()
        )));
    }
    Ok(matrix)
}

pub fn find_artifact(matrix: &Value, track: &str, artifact_id: &str) -> ProbeResult<Value> {
    let Some(track_cfg) = matrix
        .get("tracks")
        .and_then(Value::as_object)
        .and_then(|tracks| tracks.get(track))
        .and_then(Value::as_object)
    else {
        return Err(ProbeError::Matrix(format!(
            "unknown competition JIT track: {track}"
        )));
    };
    let artifacts = track_cfg
        .get("artifacts")
        .and_then(Value::as_array)
        .ok_or_else(|| ProbeError::Matrix(format!("track {track:?} must define artifacts")))?;
    for artifact in artifacts {
        if artifact.get("id").and_then(Value::as_str) == Some(artifact_id) {
            return Ok(artifact.clone());
        }
    }
    let known = artifacts
        .iter()
        .filter_map(|artifact| artifact.get("id").and_then(Value::as_str))
        .collect::<Vec<_>>()
        .join(", ");
    Err(ProbeError::Matrix(format!(
        "unknown artifact {artifact_id:?} for track {track:?}; known: {known}"
    )))
}

pub fn artifact_by_id(
    matrix: &Value,
    track: &str,
    artifact_id: Option<&str>,
) -> ProbeResult<Value> {
    if let Some(artifact_id) = artifact_id {
        return find_artifact(matrix, track, artifact_id);
    }
    matrix
        .get("tracks")
        .and_then(Value::as_object)
        .and_then(|tracks| tracks.get(track))
        .and_then(Value::as_object)
        .and_then(|track_cfg| track_cfg.get("artifacts"))
        .and_then(Value::as_array)
        .and_then(|artifacts| artifacts.first())
        .cloned()
        .ok_or_else(|| ProbeError::Matrix(format!("unknown competition JIT track: {track}")))
}

pub fn choose_candidate_mode(artifact: &Value, requested: Option<&str>) -> String {
    if let Some(requested) = requested {
        return requested.to_string();
    }
    if let Some(modes) = artifact.get("candidate_modes").and_then(Value::as_array) {
        for preferred in ["current", "solver-program", "profile-only"] {
            if modes.iter().any(|mode| mode.as_str() == Some(preferred)) {
                return preferred.to_string();
            }
        }
    }
    artifact
        .get("default_mode")
        .and_then(Value::as_str)
        .unwrap_or("profile-only")
        .to_string()
}

pub fn telemetry_counters(matrix: &Value, track: &str) -> ProbeResult<Vec<String>> {
    let counters = matrix
        .get("solve_control_plane")
        .and_then(|control| control.get("tracks"))
        .and_then(Value::as_object)
        .and_then(|tracks| tracks.get(track))
        .and_then(|track_cfg| track_cfg.get("telemetry_counters"))
        .and_then(Value::as_array)
        .ok_or_else(|| {
            ProbeError::Matrix(format!(
                "missing solve_control_plane.tracks.{track}.telemetry_counters"
            ))
        })?;
    Ok(counters
        .iter()
        .filter_map(Value::as_str)
        .map(str::to_string)
        .collect())
}

pub fn native_dispatch_counter_keys(
    artifact: &Value,
    mode: &str,
) -> (Option<String>, Option<String>) {
    let Some(counter_spec) = artifact
        .get("native_dispatch_counters")
        .and_then(Value::as_object)
        .and_then(|native_counters| native_counters.get(mode))
        .and_then(Value::as_object)
    else {
        return (None, None);
    };
    (
        non_empty_string(counter_spec.get("install_counter")),
        non_empty_string(counter_spec.get("apply_counter")),
    )
}

pub fn default_ay_binary(root: &Path) -> PathBuf {
    let release = root.join("target").join("release").join("ay");
    if release.exists() {
        return release;
    }
    root.join("target").join("debug").join("ay")
}

pub fn probe_paths(
    root: &Path,
    track: &str,
    explicit: &[PathBuf],
    max_probes: usize,
) -> ProbeResult<Vec<PathBuf>> {
    if max_probes == 0 {
        return Err(ProbeError::InvalidArgument(
            "--max-probes must be positive".to_string(),
        ));
    }
    let raw_paths: Vec<PathBuf> = if explicit.is_empty() {
        default_probes(track)?
            .iter()
            .map(|probe| PathBuf::from(*probe))
            .collect()
    } else {
        explicit.to_vec()
    };
    Ok(raw_paths
        .into_iter()
        .take(max_probes)
        .map(|path| {
            if path.is_absolute() {
                path
            } else {
                root.join(path)
            }
        })
        .collect())
}

pub fn command_for_track(
    track: &str,
    ay: &Path,
    probe: &Path,
    timeout_ms: u64,
    sat_variant: &str,
    pb_native: bool,
    extra_args: &[String],
) -> Vec<String> {
    if track == "pb" {
        let mut command = vec![
            ay.to_string_lossy().into_owned(),
            "pb".to_string(),
            "solve".to_string(),
            "--stats-json".to_string(),
            "--timeout".to_string(),
            timeout_ms.to_string(),
        ];
        if pb_native {
            command.push("--native".to_string());
        }
        command.extend(extra_args.iter().cloned());
        command.push(probe.to_string_lossy().into_owned());
        return command;
    }
    if track == "chc" {
        let mut command = vec![
            ay.to_string_lossy().into_owned(),
            "--stats-json".to_string(),
            "--timeout".to_string(),
            timeout_ms.to_string(),
        ];
        command.extend(extra_args.iter().cloned());
        command.extend(["--chc".to_string(), probe.to_string_lossy().into_owned()]);
        return command;
    }
    let mut command = vec![
        ay.to_string_lossy().into_owned(),
        "--stats-json".to_string(),
        "--no-verify-proof".to_string(),
        "--timeout".to_string(),
        timeout_ms.to_string(),
    ];
    if track == "sat" {
        command.extend(["--sat-variant".to_string(), sat_variant.to_string()]);
    }
    command.extend(extra_args.iter().cloned());
    command.push(probe.to_string_lossy().into_owned());
    command
}

pub fn run_process(
    command: &[String],
    cwd: &Path,
    env: &BTreeMap<String, String>,
    wall_timeout_sec: f64,
    _kill_grace_sec: f64,
) -> ProbeResult<ProcessOutput> {
    let Some(program) = command.first() else {
        return Err(ProbeError::Process("empty command".to_string()));
    };
    let start = Instant::now();
    let mut child = Command::new(program)
        .args(&command[1..])
        .current_dir(cwd)
        .envs(env)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    let stdout = child.stdout.take().map(read_pipe);
    let stderr = child.stderr.take().map(read_pipe);
    let timeout = duration_from_secs(wall_timeout_sec)?;
    let mut timed_out = false;
    let returncode;
    loop {
        if let Some(status) = child.try_wait()? {
            returncode = status.code().unwrap_or(128);
            break;
        }
        if start.elapsed() >= timeout {
            timed_out = true;
            let _ = child.kill();
            let _ = child.wait()?;
            returncode = 124;
            break;
        }
        thread::sleep(Duration::from_millis(5));
    }
    let elapsed_sec = start.elapsed().as_secs_f64();
    let stdout = join_reader(stdout);
    let stderr = join_reader(stderr);
    Ok(ProcessOutput {
        returncode,
        timed_out,
        elapsed_sec,
        stdout: truncate_text(&stdout, OUTPUT_CAPTURE_LIMIT),
        stderr: truncate_text(&stderr, OUTPUT_CAPTURE_LIMIT),
    })
}

pub fn run_one(invocation: &RunInvocation<'_>) -> ProbeResult<RunRecord> {
    let application_counter = artifact_string(invocation.artifact, "application_counter")?;
    let command = command_for_track(
        invocation.track,
        invocation.ay,
        invocation.probe,
        invocation.timeout_ms,
        invocation.sat_variant,
        invocation.pb_native,
        invocation.extra_args,
    );
    let expected = if invocation.probe.exists() {
        expected_from_probe(invocation.probe)
    } else {
        None
    };
    if invocation.dry_run {
        return Ok(RunRecord {
            role: invocation.role.to_string(),
            mode: invocation.mode.to_string(),
            probe: invocation.probe.to_path_buf(),
            command,
            status: "dry-run".to_string(),
            expected,
            actual: "unknown".to_string(),
            elapsed_sec: 0.0,
            par2_sec: 0.0,
            returncode: None,
            timed_out: false,
            crash: false,
            wrong_answer: false,
            stats_json_found: false,
            application_count: 0,
            counters: BTreeMap::new(),
            reason: Some("dry-run".to_string()),
        });
    }

    let mut run_env = BTreeMap::new();
    run_env.insert(
        "AY_COMPETITION_JIT_ARTIFACT".to_string(),
        artifact_string(invocation.artifact, "id")?,
    );
    run_env.insert(
        "AY_COMPETITION_JIT_MODE".to_string(),
        invocation.mode.to_string(),
    );
    run_env.insert(
        "AY_COMPETITION_JIT_CANDIDATE_MODE".to_string(),
        invocation.mode.to_string(),
    );
    run_env.insert(
        "AY_COMPETITION_JIT_APPLICATION_COUNTER".to_string(),
        application_counter.clone(),
    );

    let output = run_process(
        &command,
        invocation.root,
        &run_env,
        invocation.wall_timeout_sec,
        invocation.kill_grace_sec,
    )?;
    let stats = parse_stats_json(&output.stdout, &output.stderr);
    let elapsed_sec = stats_elapsed_sec(&stats).unwrap_or(output.elapsed_sec);
    let actual = if output.timed_out {
        "unknown".to_string()
    } else {
        parse_solver_result(&output.stdout, &output.stderr, &stats)
    };
    let wrong_answer = expected.as_deref().is_some_and(is_definitive_result)
        && is_definitive_result(&actual)
        && expected.as_deref() != Some(actual.as_str());
    let crash = !output.timed_out && !matches!(output.returncode, 0 | 10 | 20 | 30);
    let solved = is_definitive_result(&actual) && !wrong_answer && !crash;
    let timeout_sec = invocation.timeout_ms as f64 / 1000.0;
    let par2_sec = if solved {
        elapsed_sec
    } else {
        2.0 * timeout_sec
    };
    let mut requested_counters: BTreeSet<String> =
        invocation.telemetry_counters.iter().cloned().collect();
    requested_counters.insert(application_counter.clone());
    let counters = requested_counters
        .into_iter()
        .map(|key| {
            let value = counter_value(&stats, &key).unwrap_or(0);
            (key, value)
        })
        .collect::<BTreeMap<_, _>>();
    let application_count = *counters.get(&application_counter).unwrap_or(&0);
    let stats_json_found = stats.as_object().is_some_and(|object| !object.is_empty());
    Ok(RunRecord {
        role: invocation.role.to_string(),
        mode: invocation.mode.to_string(),
        probe: invocation.probe.to_path_buf(),
        command,
        status: if output.timed_out {
            "timeout".to_string()
        } else if crash {
            "crash".to_string()
        } else {
            "ok".to_string()
        },
        expected,
        actual,
        elapsed_sec,
        par2_sec,
        returncode: Some(output.returncode),
        timed_out: output.timed_out,
        crash,
        wrong_answer,
        stats_json_found,
        application_count,
        counters,
        reason: None,
    })
}

pub fn skipped_record(invocation: &RunInvocation<'_>, reason: &str) -> RunRecord {
    let command = command_for_track(
        invocation.track,
        invocation.ay,
        invocation.probe,
        invocation.timeout_ms,
        invocation.sat_variant,
        invocation.pb_native,
        invocation.extra_args,
    );
    RunRecord {
        role: invocation.role.to_string(),
        mode: invocation.mode.to_string(),
        probe: invocation.probe.to_path_buf(),
        command,
        status: "skipped".to_string(),
        expected: if invocation.probe.exists() {
            expected_from_probe(invocation.probe)
        } else {
            None
        },
        actual: "unknown".to_string(),
        elapsed_sec: 0.0,
        par2_sec: 0.0,
        returncode: None,
        timed_out: false,
        crash: false,
        wrong_answer: false,
        stats_json_found: false,
        application_count: 0,
        counters: BTreeMap::new(),
        reason: Some(reason.to_string()),
    }
}

pub fn aggregate_summary(
    track: &str,
    artifact: &Value,
    mode: &str,
    runs: &[RunRecord],
    telemetry_counters: &[String],
) -> ProbeResult<Value> {
    let application_counter = artifact_string(artifact, "application_counter")?;
    let artifact_id = artifact_string(artifact, "id")?;
    let mut counter_keys: BTreeSet<String> = telemetry_counters.iter().cloned().collect();
    counter_keys.insert(application_counter.clone());
    let mut counters = counter_keys
        .into_iter()
        .map(|key| (key, 0_i64))
        .collect::<BTreeMap<_, _>>();
    for run in runs {
        if matches!(run.status.as_str(), "skipped" | "dry-run") {
            continue;
        }
        for (key, value) in &run.counters {
            *counters.entry(key.clone()).or_insert(0) += value;
        }
    }
    let application_count = *counters.get(&application_counter).unwrap_or(&0);
    let benchmarks = runs
        .iter()
        .filter(|run| !matches!(run.status.as_str(), "skipped" | "dry-run"))
        .count();
    let par2 = runs
        .iter()
        .filter(|run| !matches!(run.status.as_str(), "skipped" | "dry-run"))
        .map(|run| run.par2_sec)
        .sum::<f64>();
    Ok(json!({
        "schema": SUMMARY_SCHEMA,
        "mode": track,
        "competition_jit": {
            "schema_version": 1,
            "track": track,
            "artifact_id": artifact_id,
            "artifact": artifact_id,
            "candidate_mode": mode,
            "requested_mode": mode,
            "application_counter": {
                "key": application_counter,
                "value": application_count,
            },
        },
        "counters": counters,
        "totals": {
            "benchmarks": benchmarks,
            "skipped": runs.iter().filter(|run| run.status == "skipped").count(),
            "solved": runs.iter().filter(|run| is_definitive_result(&run.actual) && !run.wrong_answer && !run.crash).count(),
            "par2": round6(par2),
            "wrong_answers": runs.iter().filter(|run| run.wrong_answer).count(),
            "proof_failures": 0,
            "witness_failures": 0,
            "crashes": runs.iter().filter(|run| run.crash).count(),
            "timeouts": runs.iter().filter(|run| run.timed_out).count(),
            "missing_stats_json": runs.iter().filter(|run| !matches!(run.status.as_str(), "skipped" | "dry-run") && !run.stats_json_found).count(),
        },
    }))
}

pub fn normalize_metrics(
    data: &Value,
    role: Option<&str>,
    application_counter_key: Option<&str>,
    native_install_counter_key: Option<&str>,
    native_apply_counter_key: Option<&str>,
) -> GateMetrics {
    let source = role
        .and_then(|role| data.get(role))
        .filter(|value| value.is_object())
        .unwrap_or(data);
    let mut flat = serde_json::Map::new();
    if let Some(object) = source.as_object() {
        for (key, value) in object {
            flat.insert(key.clone(), value.clone());
        }
    }
    for nested in ["metrics", "totals", "counters"] {
        if let Some(object) = source.get(nested).and_then(Value::as_object) {
            for (key, value) in object {
                flat.insert(key.clone(), value.clone());
            }
        }
    }
    let flat_value = Value::Object(flat);
    let application_count = if let Some(key) = application_counter_key {
        first_int(&flat_value, &[key]).or_else(|| counter_value(&flat_value, key))
    } else {
        first_int(&flat_value, &["application_count"])
    };
    GateMetrics {
        wrong_answers: first_int(
            &flat_value,
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
            &flat_value,
            &[
                "proof_failures",
                "proof_failure_count",
                "proof_invalid",
                "proof_errors",
            ],
        )
        .unwrap_or(0),
        witness_failures: first_int(
            &flat_value,
            &[
                "witness_failures",
                "witness_invalid",
                "witness_broken",
                "candidate_witness_failures",
            ],
        )
        .unwrap_or(0),
        crashes: first_int(
            &flat_value,
            &["crashes", "crash_count", "segfaults", "signals"],
        )
        .unwrap_or(0),
        solved: first_int(
            &flat_value,
            &["solved", "definitive", "correct", "solved_count"],
        ),
        par2: first_float(
            &flat_value,
            &["par2", "par2_total", "par2_sum_s", "par2_sec"],
        ),
        application_count,
        native_install_count: native_install_counter_key
            .and_then(|key| first_int(&flat_value, &[key])),
        native_apply_count: native_apply_counter_key.and_then(|key| first_int(&flat_value, &[key])),
        native_helper_compile_attempt_count: first_int(
            &flat_value,
            &["chc.native_code_helper_compile_attempts"],
        ),
        native_helper_compile_success_count: first_int(
            &flat_value,
            &["chc.native_code_helper_compile_successes"],
        ),
        native_helper_evaluation_count: first_int(
            &flat_value,
            &["chc.native_code_helper_evaluations"],
        ),
        native_helper_interpreter_confirmation_count: first_int(
            &flat_value,
            &["chc.native_code_helper_interpreter_confirmations"],
        ),
        native_helper_trusted_true_count: first_int(
            &flat_value,
            &["chc.native_code_helper_trusted_true_results"],
        ),
        native_helper_deopt_count: first_int(&flat_value, &["chc.native_code_helper_deopts"]),
        native_helper_fallback_count: first_int(&flat_value, &["chc.native_code_helper_fallbacks"]),
        native_helper_missing_var_fallback_count: first_int(
            &flat_value,
            &["chc.native_code_helper_missing_var_fallbacks"],
        ),
    }
}

pub fn build_gate_comparison(
    track: &str,
    artifact: &Value,
    candidate_mode: &str,
    application_counter_key: &str,
    native_install_counter_key: Option<&str>,
    native_apply_counter_key: Option<&str>,
    baseline_metrics: &GateMetrics,
    candidate_metrics: &GateMetrics,
) -> ProbeResult<Value> {
    let artifact_id = artifact_string(artifact, "id")?;
    Ok(json!({
        "schema": COMPARISON_SCHEMA,
        "track": track,
        "artifact": artifact_id,
        "artifact_id": artifact_id,
        "candidate_mode": candidate_mode,
        "gate_inputs": {
            "track": track,
            "artifact_id": artifact_id,
            "candidate_mode": candidate_mode,
            "application_counter_key": application_counter_key,
            "native_install_counter_key": native_install_counter_key,
            "native_apply_counter_key": native_apply_counter_key,
        },
        "baseline": role_payload_for_gate(
            baseline_metrics,
            application_counter_key,
            native_install_counter_key,
            native_apply_counter_key,
        ),
        "candidate": role_payload_for_gate(
            candidate_metrics,
            application_counter_key,
            native_install_counter_key,
            native_apply_counter_key,
        ),
    }))
}

pub fn missing_stats_json_failures(records: &[RunRecord], root: &Path) -> Vec<Value> {
    records
        .iter()
        .filter(|run| {
            !matches!(run.status.as_str(), "skipped" | "dry-run") && !run.stats_json_found
        })
        .map(|run| {
            json!({
                "kind": "missing-stats-json",
                "role": run.role,
                "mode": run.mode,
                "probe": display_path(&run.probe, root),
                "status": run.status,
                "returncode": run.returncode,
            })
        })
        .collect()
}

pub fn validate_options(options: &RoiProbeOptions) -> ProbeResult<()> {
    if !VALID_TRACKS.contains(&options.track.as_str()) {
        return Err(ProbeError::InvalidArgument(format!(
            "--track must be one of {}, got {}",
            VALID_TRACKS.join(", "),
            options.track
        )));
    }
    if options.max_probes == 0 {
        return Err(ProbeError::InvalidArgument(
            "--max-probes must be positive".to_string(),
        ));
    }
    if options.timeout_ms == 0 {
        return Err(ProbeError::InvalidArgument(
            "--timeout-ms must be positive".to_string(),
        ));
    }
    if options.wall_timeout_s <= 0.0 {
        return Err(ProbeError::InvalidArgument(
            "--wall-timeout-s must be positive".to_string(),
        ));
    }
    if options.kill_grace_s < 0.0 {
        return Err(ProbeError::InvalidArgument(
            "--kill-grace-s must be non-negative".to_string(),
        ));
    }
    if options.overall_timeout_s <= 0.0 {
        return Err(ProbeError::InvalidArgument(
            "--overall-timeout-s must be positive".to_string(),
        ));
    }
    Ok(())
}

pub fn run_probe(options: &RoiProbeOptions) -> ProbeResult<Value> {
    validate_options(options)?;
    let matrix = load_matrix(&options.matrix)?;
    let artifact = artifact_by_id(&matrix, &options.track, options.artifact.as_deref())?;
    let candidate_mode = choose_candidate_mode(&artifact, options.candidate_mode.as_deref());
    let baseline_mode = options.baseline_mode.clone();
    let ay = options
        .ay
        .clone()
        .unwrap_or_else(|| default_ay_binary(&options.root));
    let probes = probe_paths(
        &options.root,
        &options.track,
        &options.probes,
        options.max_probes,
    )?;
    let telemetry_counters = telemetry_counters(&matrix, &options.track)?;

    let mut records = Vec::new();
    let start = Instant::now();
    for probe in &probes {
        let roles = [
            ("baseline", baseline_mode.as_str()),
            ("candidate", candidate_mode.as_str()),
        ];
        if options.dry_run {
            for (role, mode) in roles {
                let invocation = invocation_for(
                    options,
                    &artifact,
                    role,
                    mode,
                    probe,
                    &ay,
                    &telemetry_counters,
                );
                records.push(run_one(&invocation)?);
            }
            continue;
        }
        if !probe.exists() {
            for (role, mode) in roles {
                let invocation = invocation_for(
                    options,
                    &artifact,
                    role,
                    mode,
                    probe,
                    &ay,
                    &telemetry_counters,
                );
                records.push(skipped_record(&invocation, "missing-probe-file"));
            }
            continue;
        }
        if start.elapsed().as_secs_f64() >= options.overall_timeout_s {
            for (role, mode) in roles {
                let invocation = invocation_for(
                    options,
                    &artifact,
                    role,
                    mode,
                    probe,
                    &ay,
                    &telemetry_counters,
                );
                records.push(skipped_record(&invocation, "overall-timeout"));
            }
            continue;
        }
        for (role, mode) in roles {
            let invocation = invocation_for(
                options,
                &artifact,
                role,
                mode,
                probe,
                &ay,
                &telemetry_counters,
            );
            records.push(run_one(&invocation)?);
        }
    }

    let baseline_runs = records
        .iter()
        .filter(|run| run.role == "baseline")
        .cloned()
        .collect::<Vec<_>>();
    let candidate_runs = records
        .iter()
        .filter(|run| run.role == "candidate")
        .cloned()
        .collect::<Vec<_>>();
    let baseline_summary = aggregate_summary(
        &options.track,
        &artifact,
        &baseline_mode,
        &baseline_runs,
        &telemetry_counters,
    )?;
    let candidate_summary = aggregate_summary(
        &options.track,
        &artifact,
        &candidate_mode,
        &candidate_runs,
        &telemetry_counters,
    )?;

    let application_counter_key = artifact_string(&artifact, "application_counter")?;
    let (install_counter, apply_counter) = native_dispatch_counter_keys(&artifact, &candidate_mode);
    let baseline_metrics = normalize_metrics(
        &baseline_summary,
        None,
        Some(&application_counter_key),
        install_counter.as_deref(),
        apply_counter.as_deref(),
    );
    let candidate_metrics = normalize_metrics(
        &candidate_summary,
        None,
        Some(&application_counter_key),
        install_counter.as_deref(),
        apply_counter.as_deref(),
    );
    let comparison = build_gate_comparison(
        &options.track,
        &artifact,
        &candidate_mode,
        &application_counter_key,
        install_counter.as_deref(),
        apply_counter.as_deref(),
        &baseline_metrics,
        &candidate_metrics,
    )?;

    let runnable_count = baseline_summary
        .pointer("/totals/benchmarks")
        .and_then(as_int)
        .unwrap_or(0);
    let gate_decision = if runnable_count > 0 && !options.dry_run {
        Some(
            evaluate_gate(
                &matrix,
                &options.track,
                &artifact_string(&artifact, "id")?,
                &baseline_metrics,
                &candidate_metrics,
                Some(&candidate_mode),
            )?
            .to_json(),
        )
    } else {
        None
    };
    let skipped = records.iter().filter(|run| run.status == "skipped").count();
    let evidence_failures = missing_stats_json_failures(&records, &options.root);
    let mut status = if options.dry_run {
        "dry-run".to_string()
    } else if runnable_count == 0 {
        "skipped".to_string()
    } else {
        "pass".to_string()
    };
    if !evidence_failures.is_empty() {
        status = "fail".to_string();
    }
    if gate_decision
        .as_ref()
        .and_then(|gate| gate.get("status"))
        .and_then(Value::as_str)
        .is_some_and(|gate_status| gate_status != "pass")
    {
        status = "fail".to_string();
    }

    Ok(json!({
        "schema": SCHEMA,
        "status": status,
        "settings": {
            "track": options.track,
            "artifact": artifact_string(&artifact, "id")?,
            "baseline_mode": baseline_mode,
            "candidate_mode": candidate_mode,
            "matrix": display_path(&options.matrix, &options.root),
            "ay": ay.to_string_lossy(),
            "timeout_ms": options.timeout_ms,
            "wall_timeout_s": options.wall_timeout_s,
            "overall_timeout_s": options.overall_timeout_s,
            "max_probes": options.max_probes,
            "probe_count": probes.len(),
            "skipped_runs": skipped,
        },
        "summaries": {
            "baseline": baseline_summary,
            "candidate": candidate_summary,
        },
        "comparison": comparison,
        "gate": gate_decision.unwrap_or(Value::Null),
        "evidence_failures": evidence_failures,
        "runs": records.iter().map(|run| run.to_json(&options.root)).collect::<Vec<_>>(),
    }))
}

pub fn evaluate_gate(
    matrix: &Value,
    track: &str,
    artifact_id: &str,
    baseline: &GateMetrics,
    candidate: &GateMetrics,
    candidate_mode: Option<&str>,
) -> ProbeResult<GateDecision> {
    let artifact = find_artifact(matrix, track, artifact_id)?;
    let mode = candidate_mode
        .map(str::to_string)
        .or_else(|| non_empty_string(artifact.get("default_mode")))
        .unwrap_or_else(|| "profile-only".to_string());
    if !MODES.contains(&mode.as_str()) {
        return Err(ProbeError::InvalidArgument(format!(
            "unknown JIT mode: {mode}"
        )));
    }
    let allowed_modes = artifact
        .get("candidate_modes")
        .and_then(Value::as_array)
        .map(|modes| modes.iter().filter_map(Value::as_str).collect::<Vec<_>>())
        .unwrap_or_default();
    if !allowed_modes.contains(&mode.as_str()) {
        return Err(ProbeError::InvalidArgument(format!(
            "mode {mode:?} is not allowed for {artifact_id:?}; allowed: {}",
            allowed_modes.join(", ")
        )));
    }

    let defaults = matrix.get("gate_defaults").unwrap_or(&Value::Null);
    let wrong_max = field_int(defaults, "wrong_answers_max").unwrap_or(0);
    let proof_max = field_int(defaults, "proof_failures_max").unwrap_or(0);
    let witness_max = field_int(defaults, "witness_failures_max").unwrap_or(0);
    let crashes_max = field_int(defaults, "crashes_max").unwrap_or(0);
    let solved_loss_max = field_int(defaults, "solved_count_loss_max").unwrap_or(0);
    let par2_loss_max = defaults
        .get("par2_loss_max_sec")
        .and_then(as_float)
        .unwrap_or(0.0);
    let min_applications = field_int(&artifact, "min_useful_applications")
        .or_else(|| field_int(defaults, "min_useful_applications"))
        .unwrap_or(1);
    let required_applications = required_application_minimum(&mode, &artifact, min_applications);

    let mut failures = Vec::new();
    if candidate.wrong_answers > wrong_max {
        add_failure(
            &mut failures,
            &artifact,
            "wrong_answer",
            "wrong-answer",
            format!(
                "candidate wrong answers {} > allowed {}",
                candidate.wrong_answers, wrong_max
            ),
        );
    }
    if candidate.proof_failures > proof_max {
        add_failure(
            &mut failures,
            &artifact,
            "proof_failure",
            "proof-failure",
            format!(
                "candidate proof failures {} > allowed {}",
                candidate.proof_failures, proof_max
            ),
        );
    }
    if candidate.witness_failures > witness_max {
        add_failure(
            &mut failures,
            &artifact,
            "witness_failure",
            "witness-failure",
            format!(
                "candidate witness failures {} > allowed {}",
                candidate.witness_failures, witness_max
            ),
        );
    }
    if candidate.crashes > crashes_max {
        add_failure(
            &mut failures,
            &artifact,
            "crash",
            "crash",
            format!(
                "candidate crashes {} > allowed {}",
                candidate.crashes, crashes_max
            ),
        );
    }

    match (baseline.solved, candidate.solved) {
        (Some(baseline_solved), Some(candidate_solved)) => {
            let solved_loss = baseline_solved - candidate_solved;
            if solved_loss > solved_loss_max {
                add_failure(
                    &mut failures,
                    &artifact,
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
            &artifact,
            "solved_count_loss",
            "solved-count-loss",
            "baseline and candidate solved counts are required for the A/B gate".to_string(),
        ),
    }

    match (baseline.par2, candidate.par2) {
        (Some(baseline_par2), Some(candidate_par2)) => {
            let par2_loss = candidate_par2 - baseline_par2;
            if par2_loss > par2_loss_max + EPSILON {
                add_failure(
                    &mut failures,
                    &artifact,
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
            &artifact,
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
                .map_or_else(|| "missing".to_string(), |value| value.to_string());
            add_failure(
                &mut failures,
                &artifact,
                "application_count",
                "application-count",
                format!(
                    "candidate useful applications {actual} < required {required_applications}"
                ),
            );
        }
    }

    if NATIVE_MODES.contains(&mode.as_str()) {
        let required_evidence = native_evidence_for_mode(&mode).unwrap_or("profile-only");
        let evidence_kind = artifact
            .get("evidence_kind")
            .and_then(Value::as_str)
            .unwrap_or("profile-only");
        if evidence_kind != required_evidence {
            failures.push(GateFailure {
                kind: "native-dispatch-evidence".to_string(),
                failure_mode: "profile-only".to_string(),
                detail: format!(
                    "{artifact_id} counter evidence is {evidence_kind:?}; {mode:?} requires {required_evidence:?} evidence"
                ),
            });
        }
        let (install_counter, apply_counter) = native_dispatch_counter_keys(&artifact, &mode);
        if let Some(counter) = install_counter {
            if candidate
                .native_install_count
                .is_none_or(|count| count <= 0)
            {
                failures.push(native_dispatch_counter_failure(
                    "native-install-evidence",
                    &mode,
                    &counter,
                    candidate.native_install_count,
                ));
            }
        }
        if let Some(counter) = apply_counter {
            if candidate.native_apply_count.is_none_or(|count| count <= 0) {
                failures.push(native_dispatch_counter_failure(
                    "native-apply-evidence",
                    &mode,
                    &counter,
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
        validate_chc_native_helper_current_gate(&mut failures, candidate);
    }

    let (status, recommended_mode) = if failures.is_empty() {
        ("pass".to_string(), mode.clone())
    } else if failures
        .iter()
        .any(|failure| is_integrity_failure(&failure.kind))
    {
        (
            "fail".to_string(),
            recommended_mode_from(
                failures
                    .iter()
                    .filter(|failure| is_integrity_failure(&failure.kind)),
            ),
        )
    } else {
        ("fail".to_string(), recommended_mode_from(failures.iter()))
    };
    let native_dispatch = status == "pass" && native_dispatch_allowed(&recommended_mode, &artifact);
    Ok(GateDecision {
        status,
        track: track.to_string(),
        artifact: artifact_id.to_string(),
        candidate_mode: mode,
        recommended_mode,
        native_dispatch,
        failures,
        baseline: baseline.clone(),
        candidate: candidate.clone(),
    })
}

pub fn report_json_output(report: &Value) -> ProbeResult<String> {
    Ok(format!("{}\n", serde_json::to_string_pretty(report)?))
}

pub fn write_json_report(path: &Path, report: &Value) -> ProbeResult<()> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }
    fs::write(path, report_json_output(report)?)?;
    Ok(())
}

pub fn human_report(report: &Value) -> String {
    let settings = report.get("settings").unwrap_or(&Value::Null);
    let mut lines = Vec::new();
    lines.push(format!(
        "jit_roi_probe: status={} track={} artifact={} baseline={} candidate={}",
        report.get("status").and_then(Value::as_str).unwrap_or(""),
        settings.get("track").and_then(Value::as_str).unwrap_or(""),
        settings
            .get("artifact")
            .and_then(Value::as_str)
            .unwrap_or(""),
        settings
            .get("baseline_mode")
            .and_then(Value::as_str)
            .unwrap_or(""),
        settings
            .get("candidate_mode")
            .and_then(Value::as_str)
            .unwrap_or(""),
    ));
    if let Some(runs) = report.get("runs").and_then(Value::as_array) {
        for run in runs {
            let reason = run
                .get("reason")
                .and_then(Value::as_str)
                .map(|reason| format!(" reason={reason}"))
                .unwrap_or_default();
            lines.push(format!(
                "  {} {} {} {} actual={} apps={}{}",
                run.get("role").and_then(Value::as_str).unwrap_or(""),
                run.get("mode").and_then(Value::as_str).unwrap_or(""),
                run.get("status").and_then(Value::as_str).unwrap_or(""),
                run.get("probe").and_then(Value::as_str).unwrap_or(""),
                run.get("actual").and_then(Value::as_str).unwrap_or(""),
                run.get("application_count")
                    .and_then(Value::as_i64)
                    .unwrap_or(0),
                reason,
            ));
        }
    }
    if let Some(failures) = report.get("evidence_failures").and_then(Value::as_array) {
        for failure in failures {
            lines.push(format!(
                "  failure {}: {} {} status={}",
                failure.get("kind").and_then(Value::as_str).unwrap_or(""),
                failure.get("role").and_then(Value::as_str).unwrap_or(""),
                failure.get("probe").and_then(Value::as_str).unwrap_or(""),
                failure.get("status").and_then(Value::as_str).unwrap_or(""),
            ));
        }
    }
    if let Some(gate) = report.get("gate").filter(|gate| gate.is_object()) {
        lines.push(format!(
            "gate: status={} recommended={} native_dispatch={}",
            gate.get("status").and_then(Value::as_str).unwrap_or(""),
            gate.get("recommended_mode")
                .and_then(Value::as_str)
                .unwrap_or(""),
            gate.get("native_dispatch")
                .and_then(Value::as_bool)
                .unwrap_or(false),
        ));
        if let Some(failures) = gate.get("failures").and_then(Value::as_array) {
            for failure in failures {
                lines.push(format!(
                    "  failure {}: {}",
                    failure.get("kind").and_then(Value::as_str).unwrap_or(""),
                    failure.get("detail").and_then(Value::as_str).unwrap_or(""),
                ));
            }
        }
    }
    let mut output = lines.join("\n");
    output.push('\n');
    output
}

pub fn shell_quote(arg: &str) -> String {
    if !arg.is_empty()
        && arg
            .bytes()
            .all(|byte| matches!(byte, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'@' | b'%' | b'+' | b'=' | b':' | b',' | b'.' | b'/' | b'-'))
    {
        return arg.to_string();
    }
    format!("'{}'", arg.replace('\'', "'\"'\"'"))
}

pub fn shell_join(argv: &[String]) -> String {
    argv.iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ")
}

fn default_probes(track: &str) -> ProbeResult<&'static [&'static str]> {
    match track {
        "sat" => Ok(SAT_DEFAULT_PROBES),
        "smt" => Ok(SMT_DEFAULT_PROBES),
        "pb" => Ok(PB_DEFAULT_PROBES),
        "chc" => Ok(CHC_DEFAULT_PROBES),
        _ => Err(ProbeError::InvalidArgument(format!(
            "unknown track: {track}"
        ))),
    }
}

fn status_from_smt2_prefix(text: &str) -> Option<String> {
    let lower = text.to_ascii_lowercase();
    let mut rest = lower.as_str();
    while let Some(index) = rest.find(":status") {
        rest = &rest[index + ":status".len()..];
        let token = rest
            .trim_start()
            .split(|ch: char| ch.is_whitespace() || ch == ')' || ch == '(')
            .find(|token| !token.is_empty());
        match token {
            Some("sat") => return Some("sat".to_string()),
            Some("unsat") => return Some("unsat".to_string()),
            _ => {}
        }
    }
    None
}

fn is_definitive_result(value: &str) -> bool {
    matches!(value, "sat" | "unsat" | "optimum")
}

fn value_to_string(value: &Value) -> String {
    value
        .as_str()
        .map(str::to_string)
        .unwrap_or_else(|| value.to_string())
}

fn first_int(data: &Value, names: &[&str]) -> Option<i64> {
    names
        .iter()
        .find_map(|name| data.get(*name).and_then(as_int))
}

fn first_float(data: &Value, names: &[&str]) -> Option<f64> {
    names
        .iter()
        .find_map(|name| data.get(*name).and_then(as_float))
}

fn field_int(data: &Value, key: &str) -> Option<i64> {
    data.get(key).and_then(as_int)
}

fn artifact_string(artifact: &Value, key: &str) -> ProbeResult<String> {
    artifact
        .get(key)
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| ProbeError::Matrix(format!("artifact is missing {key:?}")))
}

fn non_empty_string(value: Option<&Value>) -> Option<String> {
    value
        .and_then(Value::as_str)
        .filter(|value| !value.is_empty())
        .map(str::to_string)
}

fn read_pipe<R: Read + Send + 'static>(mut pipe: R) -> thread::JoinHandle<String> {
    thread::spawn(move || {
        let mut text = String::new();
        let _ = pipe.read_to_string(&mut text);
        text
    })
}

fn join_reader(handle: Option<thread::JoinHandle<String>>) -> String {
    handle
        .and_then(|handle| handle.join().ok())
        .unwrap_or_default()
}

fn duration_from_secs(value: f64) -> ProbeResult<Duration> {
    if value <= 0.0 || !value.is_finite() {
        return Err(ProbeError::InvalidArgument(
            "timeout seconds must be positive and finite".to_string(),
        ));
    }
    Ok(Duration::from_secs_f64(value))
}

fn round6(value: f64) -> f64 {
    (value * 1_000_000.0).round() / 1_000_000.0
}

fn invocation_for<'a>(
    options: &'a RoiProbeOptions,
    artifact: &'a Value,
    role: &'a str,
    mode: &'a str,
    probe: &'a Path,
    ay: &'a Path,
    telemetry_counters: &'a [String],
) -> RunInvocation<'a> {
    RunInvocation {
        root: &options.root,
        track: &options.track,
        artifact,
        role,
        mode,
        probe,
        ay,
        timeout_ms: options.timeout_ms,
        wall_timeout_sec: options.wall_timeout_s,
        kill_grace_sec: options.kill_grace_s,
        sat_variant: &options.sat_variant,
        pb_native: options.pb_native,
        extra_args: &options.ay_args,
        dry_run: options.dry_run,
        telemetry_counters,
    }
}

fn role_payload_for_gate(
    metrics: &GateMetrics,
    application_counter_key: &str,
    native_install_counter_key: Option<&str>,
    native_apply_counter_key: Option<&str>,
) -> Value {
    let mut counters = serde_json::Map::new();
    if let Some(value) = metrics.application_count {
        counters.insert(application_counter_key.to_string(), json!(value));
    }
    if let (Some(key), Some(value)) = (native_install_counter_key, metrics.native_install_count) {
        counters.insert(key.to_string(), json!(value));
    }
    if let (Some(key), Some(value)) = (native_apply_counter_key, metrics.native_apply_count) {
        counters.insert(key.to_string(), json!(value));
    }
    json!({
        "metrics": metrics.to_json(),
        "counters": Value::Object(counters),
    })
}

fn rule<'a>(artifact: &'a Value, name: &str) -> Option<&'a serde_json::Map<String, Value>> {
    artifact
        .get("gate")
        .and_then(Value::as_object)
        .and_then(|gate| gate.get(name))
        .and_then(Value::as_object)
}

fn add_failure(
    failures: &mut Vec<GateFailure>,
    artifact: &Value,
    rule_name: &str,
    kind: &str,
    detail: String,
) {
    let enabled = rule(artifact, rule_name)
        .and_then(|rule| rule.get("enabled"))
        .and_then(Value::as_bool)
        .unwrap_or(false);
    if !enabled && !is_integrity_failure(kind) {
        return;
    }
    failures.push(GateFailure {
        kind: kind.to_string(),
        failure_mode: safe_failure_mode(rule(artifact, rule_name), kind),
        detail,
    });
}

fn safe_failure_mode(rule: Option<&serde_json::Map<String, Value>>, kind: &str) -> String {
    if is_integrity_failure(kind) {
        return "off".to_string();
    }
    rule.and_then(|rule| rule.get("failure_mode"))
        .and_then(Value::as_str)
        .filter(|mode| matches!(*mode, "off" | "profile-only"))
        .unwrap_or("profile-only")
        .to_string()
}

fn is_integrity_failure(kind: &str) -> bool {
    INTEGRITY_FAILURES.contains(&kind)
}

fn native_evidence_for_mode(mode: &str) -> Option<&'static str> {
    match mode {
        "current" => Some("integrated-native-helper"),
        "solver-program" => Some("solver-program-native"),
        _ => None,
    }
}

fn native_dispatch_allowed(mode: &str, artifact: &Value) -> bool {
    native_evidence_for_mode(mode).is_some_and(|required| {
        artifact
            .get("evidence_kind")
            .and_then(Value::as_str)
            .unwrap_or("profile-only")
            == required
    })
}

fn required_application_minimum(mode: &str, artifact: &Value, configured_minimum: i64) -> i64 {
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
    let actual = value.map_or_else(|| "missing".to_string(), |value| value.to_string());
    GateFailure {
        kind: kind.to_string(),
        failure_mode: "profile-only".to_string(),
        detail: format!(
            "{mode:?} native dispatch requires positive {counter:?} evidence, got {actual}"
        ),
    }
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
        failures.push(GateFailure {
            kind: "native-helper-accepted-true".to_string(),
            failure_mode: "profile-only".to_string(),
            detail: format!(
                "candidate CHC native-helper accepted true evidence must be > 0, got interpreter_confirmations={confirmations}, trusted_true={trusted_true}"
            ),
        });
    }
    if accepted_true_results != applications {
        failures.push(GateFailure {
            kind: "native-helper-accepted-true".to_string(),
            failure_mode: "profile-only".to_string(),
            detail: format!(
                "candidate CHC native-helper interpreter confirmations plus trusted true results must equal useful applications {applications}, got {accepted_true_results}"
            ),
        });
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

fn positive_counter_gate_failure(kind: &str, label: &str, value: Option<i64>) -> GateFailure {
    let actual = value.map_or_else(|| "missing".to_string(), |value| value.to_string());
    GateFailure {
        kind: kind.to_string(),
        failure_mode: "profile-only".to_string(),
        detail: format!("candidate {label} evidence must be > 0, got {actual}"),
    }
}

fn zero_counter_gate_failure(kind: &str, label: &str, value: Option<i64>) -> GateFailure {
    let actual = value.map_or_else(|| "missing".to_string(), |value| value.to_string());
    GateFailure {
        kind: kind.to_string(),
        failure_mode: "profile-only".to_string(),
        detail: format!("candidate {label} evidence must be 0, got {actual}"),
    }
}

fn recommended_mode_from<'a>(failures: impl Iterator<Item = &'a GateFailure>) -> String {
    failures
        .map(|failure| failure.failure_mode.as_str())
        .min_by_key(|mode| if *mode == "off" { 0 } else { 1 })
        .unwrap_or("profile-only")
        .to_string()
}
