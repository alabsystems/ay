// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(dead_code, missing_docs, unreachable_pub)]

//! Runner-side command generation for known external code generation ROI hot inputs.
//!
//! This module provides product-owned hot-input command generation.  The
//! functions here are intentionally side-effect free:
//! callers get JSON payloads or shell text that can be written by a higher-level
//! command.

#![allow(unused_qualifications)]

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::path::{Path, PathBuf};

use serde_json::{json, Value};

pub const SCHEMA: &str = "ay.jit-roi-hot-inputs/v1";
pub const ISSUE: u64 = 9088;
pub const DEFAULT_REPORT_DIR: &str = "the development design notes";
pub const DEFAULT_TIMEOUT_MS: u64 = 1000;
pub const DEFAULT_WALL_TIMEOUT_SEC: f64 = 2.0;
pub const DEFAULT_OVERALL_TIMEOUT_SEC: f64 = 30.0;

const QF_LRA_HOT_PROBES: &[&str] = &[
    "benchmarks/smtcomp/QF_LRA/synched.base.smt2",
    "benchmarks/smtcomp/QF_LRA/constraints-tempo-width-10.smt2",
];

const PB_NATIVE_HELPER_HOT_PROBES: &[&str] = &[
    "benchmarks/pb-comp/test-instances/cardinality-5.opb",
    "benchmarks/pb-comp/test-instances/pigeonhole-3-2.opb",
];

const SMT_LRA_SPARSE_EXPECTED_COUNTERS: &[CounterExpectation] = &[
    CounterExpectation::equals("solver_program.schema_version", 1),
    CounterExpectation::equals("solver_program.profile.lra_sparse_substitute.enabled", 1),
    CounterExpectation::minimum_with_fixture(
        "lra_external_codegen_backend_substitute_wrapper_applies",
        1,
        3,
    ),
    CounterExpectation::minimum_with_fixture(
        "lra_external_codegen_backend_substitute_native_applies",
        1,
        3,
    ),
];

const SMT_LRA_BASIS_EXPECTED_COUNTERS: &[CounterExpectation] = &[
    CounterExpectation::equals("solver_program.schema_version", 1),
    CounterExpectation::equals("solver_program.profile.lra_basis_region.enabled", 1),
    CounterExpectation::minimum_with_fixture(
        "solver_program.lra_basis_region.batch_native_applies",
        1,
        5,
    ),
    CounterExpectation::minimum_with_fixture(
        "solver_program.lra_basis_region.boundary_checks",
        1,
        9,
    ),
    CounterExpectation::minimum_with_fixture(
        "solver_program.lra_basis_region.requests_queued",
        1,
        7,
    ),
];

const PB_NATIVE_EXPECTED_COUNTERS: &[CounterExpectation] = &[CounterExpectation::minimum(
    "pb_native_code_helper_applications",
    1,
)];

const EXPECTED_TOTALS: &[ExpectedTotal] = &[
    ExpectedTotal::new("minimum_solved", 2),
    ExpectedTotal::new("wrong_answers", 0),
    ExpectedTotal::new("proof_failures", 0),
    ExpectedTotal::new("witness_failures", 0),
    ExpectedTotal::new("crashes", 0),
];

pub static HOT_INPUTS: &[HotInput] = &[
    HotInput {
        id: "smt-lra-sparse-substitute-profile-hot",
        description: "QF_LRA sparse-substitute profile input pair with expected external code generation native substitute applications.",
        track: "smt",
        artifact: "smt-lra-sparse-substitute",
        candidate_mode: "profile-only",
        application_counter: "lra_external_codegen_backend_substitute_native_applies",
        probes: QF_LRA_HOT_PROBES,
        expected_counters: SMT_LRA_SPARSE_EXPECTED_COUNTERS,
        expected_totals: EXPECTED_TOTALS,
        source_fixture: "tests/fixtures/competition_jit_stats/smt_lra_sparse_substitute_stats.json",
        probe_args: &[],
    },
    HotInput {
        id: "smt-lra-basis-regions-profile-hot",
        description: "QF_LRA basis-region profile input pair with expected native batch applies plus safe-boundary and queued-region telemetry.",
        track: "smt",
        artifact: "smt-lra-basis-regions",
        candidate_mode: "profile-only",
        application_counter: "solver_program.lra_basis_region.batch_native_applies",
        probes: QF_LRA_HOT_PROBES,
        expected_counters: SMT_LRA_BASIS_EXPECTED_COUNTERS,
        expected_totals: EXPECTED_TOTALS,
        source_fixture: "tests/fixtures/competition_jit_stats/smt_lra_basis_region_stats.json",
        probe_args: &[],
    },
    HotInput {
        id: "pb-native-code-helpers-profile-hot",
        description: "PB native-code helper profile input pair with expected useful helper applications. Requires an EXTERNAL_CODEGEN feature build plus ay PB --native, emitted here through ay competition-jit probe --pb-native; this is profile-only evidence, not current-mode dispatch.",
        track: "pb",
        artifact: "pb-native-code-helpers",
        candidate_mode: "profile-only",
        application_counter: "pb_native_code_helper_applications",
        probes: PB_NATIVE_HELPER_HOT_PROBES,
        expected_counters: PB_NATIVE_EXPECTED_COUNTERS,
        expected_totals: EXPECTED_TOTALS,
        source_fixture: "",
        probe_args: &["--pb-native"],
    },
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CounterExpectation {
    pub key: &'static str,
    pub equals: Option<i64>,
    pub minimum: Option<i64>,
    pub fixture_value: Option<i64>,
}

impl CounterExpectation {
    pub const fn equals(key: &'static str, value: i64) -> Self {
        Self {
            key,
            equals: Some(value),
            minimum: None,
            fixture_value: None,
        }
    }

    pub const fn minimum(key: &'static str, value: i64) -> Self {
        Self {
            key,
            equals: None,
            minimum: Some(value),
            fixture_value: None,
        }
    }

    pub const fn minimum_with_fixture(key: &'static str, minimum: i64, fixture_value: i64) -> Self {
        Self {
            key,
            equals: None,
            minimum: Some(minimum),
            fixture_value: Some(fixture_value),
        }
    }

    pub fn to_json(self) -> Value {
        let mut spec = serde_json::Map::new();
        if let Some(value) = self.equals {
            spec.insert("equals".to_string(), json!(value));
        }
        if let Some(value) = self.minimum {
            spec.insert("minimum".to_string(), json!(value));
        }
        if let Some(value) = self.fixture_value {
            spec.insert("fixture_value".to_string(), json!(value));
        }
        Value::Object(spec)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ExpectedTotal {
    pub key: &'static str,
    pub value: i64,
}

impl ExpectedTotal {
    pub const fn new(key: &'static str, value: i64) -> Self {
        Self { key, value }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct HotInput {
    pub id: &'static str,
    pub description: &'static str,
    pub track: &'static str,
    pub artifact: &'static str,
    pub candidate_mode: &'static str,
    pub application_counter: &'static str,
    pub probes: &'static [&'static str],
    pub expected_counters: &'static [CounterExpectation],
    pub expected_totals: &'static [ExpectedTotal],
    pub source_fixture: &'static str,
    pub probe_args: &'static [&'static str],
}

#[derive(Clone, Debug, PartialEq)]
pub struct HotInputCommandOptions {
    pub artifacts: Vec<String>,
    pub ay: Option<PathBuf>,
    pub report_dir: PathBuf,
    pub timeout_ms: u64,
    pub wall_timeout_s: f64,
    pub overall_timeout_s: f64,
    pub fail_on_gate_fail: bool,
}

impl Default for HotInputCommandOptions {
    fn default() -> Self {
        Self {
            artifacts: Vec::new(),
            ay: None,
            report_dir: PathBuf::from(DEFAULT_REPORT_DIR),
            timeout_ms: DEFAULT_TIMEOUT_MS,
            wall_timeout_s: DEFAULT_WALL_TIMEOUT_SEC,
            overall_timeout_s: DEFAULT_OVERALL_TIMEOUT_SEC,
            fail_on_gate_fail: true,
        }
    }
}

#[derive(Debug)]
pub enum HotInputError {
    InvalidArgument(String),
    Json(serde_json::Error),
}

impl fmt::Display for HotInputError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidArgument(message) => f.write_str(message),
            Self::Json(err) => err.fmt(f),
        }
    }
}

impl Error for HotInputError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::InvalidArgument(_) => None,
            Self::Json(err) => Some(err),
        }
    }
}

impl From<serde_json::Error> for HotInputError {
    fn from(err: serde_json::Error) -> Self {
        Self::Json(err)
    }
}

pub type HotInputResult<T> = std::result::Result<T, HotInputError>;

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

pub fn display_path(path: impl AsRef<Path>, root: impl AsRef<Path>) -> String {
    let path = path.as_ref();
    path.strip_prefix(root.as_ref())
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

pub fn known_hot_inputs() -> &'static [HotInput] {
    HOT_INPUTS
}

pub fn artifact_ids() -> Vec<&'static str> {
    HOT_INPUTS.iter().map(|item| item.artifact).collect()
}

pub fn selected_hot_inputs(artifacts: &[String]) -> HotInputResult<Vec<&'static HotInput>> {
    if artifacts.is_empty() {
        return Ok(HOT_INPUTS.iter().collect());
    }

    let known: BTreeSet<&str> = HOT_INPUTS.iter().map(|item| item.artifact).collect();
    let unknown: Vec<&str> = artifacts
        .iter()
        .map(String::as_str)
        .filter(|artifact| !known.contains(artifact))
        .collect();
    if !unknown.is_empty() {
        return Err(HotInputError::InvalidArgument(format!(
            "unknown artifact(s): {}; known: {}",
            unknown.join(", "),
            known.iter().copied().collect::<Vec<_>>().join(", ")
        )));
    }

    let requested: BTreeSet<&str> = artifacts.iter().map(String::as_str).collect();
    Ok(HOT_INPUTS
        .iter()
        .filter(|item| requested.contains(item.artifact))
        .collect())
}

pub fn validate_options(options: &HotInputCommandOptions) -> HotInputResult<()> {
    if options.timeout_ms == 0 {
        return Err(HotInputError::InvalidArgument(
            "--timeout-ms must be positive".to_string(),
        ));
    }
    if options.wall_timeout_s <= 0.0 {
        return Err(HotInputError::InvalidArgument(
            "--wall-timeout-s must be positive".to_string(),
        ));
    }
    if options.overall_timeout_s <= 0.0 {
        return Err(HotInputError::InvalidArgument(
            "--overall-timeout-s must be positive".to_string(),
        ));
    }
    let _ = selected_hot_inputs(&options.artifacts)?;
    Ok(())
}

pub fn command_argv(item: &HotInput, options: &HotInputCommandOptions, root: &Path) -> Vec<String> {
    let report_path = options.report_dir.join(format!("{}.json", item.id));
    let mut argv = vec![
        options
            .ay
            .as_ref()
            .map(|path| path.to_string_lossy().into_owned())
            .unwrap_or_else(|| "ay".to_string()),
        "competition-jit".to_string(),
        "probe".to_string(),
        "--track".to_string(),
        item.track.to_string(),
        "--artifact".to_string(),
        item.artifact.to_string(),
        "--baseline-mode".to_string(),
        "off".to_string(),
        "--candidate-mode".to_string(),
        item.candidate_mode.to_string(),
        "--timeout-ms".to_string(),
        options.timeout_ms.to_string(),
        "--wall-timeout-s".to_string(),
        float_arg(options.wall_timeout_s),
        "--overall-timeout-s".to_string(),
        float_arg(options.overall_timeout_s),
        "--out".to_string(),
        display_path(report_path, root),
        "--json".to_string(),
    ];
    argv.extend(item.probe_args.iter().map(|arg| (*arg).to_string()));
    for probe in item.probes {
        argv.extend(["--probe".to_string(), (*probe).to_string()]);
    }
    if options.fail_on_gate_fail {
        argv.push("--fail-on-gate-fail".to_string());
    }
    argv
}

pub fn item_payload(item: &HotInput, options: &HotInputCommandOptions, root: &Path) -> Value {
    let argv = command_argv(item, options, root);
    json!({
        "id": item.id,
        "description": item.description,
        "track": item.track,
        "artifact": item.artifact,
        "candidate_mode": item.candidate_mode,
        "baseline_mode": "off",
        "application_counter": item.application_counter,
        "probes": item.probes,
        "expected_counters": expected_counters_json(item.expected_counters),
        "expected_totals": expected_totals_json(item.expected_totals),
        "source_fixture": item.source_fixture,
        "probe_args": item.probe_args,
        "argv": argv,
        "command": shell_join(&argv),
    })
}

pub fn build_packet(options: &HotInputCommandOptions) -> HotInputResult<Value> {
    build_packet_with_root(options, &default_repo_root())
}

pub fn build_packet_with_root(
    options: &HotInputCommandOptions,
    root: &Path,
) -> HotInputResult<Value> {
    validate_options(options)?;
    let commands: Vec<Value> = selected_hot_inputs(&options.artifacts)?
        .into_iter()
        .map(|item| item_payload(item, options, root))
        .collect();
    Ok(json!({
        "schema": SCHEMA,
        "issue": ISSUE,
        "generator": "ay competition-jit hot-inputs",
        "description": "Replay commands for EXTERNAL_CODEGEN/JIT ROI probes with expected positive application counters.",
        "settings": {
            "report_dir": options.report_dir.to_string_lossy(),
            "timeout_ms": options.timeout_ms,
            "wall_timeout_s": options.wall_timeout_s,
            "overall_timeout_s": options.overall_timeout_s,
            "fail_on_gate_fail": options.fail_on_gate_fail,
        },
        "commands": commands,
    }))
}

pub fn expected_counter_summary(counters: &[CounterExpectation]) -> String {
    counters
        .iter()
        .map(|spec| {
            if let Some(value) = spec.equals {
                format!("{}=={}", spec.key, value)
            } else if let Some(value) = spec.minimum {
                format!("{}>={}", spec.key, value)
            } else {
                spec.key.to_string()
            }
        })
        .collect::<Vec<_>>()
        .join(", ")
}

pub fn shell_lines(packet: &Value) -> Vec<String> {
    let mut lines = Vec::new();
    let schema = packet
        .get("schema")
        .and_then(Value::as_str)
        .unwrap_or(SCHEMA);
    let issue = packet.get("issue").and_then(Value::as_u64).unwrap_or(ISSUE);
    lines.push(format!("# {schema} issue=#{issue}"));
    if let Some(commands) = packet.get("commands").and_then(Value::as_array) {
        for entry in commands {
            let artifact = entry.get("artifact").and_then(Value::as_str).unwrap_or("");
            let summary = known_summary_for_entry(entry).unwrap_or_else(|| {
                entry
                    .get("expected_counters")
                    .map(expected_counter_summary_from_json)
                    .unwrap_or_default()
            });
            lines.push(format!("# {artifact}: {summary}"));
            lines.push(
                entry
                    .get("command")
                    .and_then(Value::as_str)
                    .unwrap_or("")
                    .to_string(),
            );
        }
    }
    lines
}

pub fn shell_output(packet: &Value) -> String {
    let mut output = shell_lines(packet).join("\n");
    output.push('\n');
    output
}

pub fn json_output(packet: &Value) -> HotInputResult<String> {
    Ok(format!("{}\n", serde_json::to_string_pretty(packet)?))
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

fn expected_counters_json(counters: &[CounterExpectation]) -> Value {
    let mut object = serde_json::Map::new();
    for counter in counters {
        object.insert(counter.key.to_string(), counter.to_json());
    }
    Value::Object(object)
}

fn expected_totals_json(totals: &[ExpectedTotal]) -> Value {
    let mut object = serde_json::Map::new();
    for total in totals {
        object.insert(total.key.to_string(), json!(total.value));
    }
    Value::Object(object)
}

fn expected_counter_summary_from_json(value: &Value) -> String {
    let Some(object) = value.as_object() else {
        return String::new();
    };
    let mut pieces = Vec::new();
    for (key, spec) in object {
        if let Some(equals) = spec.get("equals").and_then(Value::as_i64) {
            pieces.push(format!("{key}=={equals}"));
        } else if let Some(minimum) = spec.get("minimum").and_then(Value::as_i64) {
            pieces.push(format!("{key}>={minimum}"));
        } else {
            pieces.push(key.clone());
        }
    }
    pieces.join(", ")
}

fn known_summary_for_entry(entry: &Value) -> Option<String> {
    let id = entry.get("id").and_then(Value::as_str)?;
    HOT_INPUTS
        .iter()
        .find(|item| item.id == id)
        .map(|item| expected_counter_summary(item.expected_counters))
}

fn float_arg(value: f64) -> String {
    let mut text = value.to_string();
    if !text.contains('.') && !text.contains('e') && !text.contains('E') {
        text.push_str(".0");
    }
    text
}

pub fn expected_counters_as_map(
    counters: &[CounterExpectation],
) -> BTreeMap<&'static str, CounterExpectation> {
    counters
        .iter()
        .map(|counter| (counter.key, *counter))
        .collect()
}
