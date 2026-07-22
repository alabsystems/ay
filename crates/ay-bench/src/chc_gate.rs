// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! First-class CHC completion gate for CHC-COMP-shaped evidence.
//!
//! This is the native Rust replacement for score-bearing CHC workbench use:
//! it loads workbench JSON and CHC-COMP `.set` manifests, runs AY with stats
//! JSON enabled, checks validation and route telemetry, scores solved/PAR-2,
//! and writes durable admission artifacts.

use crate::error::{BenchError, Result, WithContext};
use serde::Serialize;
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{ExitStatus, Stdio};
use std::time::Instant;

const REPORT_SCHEMA: &str = "ay.chc-gate-report/v1";
const CASES_SCHEMA: &str = "ay.chc-gate-cases/v1";
const ROUTE_COUNTERS_SCHEMA: &str = "ay.chc-gate-route-counters/v1";
const DEFAULT_MODE: &str = "current";
const MAX_CHC_CASES: usize = 100_000;
const MAX_CHC_CASE_ID_BYTES: usize = 512;
const MAX_CHC_TRAVERSAL_ENTRIES: usize = 500_000;
const MAX_CHC_PENDING_DIRECTORIES: usize = 50_000;
#[cfg(not(test))]
const MAX_CHC_INPUT_BYTES: u64 = 8 * 1024 * 1024 * 1024;
#[cfg(test)]
const MAX_CHC_INPUT_BYTES: u64 = 1024 * 1024;
const DEFAULT_ROUTE_COUNTER_PREFIXES: &[&str] = &[
    "chc.",
    "chc_",
    "accelerated_summary.",
    "accelerated_summary_",
    "route_counters.",
];

pub const CORE_CHC_CATEGORIES: &[&str] = &[
    "BOOL",
    "BV",
    "BV-Lin",
    "LRA-Lin",
    "LIA-Lin",
    "LIA",
    "LIA-Arrays",
    "LIA-Lin-Arrays",
    "ADT-LIA",
    "ADT-LIA-Arrays",
    "mixed_LIA_LRA",
];

const CHC_2026_TRACK_CATEGORIES: &[&str] = &[
    "BOOL",
    "BV",
    "BV-Lin",
    "LRA-Lin",
    "LIA-Lin",
    "LIA",
    "LIA-Arrays",
    "LIA-Lin-Arrays",
    "ADT-LIA",
    "ADT-LIA-Arrays",
    "mixed_LIA_LRA",
    "LIA-Nonlin",
    "LIA-Nonlin-Arrays",
    "BV-Nonlin",
];

const SAMPLE_CASES: &[(&str, &str, &str)] = &[
    ("LIA-Lin", "benchmarks/chc/counter_safe_chccomp.smt2", "sat"),
    ("BV-Lin", "benchmarks/chc/bv64_counter_safe.smt2", "sat"),
    (
        "LIA-Lin-Arrays",
        "benchmarks/chc/array_simple_safe.smt2",
        "sat",
    ),
    (
        "ADT-LIA-Arrays",
        "tests/chc/regression/false_proof_array_chain.smt2",
        "unsat",
    ),
];

/// Arguments for `ay bench chc-gate`.
#[derive(Debug)]
pub struct ChcGateArgs {
    pub manifest: Option<PathBuf>,
    pub roots: Vec<String>,
    pub sample: bool,
    pub out_dir: PathBuf,
    pub ay: PathBuf,
    pub timeout_sec: f64,
    pub baseline: Option<PathBuf>,
    pub category: Option<String>,
    pub require_all_categories: bool,
    pub require_route_counters: Vec<String>,
    pub allow_dirty: bool,
    pub fail_on_wrong: bool,
    pub fail_on_invalid: bool,
    pub min_solved_delta: isize,
    pub max_par2_regression_pct: f64,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct ManifestCase {
    pub case_id: String,
    #[serde(skip_serializing)]
    pub path: PathBuf,
    pub category: String,
    pub family: String,
    pub expected_status: String,
    pub expected_source: String,
    pub source: String,
    pub required_route_counters: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
struct GitProvenance {
    source_commit: String,
    source_commit_short: String,
    source_branch: String,
    source_dirty: bool,
    source_dirty_entries: usize,
    source_git_status_short: String,
}

#[derive(Debug, Clone, Serialize)]
struct BinaryProvenance {
    path: String,
    exists: bool,
    sha256: String,
    size_bytes: Option<u64>,
    mtime_epoch: Option<i64>,
    version: Option<String>,
}

#[derive(Debug, Clone, Serialize, Default)]
struct ValidationTelemetry {
    safe_attempts: Option<u64>,
    safe_successes: Option<u64>,
    safe_failures: Option<u64>,
    unsafe_attempts: Option<u64>,
    unsafe_successes: Option<u64>,
    unsafe_failures: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Default)]
struct TransformMemoryTelemetry {
    reversible_count: Option<u64>,
    obligation_count: Option<u64>,
}

#[derive(Debug, Clone, Serialize, Default)]
struct RouteTelemetry {
    name: Option<String>,
    accepted_by_firewall: Option<bool>,
    fail_closed_reason: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct CaseRecord {
    schema: &'static str,
    case_id: String,
    /// Manifest/corpus path used to select the case.
    path: String,
    /// Exact private, read-only snapshot supplied to AY.
    solver_input_path: String,
    input_sha256: String,
    input_size_bytes: u64,
    category: String,
    family: String,
    expected_status: String,
    expected_source: String,
    source: String,
    status: String,
    classification: String,
    solved: bool,
    wrong: bool,
    invalid: bool,
    invalid_reasons: Vec<String>,
    elapsed_s: Option<f64>,
    par2_s: f64,
    timed_out: bool,
    exit_code: Option<i32>,
    process_status: String,
    stats_json_present: bool,
    stats_json_path: String,
    validation: ValidationTelemetry,
    transform_memory: TransformMemoryTelemetry,
    route: RouteTelemetry,
    route_counters: BTreeMap<String, f64>,
    required_route_counters: Vec<String>,
    missing_required_route_counters: Vec<String>,
    stdout: String,
    stderr: String,
    command_argv: Vec<String>,
    command_env: BTreeMap<String, String>,
}

#[derive(Debug, Clone, Serialize)]
struct CategorySummary {
    category: String,
    total: usize,
    solved: usize,
    solved_sat: usize,
    solved_unsat: usize,
    wrong: usize,
    invalid: usize,
    unknown: usize,
    timeout: usize,
    memout: usize,
    error: usize,
    par2_total: f64,
    par2_avg: f64,
    stats_json_cases: usize,
    route_counter_cases: usize,
}

#[derive(Debug, Clone, Serialize)]
struct OverallSummary {
    total: usize,
    solved: usize,
    solved_sat: usize,
    solved_unsat: usize,
    wrong: usize,
    invalid: usize,
    unknown: usize,
    timeout: usize,
    memout: usize,
    error: usize,
    par2_total: f64,
    par2_avg: f64,
    dirty: bool,
    promotable: bool,
    admitted: bool,
}

#[derive(Debug, Clone, Serialize)]
struct BaselineStats {
    source: String,
    solved: Option<usize>,
    par2_total: Option<f64>,
    resource_plan: Option<crate::resource::ResourcePlan>,
    timeout_sec: Option<f64>,
    resource_enforcement: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct GateCheck {
    name: String,
    status: String,
    reason: String,
}

#[derive(Debug, Clone, Serialize)]
struct RouteCounterSummary {
    schema: &'static str,
    required: Vec<String>,
    counters: BTreeMap<String, RouteCounterAggregate>,
}

#[derive(Debug, Clone, Serialize, Default)]
struct RouteCounterAggregate {
    rows_present: usize,
    rows_exercised: usize,
    total: f64,
    cases: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
struct ChcGateReport {
    schema: &'static str,
    manifest: String,
    out_dir: String,
    timeout_sec: f64,
    dirty_evidence_explicitly_allowed: bool,
    category_override: Option<String>,
    require_all_categories: bool,
    require_route_counters: Vec<String>,
    git: GitProvenance,
    ay: BinaryProvenance,
    evidence_warnings: Vec<String>,
    non_promotable_reasons: Vec<String>,
    checks: Vec<GateCheck>,
    summary: OverallSummary,
    categories: Vec<CategorySummary>,
    baseline: Option<BaselineStats>,
    artifacts: BTreeMap<String, String>,
    resource_plan: crate::resource::ResourcePlan,
    resource_enforcement: &'static str,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ExpectedOrigin {
    Sidecar,
    SidecarInvalid,
    None,
}

#[derive(Debug, Clone)]
struct ExpectedVerdict {
    status: Option<String>,
    source: String,
    origin: ExpectedOrigin,
}

/// Run the CHC gate and write `summary.json`, `cases.jsonl`,
/// `category-summary.csv`, `route-counters.json`, and `admission.md`.
pub fn cmd_chc_gate(args: ChcGateArgs) -> Result<()> {
    crate::resource::checked_benchmark_timeout(args.timeout_sec, "CHC gate")?;
    if !args.max_par2_regression_pct.is_finite() || args.max_par2_regression_pct < 0.0 {
        return Err(BenchError::InvalidArgs {
            reason: "--max-par2-regression-pct must be finite and non-negative".to_string(),
        });
    }
    let resources = crate::resource::PlannedResources::plan(&repo_root(), 1, "ay bench chc-gate")?;
    eprintln!(
        "chc-gate: resource plan jobs=1 memory={}MiB NBCORE={} headroom={}MiB enforcement=ay --memory + rss_watchdog",
        resources.plan.memlimit_mb_per_child,
        resources.plan.nbcore_per_child,
        resources.plan.headroom_mb,
    );

    let git = git_provenance();
    if git.source_dirty && !args.allow_dirty {
        return Err(BenchError::InvalidArgs {
            reason:
                "source tree is dirty; pass --allow-dirty to label evidence dirty/non-promotable"
                    .to_string(),
        });
    }

    let mut cases = Vec::new();
    if args.sample {
        extend_cases_bounded(
            &mut cases,
            load_sample_cases(args.category.as_deref())?,
            "sample cases",
        )?;
    }
    for root in &args.roots {
        extend_cases_bounded(
            &mut cases,
            load_root_spec(root, args.category.as_deref())?,
            root,
        )?;
    }
    if let Some(manifest) = &args.manifest {
        extend_cases_bounded(
            &mut cases,
            load_manifest_spec(&manifest.display().to_string(), args.category.as_deref())?,
            &manifest.display().to_string(),
        )?;
    }
    if cases.is_empty() {
        return Err(BenchError::InvalidArgs {
            reason: "no CHC cases found; pass --manifest, --root, or --sample".to_string(),
        });
    }
    cases.sort_by(|a, b| a.case_id.cmp(&b.case_id));
    validate_manifest_cases(&cases)?;
    let ay_pinned = crate::environment::PinnedSolver::capture(
        &args.ay,
        &resources,
        "ay bench chc-gate pinned AY version probe",
    )?;

    fs::create_dir_all(&args.out_dir).with_bench_context(|| {
        format!("creating CHC gate output dir {}", args.out_dir.display())
    })?;
    let run_dir = args.out_dir.join("runs");
    fs::create_dir_all(&run_dir)
        .with_bench_context(|| format!("creating CHC gate run dir {}", run_dir.display()))?;

    let mut records = Vec::with_capacity(cases.len());
    for case in &cases {
        records.push(run_case(
            case,
            &args,
            &run_dir,
            &resources,
            ay_pinned.execution_path(),
        )?);
    }

    let categories = summarize_categories(&records);
    let mut summary = summarize_overall(&records, git.source_dirty);
    let baseline = args
        .baseline
        .as_ref()
        .map(|path| load_baseline(path))
        .transpose()?;
    let route_counters = summarize_route_counters(&records, &args.require_route_counters);
    let mut checks = gate_checks(
        &records,
        &categories,
        baseline.as_ref(),
        &resources.plan,
        &args,
    );
    let mut non_promotable_reasons = non_promotable_reasons(&records, &git, &checks);
    if git.source_dirty && args.allow_dirty {
        non_promotable_reasons
            .push("source tree is dirty; --allow-dirty marks this as diagnostic-only".to_string());
    }
    non_promotable_reasons.sort();
    non_promotable_reasons.dedup();
    summary.promotable = non_promotable_reasons.is_empty();
    summary.admitted = summary.promotable && checks.iter().all(|check| check.status == "pass");

    let artifacts = artifact_map(&args.out_dir);
    ay_pinned.verify_source()?;
    let report = ChcGateReport {
        schema: REPORT_SCHEMA,
        manifest: manifest_label(&args),
        out_dir: args.out_dir.display().to_string(),
        timeout_sec: args.timeout_sec,
        dirty_evidence_explicitly_allowed: args.allow_dirty,
        category_override: args.category.clone(),
        require_all_categories: args.require_all_categories,
        require_route_counters: args.require_route_counters.clone(),
        git,
        ay: binary_provenance(&ay_pinned)?,
        evidence_warnings: evidence_warnings(&records),
        non_promotable_reasons,
        checks: std::mem::take(&mut checks),
        summary,
        categories,
        baseline,
        artifacts,
        resource_plan: resources.plan.clone(),
        resource_enforcement: crate::resource::ENFORCEMENT_AY_MEMORY_RSS_V1,
    };

    write_json(&args.out_dir.join("summary.json"), &report)?;
    write_cases_jsonl(&args.out_dir.join("cases.jsonl"), &records)?;
    write_category_csv(
        &args.out_dir.join("category-summary.csv"),
        &report.categories,
    )?;
    write_json(&args.out_dir.join("route-counters.json"), &route_counters)?;
    write_admission_markdown(&args.out_dir.join("admission.md"), &report)?;

    println!(
        "chc-gate summary: {}",
        args.out_dir.join("summary.json").display()
    );
    println!(
        "chc-gate admission: {}",
        args.out_dir.join("admission.md").display()
    );

    let mut fatal = Vec::new();
    if args.fail_on_wrong && report.summary.wrong > 0 {
        fatal.push(format!("wrong rows present: {}", report.summary.wrong));
    }
    if args.fail_on_invalid && report.summary.invalid > 0 {
        fatal.push(format!("invalid rows present: {}", report.summary.invalid));
    }
    fatal.extend(
        report
            .checks
            .iter()
            .filter(|check| check.status == "fail")
            .map(|check| format!("{}: {}", check.name, check.reason)),
    );
    if !fatal.is_empty() {
        return Err(BenchError::ScoringFailed {
            reason: fatal.join("; "),
        });
    }

    Ok(())
}

fn extend_cases_bounded(
    cases: &mut Vec<ManifestCase>,
    additional: Vec<ManifestCase>,
    source: &str,
) -> Result<()> {
    let total = cases
        .len()
        .checked_add(additional.len())
        .ok_or_else(|| BenchError::msg("CHC case count overflow"))?;
    if total > MAX_CHC_CASES {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "CHC inputs exceed the fixed {MAX_CHC_CASES}-case cap while adding {source}"
            ),
        });
    }
    cases.extend(additional);
    Ok(())
}

fn repo_root() -> PathBuf {
    let mut dir = std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
    loop {
        if dir.join("Cargo.toml").exists() && dir.join("crates").exists() {
            return dir;
        }
        if !dir.pop() {
            return std::env::current_dir().unwrap_or_else(|_| PathBuf::from("."));
        }
    }
}

fn display_path(path: &Path) -> String {
    let root = repo_root();
    path.strip_prefix(&root).map_or_else(
        |_| path.display().to_string(),
        |rel| rel.display().to_string(),
    )
}

fn manifest_label(args: &ChcGateArgs) -> String {
    let mut parts = Vec::new();
    if args.sample {
        parts.push("sample".to_string());
    }
    parts.extend(args.roots.iter().map(|root| format!("root:{root}")));
    if let Some(path) = &args.manifest {
        parts.push(path.display().to_string());
    }
    if parts.is_empty() {
        "none".to_string()
    } else {
        parts.join("+")
    }
}

fn parse_labeled_path(raw: &str) -> (Option<String>, String) {
    let Some((label, value)) = raw.split_once('=') else {
        return (None, raw.to_string());
    };
    if label.is_empty() || label.contains('/') || label.contains('\\') {
        return (None, raw.to_string());
    }
    (Some(label.trim().to_string()), value.trim().to_string())
}

fn resolve_cli_path(raw: &str, base: Option<&Path>) -> PathBuf {
    let path = PathBuf::from(raw);
    if path.is_absolute() {
        return path;
    }
    let root_candidate = repo_root().join(&path);
    if root_candidate.exists() {
        return root_candidate;
    }
    if let Some(base) = base {
        return base.join(path);
    }
    root_candidate
}

fn normalize_expected_status(value: &Value) -> Option<String> {
    match value {
        Value::Bool(true) => Some("sat".to_string()),
        Value::Bool(false) => Some("unsat".to_string()),
        Value::String(text) => normalize_expected_text(text),
        Value::Number(number) => normalize_expected_text(&number.to_string()),
        _ => None,
    }
}

fn normalize_expected_text(value: &str) -> Option<String> {
    let text = value
        .trim()
        .trim_matches(|ch| ch == '\'' || ch == '"')
        .to_ascii_lowercase();
    match text.as_str() {
        "sat" | "true" | "safe" => Some("sat".to_string()),
        "unsat" | "false" | "unsafe" => Some("unsat".to_string()),
        "unknown" => Some("unknown".to_string()),
        _ => None,
    }
}

fn clean_yaml_scalar(value: &str) -> String {
    value
        .split('#')
        .next()
        .unwrap_or("")
        .trim()
        .trim_end_matches(',')
        .trim_matches(|ch| ch == '\'' || ch == '"')
        .to_string()
}

fn read_sidecar_input_file(path: &Path) -> Option<PathBuf> {
    let text = crate::resource::read_bounded_text(path, 1024 * 1024, "CHC sidecar").ok()?;
    let lines = text.lines().collect::<Vec<_>>();
    for (index, raw_line) in lines.iter().enumerate() {
        let stripped = raw_line.trim();
        if !stripped.starts_with("input_files:") {
            continue;
        }
        let raw_value = clean_yaml_scalar(stripped.split_once(':')?.1);
        if !raw_value.is_empty() {
            return Some(
                path.parent()
                    .unwrap_or_else(|| Path::new(""))
                    .join(raw_value),
            );
        }
        for following in lines.iter().skip(index + 1) {
            let item = following.trim();
            if item.is_empty() {
                continue;
            }
            if !item.starts_with("- ") {
                break;
            }
            let raw_value = clean_yaml_scalar(&item[2..]);
            if !raw_value.is_empty() {
                return Some(
                    path.parent()
                        .unwrap_or_else(|| Path::new(""))
                        .join(raw_value),
                );
            }
        }
        return None;
    }
    None
}

fn read_sidecar_expected(path: &Path) -> ExpectedVerdict {
    let mut candidates = Vec::new();
    if matches!(
        path.extension().and_then(|e| e.to_str()),
        Some("yml" | "yaml")
    ) {
        candidates.push(path.to_path_buf());
    } else {
        candidates.push(path.with_extension("yml"));
        candidates.push(path.with_extension("yaml"));
    }

    for sidecar in candidates {
        if !sidecar.is_file() {
            continue;
        }
        let text = match crate::resource::read_bounded_text(&sidecar, 1024 * 1024, "CHC sidecar") {
            Ok(text) => text,
            Err(_) => {
                return ExpectedVerdict {
                    status: None,
                    source: format!("sidecar-invalid:{}", display_path(&sidecar)),
                    origin: ExpectedOrigin::SidecarInvalid,
                }
            }
        };
        if text.contains("placeholder verdict") {
            return ExpectedVerdict {
                status: None,
                source: format!("sidecar-invalid:{}", display_path(&sidecar)),
                origin: ExpectedOrigin::SidecarInvalid,
            };
        }
        let mut majority = None;
        let mut expected = None;
        let mut invalid = false;
        for raw_line in text.lines() {
            let mut stripped = raw_line.trim();
            if let Some(rest) = stripped.strip_prefix("- ") {
                stripped = rest.trim();
            }
            let Some((raw_key, raw_value)) = stripped.split_once(':') else {
                continue;
            };
            let slot = match raw_key.trim() {
                "majority_vote_verdict" => &mut majority,
                "expected_verdict" => &mut expected,
                _ => continue,
            };
            let parsed = normalize_expected_text(&clean_yaml_scalar(raw_value));
            if slot.is_some() || parsed.is_none() {
                invalid = true;
            } else {
                *slot = parsed;
            }
        }
        if majority.is_some() && expected.is_some() && majority != expected {
            invalid = true;
        }
        if invalid {
            return ExpectedVerdict {
                status: None,
                source: format!("sidecar-invalid:{}", display_path(&sidecar)),
                origin: ExpectedOrigin::SidecarInvalid,
            };
        }
        // CHC-COMP's majority vote is the preferred authoritative field when
        // both keys are present, but the two values must agree above.
        if let Some(status) = majority.or(expected) {
            return ExpectedVerdict {
                status: Some(status),
                source: format!("sidecar:{}", display_path(&sidecar)),
                origin: ExpectedOrigin::Sidecar,
            };
        }
    }

    ExpectedVerdict {
        status: None,
        source: "none".to_string(),
        origin: ExpectedOrigin::None,
    }
}

fn normalize_category_name(raw: &str) -> String {
    let stripped = raw.trim();
    if stripped.is_empty() {
        return "<root>".to_string();
    }
    if CHC_2026_TRACK_CATEGORIES.contains(&stripped) {
        return stripped.to_string();
    }
    let lowered = stripped
        .strip_prefix("chc-comp25-")
        .or_else(|| stripped.strip_prefix("chc-comp26-"))
        .unwrap_or(stripped)
        .replace('_', "-")
        .to_ascii_lowercase();
    match lowered.as_str() {
        "bool" => "BOOL".to_string(),
        "lia-lin" => "LIA-Lin".to_string(),
        "lia" => "LIA".to_string(),
        "lia-arrays" => "LIA-Arrays".to_string(),
        "lia-nonlin" => "LIA-Nonlin".to_string(),
        "lia-lin-arrays" => "LIA-Lin-Arrays".to_string(),
        "lia-nonlin-arrays" => "LIA-Nonlin-Arrays".to_string(),
        "adt-lia" => "ADT-LIA".to_string(),
        "adt-lia-arrays" => "ADT-LIA-Arrays".to_string(),
        "lra-lin" => "LRA-Lin".to_string(),
        "bv" => "BV".to_string(),
        "bv-lin" => "BV-Lin".to_string(),
        "bv-nonlin" => "BV-Nonlin".to_string(),
        "mixed-lia-lra" | "mixed_lia_lra" => "mixed_LIA_LRA".to_string(),
        _ => stripped.to_string(),
    }
}

fn infer_category(path: &Path, explicit: Option<&str>) -> String {
    if let Some(explicit) = explicit.filter(|value| !value.trim().is_empty()) {
        return normalize_category_name(explicit);
    }
    let parts = path
        .iter()
        .map(|part| part.to_string_lossy().to_string())
        .collect::<Vec<_>>();
    for category in CHC_2026_TRACK_CATEGORIES {
        if parts.iter().any(|part| part == category) {
            return (*category).to_string();
        }
    }
    let lower_parts = parts
        .iter()
        .map(|part| part.to_ascii_lowercase())
        .collect::<Vec<_>>();
    if lower_parts.iter().any(|part| part == "extra-small-lia") {
        return "LIA-Lin".to_string();
    }
    if lower_parts
        .iter()
        .any(|part| part == "bv" || part == "bv-lin")
    {
        return "BV-Lin".to_string();
    }
    if lower_parts.iter().any(|part| part.contains("array")) {
        return "LIA-Lin-Arrays".to_string();
    }
    normalize_category_name(
        path.parent()
            .and_then(Path::file_name)
            .and_then(|name| name.to_str())
            .unwrap_or("<root>"),
    )
}

fn normalize_family_name(raw: &str) -> String {
    let compact = raw
        .replace('\\', "/")
        .split('/')
        .filter(|part| !part.is_empty())
        .collect::<Vec<_>>()
        .join("/");
    if compact.is_empty() {
        "<root>".to_string()
    } else {
        compact
    }
}

fn infer_family(path: &Path, category: &str) -> String {
    let mut parts = path
        .parent()
        .map(|parent| {
            parent
                .iter()
                .map(|part| part.to_string_lossy().to_string())
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    let marker_index = parts.iter().rposition(|part| {
        matches!(
            part.as_str(),
            "chc-comp26-benchmarks-test"
                | "chc-comp26-benchmarks"
                | "chc-comp-2026"
                | "chc-comp-2025"
                | "chc-comp"
        )
    });
    if let Some(index) = marker_index {
        parts = parts.split_off(index + 1);
    }
    if parts
        .first()
        .is_some_and(|part| normalize_category_name(part) == category)
    {
        parts.remove(0);
    }
    if parts.is_empty() {
        return "<root>".to_string();
    }
    let mut family_parts = parts.into_iter().take(3).collect::<Vec<_>>();
    if family_parts
        .get(1)
        .is_some_and(|part| CHC_2026_TRACK_CATEGORIES.contains(&part.as_str()))
    {
        let first = family_parts.remove(0);
        family_parts.remove(0);
        family_parts.insert(0, first);
    }
    normalize_family_name(&family_parts.join("/"))
}

fn case_id_for(path: &Path, category: &str) -> String {
    format!("{category}:{}", display_path(path))
}

fn load_sample_cases(explicit_category: Option<&str>) -> Result<Vec<ManifestCase>> {
    let mut cases = Vec::new();
    for (category, rel_path, expected_status) in SAMPLE_CASES {
        let path = repo_root().join(rel_path);
        if !path.is_file() {
            continue;
        }
        let category = explicit_category
            .map(normalize_category_name)
            .unwrap_or_else(|| normalize_category_name(category));
        let sidecar = read_sidecar_expected(&path);
        let (expected_status, expected_source) = match (sidecar.origin, sidecar.status) {
            (ExpectedOrigin::Sidecar, Some(status)) => (status, sidecar.source),
            (ExpectedOrigin::SidecarInvalid, _) => {
                (expected_status.to_string(), "repo-sample-list".to_string())
            }
            _ => (expected_status.to_string(), "repo-sample-list".to_string()),
        };
        cases.push(ManifestCase {
            case_id: case_id_for(&path, &category),
            family: infer_family(&path, &category),
            category,
            path,
            expected_status,
            expected_source,
            source: "sample".to_string(),
            required_route_counters: Vec::new(),
        });
    }
    Ok(cases)
}

fn load_root_spec(raw_spec: &str, cli_category: Option<&str>) -> Result<Vec<ManifestCase>> {
    let (label, raw_path) = parse_labeled_path(raw_spec);
    let explicit_category = cli_category.or(label.as_deref());
    let root = resolve_cli_path(&raw_path, None);
    if !root.is_dir() {
        return Err(BenchError::InvalidArgs {
            reason: format!("CHC root not found: {raw_path}"),
        });
    }
    let mut cases = Vec::new();
    collect_smt2_cases(&root, explicit_category, &mut cases)?;
    Ok(cases)
}

fn load_manifest_spec(raw_spec: &str, cli_category: Option<&str>) -> Result<Vec<ManifestCase>> {
    let (label, raw_path) = parse_labeled_path(raw_spec);
    let explicit_category = cli_category.or(label.as_deref());
    let path = resolve_cli_path(&raw_path, None);
    if !path.exists() {
        return Err(BenchError::InvalidArgs {
            reason: format!("manifest not found: {raw_path}"),
        });
    }
    match path.extension().and_then(|ext| ext.to_str()).unwrap_or("") {
        "json" => load_json_manifest(&path, explicit_category),
        "csv" | "tsv" => load_csv_manifest(&path, explicit_category),
        "set" | "txt" => load_set_manifest(&path, explicit_category),
        "yaml" | "yml" => load_yaml_manifest(&path, explicit_category),
        other => Err(BenchError::InvalidArgs {
            reason: format!("unsupported CHC manifest type .{other}: {}", path.display()),
        }),
    }
}

fn first_present<'a>(data: &'a serde_json::Map<String, Value>, keys: &[&str]) -> Option<&'a Value> {
    keys.iter().find_map(|key| data.get(*key))
}

fn value_as_nonempty_str(value: &Value) -> Option<&str> {
    value.as_str().filter(|text| !text.trim().is_empty())
}

fn resolve_manifest_entry_path(raw: &str, manifest_path: &Path) -> PathBuf {
    resolve_cli_path(raw, manifest_path.parent())
}

fn category_from_json_entry(
    entry: &serde_json::Map<String, Value>,
    path: &Path,
    explicit_category: Option<&str>,
    manifest_category: Option<&str>,
) -> String {
    if let Some(explicit_category) = explicit_category {
        return normalize_category_name(explicit_category);
    }
    if let Some(direct) = first_present(entry, &["category", "track", "group", "logic"])
        .and_then(value_as_nonempty_str)
    {
        return normalize_category_name(direct);
    }
    if let Some(stem) = entry
        .get("set_membership")
        .and_then(Value::as_object)
        .and_then(|set| {
            set.get("set_id")
                .or_else(|| set.get("set_path"))
                .and_then(value_as_nonempty_str)
        })
        .and_then(|value| Path::new(value).file_stem())
        .and_then(|stem| stem.to_str())
    {
        return normalize_category_name(stem);
    }
    infer_category(path, manifest_category)
}

fn family_from_json_entry(
    entry: &serde_json::Map<String, Value>,
    path: &Path,
    category: &str,
) -> String {
    if let Some(direct) = first_present(
        entry,
        &["family", "family_id", "family_name", "benchmark_family"],
    )
    .and_then(value_as_nonempty_str)
    {
        return normalize_family_name(direct);
    }
    infer_family(path, category)
}

fn route_counters_from_json_entry(entry: &serde_json::Map<String, Value>) -> Vec<String> {
    match entry.get("route_counters_expected") {
        Some(Value::Object(map)) => map.keys().cloned().collect(),
        Some(Value::Array(items)) => items
            .iter()
            .filter_map(Value::as_str)
            .filter(|item| !item.trim().is_empty())
            .map(str::to_string)
            .collect(),
        _ => Vec::new(),
    }
}

fn make_case_from_json_entry(
    entry: &serde_json::Map<String, Value>,
    manifest_path: &Path,
    explicit_category: Option<&str>,
    manifest_category: Option<&str>,
) -> Option<ManifestCase> {
    let raw_path = first_present(entry, &["path", "file", "benchmark", "source", "input"])
        .and_then(value_as_nonempty_str)?;
    let path = resolve_manifest_entry_path(raw_path, manifest_path);
    let category = category_from_json_entry(entry, &path, explicit_category, manifest_category);
    let family = family_from_json_entry(entry, &path, &category);
    let manifest_expected = first_present(
        entry,
        &[
            "expected_status",
            "expected_verdict",
            "expected",
            "benchmark_expected_result",
        ],
    )
    .and_then(normalize_expected_status);
    let sidecar = read_sidecar_expected(&path);
    let (expected_status, expected_source) =
        match (sidecar.origin, sidecar.status, manifest_expected) {
            (ExpectedOrigin::Sidecar, Some(status), _) => (status, sidecar.source),
            (ExpectedOrigin::SidecarInvalid, _, _) => ("unknown".to_string(), sidecar.source),
            (_, _, Some(status)) => (status, "manifest".to_string()),
            _ => ("unknown".to_string(), "none".to_string()),
        };
    let case_id = entry
        .get("id")
        .and_then(value_as_nonempty_str)
        .map_or_else(|| case_id_for(&path, &category), str::to_string);
    Some(ManifestCase {
        case_id,
        path,
        category,
        family,
        expected_status,
        expected_source,
        source: format!("manifest:{}", display_path(manifest_path)),
        required_route_counters: route_counters_from_json_entry(entry),
    })
}

fn load_json_manifest(path: &Path, explicit_category: Option<&str>) -> Result<Vec<ManifestCase>> {
    let data: Value = serde_json::from_str(&crate::resource::read_bounded_text(
        path,
        crate::resource::MAX_METADATA_BYTES,
        "CHC JSON manifest",
    )?)?;
    let (entries, manifest_category): (&[Value], Option<String>) = match &data {
        Value::Array(entries) => (
            entries,
            explicit_category.map(str::to_string).or_else(|| {
                path.file_stem()
                    .and_then(|stem| stem.to_str())
                    .map(str::to_string)
            }),
        ),
        Value::Object(map) => {
            let entries = map
                .get("instances")
                .or_else(|| map.get("benchmarks"))
                .or_else(|| map.get("cases"))
                .and_then(Value::as_array)
                .ok_or_else(|| BenchError::InvalidArgs {
                    reason: format!(
                        "JSON manifest has no instances/benchmarks/cases list: {}",
                        path.display()
                    ),
                })?;
            let category = explicit_category.map(str::to_string).or_else(|| {
                map.get("track")
                    .or_else(|| map.get("category"))
                    .or_else(|| map.get("suite"))
                    .and_then(value_as_nonempty_str)
                    .map(str::to_string)
                    .or_else(|| {
                        path.file_stem()
                            .and_then(|stem| stem.to_str())
                            .map(str::to_string)
                    })
            });
            (entries, category)
        }
        _ => {
            return Err(BenchError::InvalidArgs {
                reason: format!("unsupported JSON manifest shape: {}", path.display()),
            });
        }
    };
    let manifest_category = manifest_category.as_deref();
    if entries.len() > MAX_CHC_CASES {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "JSON manifest {} exceeds the fixed {MAX_CHC_CASES}-case cap",
                path.display()
            ),
        });
    }
    let mut cases = Vec::with_capacity(entries.len().min(MAX_CHC_CASES));
    for entry in entries.iter().filter_map(Value::as_object) {
        if let Some(case) =
            make_case_from_json_entry(entry, path, explicit_category, manifest_category)
        {
            cases.push(case);
        }
    }
    Ok(cases)
}

fn parse_csv_record(line: &str) -> Vec<String> {
    let mut fields = Vec::new();
    let mut field = String::new();
    let mut chars = line.trim_end_matches('\r').chars().peekable();
    let mut in_quotes = false;
    while let Some(ch) = chars.next() {
        if in_quotes {
            if ch == '"' {
                if chars.peek() == Some(&'"') {
                    field.push('"');
                    chars.next();
                } else {
                    in_quotes = false;
                }
            } else {
                field.push(ch);
            }
        } else if ch == ',' {
            fields.push(field.trim().to_string());
            field.clear();
        } else if ch == '"' && field.trim().is_empty() {
            in_quotes = true;
        } else {
            field.push(ch);
        }
    }
    fields.push(field.trim().to_string());
    fields
}

fn load_csv_manifest(path: &Path, explicit_category: Option<&str>) -> Result<Vec<ManifestCase>> {
    let text = crate::resource::read_bounded_text(
        path,
        crate::resource::MAX_METADATA_BYTES,
        "CHC CSV manifest",
    )?;
    let mut lines = text.lines();
    let header = lines.next().ok_or_else(|| BenchError::InvalidArgs {
        reason: format!("empty CSV manifest {}", path.display()),
    })?;
    let delimiter = if path.extension().and_then(|ext| ext.to_str()) == Some("tsv") {
        '\t'
    } else {
        ','
    };
    let columns = if delimiter == '\t' {
        header
            .split('\t')
            .map(|field| field.trim().to_string())
            .collect()
    } else {
        parse_csv_record(header)
    };
    let column_index = |names: &[&str]| {
        names
            .iter()
            .find_map(|name| columns.iter().position(|column| column == name))
    };
    let path_col =
        column_index(&["path", "file", "benchmark", "source", "input"]).ok_or_else(|| {
            BenchError::InvalidArgs {
                reason: "CSV manifest needs path/file/benchmark/source/input column".to_string(),
            }
        })?;
    let id_col = column_index(&["id", "case_id"]);
    let category_col = column_index(&["category", "track"]);
    let family_col = column_index(&["family", "family_id"]);
    let expected_col = column_index(&["expected_status", "expected_verdict", "expected"]);
    let route_col = column_index(&["route_counters", "route_counters_expected"]);
    let mut cases = Vec::new();
    for line in lines.filter(|line| !line.trim().is_empty()) {
        let fields = if delimiter == '\t' {
            line.split('\t')
                .map(|field| field.trim().to_string())
                .collect()
        } else {
            parse_csv_record(line)
        };
        let Some(raw_path) = fields.get(path_col).filter(|field| !field.is_empty()) else {
            continue;
        };
        let source_path = resolve_manifest_entry_path(raw_path, path);
        let explicit = explicit_category.or_else(|| {
            category_col
                .and_then(|idx| fields.get(idx))
                .map(String::as_str)
                .filter(|value| !value.trim().is_empty())
        });
        let category = infer_category(&source_path, explicit);
        let family = family_col
            .and_then(|idx| fields.get(idx))
            .filter(|value| !value.trim().is_empty())
            .map_or_else(
                || infer_family(&source_path, &category),
                |value| normalize_family_name(value),
            );
        let manifest_expected = expected_col
            .and_then(|idx| fields.get(idx))
            .and_then(|value| normalize_expected_text(value));
        let sidecar = read_sidecar_expected(&source_path);
        let (expected_status, expected_source) =
            match (sidecar.origin, sidecar.status, manifest_expected) {
                (ExpectedOrigin::Sidecar, Some(status), _) => (status, sidecar.source),
                (ExpectedOrigin::SidecarInvalid, _, _) => ("unknown".to_string(), sidecar.source),
                (_, _, Some(status)) => (status, "manifest".to_string()),
                _ => ("unknown".to_string(), "none".to_string()),
            };
        let route_counters = route_col
            .and_then(|idx| fields.get(idx))
            .map(|raw| split_route_counter_list(raw))
            .unwrap_or_default();
        if cases.len() >= MAX_CHC_CASES {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "CSV manifest {} exceeds the fixed {MAX_CHC_CASES}-case cap",
                    path.display()
                ),
            });
        }
        cases.push(ManifestCase {
            case_id: id_col
                .and_then(|idx| fields.get(idx))
                .filter(|id| !id.trim().is_empty())
                .map_or_else(|| case_id_for(&source_path, &category), Clone::clone),
            path: source_path,
            category,
            family,
            expected_status,
            expected_source,
            source: format!("manifest:{}", display_path(path)),
            required_route_counters: route_counters,
        });
    }
    Ok(cases)
}

fn split_route_counter_list(raw: &str) -> Vec<String> {
    raw.split([',', ';'])
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(str::to_string)
        .collect()
}

fn set_line_to_paths(line: &str, set_path: &Path) -> (PathBuf, Option<PathBuf>) {
    let raw = line.trim();
    let mut source = resolve_manifest_entry_path(raw, set_path);
    let mut sidecar = None;
    if matches!(
        source.extension().and_then(|ext| ext.to_str()),
        Some("yml" | "yaml")
    ) {
        sidecar = Some(source.clone());
        source = read_sidecar_input_file(&source).unwrap_or_else(|| source.with_extension("smt2"));
    }
    (source, sidecar)
}

fn load_set_manifest(path: &Path, explicit_category: Option<&str>) -> Result<Vec<ManifestCase>> {
    let category = explicit_category
        .map(normalize_category_name)
        .unwrap_or_else(|| {
            normalize_category_name(
                path.file_stem()
                    .and_then(|stem| stem.to_str())
                    .unwrap_or("<root>")
                    .trim_start_matches("chc-comp25-")
                    .trim_start_matches("chc-comp26-"),
            )
        });
    let text = crate::resource::read_bounded_text(
        path,
        crate::resource::MAX_METADATA_BYTES,
        "CHC set manifest",
    )?;
    let mut cases = Vec::new();
    for raw_line in text.lines() {
        let line = raw_line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let (source, sidecar) = set_line_to_paths(line, path);
        let expected = read_sidecar_expected(sidecar.as_deref().unwrap_or(&source));
        if cases.len() >= MAX_CHC_CASES {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "set manifest {} exceeds the fixed {MAX_CHC_CASES}-case cap",
                    path.display()
                ),
            });
        }
        cases.push(ManifestCase {
            case_id: case_id_for(&source, &category),
            family: infer_family(&source, &category),
            path: source,
            category: category.clone(),
            expected_status: expected.status.unwrap_or_else(|| "unknown".to_string()),
            expected_source: expected.source,
            source: format!("set:{}", display_path(path)),
            required_route_counters: Vec::new(),
        });
    }
    Ok(cases)
}

fn parse_simple_eval_yaml(path: &Path) -> Result<BTreeMap<String, String>> {
    let text = crate::resource::read_bounded_text(
        path,
        crate::resource::MAX_METADATA_BYTES,
        "CHC YAML manifest",
    )?;
    let mut inputs = BTreeMap::new();
    let mut in_inputs = false;
    for raw_line in text.lines() {
        let line = raw_line.split('#').next().unwrap_or("").trim_end();
        if line.trim().is_empty() {
            continue;
        }
        if !line.starts_with(' ') && line.contains(':') {
            let (key, _) = line.split_once(':').unwrap_or(("", ""));
            in_inputs = key.trim() == "inputs";
            continue;
        }
        if in_inputs && line.starts_with(' ') && line.contains(':') {
            let (key, value) = line.split_once(':').unwrap_or(("", ""));
            inputs.insert(
                key.trim().to_string(),
                value
                    .trim()
                    .trim_matches(|ch| ch == '\'' || ch == '"')
                    .to_string(),
            );
        }
    }
    Ok(inputs)
}

fn load_yaml_manifest(path: &Path, explicit_category: Option<&str>) -> Result<Vec<ManifestCase>> {
    let inputs = parse_simple_eval_yaml(path)?;
    let Some(benchmarks_dir) = inputs.get("benchmarks_dir") else {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "YAML manifest is not a supported eval registry: {}",
                path.display()
            ),
        });
    };
    let root = resolve_manifest_entry_path(benchmarks_dir, path);
    if let Some(set_file) = inputs.get("set_file") {
        return load_set_manifest(&root.join(set_file), explicit_category);
    }
    let mut cases = Vec::new();
    collect_smt2_cases(&root, explicit_category, &mut cases)?;
    Ok(cases)
}

fn collect_smt2_cases(
    root: &Path,
    explicit_category: Option<&str>,
    cases: &mut Vec<ManifestCase>,
) -> Result<()> {
    collect_smt2_cases_with_limits(
        root,
        explicit_category,
        cases,
        MAX_CHC_TRAVERSAL_ENTRIES,
        MAX_CHC_PENDING_DIRECTORIES,
        MAX_CHC_CASES,
    )
}

fn collect_smt2_cases_with_limits(
    root: &Path,
    explicit_category: Option<&str>,
    cases: &mut Vec<ManifestCase>,
    max_entries: usize,
    max_pending_directories: usize,
    max_cases: usize,
) -> Result<()> {
    let metadata = fs::symlink_metadata(root)
        .with_bench_context(|| format!("statting CHC root {}", root.display()))?;
    if !metadata.file_type().is_dir() {
        return Err(BenchError::InvalidArgs {
            reason: format!(
                "CHC root is not a non-symlink directory: {}",
                root.display()
            ),
        });
    }
    let mut pending = vec![root.to_path_buf()];
    let mut visited_entries = 0_usize;
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory)
            .with_bench_context(|| format!("reading {}", directory.display()))?
        {
            let entry = entry?;
            visited_entries = visited_entries
                .checked_add(1)
                .ok_or_else(|| BenchError::msg("CHC traversal entry count overflow"))?;
            if visited_entries > max_entries {
                return Err(BenchError::InvalidArgs {
                    reason: format!("CHC traversal exceeds the fixed {max_entries}-entry cap"),
                });
            }
            let file_type = entry.file_type()?;
            let path = entry.path();
            if file_type.is_dir() {
                if pending.len() >= max_pending_directories {
                    return Err(BenchError::InvalidArgs {
                        reason: format!(
                            "CHC traversal exceeds the fixed {max_pending_directories}-pending-directory cap"
                        ),
                    });
                }
                pending.push(path);
            } else if file_type.is_file()
                && path.extension().and_then(|ext| ext.to_str()) == Some("smt2")
            {
                if cases.len() >= max_cases {
                    return Err(BenchError::InvalidArgs {
                        reason: format!(
                            "CHC root {} exceeds the fixed {max_cases}-case cap",
                            root.display()
                        ),
                    });
                }
                let category = infer_category(&path, explicit_category);
                let expected = read_sidecar_expected(&path);
                cases.push(ManifestCase {
                    case_id: case_id_for(&path, &category),
                    family: infer_family(&path, &category),
                    path,
                    category,
                    expected_status: expected.status.unwrap_or_else(|| "unknown".to_string()),
                    expected_source: expected.source,
                    source: format!("root:{}", display_path(root)),
                    required_route_counters: Vec::new(),
                });
            }
        }
    }
    Ok(())
}

fn validate_manifest_cases(cases: &[ManifestCase]) -> Result<()> {
    if cases.is_empty() {
        return Err(BenchError::InvalidArgs {
            reason: "CHC gate needs at least one manifest row".to_string(),
        });
    }
    let mut errors = Vec::new();
    let mut ids: BTreeMap<&str, String> = BTreeMap::new();
    let mut output_names: BTreeMap<String, (&str, String)> = BTreeMap::new();
    for case in cases {
        let location = format!("{} ({})", case.source, case.path.display());
        if case.case_id.is_empty()
            || case.case_id.len() > MAX_CHC_CASE_ID_BYTES
            || case.case_id.chars().any(char::is_control)
        {
            errors.push(format!(
                "invalid CHC case ID {:?} from {location}; IDs must be nonempty, control-free, and at most {MAX_CHC_CASE_ID_BYTES} bytes",
                case.case_id
            ));
        }
        if let Some(previous) = ids.insert(&case.case_id, location.clone()) {
            errors.push(format!(
                "duplicate CHC case ID {:?}: {previous} and {location}",
                case.case_id
            ));
        }
        let output_name = sanitize(&case.case_id);
        if let Some((previous_id, previous_location)) =
            output_names.insert(output_name.clone(), (&case.case_id, location.clone()))
        {
            if previous_id != case.case_id {
                errors.push(format!(
                    "CHC case IDs {previous_id:?} ({previous_location}) and {:?} ({location}) collide at output directory {output_name:?}",
                    case.case_id
                ));
            }
        }
        match fs::symlink_metadata(&case.path) {
            Ok(metadata) if metadata.file_type().is_file() => {}
            Ok(_) => errors.push(format!(
                "{} path is not a non-symlink regular file: {}",
                case.case_id,
                case.path.display()
            )),
            Err(error) => errors.push(format!(
                "{} path cannot be inspected: {}: {error}",
                case.case_id,
                case.path.display()
            )),
        }
        if !matches!(case.expected_status.as_str(), "sat" | "unsat") {
            errors.push(format!(
                "{} expected status is not score-bearing: {} from {}",
                case.case_id, case.expected_status, case.expected_source
            ));
        }
        if case.expected_source == "none"
            || case.expected_source.starts_with("sidecar-invalid:")
            || case.expected_source.contains("synthetic")
            || case.expected_source.contains("sample-filename")
        {
            errors.push(format!(
                "{} has non-admissible expected source: {}",
                case.case_id, case.expected_source
            ));
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        Err(BenchError::InvalidArgs {
            reason: errors.join("; "),
        })
    }
}

#[derive(Debug)]
struct CaseInputSnapshot {
    path: PathBuf,
    sha256: String,
    size_bytes: u64,
}

/// Copy one score-bearing input through an already-open regular-file
/// descriptor. The solver only sees this private snapshot, so later pathname
/// replacement cannot change the bytes represented by the case record.
fn snapshot_case_input(source_path: &Path, case_dir: &Path) -> Result<CaseInputSnapshot> {
    use sha2::{Digest as _, Sha256};

    let mut source_options = fs::OpenOptions::new();
    source_options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        source_options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let mut source = source_options.open(source_path).with_bench_context(|| {
        format!(
            "opening CHC input snapshot source {}",
            source_path.display()
        )
    })?;
    let before = source
        .metadata()
        .with_bench_context(|| format!("inspecting open CHC input {}", source_path.display()))?;
    if !before.file_type().is_file() {
        return Err(BenchError::msg(format!(
            "CHC input is not a non-symlink regular file: {}",
            source_path.display()
        )));
    }
    if before.len() > MAX_CHC_INPUT_BYTES {
        return Err(BenchError::msg(format!(
            "CHC input {} exceeds the fixed {MAX_CHC_INPUT_BYTES}-byte snapshot cap",
            source_path.display()
        )));
    }

    let mut snapshot = tempfile::Builder::new()
        .prefix("solver-input-")
        .suffix(".smt2")
        .tempfile_in(case_dir)
        .with_bench_context(|| {
            format!(
                "creating private CHC input snapshot in {}",
                case_dir.display()
            )
        })?;
    let mut hasher = Sha256::new();
    let mut size_bytes = 0_u64;
    let mut buffer = [0_u8; 64 * 1024];
    loop {
        let read = source.read(&mut buffer).with_bench_context(|| {
            format!(
                "reading CHC input snapshot source {}",
                source_path.display()
            )
        })?;
        if read == 0 {
            break;
        }
        size_bytes = size_bytes
            .checked_add(read as u64)
            .ok_or_else(|| BenchError::msg("CHC input snapshot size overflow"))?;
        if size_bytes > MAX_CHC_INPUT_BYTES {
            return Err(BenchError::msg(format!(
                "CHC input {} grew beyond the fixed {MAX_CHC_INPUT_BYTES}-byte snapshot cap",
                source_path.display()
            )));
        }
        hasher.update(&buffer[..read]);
        snapshot.write_all(&buffer[..read])?;
    }
    snapshot.as_file().sync_all()?;

    let after = source.metadata()?;
    let path_after = fs::symlink_metadata(source_path).with_bench_context(|| {
        format!(
            "revalidating CHC input snapshot source {}",
            source_path.display()
        )
    })?;
    if !same_chc_input_snapshot(&before, &after)
        || !same_chc_input_snapshot(&after, &path_after)
        || size_bytes != after.len()
    {
        return Err(BenchError::msg(format!(
            "CHC input changed while creating its private snapshot: {}",
            source_path.display()
        )));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        snapshot
            .as_file()
            .set_permissions(fs::Permissions::from_mode(0o400))?;
    }
    let (snapshot_file, snapshot_path) = snapshot.keep().map_err(|error| {
        BenchError::msg(format!(
            "persisting private CHC input snapshot in {}: {error}",
            case_dir.display()
        ))
    })?;
    drop(snapshot_file);

    Ok(CaseInputSnapshot {
        path: snapshot_path,
        sha256: format!("sha256:{:x}", hasher.finalize()),
        size_bytes,
    })
}

fn same_chc_input_snapshot(before: &fs::Metadata, after: &fs::Metadata) -> bool {
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        before.file_type().is_file()
            && after.file_type().is_file()
            && before.dev() == after.dev()
            && before.ino() == after.ino()
            && before.len() == after.len()
            && before.mtime() == after.mtime()
            && before.mtime_nsec() == after.mtime_nsec()
            && before.ctime() == after.ctime()
            && before.ctime_nsec() == after.ctime_nsec()
    }
    #[cfg(not(unix))]
    {
        before.file_type().is_file()
            && after.file_type().is_file()
            && before.len() == after.len()
            && before.modified().ok() == after.modified().ok()
    }
}

fn run_case(
    case: &ManifestCase,
    args: &ChcGateArgs,
    run_root: &Path,
    resources: &crate::resource::PlannedResources,
    ay_execution_path: &Path,
) -> Result<CaseRecord> {
    let case_dir = run_root.join(sanitize(&case.case_id));
    fs::create_dir_all(&case_dir)
        .with_bench_context(|| format!("creating case dir {}", case_dir.display()))?;
    let case_dir_metadata = fs::symlink_metadata(&case_dir)
        .with_bench_context(|| format!("inspecting case dir {}", case_dir.display()))?;
    if !case_dir_metadata.file_type().is_dir() {
        return Err(BenchError::msg(format!(
            "CHC case output path is not a non-symlink directory: {}",
            case_dir.display()
        )));
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt as _;
        fs::set_permissions(&case_dir, fs::Permissions::from_mode(0o700))?;
    }
    let solver_input = snapshot_case_input(&case.path, &case_dir)?;
    let stdout_path = case_dir.join("stdout.txt");
    let stderr_path = case_dir.join("stderr.txt");
    let stats_path = case_dir.join("stats.json");
    let command_path = case_dir.join("command.argv");
    let internal_timeout_ms = ((args.timeout_sec * 1000.0).round() as u64)
        .saturating_sub(250)
        .max(1);
    let mut solver_args = vec![
        format!("-t:{internal_timeout_ms}"),
        "--stats-json".to_string(),
        "--validate".to_string(),
        "--chc".to_string(),
        solver_input.path.display().to_string(),
    ];
    if resources.plan.memlimit_mb_per_child > 0 {
        solver_args.insert(1, resources.plan.memlimit_mb_per_child.to_string());
        solver_args.insert(1, "--memory".to_string());
    }
    let command_env = BTreeMap::from([
        ("LC_ALL".to_string(), "C".to_string()),
        ("TZ".to_string(), "UTC".to_string()),
        (
            "PATH".to_string(),
            "/usr/local/bin:/usr/bin:/bin".to_string(),
        ),
        ("AY_CHC_GATE".to_string(), "1".to_string()),
        (
            "AY_CHC_TRACK_WORKBENCH_MODE".to_string(),
            DEFAULT_MODE.to_string(),
        ),
        (
            "AY_COMPETITION_JIT_MODE".to_string(),
            DEFAULT_MODE.to_string(),
        ),
        (
            "AY_COMPETITION_JIT_CANDIDATE_MODE".to_string(),
            DEFAULT_MODE.to_string(),
        ),
        (
            "AY_COMPETITION_JIT_ARTIFACT".to_string(),
            "chc-native-code-helpers".to_string(),
        ),
        (
            "MEMLIMIT".to_string(),
            resources.plan.memlimit_mb_per_child.to_string(),
        ),
        (
            "NBCORE".to_string(),
            resources.plan.nbcore_per_child.to_string(),
        ),
    ]);
    let mut command = resources.external_command(ay_execution_path);
    command.args(&solver_args);
    command.env_clear();
    command.envs(&command_env);
    let stdout_file = File::create(&stdout_path)
        .with_bench_context(|| format!("creating {}", stdout_path.display()))?;
    let stderr_file = File::create(&stderr_path)
        .with_bench_context(|| format!("creating {}", stderr_path.display()))?;
    command.stdout(Stdio::piped());
    command.stderr(Stdio::piped());
    let command_argv = std::iter::once(ay_execution_path.display().to_string())
        .chain(solver_args.iter().cloned())
        .collect::<Vec<_>>();
    write_command_file(&command_path, &command_argv)?;

    let start = Instant::now();
    let mut timed_out = false;
    let mut memout = false;
    let mut stdout = String::new();
    let stderr: String;
    let mut output_incomplete = false;
    let status = match resources.spawn_external_child(&mut command, "ay bench chc-gate") {
        Ok((mut child, watchdog)) => {
            let Some(stdout_pipe) = child.stdout.take() else {
                crate::resource::terminate_guarded_child(
                    &mut child,
                    watchdog,
                    "ay bench chc-gate",
                )?;
                return Err(BenchError::msg("CHC gate solver stdout pipe missing"));
            };
            let Some(stderr_pipe) = child.stderr.take() else {
                crate::resource::terminate_guarded_child(
                    &mut child,
                    watchdog,
                    "ay bench chc-gate",
                )?;
                return Err(BenchError::msg("CHC gate solver stderr pipe missing"));
            };
            let stdout_capture =
                crate::resource::BoundedFileCapture::start(stdout_pipe, stdout_file);
            let stderr_capture =
                crate::resource::BoundedFileCapture::start(stderr_pipe, stderr_file);
            let outcome = crate::resource::wait_for_guarded_child(
                &mut child,
                watchdog,
                std::time::Duration::from_secs_f64(args.timeout_sec),
                "ay bench chc-gate",
            )?;
            timed_out = outcome.timed_out;
            memout = outcome.memout;
            let stdout_output = stdout_capture.finish()?;
            let stderr_output = stderr_capture.finish()?;
            output_incomplete = stdout_output.incomplete || stderr_output.incomplete;
            stdout = stdout_output.text;
            stderr = stderr_output.text;
            if memout {
                timed_out = false;
            }
            outcome.status
        }
        Err(error) => {
            fs::write(&stderr_path, error.to_string())
                .with_bench_context(|| format!("writing {}", stderr_path.display()))?;
            stderr = error.to_string();
            None
        }
    };
    let elapsed_s = round6(start.elapsed().as_secs_f64());
    let exit_code = status.as_ref().and_then(ExitStatus::code);
    let process_status = status
        .as_ref()
        .map(ToString::to_string)
        .unwrap_or_else(|| "not-started-or-unreaped".to_string());
    let exited_successfully = status.as_ref().is_some_and(ExitStatus::success);
    let (stats_json, stats_raw) = if output_incomplete {
        (None, None)
    } else {
        parse_stats_json(&stdout, &stderr)
    };
    if let Some(raw) = stats_raw.as_deref() {
        fs::write(&stats_path, format!("{raw}\n"))
            .with_bench_context(|| format!("writing {}", stats_path.display()))?;
    }

    let status_text = solver_status_from_process(
        memout,
        timed_out,
        output_incomplete,
        exited_successfully,
        &stdout,
    );
    let validation = stats_json
        .as_ref()
        .map_or_else(ValidationTelemetry::default, parse_validation_telemetry);
    let transform_memory = stats_json.as_ref().map_or_else(
        TransformMemoryTelemetry::default,
        parse_transform_memory_telemetry,
    );
    let route = stats_json
        .as_ref()
        .map_or_else(RouteTelemetry::default, parse_route_telemetry);
    let route_counters = stats_json.as_ref().map_or_else(BTreeMap::new, |stats| {
        route_counter_values(
            stats,
            &case.required_route_counters,
            &args.require_route_counters,
        )
    });
    let missing_required_route_counters = case
        .required_route_counters
        .iter()
        .chain(args.require_route_counters.iter())
        .filter(|counter| !counter_exercised(stats_json.as_ref(), counter))
        .cloned()
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect::<Vec<_>>();
    let wrong = is_wrong(&case.expected_status, &status_text);
    let mut invalid_reasons = Vec::new();
    if output_incomplete {
        invalid_reasons.push("solver-output-truncated-or-unreadable".to_string());
    }
    if !timed_out && !memout && !exited_successfully {
        invalid_reasons.push("solver-exit-not-successful".to_string());
    }
    if matches!(status_text.as_str(), "sat" | "unsat")
        && !validation_valid_for_status(&validation, &status_text)
    {
        invalid_reasons.push(format!(
            "missing-or-failing-{status_text}-validation-counters"
        ));
    }
    if route.accepted_by_firewall == Some(false) {
        invalid_reasons.push("route-firewall-rejected".to_string());
    }
    if route
        .fail_closed_reason
        .as_deref()
        .is_some_and(|reason| !reason.trim().is_empty())
    {
        invalid_reasons.push("route-fail-closed".to_string());
    }
    if !missing_required_route_counters.is_empty() {
        invalid_reasons.push("missing-required-route-counter".to_string());
    }
    let invalid = !invalid_reasons.is_empty();
    let solved = matches!(status_text.as_str(), "sat" | "unsat") && !wrong && !invalid;
    let classification = classify_case(&status_text, timed_out, wrong, invalid);
    let par2_s = if solved {
        elapsed_s
    } else {
        round6(2.0 * args.timeout_sec)
    };

    Ok(CaseRecord {
        schema: CASES_SCHEMA,
        case_id: case.case_id.clone(),
        path: display_path(&case.path),
        solver_input_path: solver_input.path.display().to_string(),
        input_sha256: solver_input.sha256,
        input_size_bytes: solver_input.size_bytes,
        category: case.category.clone(),
        family: case.family.clone(),
        expected_status: case.expected_status.clone(),
        expected_source: case.expected_source.clone(),
        source: case.source.clone(),
        status: status_text,
        classification,
        solved,
        wrong,
        invalid,
        invalid_reasons,
        elapsed_s: Some(elapsed_s),
        par2_s,
        timed_out,
        exit_code,
        process_status,
        stats_json_present: stats_json.is_some(),
        stats_json_path: if stats_json.is_some() {
            stats_path.display().to_string()
        } else {
            String::new()
        },
        validation,
        transform_memory,
        route,
        route_counters,
        required_route_counters: case.required_route_counters.clone(),
        missing_required_route_counters,
        stdout: stdout_path.display().to_string(),
        stderr: stderr_path.display().to_string(),
        command_argv,
        command_env,
    })
}

fn solver_status_from_process(
    memout: bool,
    timed_out: bool,
    output_incomplete: bool,
    exited_successfully: bool,
    stdout: &str,
) -> String {
    if memout {
        "memout".to_string()
    } else if timed_out {
        "timeout".to_string()
    } else if output_incomplete || !exited_successfully {
        "error".to_string()
    } else {
        let extracted = extract_solver_result(stdout);
        if matches!(extracted.as_str(), "sat" | "unsat" | "unknown") {
            extracted
        } else {
            "error".to_string()
        }
    }
}

fn write_command_file(path: &Path, argv: &[String]) -> Result<()> {
    let mut file =
        File::create(path).with_bench_context(|| format!("creating {}", path.display()))?;
    for arg in argv {
        writeln!(file, "{arg}")?;
    }
    Ok(())
}

fn parse_stats_json(stdout: &str, stderr: &str) -> (Option<Value>, Option<String>) {
    for raw_line in stderr.lines().chain(stdout.lines()).rev() {
        let line = raw_line.trim();
        if !line.starts_with('{') {
            continue;
        }
        if let Ok(value) = serde_json::from_str::<Value>(line) {
            if value.as_object().is_some_and(|object| {
                object.contains_key("mode")
                    || object.contains_key("result")
                    || object.contains_key("wall_time_ms")
            }) {
                return (Some(value), Some(line.to_string()));
            }
        }
    }
    (None, None)
}

fn extract_solver_result(stdout: &str) -> String {
    let mut verdicts = Vec::new();
    for raw_line in stdout.lines() {
        let line = raw_line.trim().to_ascii_lowercase();
        let verdict = match line.as_str() {
            "sat" | "s sat" | "s satisfiable" | "satisfiable" => Some("sat"),
            "unsat" | "s unsat" | "s unsatisfiable" | "unsatisfiable" => Some("unsat"),
            "unknown" | "s unknown" => Some("unknown"),
            _ => None,
        };
        if let Some(verdict) = verdict {
            verdicts.push(verdict);
        }
    }
    match verdicts.as_slice() {
        [verdict] => (*verdict).to_string(),
        _ => "error".to_string(),
    }
}

fn classify_case(status: &str, timed_out: bool, wrong: bool, invalid: bool) -> String {
    if wrong {
        "wrong".to_string()
    } else if invalid {
        "invalid".to_string()
    } else if timed_out || status == "timeout" {
        "timeout".to_string()
    } else if status == "memout" {
        "memout".to_string()
    } else if status == "unknown" {
        "unknown".to_string()
    } else if status == "sat" || status == "unsat" {
        "solved".to_string()
    } else {
        "error".to_string()
    }
}

fn stats_value<'a>(value: &'a Value, key: &str) -> Option<&'a Value> {
    if let Some(direct) = value.get(key) {
        return Some(direct);
    }
    let mut current = value;
    for part in key.split('.') {
        current = current.get(part)?;
    }
    Some(current)
}

fn stats_u64(value: &Value, key: &str) -> Option<u64> {
    match stats_value(value, key)? {
        Value::Number(number) => number.as_u64(),
        Value::Bool(value) => Some(u64::from(*value)),
        _ => None,
    }
}

fn stats_f64(value: &Value, key: &str) -> Option<f64> {
    match stats_value(value, key)? {
        Value::Number(number) => number.as_f64(),
        Value::Bool(value) => Some(f64::from(u8::from(*value))),
        _ => None,
    }
}

fn stats_bool(value: &Value, key: &str) -> Option<bool> {
    match stats_value(value, key)? {
        Value::Bool(value) => Some(*value),
        Value::Number(number) => number.as_u64().map(|value| value != 0),
        Value::String(text) => match text.trim().to_ascii_lowercase().as_str() {
            "1" | "true" | "yes" | "on" | "accepted" => Some(true),
            "0" | "false" | "no" | "off" | "rejected" => Some(false),
            _ => None,
        },
        _ => None,
    }
}

fn stats_string(value: &Value, key: &str) -> Option<String> {
    stats_value(value, key)?.as_str().map(str::to_string)
}

fn parse_validation_telemetry(value: &Value) -> ValidationTelemetry {
    ValidationTelemetry {
        safe_attempts: stats_u64(value, "chc.validation.safe_attempts"),
        safe_successes: stats_u64(value, "chc.validation.safe_successes"),
        safe_failures: stats_u64(value, "chc.validation.safe_failures"),
        unsafe_attempts: stats_u64(value, "chc.validation.unsafe_attempts"),
        unsafe_successes: stats_u64(value, "chc.validation.unsafe_successes"),
        unsafe_failures: stats_u64(value, "chc.validation.unsafe_failures"),
    }
}

fn parse_transform_memory_telemetry(value: &Value) -> TransformMemoryTelemetry {
    TransformMemoryTelemetry {
        reversible_count: stats_u64(value, "chc.transform_memory.reversible_count"),
        obligation_count: stats_u64(value, "chc.transform_memory.obligation_count"),
    }
}

fn parse_route_telemetry(value: &Value) -> RouteTelemetry {
    RouteTelemetry {
        name: stats_string(value, "chc.route.name")
            .or_else(|| stats_string(value, "competition_jit.artifact")),
        accepted_by_firewall: stats_bool(value, "chc.route.accepted_by_firewall"),
        fail_closed_reason: stats_string(value, "chc.route.fail_closed_reason"),
    }
}

fn validation_valid_for_status(validation: &ValidationTelemetry, status: &str) -> bool {
    match status {
        "sat" => {
            validation.safe_attempts.unwrap_or(0) > 0
                && validation.safe_successes.unwrap_or(0) > 0
                && validation.safe_failures.unwrap_or(0) == 0
        }
        "unsat" => {
            validation.unsafe_attempts.unwrap_or(0) > 0
                && validation.unsafe_successes.unwrap_or(0) > 0
                && validation.unsafe_failures.unwrap_or(0) == 0
        }
        _ => false,
    }
}

fn route_counter_values(
    value: &Value,
    row_required: &[String],
    gate_required: &[String],
) -> BTreeMap<String, f64> {
    let mut counters = BTreeMap::new();
    flatten_route_counters(value, "", &mut counters);
    counters.retain(|key, _| {
        DEFAULT_ROUTE_COUNTER_PREFIXES
            .iter()
            .any(|prefix| key.starts_with(prefix))
            || row_required.iter().any(|required| required == key)
            || gate_required.iter().any(|required| required == key)
    });
    counters
}

fn flatten_route_counters(value: &Value, prefix: &str, counters: &mut BTreeMap<String, f64>) {
    let Some(map) = value.as_object() else {
        return;
    };
    for (key, child) in map {
        let name = if prefix.is_empty() {
            key.clone()
        } else {
            format!("{prefix}.{key}")
        };
        match child {
            Value::Number(number) => {
                if let Some(value) = number.as_f64() {
                    counters.insert(name, value);
                }
            }
            Value::Bool(value) => {
                counters.insert(name, f64::from(u8::from(*value)));
            }
            Value::Object(_) => flatten_route_counters(child, &name, counters),
            _ => {}
        }
    }
}

fn counter_exercised(stats_json: Option<&Value>, counter: &str) -> bool {
    stats_json
        .and_then(|stats| stats_f64(stats, counter))
        .is_some_and(|value| value > 0.0)
}

fn is_wrong(expected: &str, actual: &str) -> bool {
    matches!(expected, "sat" | "unsat") && matches!(actual, "sat" | "unsat") && expected != actual
}

fn summarize_overall(records: &[CaseRecord], dirty: bool) -> OverallSummary {
    let total = records.len();
    let solved_sat = records
        .iter()
        .filter(|record| record.solved && record.status == "sat")
        .count();
    let solved_unsat = records
        .iter()
        .filter(|record| record.solved && record.status == "unsat")
        .count();
    let par2_total = round6(records.iter().map(|record| record.par2_s).sum());
    OverallSummary {
        total,
        solved: solved_sat + solved_unsat,
        solved_sat,
        solved_unsat,
        wrong: records.iter().filter(|record| record.wrong).count(),
        invalid: records.iter().filter(|record| record.invalid).count(),
        unknown: records
            .iter()
            .filter(|record| record.classification == "unknown")
            .count(),
        timeout: records
            .iter()
            .filter(|record| record.classification == "timeout")
            .count(),
        memout: records
            .iter()
            .filter(|record| record.classification == "memout")
            .count(),
        error: records
            .iter()
            .filter(|record| record.classification == "error")
            .count(),
        par2_total,
        par2_avg: if total == 0 {
            0.0
        } else {
            round6(par2_total / total as f64)
        },
        dirty,
        promotable: false,
        admitted: false,
    }
}

fn summarize_categories(records: &[CaseRecord]) -> Vec<CategorySummary> {
    let mut grouped: BTreeMap<String, Vec<&CaseRecord>> = BTreeMap::new();
    for record in records {
        grouped
            .entry(record.category.clone())
            .or_default()
            .push(record);
    }
    grouped
        .into_iter()
        .map(|(category, rows)| summarize_category(&category, &rows))
        .collect()
}

fn summarize_category(category: &str, rows: &[&CaseRecord]) -> CategorySummary {
    let total = rows.len();
    let solved_sat = rows
        .iter()
        .filter(|record| record.solved && record.status == "sat")
        .count();
    let solved_unsat = rows
        .iter()
        .filter(|record| record.solved && record.status == "unsat")
        .count();
    let par2_total = round6(rows.iter().map(|record| record.par2_s).sum());
    CategorySummary {
        category: category.to_string(),
        total,
        solved: solved_sat + solved_unsat,
        solved_sat,
        solved_unsat,
        wrong: rows.iter().filter(|record| record.wrong).count(),
        invalid: rows.iter().filter(|record| record.invalid).count(),
        unknown: rows
            .iter()
            .filter(|record| record.classification == "unknown")
            .count(),
        timeout: rows
            .iter()
            .filter(|record| record.classification == "timeout")
            .count(),
        memout: rows
            .iter()
            .filter(|record| record.classification == "memout")
            .count(),
        error: rows
            .iter()
            .filter(|record| record.classification == "error")
            .count(),
        par2_total,
        par2_avg: if total == 0 {
            0.0
        } else {
            round6(par2_total / total as f64)
        },
        stats_json_cases: rows
            .iter()
            .filter(|record| record.stats_json_present)
            .count(),
        route_counter_cases: rows
            .iter()
            .filter(|record| record.route_counters.values().any(|value| *value > 0.0))
            .count(),
    }
}

fn summarize_route_counters(records: &[CaseRecord], required: &[String]) -> RouteCounterSummary {
    let mut counters = BTreeMap::<String, RouteCounterAggregate>::new();
    for record in records {
        for (name, value) in &record.route_counters {
            let entry = counters.entry(name.clone()).or_default();
            entry.rows_present += 1;
            entry.total += *value;
            if *value > 0.0 {
                entry.rows_exercised += 1;
                entry.cases.push(record.case_id.clone());
            }
        }
    }
    RouteCounterSummary {
        schema: ROUTE_COUNTERS_SCHEMA,
        required: required.to_vec(),
        counters,
    }
}

fn gate_checks(
    records: &[CaseRecord],
    categories: &[CategorySummary],
    baseline: Option<&BaselineStats>,
    resource_plan: &crate::resource::ResourcePlan,
    args: &ChcGateArgs,
) -> Vec<GateCheck> {
    let mut checks = Vec::new();
    if args.require_all_categories {
        let present = categories
            .iter()
            .map(|summary| summary.category.as_str())
            .collect::<BTreeSet<_>>();
        let missing = CORE_CHC_CATEGORIES
            .iter()
            .filter(|category| !present.contains(**category))
            .copied()
            .collect::<Vec<_>>();
        checks.push(GateCheck {
            name: "require-all-core-chc-categories".to_string(),
            status: if missing.is_empty() { "pass" } else { "fail" }.to_string(),
            reason: if missing.is_empty() {
                "all core CHC categories present".to_string()
            } else {
                format!("missing categories: {}", missing.join(", "))
            },
        });
    }
    for counter in &args.require_route_counters {
        let exercised = records.iter().any(|record| {
            record
                .route_counters
                .get(counter)
                .is_some_and(|value| *value > 0.0)
        });
        checks.push(GateCheck {
            name: format!("require-route-counter:{counter}"),
            status: if exercised { "pass" } else { "fail" }.to_string(),
            reason: if exercised {
                format!("{counter} exercised by at least one row")
            } else {
                format!("{counter} was not exercised by any row")
            },
        });
    }
    if let Some(baseline) = baseline {
        checks.extend(baseline_checks(records, baseline, resource_plan, args));
    }
    checks
}

fn baseline_checks(
    records: &[CaseRecord],
    baseline: &BaselineStats,
    resource_plan: &crate::resource::ResourcePlan,
    args: &ChcGateArgs,
) -> Vec<GateCheck> {
    let current_solved = records.iter().filter(|record| record.solved).count();
    let current_par2 = round6(records.iter().map(|record| record.par2_s).sum());
    let mut checks = Vec::new();
    let current_envelope = crate::resource::effective_execution_envelope(
        resource_plan,
        crate::resource::ENFORCEMENT_AY_MEMORY_RSS_V1,
        args.timeout_sec,
    );
    let baseline_envelope = baseline
        .resource_plan
        .as_ref()
        .zip(baseline.resource_enforcement.as_deref())
        .zip(baseline.timeout_sec)
        .and_then(|((plan, enforcement), timeout_sec)| {
            crate::resource::effective_execution_envelope(plan, enforcement, timeout_sec).ok()
        });
    let comparable = current_envelope
        .as_ref()
        .ok()
        .is_some_and(|current| baseline_envelope.as_ref() == Some(current));
    checks.push(GateCheck {
        name: "baseline-resource-envelope".to_string(),
        status: if comparable { "pass" } else { "fail" }.to_string(),
        reason: if comparable {
            format!(
                "matching envelope {}",
                current_envelope.as_deref().unwrap_or("<invalid>")
            )
        } else {
            format!(
                "non-comparable: current={} baseline={}",
                current_envelope.as_deref().unwrap_or("<invalid>"),
                baseline_envelope
                    .as_deref()
                    .unwrap_or("<missing-or-legacy>")
            )
        },
    });
    if !comparable {
        return checks;
    }
    if let Some(baseline_solved) = baseline.solved {
        let delta = current_solved as isize - baseline_solved as isize;
        checks.push(GateCheck {
            name: "baseline-solved-delta".to_string(),
            status: if delta >= args.min_solved_delta {
                "pass"
            } else {
                "fail"
            }
            .to_string(),
            reason: format!(
                "current_solved={current_solved} baseline_solved={baseline_solved} delta={delta} required_delta={}",
                args.min_solved_delta
            ),
        });
    }
    if let Some(baseline_par2) = baseline.par2_total {
        let regression_pct = par2_regression_pct(current_par2, baseline_par2);
        checks.push(GateCheck {
            name: "baseline-par2-regression-pct".to_string(),
            status: if regression_pct <= args.max_par2_regression_pct {
                "pass"
            } else {
                "fail"
            }
            .to_string(),
            reason: format!(
                "current_par2={current_par2:.6} baseline_par2={baseline_par2:.6} regression_pct={regression_pct:.6} max={:.6}",
                args.max_par2_regression_pct
            ),
        });
    }
    checks
}

fn par2_regression_pct(current: f64, baseline: f64) -> f64 {
    if baseline <= 0.0 {
        if current > baseline {
            f64::INFINITY
        } else {
            0.0
        }
    } else {
        ((current - baseline) / baseline * 100.0).max(0.0)
    }
}

fn non_promotable_reasons(
    records: &[CaseRecord],
    git: &GitProvenance,
    checks: &[GateCheck],
) -> Vec<String> {
    let mut reasons = Vec::new();
    if git.source_dirty {
        reasons.push("dirty source tree".to_string());
    }
    if records.iter().any(|record| record.wrong) {
        reasons.push("wrong answers present".to_string());
    }
    if records.iter().any(|record| record.invalid) {
        reasons.push("invalid or unvalidated solved rows present".to_string());
    }
    if records.iter().any(|record| !record.stats_json_present) {
        reasons.push("missing stats JSON on at least one row".to_string());
    }
    reasons.extend(
        checks
            .iter()
            .filter(|check| check.status == "fail")
            .map(|check| format!("gate check failed: {}", check.name)),
    );
    reasons
}

fn evidence_warnings(records: &[CaseRecord]) -> Vec<String> {
    let mut warnings = Vec::new();
    if records.iter().any(|record| !record.stats_json_present) {
        warnings.push("one or more rows did not emit stats JSON".to_string());
    }
    if records.iter().any(|record| {
        matches!(record.status.as_str(), "sat" | "unsat")
            && !validation_valid_for_status(&record.validation, &record.status)
    }) {
        warnings.push("one or more solved rows lack mandatory validation counters".to_string());
    }
    warnings
}

fn load_baseline(path: &Path) -> Result<BaselineStats> {
    let data: Value = serde_json::from_str(&crate::resource::read_bounded_text(
        path,
        crate::resource::MAX_METADATA_BYTES,
        "CHC baseline",
    )?)?;
    let mut solved = None;
    let mut par2_total = None;
    let resource_plan = data
        .get("resource_plan")
        .cloned()
        .and_then(|value| serde_json::from_value(value).ok());
    let timeout_sec = data.get("timeout_sec").and_then(Value::as_f64);
    let resource_enforcement = data
        .get("resource_enforcement")
        .and_then(Value::as_str)
        .map(str::to_string);
    if let Some(summary) = data.get("summary").and_then(Value::as_object) {
        solved = summary
            .get("solved")
            .and_then(Value::as_u64)
            .and_then(|value| usize::try_from(value).ok());
        par2_total = summary
            .get("par2_total")
            .or_else(|| summary.get("par2_s"))
            .and_then(Value::as_f64);
        if solved.is_none() || par2_total.is_none() {
            if let Some(row) = summary
                .get("overall_by_mode")
                .and_then(Value::as_array)
                .and_then(|rows| {
                    rows.iter()
                        .find(|row| row.get("mode").and_then(Value::as_str) == Some(DEFAULT_MODE))
                        .or_else(|| rows.first())
                })
                .and_then(Value::as_object)
            {
                solved = solved.or_else(|| {
                    row.get("solved")
                        .and_then(Value::as_u64)
                        .and_then(|value| usize::try_from(value).ok())
                });
                par2_total = par2_total.or_else(|| {
                    row.get("par2_total")
                        .or_else(|| row.get("par2_s"))
                        .and_then(Value::as_f64)
                });
            }
        }
    }
    solved = solved.or_else(|| {
        data.get("solved")
            .or_else(|| data.get("solved_total"))
            .and_then(Value::as_u64)
            .and_then(|value| usize::try_from(value).ok())
    });
    par2_total = par2_total.or_else(|| {
        data.get("par2_total")
            .or_else(|| data.get("par2_s"))
            .and_then(Value::as_f64)
    });
    Ok(BaselineStats {
        source: display_path(path),
        solved,
        par2_total,
        resource_plan,
        timeout_sec,
        resource_enforcement,
    })
}

fn artifact_map(out_dir: &Path) -> BTreeMap<String, String> {
    [
        ("summary_json", "summary.json"),
        ("cases_jsonl", "cases.jsonl"),
        ("category_summary_csv", "category-summary.csv"),
        ("route_counters_json", "route-counters.json"),
        ("admission_md", "admission.md"),
    ]
    .into_iter()
    .map(|(name, rel)| (name.to_string(), out_dir.join(rel).display().to_string()))
    .collect()
}

fn write_json(path: &Path, value: &impl Serialize) -> Result<()> {
    let text = serde_json::to_string_pretty(value)?;
    fs::write(path, format!("{text}\n"))
        .with_bench_context(|| format!("writing {}", path.display()))
}

fn write_cases_jsonl(path: &Path, records: &[CaseRecord]) -> Result<()> {
    let mut file =
        File::create(path).with_bench_context(|| format!("creating {}", path.display()))?;
    for record in records {
        writeln!(file, "{}", serde_json::to_string(record)?)?;
    }
    Ok(())
}

fn write_category_csv(path: &Path, categories: &[CategorySummary]) -> Result<()> {
    let mut file =
        File::create(path).with_bench_context(|| format!("creating {}", path.display()))?;
    writeln!(
        file,
        "category,total,solved,solved_sat,solved_unsat,wrong,invalid,unknown,timeout,memout,error,par2_total,par2_avg,stats_json_cases,route_counter_cases"
    )?;
    for row in categories {
        writeln!(
            file,
            "{},{},{},{},{},{},{},{},{},{},{},{:.6},{:.6},{},{}",
            csv_escape(&row.category),
            row.total,
            row.solved,
            row.solved_sat,
            row.solved_unsat,
            row.wrong,
            row.invalid,
            row.unknown,
            row.timeout,
            row.memout,
            row.error,
            row.par2_total,
            row.par2_avg,
            row.stats_json_cases,
            row.route_counter_cases
        )?;
    }
    Ok(())
}

fn csv_escape(value: &str) -> String {
    if value.contains(',') || value.contains('"') || value.contains('\n') {
        format!("\"{}\"", value.replace('"', "\"\""))
    } else {
        value.to_string()
    }
}

fn write_admission_markdown(path: &Path, report: &ChcGateReport) -> Result<()> {
    let mut file =
        File::create(path).with_bench_context(|| format!("creating {}", path.display()))?;
    writeln!(file, "# CHC Gate Admission")?;
    writeln!(file)?;
    writeln!(
        file,
        "- status: {}",
        if report.summary.admitted {
            "admitted"
        } else {
            "not-admitted"
        }
    )?;
    writeln!(
        file,
        "- solved: {}/{}",
        report.summary.solved, report.summary.total
    )?;
    writeln!(file, "- par2_total: {:.6}", report.summary.par2_total)?;
    writeln!(file, "- wrong: {}", report.summary.wrong)?;
    writeln!(file, "- invalid: {}", report.summary.invalid)?;
    writeln!(file, "- memout: {}", report.summary.memout)?;
    writeln!(file, "- dirty: {}", report.summary.dirty)?;
    if !report.non_promotable_reasons.is_empty() {
        writeln!(file)?;
        writeln!(file, "## Non-Promotable Reasons")?;
        for reason in &report.non_promotable_reasons {
            writeln!(file, "- {reason}")?;
        }
    }
    if !report.checks.is_empty() {
        writeln!(file)?;
        writeln!(file, "## Checks")?;
        for check in &report.checks {
            writeln!(
                file,
                "- {}: {} ({})",
                check.name, check.status, check.reason
            )?;
        }
    }
    Ok(())
}

fn git_provenance() -> GitProvenance {
    let forced_dirty = std::env::var("AY_BENCH_CHC_GATE_FORCE_DIRTY")
        .ok()
        .is_some_and(|value| env_truthy(&value));
    let status = command_stdout("git", &["status", "--short"]).unwrap_or_default();
    let dirty = forced_dirty || !status.trim().is_empty();
    let dirty_entries = if forced_dirty && status.trim().is_empty() {
        1
    } else {
        status
            .lines()
            .filter(|line| !line.trim().is_empty())
            .count()
    };
    let commit = command_stdout("git", &["rev-parse", "HEAD"]).unwrap_or_default();
    let commit = commit.trim().to_string();
    GitProvenance {
        source_commit_short: if commit.len() >= 12 {
            commit[..12].to_string()
        } else {
            commit.clone()
        },
        source_commit: commit,
        source_branch: command_stdout("git", &["branch", "--show-current"])
            .unwrap_or_default()
            .trim()
            .to_string(),
        source_dirty: dirty,
        source_dirty_entries: dirty_entries,
        source_git_status_short: if forced_dirty && status.trim().is_empty() {
            "?? forced-dirty-by-AY_BENCH_CHC_GATE_FORCE_DIRTY".to_string()
        } else {
            status
        },
    }
}

fn command_stdout(program: &str, args: &[&str]) -> Option<String> {
    let output = crate::resource::capture_local_output(
        program,
        args.iter().copied(),
        std::time::Duration::from_secs(10),
        program,
    )
    .ok()?;
    if output.status.success() {
        Some(output.stdout)
    } else {
        None
    }
}

fn env_truthy(value: &str) -> bool {
    matches!(
        value.trim().to_ascii_lowercase().as_str(),
        "1" | "true" | "yes" | "on"
    )
}

fn binary_provenance(pinned: &crate::environment::PinnedSolver) -> Result<BinaryProvenance> {
    let provenance = pinned.provenance();
    let metadata = fs::metadata(&provenance.path)
        .with_bench_context(|| format!("reading pinned AY source metadata {}", provenance.path))?;
    Ok(BinaryProvenance {
        path: provenance.path.clone(),
        exists: true,
        sha256: provenance.sha256.clone(),
        size_bytes: Some(provenance.size_bytes),
        mtime_epoch: metadata
            .modified()
            .ok()
            .and_then(|mtime| mtime.duration_since(std::time::UNIX_EPOCH).ok())
            .and_then(|duration| i64::try_from(duration.as_secs()).ok()),
        version: Some(provenance.version_output.clone()),
    })
}

fn sanitize(value: &str) -> String {
    let sanitized = value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || matches!(ch, '.' | '-' | '_') {
                ch
            } else {
                '_'
            }
        })
        .collect::<String>();
    if sanitized.is_empty() {
        "case".to_string()
    } else {
        sanitized
    }
}

fn round6(value: f64) -> f64 {
    (value * 1_000_000.0).round() / 1_000_000.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn write_case(dir: &Path, rel: &str, sidecar: &str) -> PathBuf {
        let path = dir.join(rel);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, "(set-logic HORN)\n(check-sat)\n").unwrap();
        fs::write(path.with_extension("yml"), sidecar).unwrap();
        path
    }

    #[cfg(unix)]
    #[test]
    fn chc_gate_executes_one_pinned_snapshot_with_exact_recorded_environment() {
        use sha2::Digest as _;
        use std::os::unix::fs::PermissionsExt as _;

        assert!(std::env::var_os("HOME").is_some());
        let tmp = TempDir::new().expect("tempdir");
        let input = tmp.path().join("case.smt2");
        let original_input = "(set-logic HORN)\n; ORIGINAL_TOKEN\n(check-sat)\n";
        fs::write(&input, original_input).expect("write input");
        let solver = tmp.path().join("fake-ay.sh");
        fs::write(
            &solver,
            format!(
                "#!/bin/sh\nif [ \"$1\" = \"--version\" ]; then printf 'fake-ay 1\\n'; exit 0; fi\nif [ \"${{HOME+x}}\" = x ]; then printf 'inherited HOME\\n' >&2; exit 71; fi\nprintf '(set-logic HORN)\\n; MUTATED_SOURCE\\n(check-sat)\\n' > '{}'\nfor argument in \"$@\"; do solver_input=$argument; done\nif grep -q ORIGINAL_TOKEN \"$solver_input\"; then printf 'sat\\n'; else printf 'unsat\\n'; fi\n",
                input.display()
            ),
        )
        .expect("write solver");
        let mut permissions = fs::metadata(&solver)
            .expect("solver metadata")
            .permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&solver, permissions).expect("chmod solver");
        let resources =
            crate::resource::PlannedResources::for_test(&crate::runner::repo_root_public(), 4096);
        let pinned = crate::environment::PinnedSolver::capture(
            &solver,
            &resources,
            "CHC pinned snapshot regression",
        )
        .expect("pin solver");
        fs::write(&solver, "#!/bin/sh\nprintf 'unsat\\n'\n").expect("mutate source");
        let args = ChcGateArgs {
            manifest: None,
            roots: Vec::new(),
            sample: false,
            out_dir: tmp.path().join("out"),
            ay: solver,
            timeout_sec: 5.0,
            baseline: None,
            category: None,
            require_all_categories: false,
            require_route_counters: Vec::new(),
            allow_dirty: true,
            fail_on_wrong: true,
            fail_on_invalid: false,
            min_solved_delta: 0,
            max_par2_regression_pct: 0.0,
        };
        let run_root = tmp.path().join("runs");
        fs::create_dir(&run_root).expect("run root");
        let record = run_case(
            &ManifestCase {
                case_id: "case".to_string(),
                path: input.clone(),
                category: "LIA".to_string(),
                family: "test".to_string(),
                expected_status: "sat".to_string(),
                expected_source: "sidecar".to_string(),
                source: "test".to_string(),
                required_route_counters: Vec::new(),
            },
            &args,
            &run_root,
            &resources,
            pinned.execution_path(),
        )
        .expect("run pinned CHC solver");

        assert_eq!(record.status, "sat");
        assert!(record.command_argv[0].contains("ay-solver-pin-"));
        assert_eq!(record.path, display_path(&input));
        assert_ne!(record.solver_input_path, record.path);
        assert_eq!(
            record.command_argv.last().map(String::as_str),
            Some(record.solver_input_path.as_str())
        );
        assert_eq!(record.input_size_bytes, original_input.len() as u64);
        assert_eq!(
            record.input_sha256,
            format!(
                "sha256:{:x}",
                sha2::Sha256::digest(original_input.as_bytes())
            )
        );
        assert_eq!(
            fs::read_to_string(&record.solver_input_path).expect("read solver input snapshot"),
            original_input
        );
        assert!(
            fs::read_to_string(&input)
                .expect("read replaced source")
                .contains("MUTATED_SOURCE"),
            "the solver must mutate the original pathname before reading its argument"
        );
        assert!(!record.command_env.contains_key("HOME"));
        assert_eq!(
            record.command_env.get("LC_ALL").map(String::as_str),
            Some("C")
        );
        assert_eq!(
            record.command_env.get("MEMLIMIT").map(String::as_str),
            Some("4096")
        );
        assert!(pinned.verify_source().is_err());
    }

    #[cfg(unix)]
    #[test]
    fn chc_gate_rejects_symlink_input_before_snapshotting() {
        use std::os::unix::fs::symlink;

        let tmp = TempDir::new().expect("tempdir");
        let target = tmp.path().join("target.smt2");
        fs::write(&target, "(check-sat)\n").expect("write target");
        let link = tmp.path().join("link.smt2");
        symlink(&target, &link).expect("create input symlink");
        let case = ManifestCase {
            case_id: "linked".to_string(),
            path: link.clone(),
            category: "LIA".to_string(),
            family: "test".to_string(),
            expected_status: "sat".to_string(),
            expected_source: "manifest".to_string(),
            source: "test".to_string(),
            required_route_counters: Vec::new(),
        };
        let validation_error = validate_manifest_cases(&[case])
            .expect_err("manifest validation must reject a symlink input")
            .to_string();
        assert!(
            validation_error.contains("not a non-symlink regular file"),
            "{validation_error}"
        );

        let case_dir = tmp.path().join("run");
        fs::create_dir(&case_dir).expect("case dir");
        assert!(
            snapshot_case_input(&link, &case_dir).is_err(),
            "the authoritative snapshot open must independently reject symlinks"
        );
    }

    #[test]
    fn chc_gate_normalizes_core_categories() {
        assert_eq!(normalize_category_name("lia-lin-arrays"), "LIA-Lin-Arrays");
        assert_eq!(normalize_category_name("mixed-lia-lra"), "mixed_LIA_LRA");
        assert_eq!(normalize_category_name("BOOL"), "BOOL");
    }

    #[test]
    fn chc_gate_json_manifest_uses_sidecar_expected_and_route_counters() {
        let tmp = TempDir::new().unwrap();
        let bench = write_case(
            tmp.path(),
            "family/case.smt2",
            "properties:\n- expected_verdict: false\n  majority_vote_verdict: false\n",
        );
        let manifest = tmp.path().join("manifest.json");
        fs::write(
            &manifest,
            serde_json::json!({
                "benchmarks": [{
                    "id": "case-a",
                    "path": bench,
                    "category": "lia-lin",
                    "expected_status": "sat",
                    "route_counters_expected": ["chc.route.demo"]
                }]
            })
            .to_string(),
        )
        .unwrap();

        let cases = load_manifest_spec(manifest.to_str().unwrap(), None).unwrap();
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].case_id, "case-a");
        assert_eq!(cases[0].category, "LIA-Lin");
        assert_eq!(cases[0].expected_status, "unsat");
        assert!(cases[0].expected_source.starts_with("sidecar:"));
        assert_eq!(cases[0].required_route_counters, vec!["chc.route.demo"]);
    }

    #[test]
    fn chc_gate_sidecar_expected_keys_are_exact_unique_and_consistent() {
        let tmp = TempDir::new().unwrap();
        let unrelated = write_case(
            tmp.path(),
            "unrelated.smt2",
            "not_expected_verdict: true\nmajority_vote_verdict_note: false\n",
        );
        assert_eq!(
            read_sidecar_expected(&unrelated).origin,
            ExpectedOrigin::None
        );

        let duplicate = write_case(
            tmp.path(),
            "duplicate.smt2",
            "expected_verdict: true\n- expected_verdict: true\n",
        );
        assert_eq!(
            read_sidecar_expected(&duplicate).origin,
            ExpectedOrigin::SidecarInvalid
        );

        let conflicting = write_case(
            tmp.path(),
            "conflicting.smt2",
            "expected_verdict: true\nmajority_vote_verdict: false\n",
        );
        assert_eq!(
            read_sidecar_expected(&conflicting).origin,
            ExpectedOrigin::SidecarInvalid
        );
    }

    #[test]
    fn chc_gate_result_parser_requires_one_authoritative_stdout_line() {
        assert_eq!(extract_solver_result("sat\n"), "sat");
        assert_eq!(
            extract_solver_result("diagnostic: expected unsat\n"),
            "error"
        );
        assert_eq!(extract_solver_result("sat\nsat\n"), "error");
        assert_eq!(extract_solver_result("sat\nunsat\n"), "error");
        assert_eq!(
            solver_status_from_process(false, false, false, false, "sat\n"),
            "error",
            "a process abort after emitting a verdict is not solved"
        );
    }

    #[test]
    fn chc_gate_rejects_duplicate_and_colliding_case_ids() {
        let tmp = TempDir::new().unwrap();
        let first_path = write_case(tmp.path(), "first.smt2", "expected_verdict: true\n");
        let second_path = write_case(tmp.path(), "second.smt2", "expected_verdict: true\n");
        let make = |case_id: &str, path: &Path, source: &str| ManifestCase {
            case_id: case_id.to_string(),
            path: path.to_path_buf(),
            category: "LIA".to_string(),
            family: "test".to_string(),
            expected_status: "sat".to_string(),
            expected_source: "manifest".to_string(),
            source: source.to_string(),
            required_route_counters: Vec::new(),
        };
        let cases = vec![
            make("a/b", &first_path, "first-source"),
            make("a_b", &second_path, "second-source"),
            make("a/b", &second_path, "duplicate-source"),
        ];
        let error = validate_manifest_cases(&cases)
            .expect_err("duplicate and colliding IDs must be rejected")
            .to_string();
        assert!(error.contains("duplicate CHC case ID"), "{error}");
        assert!(error.contains("collide at output directory"), "{error}");
        assert!(error.contains("first-source"), "{error}");
        assert!(error.contains("second-source"), "{error}");
    }

    #[test]
    fn chc_gate_root_discovery_enforces_case_cap() {
        let tmp = TempDir::new().unwrap();
        for name in ["a.smt2", "b.smt2", "c.smt2"] {
            fs::write(tmp.path().join(name), "(set-logic HORN)\n").unwrap();
        }
        let mut cases = Vec::new();
        let error = collect_smt2_cases_with_limits(tmp.path(), None, &mut cases, 100, 100, 2)
            .expect_err("root discovery must enforce its case cap");
        assert!(error.to_string().contains("2-case cap"));
        assert!(cases.len() <= 2);
    }

    #[test]
    fn chc_gate_set_manifest_resolves_sidecar_input_file() {
        let tmp = TempDir::new().unwrap();
        let bench_dir = tmp.path().join("bench");
        let family = bench_dir.join("family");
        fs::create_dir_all(&family).unwrap();
        fs::write(family.join("actual.smt2"), "(check-sat)\n").unwrap();
        fs::write(
            family.join("case.yml"),
            "input_files: actual.smt2\nproperties:\n- expected_verdict: true\n",
        )
        .unwrap();
        let set = bench_dir.join("LIA.set");
        fs::write(&set, "family/case.yml\n").unwrap();

        let cases = load_manifest_spec(&format!("LIA-Lin={}", set.display()), None).unwrap();
        assert_eq!(cases.len(), 1);
        assert_eq!(cases[0].path, family.join("actual.smt2"));
        assert_eq!(cases[0].category, "LIA-Lin");
        assert_eq!(cases[0].expected_status, "sat");
    }

    #[test]
    fn chc_gate_par2_scores_unsolved_as_double_timeout() {
        let solved = CaseRecord {
            schema: CASES_SCHEMA,
            case_id: "a".to_string(),
            path: "a.smt2".to_string(),
            solver_input_path: "snapshot-a.smt2".to_string(),
            input_sha256: "sha256:test".to_string(),
            input_size_bytes: 1,
            category: "LIA".to_string(),
            family: "f".to_string(),
            expected_status: "sat".to_string(),
            expected_source: "manifest".to_string(),
            source: "manifest:m".to_string(),
            status: "sat".to_string(),
            classification: "solved".to_string(),
            solved: true,
            wrong: false,
            invalid: false,
            invalid_reasons: Vec::new(),
            elapsed_s: Some(0.25),
            par2_s: 0.25,
            timed_out: false,
            exit_code: Some(0),
            process_status: "exit status: 0".to_string(),
            stats_json_present: true,
            stats_json_path: String::new(),
            validation: ValidationTelemetry::default(),
            transform_memory: TransformMemoryTelemetry::default(),
            route: RouteTelemetry::default(),
            route_counters: BTreeMap::new(),
            required_route_counters: Vec::new(),
            missing_required_route_counters: Vec::new(),
            stdout: String::new(),
            stderr: String::new(),
            command_argv: Vec::new(),
            command_env: BTreeMap::new(),
        };
        let mut timeout = solved.clone();
        timeout.case_id = "b".to_string();
        timeout.solved = false;
        timeout.status = "timeout".to_string();
        timeout.classification = "timeout".to_string();
        timeout.par2_s = 4.0;
        let summary = summarize_overall(&[solved, timeout], false);
        assert_eq!(summary.solved, 1);
        assert_eq!(summary.par2_total, 4.25);
        assert_eq!(summary.memout, 0);
    }

    #[test]
    fn chc_gate_baseline_regression_check_fails_on_solved_loss() {
        let baseline = BaselineStats {
            source: "baseline.json".to_string(),
            solved: Some(2),
            par2_total: Some(1.0),
            resource_plan: Some(crate::resource::ResourcePlan {
                requested_jobs: 1,
                jobs: 1,
                memlimit_mb_per_child: 1024,
                nbcore_per_child: 1,
                headroom_mb: 16000,
                planner: "test".to_string(),
            }),
            timeout_sec: Some(2.0),
            resource_enforcement: Some(crate::resource::ENFORCEMENT_AY_MEMORY_RSS_V1.to_string()),
        };
        let args = ChcGateArgs {
            manifest: Some(PathBuf::from("m.json")),
            roots: Vec::new(),
            sample: false,
            out_dir: PathBuf::from("out"),
            ay: PathBuf::from("ay"),
            timeout_sec: 2.0,
            baseline: None,
            category: None,
            require_all_categories: false,
            require_route_counters: Vec::new(),
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_invalid: false,
            min_solved_delta: 0,
            max_par2_regression_pct: 0.0,
        };
        let current_plan = baseline.resource_plan.clone().unwrap();
        let checks = baseline_checks(&[], &baseline, &current_plan, &args);
        assert!(
            checks
                .iter()
                .any(|check| check.name == "baseline-solved-delta" && check.status == "fail"),
            "{checks:?}"
        );
    }

    #[test]
    fn chc_gate_memout_has_distinct_classification_and_summary_bucket() {
        assert_eq!(classify_case("memout", false, false, false), "memout");
        let mut row = CaseRecord {
            schema: CASES_SCHEMA,
            case_id: "mem".to_string(),
            path: "mem.smt2".to_string(),
            solver_input_path: "snapshot-mem.smt2".to_string(),
            input_sha256: "sha256:test".to_string(),
            input_size_bytes: 1,
            category: "LIA".to_string(),
            family: "f".to_string(),
            expected_status: "sat".to_string(),
            expected_source: "manifest".to_string(),
            source: "manifest:m".to_string(),
            status: "memout".to_string(),
            classification: "memout".to_string(),
            solved: false,
            wrong: false,
            invalid: false,
            invalid_reasons: Vec::new(),
            elapsed_s: Some(1.0),
            par2_s: 4.0,
            timed_out: false,
            exit_code: None,
            process_status: "signal: 9".to_string(),
            stats_json_present: false,
            stats_json_path: String::new(),
            validation: ValidationTelemetry::default(),
            transform_memory: TransformMemoryTelemetry::default(),
            route: RouteTelemetry::default(),
            route_counters: BTreeMap::new(),
            required_route_counters: Vec::new(),
            missing_required_route_counters: Vec::new(),
            stdout: String::new(),
            stderr: String::new(),
            command_argv: Vec::new(),
            command_env: BTreeMap::new(),
        };
        let overall = summarize_overall(std::slice::from_ref(&row), false);
        assert_eq!(overall.memout, 1);
        assert_eq!(overall.error, 0);
        let categories = summarize_categories(std::slice::from_ref(&row));
        assert_eq!(categories[0].memout, 1);
        assert_eq!(categories[0].error, 0);
        row.classification = "error".to_string();
        assert_eq!(summarize_overall(&[row], false).error, 1);
    }

    #[test]
    fn chc_gate_baseline_envelope_mismatch_skips_performance_comparison() {
        let baseline = BaselineStats {
            source: "baseline.json".to_string(),
            solved: Some(1),
            par2_total: Some(1.0),
            resource_plan: None,
            timeout_sec: None,
            resource_enforcement: None,
        };
        let args = ChcGateArgs {
            manifest: None,
            roots: Vec::new(),
            sample: false,
            out_dir: PathBuf::from("out"),
            ay: PathBuf::from("ay"),
            timeout_sec: 1.0,
            baseline: None,
            category: None,
            require_all_categories: false,
            require_route_counters: Vec::new(),
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_invalid: false,
            min_solved_delta: 0,
            max_par2_regression_pct: 0.0,
        };
        let plan = crate::resource::ResourcePlan {
            requested_jobs: 1,
            jobs: 1,
            memlimit_mb_per_child: 1024,
            nbcore_per_child: 1,
            headroom_mb: 16000,
            planner: "test".to_string(),
        };
        let checks = baseline_checks(&[], &baseline, &plan, &args);
        assert_eq!(checks.len(), 1);
        assert_eq!(checks[0].name, "baseline-resource-envelope");
        assert_eq!(checks[0].status, "fail");
        assert!(checks[0].reason.contains("non-comparable"));
    }
}
