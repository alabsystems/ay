// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! First-class SAT delta gate for SAT-COMP work.
//!
//! This is the Rust replacement for the ad-hoc SAT hard-tail Python wrappers:
//! it owns benchmark discovery, solver execution, SAT status parsing,
//! provenance capture, SAT-COMP PAR-2 scoring, and compact durable artifacts.

use crate::error::{BenchError, Result, WithContext};
use serde::Serialize;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::Instant;

const REPORT_SCHEMA: &str = "ay.sat-delta-report/v1";
const AY_ENV_PROVENANCE_NOTE: &str = "--ay-env records requested env provenance; AY-only stats-json capture records whether known env-gated solver behavior was exercised.";
const BCP_RELOCATION_ENV: &str = "AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION";
const BCP_SEARCH_INPLACE_WATCH_SCAN_ENV: &str = "AY_SAT_BCP_SEARCH_INPLACE_WATCH_SCAN";
const DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV: &str = "AY_SAT_DENSE_MUTEX_FOCUSED_RESTART_GATE";
const AY_TIMEOUT_CLEANUP_GRACE_MAX_SEC: f64 = 5.0;
const BCP_RELOCATION_ENABLED_KEY: &str = "sat.bcp_learned_1963_true_tail_relocation_enabled";
const BCP_RELOCATION_ATTEMPTS_KEY: &str = "sat.bcp_learned_1963_true_tail_relocation_attempts";
const BCP_RELOCATION_MOVES_KEY: &str = "sat.bcp_learned_1963_true_tail_relocation_moves";
const BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_requested";
const BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY: &str = "sat.bcp_search_inplace_watch_scan_enabled";
const BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY: &str =
    "sat.bcp_search_inplace_watch_scan_exercised";
const DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_requested";
const DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_enabled";
const FOCUSED_RESTART_GATE_FINAL_KEY: &str = "sat.focused_restart_gate_final";
const DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY: &str =
    "sat.dense_mutex_focused_restart_gate_updates";
const DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY: &str =
    "sat.dense_mutex_focused_restart_runtime_checked";
const DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY: &str =
    "sat.dense_mutex_focused_restart_active_vars";
const DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY: &str =
    "sat.dense_mutex_focused_restart_active_clauses";
const DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY: &str =
    "sat.dense_mutex_focused_restart_active_binary_clauses";
const DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY: &str =
    "sat.dense_mutex_focused_restart_runtime_candidate";
const DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY: &str =
    "sat.dense_mutex_focused_restart_previous_gate";
const DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY: &str =
    "sat.dense_mutex_focused_restart_computed_gate";
const VERIFIED_PROOF_LINES: &[&str] = &["VERIFIED", "s VERIFIED", "s VERIFIED UNSAT"];
const RAW_TSV_COLUMNS: &[&str] = &[
    "solver",
    "instance",
    "path",
    "expected",
    "actual",
    "family",
    "category",
    "elapsed_s",
    "par2_s",
    "exit_code",
    "wrong",
    "invalid",
    "proof_status",
    "model_status",
    "timeout",
    "binary_path",
    "binary_sha256",
    "binary_size_bytes",
    "binary_mtime_epoch",
    "command_path",
    "command_sha256",
    "command_argv_json",
    "ay_env_json",
    "stats_json_path",
    "stats_json_sha256",
    "stats_capture_status",
    "stats_mode",
    "stats_result",
    "stats_wall_time_ms",
    "bcp_relocation_enabled",
    "bcp_relocation_attempts",
    "bcp_relocation_moves",
    "bcp_relocation_exercised",
    "bcp_search_inplace_watch_scan_requested",
    "bcp_search_inplace_watch_scan_enabled",
    "bcp_search_inplace_watch_scan_exercised",
    "dense_mutex_focused_restart_gate_requested",
    "dense_mutex_focused_restart_gate_enabled",
    "focused_restart_gate_final",
    "dense_mutex_focused_restart_gate_updates",
    "dense_mutex_focused_restart_runtime_checked",
    "dense_mutex_focused_restart_active_vars",
    "dense_mutex_focused_restart_active_clauses",
    "dense_mutex_focused_restart_active_binary_clauses",
    "dense_mutex_focused_restart_runtime_candidate",
    "dense_mutex_focused_restart_previous_gate",
    "dense_mutex_focused_restart_computed_gate",
    "dense_mutex_focused_restart_gate_exercised",
    "proof_path",
    "proof_checker_command_path",
    "proof_checker_command_sha256",
    "proof_checker_exit_code",
    "proof_checker_stdout",
    "proof_checker_stderr",
    "stdout",
    "stderr",
];

/// Arguments for `ay bench sat-delta`.
#[derive(Debug)]
pub struct SatDeltaArgs {
    pub manifest: Option<PathBuf>,
    pub benchmark_root: PathBuf,
    pub out_dir: PathBuf,
    pub ay: PathBuf,
    pub ay_env: Vec<(String, String)>,
    pub reference_solvers: Vec<(String, PathBuf)>,
    pub timeout_sec: f64,
    pub sat_variant: String,
    pub proof_format: String,
    pub proof_checker: Option<PathBuf>,
    pub allow_dirty: bool,
    pub fail_on_wrong: bool,
    pub fail_on_ay_ref_loss: bool,
    pub require_bcp_relocation_exercise: bool,
    pub require_bcp_search_inplace_watch_scan_exercise: bool,
    pub require_dense_mutex_focused_restart_gate_exercise: bool,
}

#[derive(Debug, Clone)]
struct Benchmark {
    path: PathBuf,
    expected: String,
    family: String,
    category: String,
    name: String,
}

#[derive(Debug, Clone, Serialize)]
struct BinaryProvenance {
    path: String,
    exists: bool,
    executable: bool,
    sha256: String,
    size_bytes: Option<u64>,
    mtime_epoch: Option<i64>,
    version: Option<String>,
    build_profile: Option<String>,
}

#[derive(Debug, Clone, Serialize)]
struct GitProvenance {
    source_commit: String,
    source_commit_short: String,
    source_branch: String,
    source_dirty: bool,
    source_dirty_entries: usize,
    source_git_status_sha256: String,
    source_git_status_short: String,
}

#[derive(Debug, Clone, Serialize)]
struct RunRecord {
    solver: String,
    instance: String,
    path: String,
    expected: String,
    actual: String,
    family: String,
    category: String,
    elapsed_s: f64,
    par2_s: f64,
    exit_code: Option<i32>,
    wrong: bool,
    invalid: bool,
    proof_status: String,
    model_status: String,
    timeout: bool,
    binary_path: String,
    binary_sha256: String,
    binary_size_bytes: Option<u64>,
    binary_mtime_epoch: Option<i64>,
    command_path: String,
    command_sha256: String,
    command_argv: Vec<String>,
    command_display: String,
    ay_env: Vec<String>,
    stats: StatsCapture,
    bcp_relocation: BcpRelocationStats,
    bcp_search_inplace_watch_scan: BcpSearchInplaceWatchScanStats,
    dense_mutex_focused_restart_gate: DenseMutexFocusedRestartGateStats,
    proof_path: String,
    proof_checker_command_path: String,
    proof_checker_command_sha256: String,
    proof_checker_exit_code: Option<i32>,
    proof_checker_stdout: String,
    proof_checker_stderr: String,
    stdout: String,
    stderr: String,
}

#[derive(Debug, Clone, Serialize)]
struct StatsCapture {
    path: String,
    sha256: String,
    status: String,
    mode: String,
    result: String,
    wall_time_ms: Option<u64>,
}

impl StatsCapture {
    fn not_applicable() -> Self {
        Self {
            path: String::new(),
            sha256: String::new(),
            status: "not-applicable".to_string(),
            mode: String::new(),
            result: String::new(),
            wall_time_ms: None,
        }
    }

    fn missing(status: &str) -> Self {
        Self {
            path: String::new(),
            sha256: String::new(),
            status: status.to_string(),
            mode: String::new(),
            result: String::new(),
            wall_time_ms: None,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct BcpRelocationStats {
    enabled: Option<bool>,
    attempts: Option<u64>,
    moves: Option<u64>,
    exercised: bool,
}

impl BcpRelocationStats {
    fn none() -> Self {
        Self {
            enabled: None,
            attempts: None,
            moves: None,
            exercised: false,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct BcpSearchInplaceWatchScanStats {
    requested: Option<bool>,
    enabled: Option<bool>,
    exercised: bool,
}

impl BcpSearchInplaceWatchScanStats {
    fn none() -> Self {
        Self {
            requested: None,
            enabled: None,
            exercised: false,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct DenseMutexFocusedRestartGateStats {
    requested: Option<bool>,
    enabled: Option<bool>,
    focused_gate_final: Option<u64>,
    updates: Option<u64>,
    runtime_checked: Option<u64>,
    active_vars: Option<u64>,
    active_clauses: Option<u64>,
    active_binary_clauses: Option<u64>,
    runtime_candidate: Option<bool>,
    previous_gate: Option<u64>,
    computed_gate: Option<u64>,
    exercised: bool,
}

impl DenseMutexFocusedRestartGateStats {
    fn none() -> Self {
        Self {
            requested: None,
            enabled: None,
            focused_gate_final: None,
            updates: None,
            runtime_checked: None,
            active_vars: None,
            active_clauses: None,
            active_binary_clauses: None,
            runtime_candidate: None,
            previous_gate: None,
            computed_gate: None,
            exercised: false,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct Summary {
    total: usize,
    solved: usize,
    solved_sat: usize,
    solved_unsat: usize,
    wrong: usize,
    invalid: usize,
    timeout: usize,
    memout: usize,
    unknown: usize,
    par2_total: f64,
    par2_avg: f64,
    disqualified: bool,
}

#[derive(Debug, Clone, Serialize)]
struct ReferenceDelta {
    reference: String,
    ay_solved: usize,
    reference_solved: usize,
    solved_delta: isize,
    ay_par2_total: f64,
    reference_par2_total: f64,
    par2_delta: f64,
    ref_only_solved: usize,
    ay_only_solved: usize,
    definitive_disagree: usize,
}

#[derive(Debug, Serialize)]
struct SatDeltaReport {
    schema: &'static str,
    git: GitProvenance,
    runner: BinaryProvenance,
    evidence_warnings: Vec<String>,
    timeout_sec: f64,
    sat_variant: String,
    proof_format: String,
    proof_checker: Option<String>,
    proof_checker_provenance: Option<BinaryProvenance>,
    ay_env: Vec<String>,
    ay_env_note: &'static str,
    require_bcp_relocation_exercise: bool,
    bcp_relocation_env_requested: bool,
    require_bcp_search_inplace_watch_scan_exercise: bool,
    bcp_search_inplace_watch_scan_env_requested: bool,
    require_dense_mutex_focused_restart_gate_exercise: bool,
    dense_mutex_focused_restart_gate_env_requested: bool,
    dirty_evidence_explicitly_allowed: bool,
    manifest: String,
    out_dir: String,
    solvers: BTreeMap<String, BinaryProvenance>,
    summaries: BTreeMap<String, Summary>,
    reference_deltas: Vec<ReferenceDelta>,
    records: Vec<RunRecord>,
    resource_plan: crate::resource::ResourcePlan,
}

/// Run the SAT delta gate and write compact artifacts under `out_dir`.
pub fn cmd_sat_delta(args: SatDeltaArgs) -> Result<()> {
    crate::resource::checked_benchmark_timeout(args.timeout_sec, "SAT delta")?;
    let resources = crate::resource::PlannedResources::plan(&repo_root(), 1, "ay bench sat-delta")?;
    eprintln!(
        "sat-delta: resource plan jobs=1 memory={}MiB NBCORE={} headroom={}MiB enforcement=rss_watchdog",
        resources.plan.memlimit_mb_per_child,
        resources.plan.nbcore_per_child,
        resources.plan.headroom_mb,
    );

    let git = git_provenance();
    if git.source_dirty && !args.allow_dirty {
        return Err(BenchError::InvalidArgs {
            reason: "source tree is dirty; pass --allow-dirty to label evidence dirty".to_string(),
        });
    }

    let manifest_rows = if let Some(manifest) = &args.manifest {
        load_manifest(manifest)?
    } else {
        default_hard_tail_rows(&args.benchmark_root)?
    };
    if manifest_rows.is_empty() {
        return Err(BenchError::InvalidArgs {
            reason: "SAT delta needs at least one benchmark row".to_string(),
        });
    }

    fs::create_dir_all(&args.out_dir).with_bench_context(|| {
        format!("creating SAT delta output dir {}", args.out_dir.display())
    })?;
    let run_dir = args.out_dir.join("runs");
    fs::create_dir_all(&run_dir)
        .with_bench_context(|| format!("creating run dir {}", run_dir.display()))?;

    let mut solvers: Vec<(String, PathBuf, SolverKind)> =
        vec![("ay".to_string(), args.ay.clone(), SolverKind::AY)];
    for (name, path) in &args.reference_solvers {
        solvers.push((name.clone(), path.clone(), SolverKind::Reference));
    }

    let mut solver_provenance = BTreeMap::new();
    for (name, path, kind) in &solvers {
        solver_provenance.insert(name.clone(), binary_provenance(path, *kind, &resources));
    }
    let runner = current_runner_provenance(&resources);
    let proof_checker_provenance = args
        .proof_checker
        .as_ref()
        .map(|path| binary_provenance(path, SolverKind::Reference, &resources));
    let evidence_warnings = evidence_warnings(
        &git,
        &runner,
        &solver_provenance,
        &args.proof_format,
        proof_checker_provenance.as_ref(),
    );

    let mut records = Vec::new();
    for (solver_name, solver_path, kind) in &solvers {
        for benchmark in &manifest_rows {
            let record = run_one(
                solver_name,
                solver_path,
                *kind,
                benchmark,
                &args,
                &run_dir,
                &resources,
            )?;
            records.push(record);
        }
    }

    let summaries = summarize_by_solver(&records);
    let reference_deltas = reference_deltas(&records, &summaries);
    let bcp_relocation_env_requested = bcp_relocation_requested(&args);
    let bcp_relocation_gate_failure = bcp_relocation_gate_failure(&records, &args);
    let bcp_search_inplace_watch_scan_env_requested =
        bcp_search_inplace_watch_scan_requested(&args);
    let bcp_search_inplace_watch_scan_gate_failure =
        bcp_search_inplace_watch_scan_gate_failure(&records, &args);
    let dense_mutex_focused_restart_gate_env_requested =
        dense_mutex_focused_restart_gate_requested(&args);
    let dense_mutex_focused_restart_gate_failure =
        dense_mutex_focused_restart_gate_failure(&records, &args);
    let report = SatDeltaReport {
        schema: REPORT_SCHEMA,
        git,
        runner,
        evidence_warnings,
        timeout_sec: args.timeout_sec,
        sat_variant: args.sat_variant,
        proof_format: args.proof_format,
        proof_checker: args
            .proof_checker
            .as_ref()
            .map(|path| path.display().to_string()),
        proof_checker_provenance,
        ay_env: env_display_list(&args.ay_env),
        ay_env_note: AY_ENV_PROVENANCE_NOTE,
        require_bcp_relocation_exercise: args.require_bcp_relocation_exercise,
        bcp_relocation_env_requested,
        require_bcp_search_inplace_watch_scan_exercise: args
            .require_bcp_search_inplace_watch_scan_exercise,
        bcp_search_inplace_watch_scan_env_requested,
        require_dense_mutex_focused_restart_gate_exercise: args
            .require_dense_mutex_focused_restart_gate_exercise,
        dense_mutex_focused_restart_gate_env_requested,
        dirty_evidence_explicitly_allowed: args.allow_dirty,
        manifest: args.manifest.as_ref().map_or_else(
            || "<built-in-hard-tail>".to_string(),
            |p| p.display().to_string(),
        ),
        out_dir: args.out_dir.display().to_string(),
        solvers: solver_provenance,
        summaries,
        reference_deltas,
        records,
        resource_plan: resources.plan.clone(),
    };

    write_json(&args.out_dir.join("sat-delta-report.json"), &report)?;
    write_raw_tsv(&args.out_dir.join("raw.tsv"), &report.records)?;
    write_markdown(&args.out_dir.join("scoreboard.md"), &report)?;

    println!(
        "sat-delta report: {}",
        args.out_dir.join("sat-delta-report.json").display()
    );
    println!(
        "sat-delta scoreboard: {}",
        args.out_dir.join("scoreboard.md").display()
    );

    if args.fail_on_wrong && report.records.iter().any(|r| r.wrong || r.invalid) {
        return Err(BenchError::ScoringFailed {
            reason: "wrong or invalid row in SAT delta report".to_string(),
        });
    }
    if let Some(reason) = bcp_relocation_gate_failure {
        return Err(BenchError::ScoringFailed { reason });
    }
    if let Some(reason) = bcp_search_inplace_watch_scan_gate_failure {
        return Err(BenchError::ScoringFailed { reason });
    }
    if let Some(reason) = dense_mutex_focused_restart_gate_failure {
        return Err(BenchError::ScoringFailed { reason });
    }
    if args.fail_on_ay_ref_loss
        && report
            .reference_deltas
            .iter()
            .any(|delta| delta.solved_delta < 0 || delta.par2_delta > 0.0)
    {
        return Err(BenchError::ScoringFailed {
            reason: "AY loses to at least one reference solver".to_string(),
        });
    }

    Ok(())
}

#[derive(Debug, Clone, Copy)]
enum SolverKind {
    AY,
    Reference,
}

#[derive(Debug, Clone)]
struct RowValidation {
    proof_status: String,
    model_status: String,
    invalid: bool,
    proof_checker_command_path: String,
    proof_checker_command_sha256: String,
    proof_checker_exit_code: Option<i32>,
    proof_checker_stdout: String,
    proof_checker_stderr: String,
}

impl RowValidation {
    fn not_applicable() -> Self {
        Self {
            proof_status: "n/a".to_string(),
            model_status: "n/a".to_string(),
            invalid: false,
            proof_checker_command_path: String::new(),
            proof_checker_command_sha256: String::new(),
            proof_checker_exit_code: None,
            proof_checker_stdout: String::new(),
            proof_checker_stderr: String::new(),
        }
    }
}

fn load_manifest(path: &Path) -> Result<Vec<Benchmark>> {
    let text = crate::resource::read_bounded_text(
        path,
        crate::resource::MAX_METADATA_BYTES,
        "SAT delta manifest",
    )?;
    let mut lines = text.lines();
    let header = lines.next().ok_or_else(|| BenchError::InvalidArgs {
        reason: format!("empty manifest {}", path.display()),
    })?;
    let columns = parse_csv_record(header);
    let column_index = |name: &str| columns.iter().position(|col| col == name);
    let path_col = column_index("local_path")
        .or_else(|| column_index("path"))
        .ok_or_else(|| BenchError::InvalidArgs {
            reason: "manifest needs local_path or path column".to_string(),
        })?;
    let expected_col = column_index("result").or_else(|| column_index("expected"));
    let family_col = column_index("family");
    let category_col = column_index("category");

    let mut rows = Vec::new();
    for (line_no, line) in lines.enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let fields = parse_csv_record(line);
        let Some(raw_path) = fields.get(path_col).filter(|s| !s.is_empty()) else {
            return Err(BenchError::InvalidArgs {
                reason: format!(
                    "manifest {} line {} missing path",
                    path.display(),
                    line_no + 2
                ),
            });
        };
        let path = PathBuf::from(raw_path);
        let path = if path.is_absolute() {
            path
        } else {
            repo_root().join(path)
        };
        rows.push(Benchmark {
            name: path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("<unknown>")
                .to_string(),
            path,
            expected: expected_col
                .and_then(|idx| fields.get(idx))
                .map_or_else(|| "unknown".to_string(), |s| normalize_expected(s)),
            family: family_col
                .and_then(|idx| fields.get(idx))
                .filter(|s| !s.is_empty())
                .map_or_else(|| "unknown".to_string(), Clone::clone),
            category: category_col
                .and_then(|idx| fields.get(idx))
                .filter(|s| !s.is_empty())
                .map_or_else(|| "unknown".to_string(), Clone::clone),
        });
    }
    Ok(rows)
}

fn default_hard_tail_rows(root: &Path) -> Result<Vec<Benchmark>> {
    let manifest_rows = load_root_manifest_if_present(root)?;
    let specs = [
        ("clique_n2_k10", "*clique_n2_k10*", true),
        ("Circuit_multiplier22", "*Circuit_multiplier22*", false),
        ("FmlaEquivChain_4_6_6", "*FmlaEquivChain_4_6_6*", false),
    ];
    let mut rows = Vec::new();
    for (family, needle, required) in specs {
        let pattern = needle.trim_matches('*');
        let found = find_named_cnf(root, pattern)?;
        match found {
            Some(path) => {
                let expected = manifest_rows
                    .as_ref()
                    .and_then(|manifest| manifest_expected_for_pattern(manifest, pattern))
                    .unwrap_or_else(|| "unknown".to_string());
                rows.push(Benchmark {
                    name: path
                        .file_name()
                        .and_then(|name| name.to_str())
                        .unwrap_or("<unknown>")
                        .to_string(),
                    path,
                    expected,
                    family: family.to_string(),
                    category: "hard-tail".to_string(),
                });
            }
            None if required => {
                return Err(BenchError::InvalidArgs {
                    reason: format!("required hard-tail benchmark matching {needle} not found"),
                });
            }
            None => {}
        }
    }
    if rows.len() < 2 {
        return Err(BenchError::InvalidArgs {
            reason: "built-in hard-tail preset needs at least two available rows".to_string(),
        });
    }
    Ok(rows)
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

fn normalize_expected(value: &str) -> String {
    let expected = value.trim().to_ascii_lowercase();
    if matches!(expected.as_str(), "sat" | "unsat") {
        expected
    } else {
        "unknown".to_string()
    }
}

fn load_root_manifest_if_present(root: &Path) -> Result<Option<Vec<Benchmark>>> {
    let manifest = root.join("manifest.csv");
    if manifest.is_file() {
        load_manifest(&manifest).map(Some)
    } else {
        Ok(None)
    }
}

fn manifest_expected_for_pattern(rows: &[Benchmark], pattern: &str) -> Option<String> {
    rows.iter()
        .find(|row| row.name.contains(pattern))
        .map(|row| row.expected.clone())
}

fn find_named_cnf(root: &Path, needle: &str) -> Result<Option<PathBuf>> {
    let mut plain = Vec::new();
    let mut compressed = Vec::new();
    collect_named_cnf(root, needle, &mut plain, &mut compressed)?;
    plain.sort();
    compressed.sort();
    Ok(plain
        .into_iter()
        .next()
        .or_else(|| compressed.into_iter().next()))
}

fn collect_named_cnf(
    dir: &Path,
    needle: &str,
    plain: &mut Vec<PathBuf>,
    compressed: &mut Vec<PathBuf>,
) -> Result<()> {
    for entry in fs::read_dir(dir).with_bench_context(|| format!("reading {}", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_named_cnf(&path, needle, plain, compressed)?;
            continue;
        }
        let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
            continue;
        };
        if !name.contains(needle) {
            continue;
        }
        if name.ends_with(".cnf") || name.ends_with(".dimacs") {
            plain.push(path);
        } else if name.ends_with(".cnf.xz")
            || name.ends_with(".cnf.gz")
            || name.ends_with(".cnf.bz2")
        {
            compressed.push(path);
        }
    }
    Ok(())
}

fn run_one(
    solver_name: &str,
    solver_path: &Path,
    kind: SolverKind,
    benchmark: &Benchmark,
    args: &SatDeltaArgs,
    run_root: &Path,
    resources: &crate::resource::PlannedResources,
) -> Result<RunRecord> {
    let case_dir = run_root
        .join(sanitize(solver_name))
        .join(sanitize(&benchmark.name));
    fs::create_dir_all(&case_dir)
        .with_bench_context(|| format!("creating case dir {}", case_dir.display()))?;

    let input = prepare_input(&benchmark.path, &case_dir, resources, args.timeout_sec)?;
    let stdout_path = case_dir.join("stdout.txt");
    let stderr_path = case_dir.join("stderr.txt");
    let proof_path = case_dir.join("proof.out");
    let command_path = case_dir.join("command.argv");

    let mut command = resources.external_command(solver_path);
    match kind {
        SolverKind::AY => {
            for (key, value) in &args.ay_env {
                command.env(key.as_str(), value.as_str());
            }
            command.arg("solve");
            if resources.plan.memlimit_mb_per_child > 0 {
                command
                    .arg("--memory")
                    .arg(resources.plan.memlimit_mb_per_child.to_string());
            }
            command
                .arg("--stats-json")
                .arg(format!(
                    "--timeout={}",
                    (args.timeout_sec * 1000.0).round() as u64
                ))
                .arg("--sat-variant")
                .arg(&args.sat_variant)
                .arg("--proof")
                .arg(&proof_path)
                .arg("--proof-format")
                .arg(&args.proof_format)
                .arg("--no-verify-proof")
                .arg(&input);
        }
        SolverKind::Reference => {
            command.arg(&input);
        }
    }
    command.env("MEMLIMIT", resources.plan.memlimit_mb_per_child.to_string());
    command.env("NBCORE", resources.plan.nbcore_per_child.to_string());
    let command_argv = collect_command_argv(solver_path, &command);
    write_command_file(&command_path, &command_argv)?;
    let command_sha256 = sha256_file(&command_path)?;

    let stdout_file = File::create(&stdout_path)
        .with_bench_context(|| format!("creating {}", stdout_path.display()))?;
    let stderr_file = File::create(&stderr_path)
        .with_bench_context(|| format!("creating {}", stderr_path.display()))?;
    command.stdout(Stdio::piped());
    command.stderr(Stdio::piped());
    let start = Instant::now();
    let (mut child, watchdog) = resources
        .spawn_external_child(&mut command, "ay bench sat-delta")
        .with_bench_context(|| format!("spawning solver {}", solver_path.display()))?;
    let Some(stdout_pipe) = child.stdout.take() else {
        crate::resource::terminate_guarded_child(&mut child, watchdog, "ay bench sat-delta")?;
        return Err(BenchError::msg("sat-delta solver stdout pipe missing"));
    };
    let Some(stderr_pipe) = child.stderr.take() else {
        crate::resource::terminate_guarded_child(&mut child, watchdog, "ay bench sat-delta")?;
        return Err(BenchError::msg("sat-delta solver stderr pipe missing"));
    };
    let stdout_capture = crate::resource::BoundedFileCapture::start(stdout_pipe, stdout_file);
    let stderr_capture = crate::resource::BoundedFileCapture::start(stderr_pipe, stderr_file);
    let wait_timeout = wait_timeout_for_solver(kind, args.timeout_sec);
    let outcome = crate::resource::wait_for_guarded_child(
        &mut child,
        watchdog,
        wait_timeout,
        "ay bench sat-delta",
    )?;
    let externally_timed_out = outcome.timed_out;
    let status = outcome.status;
    let memout = outcome.memout;
    let stdout_output = stdout_capture.finish()?;
    let stderr_output = stderr_capture.finish()?;
    let elapsed = start.elapsed();
    let timed_out = !memout
        && (externally_timed_out
            || ay_elapsed_exceeded_time_budget(kind, elapsed, args.timeout_sec));
    let elapsed_s = round3(elapsed.as_secs_f64());
    let exit_code = status.as_ref().and_then(ExitStatus::code);

    let stdout_text = stdout_output.text;
    let stderr_text = stderr_output.text;
    let output_incomplete = stdout_output.incomplete || stderr_output.incomplete;
    let (stats, bcp_relocation, bcp_search_inplace_watch_scan, dense_mutex_focused_restart_gate) =
        capture_run_stats(kind, &stderr_text, &case_dir)?;
    let actual = if memout {
        "memout".to_string()
    } else if timed_out {
        "timeout".to_string()
    } else if output_incomplete {
        "error".to_string()
    } else {
        parse_sat_status(&stdout_text)
            .or_else(|| parse_sat_status(&stderr_text))
            .unwrap_or_else(|| "unknown".to_string())
    };
    let mut invalid = output_incomplete
        || (!timed_out && actual == "unknown" && !mentions_unknown(&stdout_text, &stderr_text));
    let validation = validate_row(
        kind,
        &actual,
        timed_out,
        &input,
        &stdout_text,
        &proof_path,
        args,
        &case_dir,
        Some(resources),
    )?;
    invalid |= validation.invalid;
    let wrong = is_wrong(&benchmark.expected, &actual);
    let solved = is_definitive(&actual) && !wrong && !invalid;
    let par2_s = if solved {
        elapsed_s
    } else {
        round3(2.0 * args.timeout_sec)
    };
    let binary = binary_provenance(solver_path, kind, resources);

    Ok(RunRecord {
        solver: solver_name.to_string(),
        instance: benchmark.name.clone(),
        path: benchmark.path.display().to_string(),
        expected: benchmark.expected.clone(),
        actual,
        family: benchmark.family.clone(),
        category: benchmark.category.clone(),
        elapsed_s,
        par2_s,
        exit_code,
        wrong,
        invalid,
        proof_status: validation.proof_status,
        model_status: validation.model_status,
        timeout: timed_out,
        binary_path: binary.path,
        binary_sha256: binary.sha256,
        binary_size_bytes: binary.size_bytes,
        binary_mtime_epoch: binary.mtime_epoch,
        command_path: command_path.display().to_string(),
        command_sha256,
        command_display: display_command(&command_argv),
        command_argv,
        ay_env: if matches!(kind, SolverKind::AY) {
            env_display_list(&args.ay_env)
        } else {
            Vec::new()
        },
        stats,
        bcp_relocation,
        bcp_search_inplace_watch_scan,
        dense_mutex_focused_restart_gate,
        proof_path: proof_path.display().to_string(),
        proof_checker_command_path: validation.proof_checker_command_path,
        proof_checker_command_sha256: validation.proof_checker_command_sha256,
        proof_checker_exit_code: validation.proof_checker_exit_code,
        proof_checker_stdout: validation.proof_checker_stdout,
        proof_checker_stderr: validation.proof_checker_stderr,
        stdout: stdout_path.display().to_string(),
        stderr: stderr_path.display().to_string(),
    })
}

fn ay_timeout_cleanup_grace_sec(timeout_sec: f64) -> f64 {
    (1.0 + timeout_sec * 0.05).min(AY_TIMEOUT_CLEANUP_GRACE_MAX_SEC)
}

fn wait_timeout_for_solver(kind: SolverKind, timeout_sec: f64) -> std::time::Duration {
    let extra_sec = match kind {
        SolverKind::AY => ay_timeout_cleanup_grace_sec(timeout_sec),
        SolverKind::Reference => 0.0,
    };
    std::time::Duration::from_secs_f64(timeout_sec + extra_sec)
}

fn ay_elapsed_exceeded_time_budget(
    kind: SolverKind,
    elapsed: std::time::Duration,
    timeout_sec: f64,
) -> bool {
    matches!(kind, SolverKind::AY) && elapsed.as_secs_f64() > timeout_sec
}

fn prepare_input(
    path: &Path,
    case_dir: &Path,
    resources: &crate::resource::PlannedResources,
    timeout_sec: f64,
) -> Result<PathBuf> {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return Err(BenchError::InvalidArgs {
            reason: format!("benchmark path has no filename: {}", path.display()),
        });
    };
    if name.ends_with(".xz") || name.ends_with(".gz") || name.ends_with(".bz2") {
        let output_name = name
            .trim_end_matches(".xz")
            .trim_end_matches(".gz")
            .trim_end_matches(".bz2");
        let output = case_dir.join(output_name);
        let tool = if name.ends_with(".xz") {
            "xz"
        } else if name.ends_with(".gz") {
            "gzip"
        } else {
            "bzip2"
        };
        let output_file = File::create(&output)
            .with_bench_context(|| format!("creating decompressed input {}", output.display()))?;
        let mut command = resources.external_command(tool);
        command
            .arg("-dc")
            .arg(path)
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .stdin(Stdio::null())
            .env("MEMLIMIT", resources.plan.memlimit_mb_per_child.to_string())
            .env("NBCORE", resources.plan.nbcore_per_child.to_string());
        let (mut child, watchdog) = resources
            .spawn_external_child(&mut command, "ay bench sat-delta decompress")
            .with_bench_context(|| format!("decompressing {}", path.display()))?;
        let Some(stdout_pipe) = child.stdout.take() else {
            crate::resource::terminate_guarded_child(
                &mut child,
                watchdog,
                "ay bench sat-delta decompress",
            )?;
            fs::remove_file(&output)
                .with_bench_context(|| format!("removing {}", output.display()))?;
            return Err(BenchError::msg(
                "sat-delta decompressor stdout pipe missing",
            ));
        };
        let capture = crate::resource::LimitedFileCapture::start(
            stdout_pipe,
            output_file,
            crate::resource::MAX_DECOMPRESSED_BYTES,
        );
        let capture_breach = capture.breach_flag();
        let outcome = crate::resource::wait_for_guarded_child_with_limits(
            &mut child,
            watchdog,
            std::time::Duration::from_secs_f64(timeout_sec),
            "ay bench sat-delta decompress",
            None,
            Some(capture_breach.as_ref()),
        );
        let capture = capture.finish();
        let outcome = match outcome {
            Ok(outcome) => outcome,
            Err(error) => {
                let _ = fs::remove_file(&output);
                return Err(error);
            }
        };
        let capture = match capture {
            Ok(capture) => capture,
            Err(error) => {
                let _ = fs::remove_file(&output);
                return Err(error);
            }
        };
        if capture.exceeded {
            let _ = fs::remove_file(&output);
            return Err(BenchError::msg(format!(
                "decompressed input {} exceeded the fixed {}-byte cap",
                path.display(),
                crate::resource::MAX_DECOMPRESSED_BYTES
            )));
        }
        if capture.write_failed {
            let _ = fs::remove_file(&output);
            return Err(BenchError::msg(format!(
                "writing decompressed input {} failed",
                output.display()
            )));
        }
        if outcome.memout
            || outcome.timed_out
            || outcome
                .status
                .as_ref()
                .is_none_or(|status| !status.success())
        {
            let _ = fs::remove_file(&output);
            return Err(BenchError::UnsupportedFormat {
                path: path.to_path_buf(),
            });
        }
        Ok(output)
    } else {
        Ok(path.to_path_buf())
    }
}

fn collect_command_argv(program: &Path, command: &Command) -> Vec<String> {
    let args = command.get_args().collect::<Vec<_>>();
    let solver_args = args
        .iter()
        .position(|arg| *arg == program.as_os_str())
        .map_or(args.as_slice(), |index| &args[index + 1..]);
    std::iter::once(program.display().to_string())
        .chain(
            solver_args
                .iter()
                .map(|arg| arg.to_string_lossy().to_string()),
        )
        .collect()
}

fn write_command_file(path: &Path, argv: &[String]) -> Result<()> {
    let mut file =
        File::create(path).with_bench_context(|| format!("creating {}", path.display()))?;
    for arg in argv {
        writeln!(file, "{arg}")?;
    }
    Ok(())
}

fn display_command(argv: &[String]) -> String {
    argv.iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(arg: &str) -> String {
    if !arg.is_empty()
        && arg.bytes().all(|b| {
            b.is_ascii_alphanumeric()
                || matches!(
                    b,
                    b'@' | b'%' | b'_' | b'+' | b'=' | b':' | b',' | b'.' | b'/' | b'-'
                )
        })
    {
        arg.to_string()
    } else {
        format!("'{}'", arg.replace('\'', "'\\''"))
    }
}

fn env_display_list(env: &[(String, String)]) -> Vec<String> {
    env.iter()
        .map(|(key, value)| format!("{key}={value}"))
        .collect()
}

fn capture_run_stats(
    kind: SolverKind,
    stderr: &str,
    case_dir: &Path,
) -> Result<(
    StatsCapture,
    BcpRelocationStats,
    BcpSearchInplaceWatchScanStats,
    DenseMutexFocusedRestartGateStats,
)> {
    if !matches!(kind, SolverKind::AY) {
        return Ok((
            StatsCapture::not_applicable(),
            BcpRelocationStats::none(),
            BcpSearchInplaceWatchScanStats::none(),
            DenseMutexFocusedRestartGateStats::none(),
        ));
    }

    let stats_path = case_dir.join("stats.json");
    let parsed = match extract_stats_json(stderr) {
        StatsJsonCapture::Captured(value, raw_line) => (value, raw_line),
        StatsJsonCapture::Missing => {
            return Ok((
                StatsCapture::missing("missing"),
                BcpRelocationStats::none(),
                BcpSearchInplaceWatchScanStats::none(),
                DenseMutexFocusedRestartGateStats::none(),
            ));
        }
        StatsJsonCapture::ParseError => {
            return Ok((
                StatsCapture::missing("parse-error"),
                BcpRelocationStats::none(),
                BcpSearchInplaceWatchScanStats::none(),
                DenseMutexFocusedRestartGateStats::none(),
            ));
        }
        StatsJsonCapture::InvalidShape => {
            return Ok((
                StatsCapture::missing("invalid-shape"),
                BcpRelocationStats::none(),
                BcpSearchInplaceWatchScanStats::none(),
                DenseMutexFocusedRestartGateStats::none(),
            ));
        }
    };

    let (value, raw_line) = parsed;
    fs::write(&stats_path, format!("{raw_line}\n"))
        .with_bench_context(|| format!("writing stats JSON {}", stats_path.display()))?;
    let stats = StatsCapture {
        path: stats_path.display().to_string(),
        sha256: sha256_file(&stats_path)?,
        status: "captured".to_string(),
        mode: stats_json_str(&value, "mode").unwrap_or_default(),
        result: stats_json_str(&value, "result").unwrap_or_default(),
        wall_time_ms: stats_json_u64(&value, "wall_time_ms"),
    };
    let bcp_relocation = parse_bcp_relocation_stats(&value);
    let bcp_search_inplace_watch_scan = parse_bcp_search_inplace_watch_scan_stats(&value);
    let dense_mutex_focused_restart_gate = parse_dense_mutex_focused_restart_gate_stats(&value);
    Ok((
        stats,
        bcp_relocation,
        bcp_search_inplace_watch_scan,
        dense_mutex_focused_restart_gate,
    ))
}

enum StatsJsonCapture {
    Captured(serde_json::Value, String),
    Missing,
    ParseError,
    InvalidShape,
}

fn extract_stats_json(stderr: &str) -> StatsJsonCapture {
    for line in stderr.lines() {
        let trimmed = line.trim();
        if !trimmed.starts_with('{') {
            continue;
        }
        let Ok(value) = serde_json::from_str::<serde_json::Value>(trimmed) else {
            return StatsJsonCapture::ParseError;
        };
        let Some(object) = value.as_object() else {
            return StatsJsonCapture::InvalidShape;
        };
        if object.contains_key("mode")
            && object.contains_key("result")
            && object.contains_key("wall_time_ms")
        {
            return StatsJsonCapture::Captured(value, trimmed.to_string());
        }
        return StatsJsonCapture::InvalidShape;
    }
    StatsJsonCapture::Missing
}

fn stats_json_str(value: &serde_json::Value, key: &str) -> Option<String> {
    value.get(key)?.as_str().map(str::to_string)
}

fn stats_json_u64(value: &serde_json::Value, key: &str) -> Option<u64> {
    value.get(key)?.as_u64()
}

fn stats_json_bool(value: &serde_json::Value, key: &str) -> Option<bool> {
    match value.get(key)? {
        serde_json::Value::Bool(value) => Some(*value),
        serde_json::Value::Number(value) => value.as_u64().map(|value| value != 0),
        _ => None,
    }
}

fn parse_bcp_relocation_stats(value: &serde_json::Value) -> BcpRelocationStats {
    let enabled = stats_json_bool(value, BCP_RELOCATION_ENABLED_KEY);
    let attempts = stats_json_u64(value, BCP_RELOCATION_ATTEMPTS_KEY);
    let moves = stats_json_u64(value, BCP_RELOCATION_MOVES_KEY);
    let exercised =
        enabled.unwrap_or(false) && (attempts.unwrap_or(0) > 0 || moves.unwrap_or(0) > 0);
    BcpRelocationStats {
        enabled,
        attempts,
        moves,
        exercised,
    }
}

fn parse_bcp_search_inplace_watch_scan_stats(
    value: &serde_json::Value,
) -> BcpSearchInplaceWatchScanStats {
    let requested = stats_json_bool(value, BCP_SEARCH_INPLACE_WATCH_SCAN_REQUESTED_KEY);
    let enabled = stats_json_bool(value, BCP_SEARCH_INPLACE_WATCH_SCAN_ENABLED_KEY);
    let exercised =
        stats_json_bool(value, BCP_SEARCH_INPLACE_WATCH_SCAN_EXERCISED_KEY).unwrap_or(false);
    BcpSearchInplaceWatchScanStats {
        requested,
        enabled,
        exercised,
    }
}

fn parse_dense_mutex_focused_restart_gate_stats(
    value: &serde_json::Value,
) -> DenseMutexFocusedRestartGateStats {
    let requested = stats_json_bool(value, DENSE_MUTEX_FOCUSED_RESTART_GATE_REQUESTED_KEY);
    let enabled = stats_json_bool(value, DENSE_MUTEX_FOCUSED_RESTART_GATE_ENABLED_KEY);
    let focused_gate_final = stats_json_u64(value, FOCUSED_RESTART_GATE_FINAL_KEY);
    let updates = stats_json_u64(value, DENSE_MUTEX_FOCUSED_RESTART_GATE_UPDATES_KEY);
    let runtime_checked = stats_json_u64(value, DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CHECKED_KEY);
    let active_vars = stats_json_u64(value, DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_VARS_KEY);
    let active_clauses = stats_json_u64(value, DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_CLAUSES_KEY);
    let active_binary_clauses =
        stats_json_u64(value, DENSE_MUTEX_FOCUSED_RESTART_ACTIVE_BINARY_CLAUSES_KEY);
    let runtime_candidate =
        stats_json_bool(value, DENSE_MUTEX_FOCUSED_RESTART_RUNTIME_CANDIDATE_KEY);
    let previous_gate = stats_json_u64(value, DENSE_MUTEX_FOCUSED_RESTART_PREVIOUS_GATE_KEY);
    let computed_gate = stats_json_u64(value, DENSE_MUTEX_FOCUSED_RESTART_COMPUTED_GATE_KEY);
    let exercised =
        requested.unwrap_or(false) && enabled.unwrap_or(false) && updates.unwrap_or(0) > 0;
    DenseMutexFocusedRestartGateStats {
        requested,
        enabled,
        focused_gate_final,
        updates,
        runtime_checked,
        active_vars,
        active_clauses,
        active_binary_clauses,
        runtime_candidate,
        previous_gate,
        computed_gate,
        exercised,
    }
}

fn parse_sat_status(text: &str) -> Option<String> {
    for line in text.lines() {
        match line.trim() {
            "s SATISFIABLE" => return Some("sat".to_string()),
            "s UNSATISFIABLE" => return Some("unsat".to_string()),
            "s UNKNOWN" => return Some("unknown".to_string()),
            _ => {}
        }
    }
    None
}

fn mentions_unknown(stdout: &str, stderr: &str) -> bool {
    stdout
        .lines()
        .chain(stderr.lines())
        .any(|line| line.trim() == "s UNKNOWN")
}

#[allow(clippy::too_many_arguments)]
fn validate_row(
    kind: SolverKind,
    actual: &str,
    timed_out: bool,
    cnf_path: &Path,
    stdout: &str,
    proof_path: &Path,
    args: &SatDeltaArgs,
    case_dir: &Path,
    resources: Option<&crate::resource::PlannedResources>,
) -> Result<RowValidation> {
    if !matches!(kind, SolverKind::AY) || timed_out || actual == "memout" {
        return Ok(RowValidation::not_applicable());
    }

    let mut validation = RowValidation::not_applicable();
    match actual {
        "sat" => {
            validation.model_status = verify_sat_model(cnf_path, stdout);
            validation.invalid = validation.model_status != "valid";
            if proof_file_nonempty(proof_path) {
                validation.proof_status = "unexpected".to_string();
                validation.invalid = true;
            }
        }
        "unsat" => {
            if solver_output_has_model_lines(stdout) {
                validation.model_status = "unexpected".to_string();
                validation.invalid = true;
            }
            let proof = verify_unsat_proof(cnf_path, proof_path, args, case_dir, resources)?;
            validation.proof_status = proof.proof_status;
            validation.proof_checker_command_path = proof.proof_checker_command_path;
            validation.proof_checker_command_sha256 = proof.proof_checker_command_sha256;
            validation.proof_checker_exit_code = proof.proof_checker_exit_code;
            validation.proof_checker_stdout = proof.proof_checker_stdout;
            validation.proof_checker_stderr = proof.proof_checker_stderr;
            validation.invalid |= validation.proof_status != "valid";
        }
        _ => {
            if solver_output_has_model_lines(stdout) {
                validation.model_status = "unexpected".to_string();
                validation.invalid = true;
            }
            if proof_file_nonempty(proof_path) {
                validation.proof_status = "unexpected".to_string();
                validation.invalid = true;
            }
        }
    }
    Ok(validation)
}

fn solver_output_has_model_lines(stdout: &str) -> bool {
    stdout.lines().any(|line| line.starts_with('v'))
}

const MAX_PARENT_DIMACS_VALIDATION_BYTES: u64 = 512 * 1024 * 1024;
const MAX_DIMACS_LINE_BYTES: usize = 1024 * 1024;

/// Check a model against DIMACS in one pass. Only one bounded line is retained,
/// rather than a `String` plus a second in-memory copy of every clause.
fn stream_validate_dimacs_model(
    path: &Path,
    assignment: &BTreeMap<usize, bool>,
) -> std::result::Result<bool, String> {
    use std::io::BufRead as _;

    let metadata = fs::metadata(path).map_err(|error| error.to_string())?;
    if metadata.len() > MAX_PARENT_DIMACS_VALIDATION_BYTES {
        return Err(format!(
            "cnf-too-large-for-parent-validation:{}>{}",
            metadata.len(),
            MAX_PARENT_DIMACS_VALIDATION_BYTES
        ));
    }
    let file = File::open(path).map_err(|error| error.to_string())?;
    let mut reader = std::io::BufReader::with_capacity(64 * 1024, file);
    let mut line = String::new();
    let mut line_no = 0_usize;
    let mut num_vars = None;
    let mut clause_satisfied = false;
    let mut clause_has_literal = false;
    loop {
        line.clear();
        let read = reader
            .read_line(&mut line)
            .map_err(|error| error.to_string())?;
        if read == 0 {
            break;
        }
        line_no += 1;
        if read > MAX_DIMACS_LINE_BYTES {
            return Err(format!("cnf-line-too-long:{line_no}"));
        }
        let stripped = line.trim();
        if stripped.is_empty() || stripped.starts_with('c') {
            continue;
        }
        if stripped.starts_with('p') {
            let mut parts = stripped.split_whitespace();
            if parts.next() != Some("p") || parts.next() != Some("cnf") {
                return Err(format!("malformed-cnf-header:{line_no}"));
            }
            num_vars = parts.next().and_then(|token| token.parse::<usize>().ok());
            if num_vars.is_none() {
                return Err(format!("malformed-cnf-header:{line_no}"));
            }
            continue;
        }
        if stripped.starts_with('%') {
            break;
        }
        for token in stripped.split_whitespace() {
            let lit = token
                .parse::<i64>()
                .map_err(|_| format!("malformed-cnf-token:{line_no}"))?;
            if lit == 0 {
                if !clause_satisfied {
                    return Ok(false);
                }
                clause_satisfied = false;
                clause_has_literal = false;
                continue;
            }
            clause_has_literal = true;
            let abs_lit = lit
                .checked_abs()
                .ok_or_else(|| format!("malformed-cnf-token:{line_no}"))?;
            let var =
                usize::try_from(abs_lit).map_err(|_| format!("malformed-cnf-token:{line_no}"))?;
            if num_vars.is_some_and(|limit| var > limit) {
                return Err(format!("cnf-variable-out-of-range:{line_no}"));
            }
            clause_satisfied |= assignment.get(&var).copied() == Some(lit > 0);
        }
    }
    if clause_has_literal && !clause_satisfied {
        return Ok(false);
    }
    if let Some(limit) = num_vars {
        if assignment.keys().any(|variable| *variable > limit) {
            return Ok(false);
        }
    }
    Ok(true)
}

fn verify_sat_model(cnf_path: &Path, stdout: &str) -> String {
    let mut assignment = BTreeMap::new();
    let mut saw_model_line = false;
    let mut saw_terminator = false;

    for (line_index, line) in stdout.lines().enumerate() {
        let line_no = line_index + 1;
        if !line.starts_with('v') {
            continue;
        }
        saw_model_line = true;
        if line != "v" && !line.starts_with("v ") {
            return format!("malformed:{line_no}");
        }
        let tokens = line[1..].split_whitespace().collect::<Vec<_>>();
        if tokens.is_empty() {
            return format!("malformed:{line_no}");
        }
        if saw_terminator {
            for token in tokens {
                let Ok(lit) = token.parse::<i64>() else {
                    return format!("malformed:{line_no}");
                };
                if lit == 0 {
                    return format!("duplicate-terminator:{line_no}");
                }
            }
            return format!("malformed:{line_no}");
        }
        for (token_index, token) in tokens.iter().enumerate() {
            let Ok(lit) = token.parse::<i64>() else {
                return format!("malformed:{line_no}");
            };
            if lit == 0 {
                if token_index != tokens.len() - 1 {
                    for trailing in &tokens[token_index + 1..] {
                        let Ok(trailing_lit) = trailing.parse::<i64>() else {
                            return format!("malformed:{line_no}");
                        };
                        if trailing_lit == 0 {
                            return format!("duplicate-terminator:{line_no}");
                        }
                    }
                    return format!("malformed:{line_no}");
                }
                saw_terminator = true;
                break;
            }
            let Some(abs_lit) = lit.checked_abs() else {
                return format!("malformed:{line_no}");
            };
            let Ok(var) = usize::try_from(abs_lit) else {
                return "invalid".to_string();
            };
            let value = lit > 0;
            if let Some(previous) = assignment.insert(var, value) {
                if previous != value {
                    return "contradictory".to_string();
                }
                return format!("duplicate-assignment:{line_no}");
            }
        }
    }

    if !saw_model_line || assignment.is_empty() {
        return "missing".to_string();
    }
    if !saw_terminator {
        return "unterminated".to_string();
    }
    match stream_validate_dimacs_model(cnf_path, &assignment) {
        Ok(true) => "valid".to_string(),
        Ok(false) => "invalid".to_string(),
        Err(error) => format!("error:{error}"),
    }
}

fn proof_file_nonempty(path: &Path) -> bool {
    fs::metadata(path)
        .ok()
        .is_some_and(|meta| meta.is_file() && meta.len() > 0)
}

fn proof_checker_output_is_verified(stdout: &str, stderr: &str) -> bool {
    let lines = stdout.lines().collect::<Vec<_>>();
    lines.len() == 1
        && VERIFIED_PROOF_LINES.contains(&lines[0])
        && proof_checker_stderr_is_comment_only(stderr)
}

fn proof_checker_stderr_is_comment_only(stderr: &str) -> bool {
    stderr
        .lines()
        .all(|line| line.is_empty() || line == "c" || line.starts_with("c "))
}

fn verify_unsat_proof(
    cnf_path: &Path,
    proof_path: &Path,
    args: &SatDeltaArgs,
    case_dir: &Path,
    resources: Option<&crate::resource::PlannedResources>,
) -> Result<RowValidation> {
    let mut validation = RowValidation::not_applicable();
    if !proof_path.exists() {
        validation.proof_status = "missing".to_string();
        return Ok(validation);
    }
    if fs::metadata(proof_path)
        .map(|meta| !meta.is_file() || meta.len() == 0)
        .unwrap_or(true)
    {
        validation.proof_status = "empty".to_string();
        return Ok(validation);
    }
    let Some(checker) = args.proof_checker.as_ref() else {
        validation.proof_status = "unchecked".to_string();
        return Ok(validation);
    };
    if !checker.is_file() {
        validation.proof_status = "checker-missing".to_string();
        return Ok(validation);
    }
    let Some(resources) = resources else {
        validation.proof_status = "resource-plan-missing".to_string();
        return Ok(validation);
    };

    let stdout_path = case_dir.join("proof-checker.stdout.txt");
    let stderr_path = case_dir.join("proof-checker.stderr.txt");
    let command_path = case_dir.join("proof-checker.argv");
    let command_argv = proof_checker_argv(checker, &args.proof_format, cnf_path, proof_path);
    write_command_file(&command_path, &command_argv)?;
    validation.proof_checker_command_path = command_path.display().to_string();
    validation.proof_checker_command_sha256 = sha256_file(&command_path)?;
    validation.proof_checker_stdout = stdout_path.display().to_string();
    validation.proof_checker_stderr = stderr_path.display().to_string();

    let stdout_file = File::create(&stdout_path)
        .with_bench_context(|| format!("creating {}", stdout_path.display()))?;
    let stderr_file = File::create(&stderr_path)
        .with_bench_context(|| format!("creating {}", stderr_path.display()))?;
    let mut command = resources.external_command(checker);
    for arg in command_argv.iter().skip(1) {
        command.arg(arg);
    }
    command.stdout(Stdio::piped());
    command.stderr(Stdio::piped());
    command.env("MEMLIMIT", resources.plan.memlimit_mb_per_child.to_string());
    command.env("NBCORE", resources.plan.nbcore_per_child.to_string());
    match resources.spawn_external_child(&mut command, "ay bench sat-delta proof checker") {
        Ok((mut child, watchdog)) => {
            let Some(stdout_pipe) = child.stdout.take() else {
                crate::resource::terminate_guarded_child(
                    &mut child,
                    watchdog,
                    "ay bench sat-delta proof checker",
                )?;
                validation.proof_status = "checker-capture-error".to_string();
                return Ok(validation);
            };
            let Some(stderr_pipe) = child.stderr.take() else {
                crate::resource::terminate_guarded_child(
                    &mut child,
                    watchdog,
                    "ay bench sat-delta proof checker",
                )?;
                validation.proof_status = "checker-capture-error".to_string();
                return Ok(validation);
            };
            let stdout_capture =
                crate::resource::BoundedFileCapture::start(stdout_pipe, stdout_file);
            let stderr_capture =
                crate::resource::BoundedFileCapture::start(stderr_pipe, stderr_file);
            let timeout = std::time::Duration::from_secs_f64(args.timeout_sec.max(1.0));
            let outcome = crate::resource::wait_for_guarded_child(
                &mut child,
                watchdog,
                timeout,
                "ay bench sat-delta proof checker",
            )?;
            let stdout_output = stdout_capture.finish()?;
            let stderr_output = stderr_capture.finish()?;
            validation.proof_checker_exit_code = outcome.status.as_ref().and_then(ExitStatus::code);
            if outcome.memout {
                validation.proof_status = "memout".to_string();
                return Ok(validation);
            }
            if outcome.timed_out {
                validation.proof_status = "timeout".to_string();
                return Ok(validation);
            }
            if stdout_output.incomplete || stderr_output.incomplete {
                validation.proof_status = "checker-output-truncated".to_string();
                return Ok(validation);
            }
            validation.proof_status = if validation.proof_checker_exit_code == Some(0)
                && proof_checker_output_is_verified(&stdout_output.text, &stderr_output.text)
            {
                "valid".to_string()
            } else {
                "invalid".to_string()
            };
            Ok(validation)
        }
        Err(err) => {
            fs::write(&stderr_path, err.to_string())
                .with_bench_context(|| format!("writing {}", stderr_path.display()))?;
            validation.proof_status = "checker-spawn-error".to_string();
            Ok(validation)
        }
    }
}

fn proof_checker_argv(
    checker: &Path,
    proof_format: &str,
    cnf_path: &Path,
    proof_path: &Path,
) -> Vec<String> {
    if checker.file_name().and_then(|name| name.to_str()) == Some("ay") {
        vec![
            checker.display().to_string(),
            "check".to_string(),
            proof_format.to_string(),
            cnf_path.display().to_string(),
            proof_path.display().to_string(),
        ]
    } else {
        vec![
            checker.display().to_string(),
            cnf_path.display().to_string(),
            proof_path.display().to_string(),
        ]
    }
}

fn is_definitive(actual: &str) -> bool {
    actual == "sat" || actual == "unsat"
}

fn is_wrong(expected: &str, actual: &str) -> bool {
    matches!(expected, "sat" | "unsat") && is_definitive(actual) && expected != actual
}

fn env_value_truthy(value: &str) -> bool {
    let value = value.trim();
    value == "1"
        || value.eq_ignore_ascii_case("true")
        || value.eq_ignore_ascii_case("yes")
        || value.eq_ignore_ascii_case("on")
}

fn bcp_relocation_requested(args: &SatDeltaArgs) -> bool {
    args.ay_env
        .iter()
        .any(|(key, value)| key == BCP_RELOCATION_ENV && env_value_truthy(value))
}

fn bcp_search_inplace_watch_scan_requested(args: &SatDeltaArgs) -> bool {
    args.ay_env
        .iter()
        .any(|(key, value)| key == BCP_SEARCH_INPLACE_WATCH_SCAN_ENV && env_value_truthy(value))
}

fn dense_mutex_focused_restart_gate_requested(args: &SatDeltaArgs) -> bool {
    args.ay_env
        .iter()
        .any(|(key, value)| key == DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV && env_value_truthy(value))
}

fn bcp_relocation_gate_failure(records: &[RunRecord], args: &SatDeltaArgs) -> Option<String> {
    if !args.require_bcp_relocation_exercise {
        return None;
    }
    if !bcp_relocation_requested(args) {
        return Some(format!(
            "--require-bcp-relocation-exercise requires truthy --ay-env {BCP_RELOCATION_ENV}=1"
        ));
    }

    let ay_rows = records
        .iter()
        .filter(|record| record.solver == "ay")
        .collect::<Vec<_>>();
    if ay_rows.is_empty() {
        return Some("BCP relocation exercise required but no AY rows were run".to_string());
    }

    let failures = ay_rows
        .iter()
        .filter(|record| {
            record.stats.status != "captured"
                || record.bcp_relocation.enabled != Some(true)
                || !record.bcp_relocation.exercised
        })
        .map(|record| {
            format!(
                "{} stats={} enabled={} attempts={} moves={}",
                record.instance,
                record.stats.status,
                display_optional_bool(record.bcp_relocation.enabled),
                display_optional_u64(record.bcp_relocation.attempts),
                display_optional_u64(record.bcp_relocation.moves)
            )
        })
        .collect::<Vec<_>>();

    if failures.is_empty() {
        return None;
    }

    let examples = failures
        .iter()
        .take(5)
        .cloned()
        .collect::<Vec<_>>()
        .join("; ");
    let suffix = if failures.len() > 5 {
        format!("; ... {} more", failures.len() - 5)
    } else {
        String::new()
    };
    Some(format!(
        "BCP relocation exercise required but {} of {} AY rows did not exercise {BCP_RELOCATION_ENV}; {examples}{suffix}",
        failures.len(),
        ay_rows.len()
    ))
}

fn bcp_search_inplace_watch_scan_gate_failure(
    records: &[RunRecord],
    args: &SatDeltaArgs,
) -> Option<String> {
    if !args.require_bcp_search_inplace_watch_scan_exercise {
        return None;
    }
    if !bcp_search_inplace_watch_scan_requested(args) {
        return Some(format!(
            "--require-bcp-search-inplace-watch-scan-exercise requires truthy --ay-env {BCP_SEARCH_INPLACE_WATCH_SCAN_ENV}=1"
        ));
    }

    let ay_rows = records
        .iter()
        .filter(|record| record.solver == "ay")
        .collect::<Vec<_>>();
    if ay_rows.is_empty() {
        return Some(
            "BCP SEARCH in-place watch scan exercise required but no AY rows were run".to_string(),
        );
    }

    let failures = ay_rows
        .iter()
        .filter(|record| {
            record.stats.status != "captured"
                || record.bcp_search_inplace_watch_scan.requested != Some(true)
                || record.bcp_search_inplace_watch_scan.enabled != Some(true)
                || !record.bcp_search_inplace_watch_scan.exercised
        })
        .map(|record| {
            format!(
                "{} stats={} requested={} enabled={} exercised={}",
                record.instance,
                record.stats.status,
                display_optional_bool(record.bcp_search_inplace_watch_scan.requested),
                display_optional_bool(record.bcp_search_inplace_watch_scan.enabled),
                u8::from(record.bcp_search_inplace_watch_scan.exercised)
            )
        })
        .collect::<Vec<_>>();

    if failures.is_empty() {
        return None;
    }

    let examples = failures
        .iter()
        .take(5)
        .cloned()
        .collect::<Vec<_>>()
        .join("; ");
    let suffix = if failures.len() > 5 {
        format!("; ... {} more", failures.len() - 5)
    } else {
        String::new()
    };
    Some(format!(
        "BCP SEARCH in-place watch scan exercise required but {} of {} AY rows did not exercise {BCP_SEARCH_INPLACE_WATCH_SCAN_ENV}; {examples}{suffix}",
        failures.len(),
        ay_rows.len()
    ))
}

fn dense_mutex_focused_restart_gate_failure(
    records: &[RunRecord],
    args: &SatDeltaArgs,
) -> Option<String> {
    if !args.require_dense_mutex_focused_restart_gate_exercise {
        return None;
    }
    if !dense_mutex_focused_restart_gate_requested(args) {
        return Some(format!(
            "--require-dense-mutex-focused-restart-gate-exercise requires truthy --ay-env {DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV}=1"
        ));
    }

    let ay_rows = records
        .iter()
        .filter(|record| record.solver == "ay")
        .collect::<Vec<_>>();
    if ay_rows.is_empty() {
        return Some(
            "dense-mutex focused restart gate exercise required but no AY rows were run"
                .to_string(),
        );
    }

    let failures = ay_rows
        .iter()
        .filter(|record| {
            record.stats.status != "captured"
                || record.dense_mutex_focused_restart_gate.requested != Some(true)
                || record.dense_mutex_focused_restart_gate.enabled != Some(true)
                || !record.dense_mutex_focused_restart_gate.exercised
        })
        .map(|record| {
            format!(
                "{} stats={} requested={} enabled={} final_gate={} updates={} runtime_checked={} runtime_candidate={} active_vars={} active_clauses={} active_binary={} previous_gate={} computed_gate={}",
                record.instance,
                record.stats.status,
                display_optional_bool(record.dense_mutex_focused_restart_gate.requested),
                display_optional_bool(record.dense_mutex_focused_restart_gate.enabled),
                display_optional_u64(record.dense_mutex_focused_restart_gate.focused_gate_final),
                display_optional_u64(record.dense_mutex_focused_restart_gate.updates),
                display_optional_u64(record.dense_mutex_focused_restart_gate.runtime_checked),
                display_optional_bool(record.dense_mutex_focused_restart_gate.runtime_candidate),
                display_optional_u64(record.dense_mutex_focused_restart_gate.active_vars),
                display_optional_u64(record.dense_mutex_focused_restart_gate.active_clauses),
                display_optional_u64(
                    record
                        .dense_mutex_focused_restart_gate
                        .active_binary_clauses,
                ),
                display_optional_u64(record.dense_mutex_focused_restart_gate.previous_gate),
                display_optional_u64(record.dense_mutex_focused_restart_gate.computed_gate)
            )
        })
        .collect::<Vec<_>>();

    if failures.is_empty() {
        return None;
    }

    let examples = failures
        .iter()
        .take(5)
        .cloned()
        .collect::<Vec<_>>()
        .join("; ");
    let suffix = if failures.len() > 5 {
        format!("; ... {} more", failures.len() - 5)
    } else {
        String::new()
    };
    Some(format!(
        "dense-mutex focused restart gate exercise required but {} of {} AY rows did not exercise {DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV}; {examples}{suffix}",
        failures.len(),
        ay_rows.len()
    ))
}

fn summarize_by_solver(records: &[RunRecord]) -> BTreeMap<String, Summary> {
    let mut grouped: BTreeMap<String, Vec<&RunRecord>> = BTreeMap::new();
    for record in records {
        grouped
            .entry(record.solver.clone())
            .or_default()
            .push(record);
    }
    grouped
        .into_iter()
        .map(|(solver, rows)| (solver, summarize_rows(&rows)))
        .collect()
}

fn summarize_rows(rows: &[&RunRecord]) -> Summary {
    let total = rows.len();
    let solved_sat = rows
        .iter()
        .filter(|row| row.actual == "sat" && !row.wrong && !row.invalid)
        .count();
    let solved_unsat = rows
        .iter()
        .filter(|row| row.actual == "unsat" && !row.wrong && !row.invalid)
        .count();
    let solved = solved_sat + solved_unsat;
    let wrong = rows.iter().filter(|row| row.wrong).count();
    let invalid = rows.iter().filter(|row| row.invalid).count();
    let timeout = rows.iter().filter(|row| row.timeout).count();
    let memout = rows.iter().filter(|row| row.actual == "memout").count();
    let unknown = rows.iter().filter(|row| row.actual == "unknown").count();
    let par2_total = round3(rows.iter().map(|row| row.par2_s).sum());
    Summary {
        total,
        solved,
        solved_sat,
        solved_unsat,
        wrong,
        invalid,
        timeout,
        memout,
        unknown,
        par2_total,
        par2_avg: if total == 0 {
            0.0
        } else {
            round3(par2_total / total as f64)
        },
        disqualified: wrong > 0 || invalid > 0,
    }
}

fn reference_deltas(
    records: &[RunRecord],
    summaries: &BTreeMap<String, Summary>,
) -> Vec<ReferenceDelta> {
    let Some(ay_summary) = summaries.get("ay") else {
        return Vec::new();
    };
    let ay_by_instance: BTreeMap<&str, &RunRecord> = records
        .iter()
        .filter(|record| record.solver == "ay")
        .map(|record| (record.instance.as_str(), record))
        .collect();
    let mut deltas = Vec::new();
    for (solver, summary) in summaries {
        if solver == "ay" {
            continue;
        }
        let mut ref_only_solved = 0usize;
        let mut ay_only_solved = 0usize;
        let mut definitive_disagree = 0usize;
        for reference in records.iter().filter(|record| &record.solver == solver) {
            let Some(ay) = ay_by_instance.get(reference.instance.as_str()) else {
                continue;
            };
            let ay_solved = is_definitive(&ay.actual) && !ay.wrong && !ay.invalid;
            let ref_solved =
                is_definitive(&reference.actual) && !reference.wrong && !reference.invalid;
            if ref_solved && !ay_solved {
                ref_only_solved += 1;
            }
            if ay_solved && !ref_solved {
                ay_only_solved += 1;
            }
            if ay_solved && ref_solved && ay.actual != reference.actual {
                definitive_disagree += 1;
            }
        }
        deltas.push(ReferenceDelta {
            reference: solver.clone(),
            ay_solved: ay_summary.solved,
            reference_solved: summary.solved,
            solved_delta: ay_summary.solved as isize - summary.solved as isize,
            ay_par2_total: ay_summary.par2_total,
            reference_par2_total: summary.par2_total,
            par2_delta: round3(ay_summary.par2_total - summary.par2_total),
            ref_only_solved,
            ay_only_solved,
            definitive_disagree,
        });
    }
    deltas
}

fn write_json(path: &Path, report: &SatDeltaReport) -> Result<()> {
    let text = serde_json::to_string_pretty(report)?;
    fs::write(path, text).with_bench_context(|| format!("writing {}", path.display()))
}

fn write_raw_tsv(path: &Path, records: &[RunRecord]) -> Result<()> {
    let mut file =
        File::create(path).with_bench_context(|| format!("creating {}", path.display()))?;
    writeln!(file, "{}", RAW_TSV_COLUMNS.join("\t"))?;
    for row in records {
        writeln!(
            file,
            "{}",
            [
                row.solver.clone(),
                row.instance.clone(),
                row.path.clone(),
                row.expected.clone(),
                row.actual.clone(),
                row.family.clone(),
                row.category.clone(),
                row.elapsed_s.to_string(),
                row.par2_s.to_string(),
                row.exit_code
                    .map_or_else(String::new, |code| code.to_string()),
                u8::from(row.wrong).to_string(),
                u8::from(row.invalid).to_string(),
                row.proof_status.clone(),
                row.model_status.clone(),
                u8::from(row.timeout).to_string(),
                row.binary_path.clone(),
                row.binary_sha256.clone(),
                row.binary_size_bytes
                    .map_or_else(String::new, |size| size.to_string()),
                row.binary_mtime_epoch
                    .map_or_else(String::new, |mtime| mtime.to_string()),
                row.command_path.clone(),
                row.command_sha256.clone(),
                serde_json::to_string(&row.command_argv)?,
                serde_json::to_string(&row.ay_env)?,
                row.stats.path.clone(),
                row.stats.sha256.clone(),
                row.stats.status.clone(),
                row.stats.mode.clone(),
                row.stats.result.clone(),
                row.stats
                    .wall_time_ms
                    .map_or_else(String::new, |value| value.to_string()),
                display_optional_bool(row.bcp_relocation.enabled),
                display_optional_u64(row.bcp_relocation.attempts),
                display_optional_u64(row.bcp_relocation.moves),
                u8::from(row.bcp_relocation.exercised).to_string(),
                display_optional_bool(row.bcp_search_inplace_watch_scan.requested),
                display_optional_bool(row.bcp_search_inplace_watch_scan.enabled),
                u8::from(row.bcp_search_inplace_watch_scan.exercised).to_string(),
                display_optional_bool(row.dense_mutex_focused_restart_gate.requested),
                display_optional_bool(row.dense_mutex_focused_restart_gate.enabled),
                display_optional_u64(row.dense_mutex_focused_restart_gate.focused_gate_final),
                display_optional_u64(row.dense_mutex_focused_restart_gate.updates),
                display_optional_u64(row.dense_mutex_focused_restart_gate.runtime_checked),
                display_optional_u64(row.dense_mutex_focused_restart_gate.active_vars),
                display_optional_u64(row.dense_mutex_focused_restart_gate.active_clauses),
                display_optional_u64(row.dense_mutex_focused_restart_gate.active_binary_clauses,),
                display_optional_bool(row.dense_mutex_focused_restart_gate.runtime_candidate),
                display_optional_u64(row.dense_mutex_focused_restart_gate.previous_gate),
                display_optional_u64(row.dense_mutex_focused_restart_gate.computed_gate),
                u8::from(row.dense_mutex_focused_restart_gate.exercised).to_string(),
                row.proof_path.clone(),
                row.proof_checker_command_path.clone(),
                row.proof_checker_command_sha256.clone(),
                row.proof_checker_exit_code
                    .map_or_else(String::new, |code| code.to_string()),
                row.proof_checker_stdout.clone(),
                row.proof_checker_stderr.clone(),
                row.stdout.clone(),
                row.stderr.clone(),
            ]
            .join("\t")
        )?;
    }
    Ok(())
}

fn write_markdown(path: &Path, report: &SatDeltaReport) -> Result<()> {
    let mut file =
        File::create(path).with_bench_context(|| format!("creating {}", path.display()))?;
    writeln!(file, "# SAT Delta Scoreboard")?;
    writeln!(file)?;
    writeln!(file, "Schema: `{}`", report.schema)?;
    writeln!(file, "Source: `{}`", report.git.source_commit)?;
    writeln!(file, "Dirty: `{}`", report.git.source_dirty)?;
    writeln!(file, "Timeout: `{:.3}s`", report.timeout_sec)?;
    writeln!(file, "Runner: `{}`", report.runner.path)?;
    writeln!(file, "Runner SHA256: `{}`", report.runner.sha256)?;
    writeln!(
        file,
        "Require BCP relocation exercise: `{}`",
        report.require_bcp_relocation_exercise
    )?;
    writeln!(
        file,
        "BCP relocation env requested: `{}`",
        report.bcp_relocation_env_requested
    )?;
    writeln!(
        file,
        "Require BCP SEARCH in-place watch scan exercise: `{}`",
        report.require_bcp_search_inplace_watch_scan_exercise
    )?;
    writeln!(
        file,
        "BCP SEARCH in-place watch scan env requested: `{}`",
        report.bcp_search_inplace_watch_scan_env_requested
    )?;
    writeln!(
        file,
        "Require dense-mutex focused restart gate exercise: `{}`",
        report.require_dense_mutex_focused_restart_gate_exercise
    )?;
    writeln!(
        file,
        "Dense-mutex focused restart gate env requested: `{}`",
        report.dense_mutex_focused_restart_gate_env_requested
    )?;
    writeln!(
        file,
        "AY env: `{}`",
        if report.ay_env.is_empty() {
            "-".to_string()
        } else {
            report.ay_env.join(" ")
        }
    )?;
    writeln!(file, "AY env note: {}", report.ay_env_note)?;
    if let Some(version) = &report.runner.version {
        writeln!(file, "Runner version: `{}`", version)?;
    }
    if let Some(checker) = &report.proof_checker {
        writeln!(file, "Proof checker: `{checker}`")?;
    }
    if !report.evidence_warnings.is_empty() {
        writeln!(file)?;
        writeln!(file, "## Evidence Warnings")?;
        writeln!(file)?;
        for warning in &report.evidence_warnings {
            writeln!(file, "- {}", warning)?;
        }
    }
    writeln!(file)?;
    writeln!(file, "## Solver Binaries")?;
    writeln!(file)?;
    writeln!(
        file,
        "| solver | path | profile | sha256 | size | mtime epoch | version |"
    )?;
    writeln!(file, "| --- | --- | --- | --- | ---: | ---: | --- |")?;
    writeln!(
        file,
        "| `runner` | `{}` | {} | `{}` | {} | {} | {} |",
        report.runner.path,
        markdown_optional(&report.runner.build_profile),
        report.runner.sha256,
        report
            .runner
            .size_bytes
            .map_or_else(|| "-".to_string(), |size| size.to_string()),
        report
            .runner
            .mtime_epoch
            .map_or_else(|| "-".to_string(), |mtime| mtime.to_string()),
        markdown_optional(&report.runner.version)
    )?;
    for (solver, provenance) in &report.solvers {
        writeln!(
            file,
            "| `{}` | `{}` | {} | `{}` | {} | {} | {} |",
            solver,
            provenance.path,
            markdown_optional(&provenance.build_profile),
            provenance.sha256,
            provenance
                .size_bytes
                .map_or_else(|| "-".to_string(), |size| size.to_string()),
            provenance
                .mtime_epoch
                .map_or_else(|| "-".to_string(), |mtime| mtime.to_string()),
            markdown_optional(&provenance.version)
        )?;
    }
    if let Some(provenance) = &report.proof_checker_provenance {
        writeln!(
            file,
            "| `proof-checker` | `{}` | {} | `{}` | {} | {} | {} |",
            provenance.path,
            markdown_optional(&provenance.build_profile),
            provenance.sha256,
            provenance
                .size_bytes
                .map_or_else(|| "-".to_string(), |size| size.to_string()),
            provenance
                .mtime_epoch
                .map_or_else(|| "-".to_string(), |mtime| mtime.to_string()),
            markdown_optional(&provenance.version)
        )?;
    }
    writeln!(file)?;
    writeln!(file, "## Scoreboard")?;
    writeln!(file)?;
    writeln!(
        file,
        "| solver | total | solved | SAT | UNSAT | wrong | invalid | timeout | memout | PAR-2 total | PAR-2 avg | disqualified |"
    )?;
    writeln!(
        file,
        "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |"
    )?;
    for (solver, summary) in &report.summaries {
        writeln!(
            file,
            "| `{}` | {} | {} | {} | {} | {} | {} | {} | {} | {:.3} | {:.3} | {} |",
            solver,
            summary.total,
            summary.solved,
            summary.solved_sat,
            summary.solved_unsat,
            summary.wrong,
            summary.invalid,
            summary.timeout,
            summary.memout,
            summary.par2_total,
            summary.par2_avg,
            if summary.disqualified { "yes" } else { "no" }
        )?;
    }
    if !report.records.is_empty() {
        writeln!(file)?;
        writeln!(file, "## Stats Capture")?;
        writeln!(file)?;
        writeln!(
            file,
            "| solver | instance | status | stats sha256 | mode | result | wall ms | reloc enabled | attempts | moves | reloc exercised | search requested | search enabled | search exercised | dense requested | dense enabled | focused gate | dense updates | runtime checked | active vars | active clauses | active binary | runtime candidate | previous gate | computed gate | dense exercised | stats path |"
        )?;
        writeln!(
            file,
            "| --- | --- | --- | --- | --- | --- | ---: | --- | ---: | ---: | --- | --- | --- | --- | --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | ---: | ---: | --- | --- |"
        )?;
        for record in &report.records {
            writeln!(
                file,
                "| `{}` | `{}` | `{}` | `{}` | `{}` | `{}` | {} | `{}` | {} | {} | {} | `{}` | `{}` | {} | `{}` | `{}` | {} | {} | {} | {} | {} | {} | `{}` | {} | {} | {} | `{}` |",
                record.solver,
                record.instance,
                record.stats.status,
                record.stats.sha256,
                record.stats.mode,
                record.stats.result,
                record
                    .stats
                    .wall_time_ms
                    .map_or_else(|| "-".to_string(), |value| value.to_string()),
                display_optional_bool(record.bcp_relocation.enabled),
                display_optional_u64(record.bcp_relocation.attempts),
                display_optional_u64(record.bcp_relocation.moves),
                if record.bcp_relocation.exercised {
                    "yes"
                } else {
                    "no"
                },
                display_optional_bool(record.bcp_search_inplace_watch_scan.requested),
                display_optional_bool(record.bcp_search_inplace_watch_scan.enabled),
                if record.bcp_search_inplace_watch_scan.exercised {
                    "yes"
                } else {
                    "no"
                },
                display_optional_bool(record.dense_mutex_focused_restart_gate.requested),
                display_optional_bool(record.dense_mutex_focused_restart_gate.enabled),
                display_optional_u64(record.dense_mutex_focused_restart_gate.focused_gate_final),
                display_optional_u64(record.dense_mutex_focused_restart_gate.updates),
                display_optional_u64(record.dense_mutex_focused_restart_gate.runtime_checked),
                display_optional_u64(record.dense_mutex_focused_restart_gate.active_vars),
                display_optional_u64(record.dense_mutex_focused_restart_gate.active_clauses),
                display_optional_u64(
                    record
                        .dense_mutex_focused_restart_gate
                        .active_binary_clauses,
                ),
                display_optional_bool(record.dense_mutex_focused_restart_gate.runtime_candidate),
                display_optional_u64(record.dense_mutex_focused_restart_gate.previous_gate),
                display_optional_u64(record.dense_mutex_focused_restart_gate.computed_gate),
                if record.dense_mutex_focused_restart_gate.exercised {
                    "yes"
                } else {
                    "no"
                },
                record.stats.path
            )?;
        }
    }
    if !report.records.is_empty() {
        writeln!(file)?;
        writeln!(file, "## Row Validation")?;
        writeln!(file)?;
        writeln!(
            file,
            "| solver | instance | actual | proof status | model status | invalid | proof checker argv |"
        )?;
        writeln!(file, "| --- | --- | --- | --- | --- | ---: | --- |")?;
        for record in &report.records {
            writeln!(
                file,
                "| `{}` | `{}` | `{}` | `{}` | `{}` | {} | `{}` |",
                record.solver,
                record.instance,
                record.actual,
                record.proof_status,
                record.model_status,
                u8::from(record.invalid),
                record.proof_checker_command_path
            )?;
        }
    }
    if !report.reference_deltas.is_empty() {
        writeln!(file)?;
        writeln!(file, "## AY vs Reference")?;
        writeln!(file)?;
        writeln!(
            file,
            "| reference | AY solved | ref solved | solved delta | AY PAR-2 | ref PAR-2 | PAR-2 delta | ref-only solved | AY-only solved | disagree |"
        )?;
        writeln!(
            file,
            "| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |"
        )?;
        for delta in &report.reference_deltas {
            writeln!(
                file,
                "| `{}` | {} | {} | {} | {:.3} | {:.3} | {:.3} | {} | {} | {} |",
                delta.reference,
                delta.ay_solved,
                delta.reference_solved,
                delta.solved_delta,
                delta.ay_par2_total,
                delta.reference_par2_total,
                delta.par2_delta,
                delta.ref_only_solved,
                delta.ay_only_solved,
                delta.definitive_disagree
            )?;
        }
    }
    if !report.records.is_empty() {
        writeln!(file)?;
        writeln!(file, "## Commands")?;
        writeln!(file)?;
        writeln!(
            file,
            "| solver | instance | command sha256 | argv file | ay env | command |"
        )?;
        writeln!(file, "| --- | --- | --- | --- | --- | --- |")?;
        for record in &report.records {
            writeln!(
                file,
                "| `{}` | `{}` | `{}` | `{}` | `{}` | `{}` |",
                record.solver,
                record.instance,
                record.command_sha256,
                record.command_path,
                record.ay_env.join(" ").replace('`', "\\`"),
                record.command_display.replace('`', "\\`")
            )?;
        }
    }
    Ok(())
}

fn markdown_optional(value: &Option<String>) -> String {
    value
        .as_ref()
        .map_or_else(|| "-".to_string(), |value| format!("`{}`", value))
}

fn display_optional_bool(value: Option<bool>) -> String {
    value.map_or_else(String::new, |value| value.to_string())
}

fn display_optional_u64(value: Option<u64>) -> String {
    value.map_or_else(String::new, |value| value.to_string())
}

fn binary_provenance(
    path: &Path,
    kind: SolverKind,
    resources: &crate::resource::PlannedResources,
) -> BinaryProvenance {
    let resolved = absolute_path(path);
    let metadata = fs::metadata(&resolved).ok();
    let build_profile = infer_build_profile(&resolved);
    BinaryProvenance {
        path: resolved.display().to_string(),
        exists: metadata.is_some(),
        executable: metadata.as_ref().is_some_and(|meta| !meta.is_dir()),
        sha256: metadata
            .as_ref()
            .and_then(|_| sha256_file(&resolved).ok())
            .unwrap_or_else(|| "unavailable".to_string()),
        size_bytes: metadata.as_ref().map(std::fs::Metadata::len),
        mtime_epoch: metadata
            .as_ref()
            .and_then(|meta| meta.modified().ok())
            .and_then(|time| time.duration_since(std::time::UNIX_EPOCH).ok())
            .map(|duration| duration.as_secs() as i64),
        version: solver_version(&resolved, kind, resources),
        build_profile,
    }
}

fn current_runner_provenance(resources: &crate::resource::PlannedResources) -> BinaryProvenance {
    let path = std::env::current_exe().unwrap_or_else(|_| PathBuf::from("<unknown-runner>"));
    binary_provenance(&path, SolverKind::AY, resources)
}

fn infer_build_profile(path: &Path) -> Option<String> {
    for component in path.components().rev() {
        let name = component.as_os_str().to_string_lossy();
        if matches!(name.as_ref(), "release-perf" | "release" | "debug") {
            return Some(name.into_owned());
        }
    }
    None
}

fn evidence_warnings(
    git: &GitProvenance,
    runner: &BinaryProvenance,
    solvers: &BTreeMap<String, BinaryProvenance>,
    proof_format: &str,
    proof_checker: Option<&BinaryProvenance>,
) -> Vec<String> {
    let mut warnings = Vec::new();
    if git.source_dirty {
        warnings.push(format!(
            "source tree is dirty ({} entries, status sha256 {}); do not cite as clean SAT-COMP speed evidence",
            git.source_dirty_entries, git.source_git_status_sha256
        ));
    }
    push_binary_stamp_warning("runner", runner, git, &mut warnings);
    for (solver, provenance) in solvers {
        if !provenance.exists {
            warnings.push(format!(
                "{solver} binary path does not exist: {}",
                provenance.path
            ));
        }
        if solver == "ay" {
            push_binary_stamp_warning("ay solver", provenance, git, &mut warnings);
            match provenance.build_profile.as_deref() {
                Some("release" | "release-perf") => {}
                Some(profile) => warnings.push(format!(
                    "ay solver build profile is {profile}; score-bearing evidence normally requires release or release-perf"
                )),
                None => warnings.push(
                    "ay solver build profile is unknown; stale or non-Cargo binary cannot be ruled out"
                        .to_string(),
                ),
            }
        }
    }
    push_proof_checker_warnings(proof_format, proof_checker, &mut warnings);
    warnings
}

fn push_proof_checker_warnings(
    proof_format: &str,
    proof_checker: Option<&BinaryProvenance>,
    warnings: &mut Vec<String>,
) {
    let proof_format = proof_format.trim().to_ascii_lowercase();
    if !matches!(proof_format.as_str(), "lrat" | "drat") {
        warnings.push(format!(
            "proof format is {proof_format}; SAT-COMP Main UNSAT evidence normally needs LRAT/DRAT plus checker verdicts"
        ));
        return;
    }
    match proof_checker {
        Some(checker) if !checker.exists => warnings.push(format!(
            "proof checker path does not exist: {}; UNSAT rows cannot be treated as externally verified",
            checker.path
        )),
        Some(checker) if !checker.executable => warnings.push(format!(
            "proof checker path is not executable: {}; UNSAT rows cannot be treated as externally verified",
            checker.path
        )),
        Some(_) => {}
        None => warnings.push(format!(
            "proof format is {proof_format}, but no --proof-checker was provided; definitive AY UNSAT rows will be marked invalid by sat-delta"
        )),
    }
}

fn push_binary_stamp_warning(
    label: &str,
    provenance: &BinaryProvenance,
    git: &GitProvenance,
    warnings: &mut Vec<String>,
) {
    let Some(version) = provenance.version.as_deref() else {
        warnings.push(format!(
            "{label} version is unavailable; binary/source match cannot be checked"
        ));
        return;
    };
    let Some(stamp) = version_commit_token(version) else {
        warnings.push(format!(
            "{label} version has no recognizable git stamp: {version}"
        ));
        return;
    };
    if !git.source_commit.starts_with(&stamp) && !stamp.starts_with(&git.source_commit_short) {
        warnings.push(format!(
            "{label} git stamp {stamp} does not match source HEAD {}",
            git.source_commit_short
        ));
    }
}

fn version_commit_token(version: &str) -> Option<String> {
    let mut best = String::new();
    let mut current = String::new();
    for ch in version.chars() {
        if ch.is_ascii_hexdigit() {
            current.push(ch);
        } else {
            if current.len() > best.len() {
                best = std::mem::take(&mut current);
            }
            current.clear();
        }
    }
    if current.len() > best.len() {
        best = current;
    }
    if best.len() >= 7 {
        Some(best)
    } else {
        None
    }
}

fn solver_version(
    path: &Path,
    _kind: SolverKind,
    resources: &crate::resource::PlannedResources,
) -> Option<String> {
    let output = resources
        .capture_external_output(
            path,
            ["--version"],
            std::time::Duration::from_secs(10),
            "ay bench sat-delta version probe",
        )
        .ok()?;
    if !output.status.success() {
        return None;
    }
    let text = if output.stdout.is_empty() {
        output.stderr
    } else {
        output.stdout
    };
    text.lines()
        .next()
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
}

fn sha256_file(path: &Path) -> Result<String> {
    let mut file = File::open(path).with_bench_context(|| format!("opening {}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buf = [0u8; 64 * 1024];
    loop {
        let n = file
            .read(&mut buf)
            .with_bench_context(|| format!("reading {}", path.display()))?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn git_provenance() -> GitProvenance {
    let status = run_text(["git", "status", "--short"]);
    GitProvenance {
        source_commit: run_text(["git", "rev-parse", "HEAD"]),
        source_commit_short: run_text(["git", "rev-parse", "--short", "HEAD"]),
        source_branch: run_text(["git", "branch", "--show-current"]),
        source_dirty: !status.trim().is_empty(),
        source_dirty_entries: status
            .lines()
            .filter(|line| !line.trim().is_empty())
            .count(),
        source_git_status_sha256: sha256_bytes(status.as_bytes()),
        source_git_status_short: status,
    }
}

fn run_text<const N: usize>(args: [&str; N]) -> String {
    let output = crate::resource::capture_local_output(
        args[0],
        args[1..].iter().copied(),
        std::time::Duration::from_secs(10),
        args[0],
    );
    match output {
        Ok(output) if output.status.success() => output.stdout.trim().to_string(),
        _ => "unknown".to_string(),
    }
}

fn sha256_bytes(bytes: &[u8]) -> String {
    let mut hasher = Sha256::new();
    hasher.update(bytes);
    format!("{:x}", hasher.finalize())
}

fn absolute_path(path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()
            .unwrap_or_else(|_| PathBuf::from("."))
            .join(path)
    }
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

fn sanitize(value: &str) -> String {
    value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || matches!(ch, '.' | '-' | '_') {
                ch
            } else {
                '_'
            }
        })
        .collect()
}

fn round3(value: f64) -> f64 {
    (value * 1000.0).round() / 1000.0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn test_resources() -> crate::resource::PlannedResources {
        crate::resource::PlannedResources::for_test(&crate::runner::repo_root_public(), 4096)
    }

    #[test]
    fn parse_sat_status_requires_exact_status_line() {
        assert_eq!(
            parse_sat_status("c comment\ns SATISFIABLE\n"),
            Some("sat".to_string())
        );
        assert_eq!(
            parse_sat_status("s UNSATISFIABLE\n"),
            Some("unsat".to_string())
        );
        assert_eq!(parse_sat_status("s UNKNOWN\n"), Some("unknown".to_string()));
        assert_eq!(parse_sat_status("SATISFIABLE\n"), None);
    }

    #[test]
    fn sat_summary_uses_par2_for_unknown_rows() {
        let rows = [
            RunRecord {
                solver: "ay".to_string(),
                instance: "a.cnf".to_string(),
                path: "a.cnf".to_string(),
                expected: "unknown".to_string(),
                actual: "unsat".to_string(),
                family: "f".to_string(),
                category: "c".to_string(),
                elapsed_s: 1.5,
                par2_s: 1.5,
                exit_code: Some(20),
                wrong: false,
                invalid: false,
                proof_status: "n/a".to_string(),
                model_status: "n/a".to_string(),
                timeout: false,
                binary_path: "ay".to_string(),
                binary_sha256: "sha".to_string(),
                binary_size_bytes: Some(1),
                binary_mtime_epoch: Some(1),
                command_path: "cmd".to_string(),
                command_sha256: "cmd-sha".to_string(),
                command_argv: vec!["ay".to_string(), "solve".to_string(), "a.cnf".to_string()],
                command_display: "ay solve a.cnf".to_string(),
                ay_env: Vec::new(),
                stats: StatsCapture::not_applicable(),
                bcp_relocation: BcpRelocationStats::none(),
                bcp_search_inplace_watch_scan: BcpSearchInplaceWatchScanStats::none(),
                dense_mutex_focused_restart_gate: DenseMutexFocusedRestartGateStats::none(),
                proof_path: "proof.out".to_string(),
                proof_checker_command_path: String::new(),
                proof_checker_command_sha256: String::new(),
                proof_checker_exit_code: None,
                proof_checker_stdout: String::new(),
                proof_checker_stderr: String::new(),
                stdout: "out".to_string(),
                stderr: "err".to_string(),
            },
            RunRecord {
                actual: "unknown".to_string(),
                par2_s: 20.0,
                ..dummy_record()
            },
        ];
        let refs: Vec<&RunRecord> = rows.iter().collect();
        let summary = summarize_rows(&refs);
        assert_eq!(summary.solved, 1);
        assert_eq!(summary.par2_total, 21.5);
    }

    #[test]
    fn default_hard_tail_discovery_recurses_and_prefers_plain_cnf() {
        let tmp = tempfile::tempdir().unwrap();
        let nested = tmp.path().join("family").join("deep");
        fs::create_dir_all(&nested).unwrap();
        let compressed = nested.join("case_clique_n2_k10.cnf.xz");
        let plain = nested.join("case_clique_n2_k10.cnf");
        fs::write(&compressed, b"compressed").unwrap();
        fs::write(&plain, b"p cnf 1 1\n1 0\n").unwrap();

        let found = find_named_cnf(tmp.path(), "clique_n2_k10")
            .unwrap()
            .unwrap();

        assert_eq!(found, plain);
    }

    #[test]
    fn manifest_parser_handles_quoted_commas_before_path() {
        let tmp = tempfile::tempdir().unwrap();
        let manifest = tmp.path().join("manifest.csv");
        fs::write(
            &manifest,
            "hash,filename,family,result,track,local_path\n\
             abc,case.cnf.xz,quoted-family,unsat,\"main_2024,main_2025\",benchmarks/sat/case.cnf.xz\n",
        )
        .unwrap();

        let rows = load_manifest(&manifest).unwrap();

        assert_eq!(rows.len(), 1);
        assert_eq!(rows[0].expected, "unsat");
        assert_eq!(rows[0].family, "quoted-family");
        assert_eq!(rows[0].path, repo_root().join("benchmarks/sat/case.cnf.xz"));
    }

    #[test]
    fn default_hard_tail_loads_expected_from_root_manifest() {
        let tmp = tempfile::tempdir().unwrap();
        let clique = tmp.path().join("case_clique_n2_k10.cnf.xz");
        let multiplier = tmp.path().join("case_Circuit_multiplier22.cnf.xz");
        fs::write(&clique, b"compressed").unwrap();
        fs::write(&multiplier, b"compressed").unwrap();
        fs::write(
            tmp.path().join("manifest.csv"),
            format!(
                "filename,result,track,local_path\n\
                 {},unsat,\"main_2024,main_2025\",{}\n\
                 {},sat,\"main_2024,main_2025\",{}\n",
                clique.file_name().unwrap().to_string_lossy(),
                clique.display(),
                multiplier.file_name().unwrap().to_string_lossy(),
                multiplier.display()
            ),
        )
        .unwrap();

        let rows = default_hard_tail_rows(tmp.path()).unwrap();

        assert_eq!(rows.len(), 2);
        assert_eq!(rows[0].family, "clique_n2_k10");
        assert_eq!(rows[0].expected, "unsat");
        assert_eq!(rows[1].family, "Circuit_multiplier22");
        assert_eq!(rows[1].expected, "sat");
    }

    #[test]
    fn expected_status_is_clamped_to_sat_unsat_unknown() {
        assert_eq!(normalize_expected("SAT"), "sat");
        assert_eq!(normalize_expected("unsat"), "unsat");
        assert_eq!(normalize_expected("empty"), "unknown");
        assert_eq!(normalize_expected(""), "unknown");
    }

    #[test]
    fn command_display_quotes_arguments_without_losing_exact_argv() {
        let argv = vec![
            "target/release/ay".to_string(),
            "solve".to_string(),
            "--proof".to_string(),
            "path with spaces/proof.out".to_string(),
            "weird'quote.cnf".to_string(),
        ];

        assert_eq!(
            display_command(&argv),
            "target/release/ay solve --proof 'path with spaces/proof.out' 'weird'\\''quote.cnf'"
        );
    }

    #[test]
    fn evidence_warnings_flag_stale_ay_binary_stamp() {
        let git = GitProvenance {
            source_commit: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa".to_string(),
            source_commit_short: "aaaaaaaaaa".to_string(),
            source_branch: "main".to_string(),
            source_dirty: false,
            source_dirty_entries: 0,
            source_git_status_sha256: sha256_bytes(b""),
            source_git_status_short: String::new(),
        };
        let runner = BinaryProvenance {
            path: "target/debug/ay".to_string(),
            exists: true,
            executable: true,
            sha256: "runner-sha".to_string(),
            size_bytes: Some(1),
            mtime_epoch: Some(1),
            version: Some("ay 0.10.0+build.1.aaaaaaaaaaaa@now".to_string()),
            build_profile: Some("debug".to_string()),
        };
        let mut solvers = BTreeMap::new();
        solvers.insert(
            "ay".to_string(),
            BinaryProvenance {
                path: "target/release/ay".to_string(),
                exists: true,
                executable: true,
                sha256: "ay-sha".to_string(),
                size_bytes: Some(1),
                mtime_epoch: Some(1),
                version: Some("ay 0.10.0+build.1.bbbbbbbbbbbb-dirty@now".to_string()),
                build_profile: Some("release".to_string()),
            },
        );

        let warnings = evidence_warnings(&git, &runner, &solvers, "lrat", None);

        assert!(warnings
            .iter()
            .any(|warning| warning.contains("ay solver git stamp bbbbbbbbbbbb")));
    }

    #[test]
    fn evidence_warnings_flag_missing_lrat_checker() {
        let git = clean_git("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        let runner = dummy_binary("target/release-perf/ay", "aaaaaaaaaaaa", "release-perf");
        let mut solvers = BTreeMap::new();
        solvers.insert(
            "ay".to_string(),
            dummy_binary("target/release-perf/ay", "aaaaaaaaaaaa", "release-perf"),
        );

        let warnings = evidence_warnings(&git, &runner, &solvers, "lrat", None);

        assert!(warnings
            .iter()
            .any(|warning| warning.contains("no --proof-checker was provided")));
    }

    #[test]
    fn evidence_warnings_accept_configured_lrat_checker() {
        let git = clean_git("aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa");
        let runner = dummy_binary("target/release-perf/ay", "aaaaaaaaaaaa", "release-perf");
        let checker = dummy_binary(
            "cache/tools/sat26-checkers/bin/cake_lpr",
            "cccccccccccc",
            "",
        );
        let mut solvers = BTreeMap::new();
        solvers.insert(
            "ay".to_string(),
            dummy_binary("target/release-perf/ay", "aaaaaaaaaaaa", "release-perf"),
        );

        let warnings = evidence_warnings(&git, &runner, &solvers, "lrat", Some(&checker));

        assert!(!warnings
            .iter()
            .any(|warning| warning.contains("not invoked by sat-delta")));
    }

    #[test]
    fn sat_model_validation_checks_original_dimacs_clauses() {
        let tmp = tempfile::tempdir().unwrap();
        let cnf = tmp.path().join("case.cnf");
        fs::write(&cnf, "p cnf 2 2\n1 2 0\n-1 2 0\n").unwrap();

        assert_eq!(verify_sat_model(&cnf, "s SATISFIABLE\nv -1 2 0\n"), "valid");
        assert_eq!(
            verify_sat_model(&cnf, "s SATISFIABLE\nv 1 -2 0\n"),
            "invalid"
        );
        assert_eq!(
            verify_sat_model(&cnf, "s SATISFIABLE\nv 1 1 0\n"),
            "duplicate-assignment:2"
        );
        assert_eq!(
            verify_sat_model(&cnf, "s SATISFIABLE\nv 1 0\nv 0\n"),
            "duplicate-terminator:3"
        );
    }

    #[test]
    fn proof_checker_verdict_requires_single_verified_unsat_line() {
        assert!(proof_checker_output_is_verified("s VERIFIED UNSAT\n", ""));
        assert!(proof_checker_output_is_verified(
            "s VERIFIED\n",
            "c ay.build.stamp: test\nc proof counters\n"
        ));
        assert!(!proof_checker_output_is_verified(
            "s VERIFIED UNSAT\ns UNKNOWN\n",
            ""
        ));
        assert!(!proof_checker_output_is_verified(
            "s VERIFIED UNSAT\n",
            "warning\n"
        ));
    }

    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn unsat_proof_validation_accepts_verified_stdout_with_comment_stderr() {
        let tmp = tempfile::tempdir().unwrap();
        let cnf = tmp.path().join("case.cnf");
        let proof = tmp.path().join("proof.out");
        let checker = tmp.path().join("checker.sh");
        let case_dir = tmp.path().join("case");
        fs::create_dir(&case_dir).unwrap();
        fs::write(&cnf, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
        fs::write(&proof, "dummy proof\n").unwrap();
        fs::write(
            &checker,
            "#!/bin/sh\nprintf 's VERIFIED\\n'\nprintf 'c checker progress\\nc proof counters\\n' >&2\n",
        )
        .unwrap();
        make_executable(&checker);

        let args = SatDeltaArgs {
            manifest: None,
            benchmark_root: tmp.path().to_path_buf(),
            out_dir: tmp.path().join("out"),
            ay: checker.clone(),
            ay_env: Vec::new(),
            reference_solvers: Vec::new(),
            timeout_sec: 5.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: Some(checker),
            allow_dirty: true,
            fail_on_wrong: true,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        };

        let resources = test_resources();
        let validation =
            verify_unsat_proof(&cnf, &proof, &args, &case_dir, Some(&resources)).unwrap();

        assert_eq!(validation.proof_status, "valid");
        assert_eq!(validation.proof_checker_exit_code, Some(0));
        assert!(fs::read_to_string(validation.proof_checker_stderr)
            .unwrap()
            .contains("c checker progress"));
    }

    #[test]
    fn stats_json_capture_parses_bcp_relocation_exercise() {
        let tmp = tempfile::tempdir().unwrap();
        let stderr = r#"c before
{"mode":"dimacs-sat","result":"sat","wall_time_ms":42,"sat.bcp_learned_1963_true_tail_relocation_enabled":true,"sat.bcp_learned_1963_true_tail_relocation_attempts":7,"sat.bcp_learned_1963_true_tail_relocation_moves":0,"sat.bcp_search_inplace_watch_scan_requested":true,"sat.bcp_search_inplace_watch_scan_enabled":true,"sat.bcp_search_inplace_watch_scan_exercised":true,"sat.dense_mutex_focused_restart_gate_requested":true,"sat.dense_mutex_focused_restart_gate_enabled":true,"sat.focused_restart_gate_final":45,"sat.dense_mutex_focused_restart_gate_updates":1,"sat.dense_mutex_focused_restart_runtime_checked":1,"sat.dense_mutex_focused_restart_active_vars":180,"sat.dense_mutex_focused_restart_active_clauses":3160,"sat.dense_mutex_focused_restart_active_binary_clauses":3150,"sat.dense_mutex_focused_restart_runtime_candidate":true,"sat.dense_mutex_focused_restart_previous_gate":4,"sat.dense_mutex_focused_restart_computed_gate":45}
c after
"#;

        let (stats, bcp, search, dense_restart) =
            capture_run_stats(SolverKind::AY, stderr, tmp.path()).unwrap();

        assert_eq!(stats.status, "captured");
        assert_eq!(stats.mode, "dimacs-sat");
        assert_eq!(stats.result, "sat");
        assert_eq!(stats.wall_time_ms, Some(42));
        assert!(Path::new(&stats.path).is_file());
        assert_eq!(bcp.enabled, Some(true));
        assert_eq!(bcp.attempts, Some(7));
        assert_eq!(bcp.moves, Some(0));
        assert!(bcp.exercised);
        assert_eq!(search.requested, Some(true));
        assert_eq!(search.enabled, Some(true));
        assert!(search.exercised);
        assert_eq!(dense_restart.requested, Some(true));
        assert_eq!(dense_restart.enabled, Some(true));
        assert_eq!(dense_restart.focused_gate_final, Some(45));
        assert_eq!(dense_restart.updates, Some(1));
        assert_eq!(dense_restart.runtime_checked, Some(1));
        assert_eq!(dense_restart.active_vars, Some(180));
        assert_eq!(dense_restart.active_clauses, Some(3160));
        assert_eq!(dense_restart.active_binary_clauses, Some(3150));
        assert_eq!(dense_restart.runtime_candidate, Some(true));
        assert_eq!(dense_restart.previous_gate, Some(4));
        assert_eq!(dense_restart.computed_gate, Some(45));
        assert!(dense_restart.exercised);
    }

    #[test]
    fn stats_json_capture_is_ay_only() {
        let tmp = tempfile::tempdir().unwrap();
        let (stats, bcp, search, dense_restart) = capture_run_stats(
            SolverKind::Reference,
            r#"{"mode":"dimacs-sat","result":"sat","wall_time_ms":1}"#,
            tmp.path(),
        )
        .unwrap();

        assert_eq!(stats.status, "not-applicable");
        assert!(stats.path.is_empty());
        assert_eq!(bcp.enabled, None);
        assert!(!bcp.exercised);
        assert_eq!(search.requested, None);
        assert!(!search.exercised);
        assert_eq!(dense_restart.requested, None);
        assert!(!dense_restart.exercised);
    }

    #[test]
    fn require_bcp_relocation_exercise_fails_when_requested_but_idle() {
        let mut record = dummy_record();
        record.timeout = false;
        record.stats = StatsCapture {
            path: "stats.json".to_string(),
            sha256: "sha".to_string(),
            status: "captured".to_string(),
            mode: "dimacs-sat".to_string(),
            result: "sat".to_string(),
            wall_time_ms: Some(5),
        };
        record.bcp_relocation = BcpRelocationStats {
            enabled: Some(true),
            attempts: Some(0),
            moves: Some(0),
            exercised: false,
        };
        let args = SatDeltaArgs {
            manifest: None,
            benchmark_root: PathBuf::from("benchmarks"),
            out_dir: PathBuf::from("out"),
            ay: PathBuf::from("ay"),
            ay_env: vec![(BCP_RELOCATION_ENV.to_string(), "1".to_string())],
            reference_solvers: Vec::new(),
            timeout_sec: 1.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: None,
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: true,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        };

        let failure = bcp_relocation_gate_failure(&[record], &args).unwrap();

        assert!(failure.contains("did not exercise"));
        assert!(failure.contains(BCP_RELOCATION_ENV));
    }

    #[test]
    fn require_bcp_search_inplace_watch_scan_exercise_fails_when_requested_but_idle() {
        let mut record = dummy_record();
        record.timeout = false;
        record.stats = StatsCapture {
            path: "stats.json".to_string(),
            sha256: "sha".to_string(),
            status: "captured".to_string(),
            mode: "dimacs-sat".to_string(),
            result: "sat".to_string(),
            wall_time_ms: Some(5),
        };
        record.bcp_search_inplace_watch_scan = BcpSearchInplaceWatchScanStats {
            requested: Some(true),
            enabled: Some(true),
            exercised: false,
        };
        let args = SatDeltaArgs {
            manifest: None,
            benchmark_root: PathBuf::from("benchmarks"),
            out_dir: PathBuf::from("out"),
            ay: PathBuf::from("ay"),
            ay_env: vec![(
                BCP_SEARCH_INPLACE_WATCH_SCAN_ENV.to_string(),
                "1".to_string(),
            )],
            reference_solvers: Vec::new(),
            timeout_sec: 1.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: None,
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: true,
            require_dense_mutex_focused_restart_gate_exercise: false,
        };

        let failure = bcp_search_inplace_watch_scan_gate_failure(&[record], &args).unwrap();

        assert!(failure.contains("did not exercise"));
        assert!(failure.contains(BCP_SEARCH_INPLACE_WATCH_SCAN_ENV));
    }

    #[test]
    fn require_dense_mutex_focused_restart_gate_exercise_fails_when_requested_but_idle() {
        let mut record = dummy_record();
        record.timeout = false;
        record.stats = StatsCapture {
            path: "stats.json".to_string(),
            sha256: "sha".to_string(),
            status: "captured".to_string(),
            mode: "dimacs-sat".to_string(),
            result: "sat".to_string(),
            wall_time_ms: Some(5),
        };
        record.dense_mutex_focused_restart_gate = DenseMutexFocusedRestartGateStats {
            requested: Some(true),
            enabled: Some(true),
            focused_gate_final: Some(10),
            updates: Some(0),
            runtime_checked: Some(1),
            active_vars: Some(180),
            active_clauses: Some(3160),
            active_binary_clauses: Some(3150),
            runtime_candidate: Some(true),
            previous_gate: Some(40),
            computed_gate: Some(40),
            exercised: false,
        };
        let args = SatDeltaArgs {
            manifest: None,
            benchmark_root: PathBuf::from("benchmarks"),
            out_dir: PathBuf::from("out"),
            ay: PathBuf::from("ay"),
            ay_env: vec![(
                DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV.to_string(),
                "1".to_string(),
            )],
            reference_solvers: Vec::new(),
            timeout_sec: 1.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: None,
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: true,
        };

        let failure = dense_mutex_focused_restart_gate_failure(&[record], &args).unwrap();

        assert!(failure.contains("did not exercise"));
        assert!(failure.contains(DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV));
        assert!(failure.contains("updates=0"));
        assert!(failure.contains("runtime_candidate=true"));
        assert!(failure.contains("computed_gate=40"));
    }

    #[test]
    fn dense_mutex_focused_restart_gate_env_requested_without_require_allows_idle_control() {
        let mut record = dummy_record();
        record.stats = StatsCapture {
            path: "stats.json".to_string(),
            sha256: "sha".to_string(),
            status: "captured".to_string(),
            mode: "dimacs-sat".to_string(),
            result: "unknown".to_string(),
            wall_time_ms: Some(5),
        };
        record.dense_mutex_focused_restart_gate = DenseMutexFocusedRestartGateStats {
            requested: Some(true),
            enabled: Some(false),
            focused_gate_final: Some(50),
            updates: Some(0),
            runtime_checked: Some(0),
            active_vars: Some(0),
            active_clauses: Some(0),
            active_binary_clauses: Some(0),
            runtime_candidate: Some(false),
            previous_gate: Some(0),
            computed_gate: Some(0),
            exercised: false,
        };
        let args = SatDeltaArgs {
            manifest: None,
            benchmark_root: PathBuf::from("benchmarks"),
            out_dir: PathBuf::from("out"),
            ay: PathBuf::from("ay"),
            ay_env: vec![(
                DENSE_MUTEX_FOCUSED_RESTART_GATE_ENV.to_string(),
                "1".to_string(),
            )],
            reference_solvers: Vec::new(),
            timeout_sec: 1.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: None,
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        };

        assert!(dense_mutex_focused_restart_gate_failure(&[record], &args).is_none());
    }

    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn ay_unsat_validation_invokes_external_checker() {
        let tmp = tempfile::tempdir().unwrap();
        let cnf = tmp.path().join("case.cnf");
        let proof = tmp.path().join("proof.out");
        let checker = tmp.path().join("checker.sh");
        fs::write(&cnf, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
        fs::write(&proof, "1 0\n").unwrap();
        fs::write(
            &checker,
            "#!/bin/sh\n[ -s \"$1\" ] && [ -s \"$2\" ] && printf 's VERIFIED UNSAT\\n'\n",
        )
        .unwrap();
        make_executable(&checker);
        let args = SatDeltaArgs {
            manifest: None,
            benchmark_root: tmp.path().to_path_buf(),
            out_dir: tmp.path().join("out"),
            ay: PathBuf::from("ay"),
            ay_env: Vec::new(),
            reference_solvers: Vec::new(),
            timeout_sec: 5.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: Some(checker),
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        };

        let resources = test_resources();
        let validation = validate_row(
            SolverKind::AY,
            "unsat",
            false,
            &cnf,
            "s UNSATISFIABLE\n",
            &proof,
            &args,
            tmp.path(),
            Some(&resources),
        )
        .unwrap();

        assert_eq!(validation.proof_status, "valid");
        assert_eq!(validation.model_status, "n/a");
        assert!(!validation.invalid);
        assert!(Path::new(&validation.proof_checker_command_path).is_file());
        assert!(Path::new(&validation.proof_checker_stdout).is_file());
    }

    #[test]
    fn ay_sat_validation_fails_closed_on_invalid_model() {
        let tmp = tempfile::tempdir().unwrap();
        let cnf = tmp.path().join("case.cnf");
        let proof = tmp.path().join("proof.out");
        fs::write(&cnf, "p cnf 1 1\n1 0\n").unwrap();
        let args = SatDeltaArgs {
            manifest: None,
            benchmark_root: tmp.path().to_path_buf(),
            out_dir: tmp.path().join("out"),
            ay: PathBuf::from("ay"),
            ay_env: Vec::new(),
            reference_solvers: Vec::new(),
            timeout_sec: 1.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: None,
            allow_dirty: true,
            fail_on_wrong: false,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        };

        let validation = validate_row(
            SolverKind::AY,
            "sat",
            false,
            &cnf,
            "s SATISFIABLE\nv -1 0\n",
            &proof,
            &args,
            tmp.path(),
            None,
        )
        .unwrap();

        assert_eq!(validation.model_status, "invalid");
        assert!(validation.invalid);
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn sat_delta_report_records_ay_model_and_proof_statuses() {
        let tmp = tempfile::tempdir().unwrap();
        let sat = tmp.path().join("sat.cnf");
        let unsat = tmp.path().join("unsat.cnf");
        let manifest = tmp.path().join("manifest.csv");
        let out_dir = tmp.path().join("out");
        let solver = tmp.path().join("fake-ay.sh");
        let checker = tmp.path().join("checker.sh");
        fs::write(&sat, "p cnf 1 1\n1 0\n").unwrap();
        fs::write(&unsat, "p cnf 1 2\n1 0\n-1 0\n").unwrap();
        fs::write(
            &manifest,
            format!(
                "path,result,family,category\n{},sat,fixture,sat\n{},unsat,fixture,unsat\n",
                sat.display(),
                unsat.display()
            ),
        )
        .unwrap();
        fs::write(
            &solver,
            r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  printf 'ay fake 0000000\n'
  exit 0
fi
if [ "${AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION:-}" != "1" ]; then
  printf 'missing true-tail env\n' >&2
  exit 64
fi
if [ "${AY_EMPTY_VALUE+x}" != "x" ]; then
  printf 'missing empty env\n' >&2
  exit 65
fi
proof=""
input=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --stats-json)
      shift
      ;;
    --proof)
      proof="$2"
      shift 2
      ;;
    --proof-format|--sat-variant)
      shift 2
      ;;
    --timeout=*|solve|--no-verify-proof)
      shift
      ;;
    *)
      input="$1"
      shift
      ;;
  esac
done
case "$input" in
  *unsat.cnf)
    printf 's UNSATISFIABLE\n'
    printf '1 0\n' > "$proof"
    printf '{"mode":"dimacs-sat","result":"unsat","wall_time_ms":17,"sat.bcp_learned_1963_true_tail_relocation_enabled":true,"sat.bcp_learned_1963_true_tail_relocation_attempts":3,"sat.bcp_learned_1963_true_tail_relocation_moves":1}\n' >&2
    ;;
  *)
    printf 's SATISFIABLE\nv 1 0\n'
    printf '{"mode":"dimacs-sat","result":"sat","wall_time_ms":11,"sat.bcp_learned_1963_true_tail_relocation_enabled":true,"sat.bcp_learned_1963_true_tail_relocation_attempts":2,"sat.bcp_learned_1963_true_tail_relocation_moves":1}\n' >&2
    ;;
esac
"#,
        )
        .unwrap();
        fs::write(
            &checker,
            "#!/bin/sh\n[ -s \"$1\" ] && [ -s \"$2\" ] && printf 's VERIFIED UNSAT\\n'\n",
        )
        .unwrap();
        make_executable(&solver);
        make_executable(&checker);

        cmd_sat_delta(SatDeltaArgs {
            manifest: Some(manifest),
            benchmark_root: tmp.path().to_path_buf(),
            out_dir: out_dir.clone(),
            ay: solver,
            ay_env: vec![
                (
                    "AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION".to_string(),
                    "1".to_string(),
                ),
                ("AY_EMPTY_VALUE".to_string(), String::new()),
            ],
            reference_solvers: Vec::new(),
            timeout_sec: 2.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: Some(checker),
            allow_dirty: true,
            fail_on_wrong: true,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        })
        .unwrap();

        let report: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("sat-delta-report.json")).unwrap(),
        )
        .unwrap();
        let records = report["records"].as_array().unwrap();
        let sat_row = records
            .iter()
            .find(|row| row["instance"] == "sat.cnf")
            .unwrap();
        let unsat_row = records
            .iter()
            .find(|row| row["instance"] == "unsat.cnf")
            .unwrap();
        assert_eq!(sat_row["model_status"], "valid");
        assert_eq!(sat_row["proof_status"], "n/a");
        assert_eq!(unsat_row["proof_status"], "valid");
        assert_eq!(unsat_row["model_status"], "n/a");
        assert_eq!(sat_row["stats"]["status"], "captured");
        assert_eq!(sat_row["stats"]["mode"], "dimacs-sat");
        assert_eq!(sat_row["stats"]["result"], "sat");
        assert_eq!(sat_row["stats"]["wall_time_ms"], 11);
        assert!(Path::new(sat_row["stats"]["path"].as_str().unwrap()).is_file());
        assert_ne!(sat_row["stats"]["sha256"], "");
        assert_eq!(sat_row["bcp_relocation"]["enabled"], true);
        assert_eq!(sat_row["bcp_relocation"]["attempts"], 2);
        assert_eq!(sat_row["bcp_relocation"]["moves"], 1);
        assert_eq!(sat_row["bcp_relocation"]["exercised"], true);
        assert_eq!(report["summaries"]["ay"]["solved"], 2);
        assert_eq!(
            report["ay_env"],
            serde_json::json!([
                "AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION=1",
                "AY_EMPTY_VALUE="
            ])
        );
        assert_eq!(sat_row["ay_env"], report["ay_env"]);

        let raw_tsv = fs::read_to_string(out_dir.join("raw.tsv")).unwrap();
        assert!(raw_tsv.contains("proof_status\tmodel_status"));
        assert!(raw_tsv.contains("ay_env_json"));
        assert!(raw_tsv.contains("stats_json_path\tstats_json_sha256\tstats_capture_status"));
        assert!(raw_tsv.contains("captured\tdimacs-sat\tsat\t11\ttrue\t2\t1\t1"));
        assert!(raw_tsv.contains("AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION=1"));
        assert!(raw_tsv.contains("proof-checker.argv"));

        let scoreboard = fs::read_to_string(out_dir.join("scoreboard.md")).unwrap();
        assert!(scoreboard.contains("AY env: `AY_SAT_BCP_LEARNED_1963_TRUE_TAIL_RELOCATION=1"));
        assert!(scoreboard.contains(AY_ENV_PROVENANCE_NOTE));
        assert!(scoreboard.contains("## Stats Capture"));
        assert!(scoreboard.contains("| `ay` | `sat.cnf` | `captured`"));
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn sat_delta_gives_ay_cleanup_grace_but_scores_after_budget_as_timeout() {
        let tmp = tempfile::tempdir().unwrap();
        let cnf = tmp.path().join("slow.cnf");
        let manifest = tmp.path().join("manifest.csv");
        let out_dir = tmp.path().join("out");
        let solver = tmp.path().join("fake-ay-timeout.sh");
        fs::write(&cnf, "p cnf 1 1\n1 0\n").unwrap();
        fs::write(
            &manifest,
            format!(
                "path,result,family,category\n{},sat,fixture,timeout\n",
                cnf.display()
            ),
        )
        .unwrap();
        fs::write(
            &solver,
            r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  printf 'ay fake timeout 0000000\n'
  exit 0
fi
proof=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --proof)
      proof="$2"
      shift 2
      ;;
    --proof-format|--sat-variant)
      shift 2
      ;;
    --timeout=*|--stats-json|solve|--no-verify-proof)
      shift
      ;;
    *)
      shift
      ;;
  esac
done
printf 'stale proof bytes\n' > "$proof"
sleep 1.1
rm -f "$proof"
printf 's UNKNOWN\n'
printf '{"mode":"dimacs-sat","result":"unknown","wall_time_ms":1100}\n' >&2
"#,
        )
        .unwrap();
        make_executable(&solver);

        cmd_sat_delta(SatDeltaArgs {
            manifest: Some(manifest),
            benchmark_root: tmp.path().to_path_buf(),
            out_dir: out_dir.clone(),
            ay: solver,
            ay_env: Vec::new(),
            reference_solvers: Vec::new(),
            timeout_sec: 1.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: None,
            allow_dirty: true,
            fail_on_wrong: true,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        })
        .unwrap();

        let report: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("sat-delta-report.json")).unwrap(),
        )
        .unwrap();
        let row = report["records"].as_array().unwrap().first().unwrap();
        assert_eq!(row["actual"], "timeout");
        assert_eq!(row["timeout"], true);
        assert_eq!(row["invalid"], false);
        assert_eq!(report["summaries"]["ay"]["timeout"], 1);
        assert!(
            !Path::new(row["proof_path"].as_str().unwrap()).exists(),
            "AY cleanup grace should let the solver remove non-UNSAT proof sidecars"
        );
    }

    #[cfg(unix)]
    #[test]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn sat_delta_keeps_ay_env_and_stats_flag_off_reference_solvers() {
        let tmp = tempfile::tempdir().unwrap();
        let cnf = tmp.path().join("sat.cnf");
        let manifest = tmp.path().join("manifest.csv");
        let out_dir = tmp.path().join("out");
        let ay_solver = tmp.path().join("fake-ay.sh");
        let reference_solver = tmp.path().join("fake-ref.sh");
        fs::write(&cnf, "p cnf 1 1\n1 0\n").unwrap();
        fs::write(
            &manifest,
            format!(
                "path,result,family,category\n{},sat,fixture,sat\n",
                cnf.display()
            ),
        )
        .unwrap();
        fs::write(
            &ay_solver,
            r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  printf 'ay fake 0000000\n'
  exit 0
fi
if [ "${AY_SAT_DELTA_ENV_ISOLATION:-}" != "1" ]; then
  printf 'missing ay-only env\n' >&2
  exit 64
fi
saw_stats=0
while [ "$#" -gt 0 ]; do
  case "$1" in
    --stats-json)
      saw_stats=1
      shift
      ;;
    --proof)
      shift 2
      ;;
    --proof-format|--sat-variant)
      shift 2
      ;;
    --timeout=*|solve|--no-verify-proof)
      shift
      ;;
    *)
      shift
      ;;
  esac
done
if [ "$saw_stats" != "1" ]; then
  printf 'missing --stats-json\n' >&2
  exit 65
fi
printf 's SATISFIABLE\nv 1 0\n'
printf '{"mode":"dimacs-sat","result":"sat","wall_time_ms":9,"sat.bcp_learned_1963_true_tail_relocation_enabled":true,"sat.bcp_learned_1963_true_tail_relocation_attempts":1,"sat.bcp_learned_1963_true_tail_relocation_moves":0}\n' >&2
"#,
        )
        .unwrap();
        fs::write(
            &reference_solver,
            r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  printf 'reference fake 0000000\n'
  exit 0
fi
for arg in "$@"; do
  if [ "$arg" = "--stats-json" ]; then
    printf 'reference received --stats-json\n' >&2
    exit 70
  fi
done
if [ "${AY_SAT_DELTA_ENV_ISOLATION+x}" = "x" ]; then
  printf 'reference received ay-only env\n' >&2
  exit 71
fi
printf 's SATISFIABLE\n'
"#,
        )
        .unwrap();
        make_executable(&ay_solver);
        make_executable(&reference_solver);

        cmd_sat_delta(SatDeltaArgs {
            manifest: Some(manifest),
            benchmark_root: tmp.path().to_path_buf(),
            out_dir: out_dir.clone(),
            ay: ay_solver,
            ay_env: vec![("AY_SAT_DELTA_ENV_ISOLATION".to_string(), "1".to_string())],
            reference_solvers: vec![("ref".to_string(), reference_solver)],
            timeout_sec: 2.0,
            sat_variant: "default".to_string(),
            proof_format: "lrat".to_string(),
            proof_checker: None,
            allow_dirty: true,
            fail_on_wrong: true,
            fail_on_ay_ref_loss: false,
            require_bcp_relocation_exercise: false,
            require_bcp_search_inplace_watch_scan_exercise: false,
            require_dense_mutex_focused_restart_gate_exercise: false,
        })
        .unwrap();

        let report: serde_json::Value = serde_json::from_str(
            &fs::read_to_string(out_dir.join("sat-delta-report.json")).unwrap(),
        )
        .unwrap();
        let records = report["records"].as_array().unwrap();
        let ay_row = records.iter().find(|row| row["solver"] == "ay").unwrap();
        let ref_row = records.iter().find(|row| row["solver"] == "ref").unwrap();
        let ay_argv = ay_row["command_argv"].as_array().unwrap();
        let ref_argv = ref_row["command_argv"].as_array().unwrap();

        assert!(ay_argv.iter().any(|arg| arg == "--stats-json"));
        assert!(!ref_argv.iter().any(|arg| arg == "--stats-json"));
        assert_eq!(
            ay_row["ay_env"],
            serde_json::json!(["AY_SAT_DELTA_ENV_ISOLATION=1"])
        );
        assert_eq!(ref_row["ay_env"], serde_json::json!([]));
        assert_eq!(ay_row["stats"]["status"], "captured");
        assert_eq!(ref_row["stats"]["status"], "not-applicable");
        assert!(ref_row["bcp_relocation"]["enabled"].is_null());
    }

    fn clean_git(commit: &str) -> GitProvenance {
        GitProvenance {
            source_commit: commit.to_string(),
            source_commit_short: commit.chars().take(10).collect(),
            source_branch: "main".to_string(),
            source_dirty: false,
            source_dirty_entries: 0,
            source_git_status_sha256: sha256_bytes(b""),
            source_git_status_short: String::new(),
        }
    }

    fn dummy_binary(path: &str, stamp: &str, profile: &str) -> BinaryProvenance {
        BinaryProvenance {
            path: path.to_string(),
            exists: true,
            executable: true,
            sha256: "sha".to_string(),
            size_bytes: Some(1),
            mtime_epoch: Some(1),
            version: Some(format!("ay 0.10.0+build.1.{stamp}@now")),
            build_profile: if profile.is_empty() {
                None
            } else {
                Some(profile.to_string())
            },
        }
    }

    fn dummy_record() -> RunRecord {
        RunRecord {
            solver: "ay".to_string(),
            instance: "b.cnf".to_string(),
            path: "b.cnf".to_string(),
            expected: "unknown".to_string(),
            actual: "unknown".to_string(),
            family: "f".to_string(),
            category: "c".to_string(),
            elapsed_s: 10.0,
            par2_s: 20.0,
            exit_code: None,
            wrong: false,
            invalid: false,
            proof_status: "n/a".to_string(),
            model_status: "n/a".to_string(),
            timeout: true,
            binary_path: "ay".to_string(),
            binary_sha256: "sha".to_string(),
            binary_size_bytes: Some(1),
            binary_mtime_epoch: Some(1),
            command_path: "cmd".to_string(),
            command_sha256: "cmd-sha".to_string(),
            command_argv: vec!["ay".to_string(), "solve".to_string(), "b.cnf".to_string()],
            command_display: "ay solve b.cnf".to_string(),
            ay_env: Vec::new(),
            stats: StatsCapture::not_applicable(),
            bcp_relocation: BcpRelocationStats::none(),
            bcp_search_inplace_watch_scan: BcpSearchInplaceWatchScanStats::none(),
            dense_mutex_focused_restart_gate: DenseMutexFocusedRestartGateStats::none(),
            proof_path: "proof.out".to_string(),
            proof_checker_command_path: String::new(),
            proof_checker_command_sha256: String::new(),
            proof_checker_exit_code: None,
            proof_checker_stdout: String::new(),
            proof_checker_stderr: String::new(),
            stdout: "out".to_string(),
            stderr: "err".to_string(),
        }
    }

    #[test]
    fn sat_delta_summary_counts_memout_separately() {
        let mut record = dummy_record();
        record.actual = "memout".to_string();
        record.timeout = false;
        let summary = summarize_rows(&[&record]);
        assert_eq!(summary.memout, 1);
        assert_eq!(summary.timeout, 0);
        assert_eq!(summary.unknown, 0);
        assert_eq!(summary.total, summary.solved + summary.memout);
    }

    #[cfg(unix)]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn make_executable(path: &Path) {
        use std::os::unix::fs::PermissionsExt;

        let mut perms = fs::metadata(path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(path, perms).unwrap();
    }

    #[cfg(not(unix))]
    #[cfg(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        all(target_os = "linux", not(target_env = "uclibc"))
    ))]
    fn make_executable(_path: &Path) {}
}
