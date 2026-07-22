// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rust-owned SAT-COMP matrix preflight.
//!
//! This is the first consolidation step away from `scripts/satcomp_matrix.py`.
//! It owns the score-bearing validation path for SAT models and UNSAT proofs;
//! Python compatibility scripts can remain as shims while the remaining
//! reporting surface is ported.

use std::collections::BTreeMap;
use std::env;
use std::fs::{self, File};
use std::io::{BufRead, BufReader, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

use anyhow::{bail, Context, Result};
use clap::{Args, Subcommand};
use serde_json::{json, Value as JsonValue};
use sha2::{Digest, Sha256};
use wait_timeout::ChildExt;

const DEFAULT_SUBMISSION_ROOT: &str = "target/sat26-submission";
const DEFAULT_OUTPUT_DIR: &str = "target/satcomp-matrix";
const DEFAULT_OFFICIAL_MIRROR_ROOT: &str = "win-all-software-proof-competitions";
const EXTERNAL_CHECKER_VERDICT_SCHEMA: &str = "ay.fmla-main-lrat-external-checker-verdict/v1";
const EXTERNAL_CHECKER_VERDICT_ARTIFACT: &str = "fmla-main-lrat-external-checker-verdict.json";
const FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_ARTIFACT: &str =
    "fmla-main-lrat-postcheck-admission-replay.json";
const FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_REPORT: &str =
    "fmla-main-lrat-postcheck-admission-report.json";
const FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SUMMARY_TSV: &str =
    "fmla-main-lrat-postcheck-admission-replay.tsv";
const FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_ENV: &str =
    "AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY";
const FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_ENV: &str = "AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT";
const FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA: &str =
    "ay.fmla-learned-lrat-dry-run-proof-artifact/v1";
const FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_CANDIDATES: &[&str] = &[
    "fmla-learned-lrat-dry-run-proof-artifact.json",
    "fmla-learned-lrat-dry-run-artifact.json",
    "learned-lrat-dry-run-proof-artifact.json",
    "learned_lrat_dry_run_artifact.json",
];
const FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT_PATH_FIELDS: &[&str] = &[
    "fmla_learned_lrat_dry_run_artifact",
    "fmla_learned_lrat_dry_run_artifact_path",
    "learned_lrat_dry_run_artifact",
    "learned_lrat_dry_run_artifact_path",
];
const FMLA_MATERIALIZER_ATTEMPTS_COUNTER: &str =
    "sat.decompose_lrat_preflight_main_rewrite_materializer_attempts";
const FMLA_MATERIALIZER_PROOF_EMIT_RECORDS_SEEN_COUNTER: &str =
    "sat.decompose_lrat_preflight_main_rewrite_materializer_proof_emit_records_seen";
const FMLA_MATERIALIZER_RECORDS_COUNTER: &str =
    "sat.decompose_lrat_preflight_main_rewrite_materializer_records";
const FMLA_MATERIALIZER_FAIL_CLOSED_COUNTER: &str =
    "sat.decompose_lrat_preflight_main_rewrite_materializer_fail_closed";
const FMLA_MATERIALIZER_MISSING_RUNTIME_RECORDS_COUNTER: &str =
    "sat.decompose_lrat_preflight_main_rewrite_materializer_missing_runtime_records";
const FMLA_PREPROCESS_TX_FAIL_CLOSED_COUNTER: &str = "sat.preprocess_tx_fail_closed";
const FMLA_PREPROCESS_TX_COMMITTED_COUNTER: &str = "sat.preprocess_tx_committed";
const FMLA_POSTCHECK_COUNTER_FIELDS: &[&str] = &[
    FMLA_MATERIALIZER_ATTEMPTS_COUNTER,
    FMLA_MATERIALIZER_PROOF_EMIT_RECORDS_SEEN_COUNTER,
    FMLA_MATERIALIZER_RECORDS_COUNTER,
    FMLA_MATERIALIZER_FAIL_CLOSED_COUNTER,
    FMLA_MATERIALIZER_MISSING_RUNTIME_RECORDS_COUNTER,
    FMLA_PREPROCESS_TX_FAIL_CLOSED_COUNTER,
    FMLA_PREPROCESS_TX_COMMITTED_COUNTER,
];
const SAT_MODEL_CHECK_ARTIFACT: &str = "sat-model-check.json";
const SAT_MODEL_CHECK_ARTIFACT_SCHEMA: &str = "ay.satcomp-model-check/v1";
const STATS_JSON_SCHEMA: &str = "ay.stats-json/v1";
const SATCOMP_MATRIX_EVIDENCE_SCHEMA: &str = "ay.satcomp-matrix-evidence-summary/v1";
const STALE_NON_AUTHORITATIVE_PROOF_STATUS: &str = "stale_non_authoritative";
const OFFICIAL_MIRROR_MANIFEST_CANDIDATES: &[&str] = &[
    "benchmarks/sat/satcomp2026-main/manifest.csv",
    "benchmarks/sat/satcomp2026/manifest.csv",
    "satcomp/2026/main/manifest.csv",
    "sat/2026/main/manifest.csv",
];
const OFFICIAL_MIRROR_DIR_CANDIDATES: &[&str] = &[
    "benchmarks/sat/satcomp2026-main",
    "benchmarks/sat/satcomp2026",
    "satcomp/2026/main",
    "sat/2026/main",
    "benchmarks/sat",
];
const SAT_NATIVE_HELPER_ARTIFACT: &str = "sat-native-code-helpers";
const SAT_NATIVE_HELPER_COUNTER: &str = "sat_native_code_helper_applications";
const SAT_CONFLICT_ANALYSIS_COUNTER: &str = "sat.conflict_analysis_native_applications";
const SAT_REQUIRED_EVIDENCE_COUNTERS: &[&str] = &[
    "sat_learned_clause_candidate_applications",
    "solver_program.sat_whole_loop.installs",
    "solver_program.sat_whole_loop.applies",
    SAT_NATIVE_HELPER_COUNTER,
    SAT_CONFLICT_ANALYSIS_COUNTER,
    "sat.subsumption_native_applications",
];
const FMLA_EQUIV_CHAIN_4_6_6_MARKER: &str = "FmlaEquivChain_4_6_6";
const FMLA_RECONSTRUCTED_MODEL_CHECKER: &str = "the development design notes";
const FMLA_RECONSTRUCTED_MODEL_REQUIRED_VALID_PACKET_FIELDS: &[&str] = &[
    "reconstructed_original_dimacs_model_original_path",
    "reconstructed_original_dimacs_model_original_sha256",
    "reconstructed_original_dimacs_model_solver_stdout",
    "reconstructed_original_dimacs_model_solver_stdout_sha256",
    "reconstructed_original_dimacs_model_stdout",
    "reconstructed_original_dimacs_model_stdout_sha256",
    "reconstructed_original_dimacs_model_stdout_present",
    "reconstructed_original_dimacs_model_stdout_matches_solver_stdout",
    "reconstructed_original_dimacs_model_reconstruction_source",
    "reconstructed_original_dimacs_model_check_command",
    "reconstructed_original_dimacs_model_checker_exit_code",
    "reconstructed_original_dimacs_model_verdict",
    "reconstructed_original_dimacs_model_verdict_written",
    "reconstructed_original_dimacs_model_packet_status",
];
const FMLA_RECONSTRUCTED_MODEL_REQUIRED_COMMAND_FLAGS: &[&str] = &[
    "--original-dimacs",
    "--check-reconstructed-model",
    "--verdict-out",
];
const FMLA_RECONSTRUCTED_MODEL_SHA256_FIELDS: &[&str] = &[
    "reconstructed_original_dimacs_model_original_sha256",
    "reconstructed_original_dimacs_model_solver_stdout_sha256",
    "reconstructed_original_dimacs_model_stdout_sha256",
];
const DESTRUCTIVE_TRANSFORM_ACTIVITY_COUNTER_FIELDS: &[&str] = &[
    "sat.bve_eliminated",
    "sat.bve_fast_elim_vars",
    "sat.bve_fast_elim_clauses",
    "sat.bve_cls_removed",
    "sat.bve_resolvents",
    "sat.bve_tautologies",
    "sat.bve_bw_subsumed",
    "sat.bve_bw_strengthened",
    "sat.bve_bw_units",
    "sat.factor_count",
    "sat.factor_rounds",
    "sat.sweep_lits_rwt",
    "sat.sweep_rounds",
    "sat.decomp_rounds",
    "sat.decomp_subst",
    "sat.decompose_lrat_preflight_attempts",
    "sat.decompose_lrat_preflight_candidate_count",
    "sat.decompose_lrat_preflight_no_substitution",
    "sat.decompose_lrat_preflight_empty_candidates",
    "sat.decompose_lrat_preflight_slices",
    "sat.decompose_lrat_preflight_rejected",
    "sat.decompose_lrat_preflight_missing_source_id",
    "sat.decompose_lrat_preflight_missing_chain_edge_id",
    "sat.decompose_lrat_preflight_missing_equiv_chain",
    "sat.decompose_lrat_preflight_malformed_rewrite",
    "sat.decompose_lrat_preflight_contradiction",
    "sat.decompose_lrat_preflight_missing_level0_unit_id",
    "sat.decompose_lrat_preflight_planned_add_rejected",
    "sat.decompose_lrat_preflight_missing_substitution_hint",
    "sat.decompose_lrat_preflight_missing_transient_equiv_id",
    "sat.decompose_lrat_preflight_proof_obligations",
    "sat.decompose_lrat_preflight_reconstruction_witnesses",
    "sat.decompose_lrat_preflight_main_rewrite_materializer_attempts",
    "sat.decompose_lrat_preflight_main_rewrite_materializer_proof_emit_records_seen",
    "sat.decompose_lrat_preflight_main_rewrite_materializer_records",
    "sat.decompose_lrat_preflight_main_rewrite_materializer_fail_closed",
    "sat.decompose_lrat_preflight_main_rewrite_materializer_missing_runtime_records",
    "sat.decompose_lrat_preflight_fmla_lift_destructive_allowed",
];
const PREPROCESS_TX_COUNTER_FIELDS: &[&str] = &[
    "sat.preprocess_tx_started",
    "sat.preprocess_tx_attempted",
    "sat.preprocess_tx_committed",
    "sat.preprocess_tx_rolled_back",
    "sat.preprocess_tx_fail_closed",
    "sat.preprocess_tx_rejected",
    "sat.preprocess_tx_proof_obligation_not_required",
    "sat.preprocess_tx_proof_obligation_satisfied",
    "sat.preprocess_tx_proof_obligation_rejected",
    "sat.preprocess_tx_proof_obligation_pending",
    "sat.preprocess_tx_reconstruction_witness_not_applicable",
    "sat.preprocess_tx_reconstruction_witness_present",
    "sat.preprocess_tx_reconstruction_witness_missing",
    "sat.preprocess_tx_touched_variables_total",
    "sat.preprocess_tx_eliminated_variables_total",
    "sat.preprocess_tx_equivalent_variables_total",
    "sat.preprocess_tx_planned_substitutions_total",
    "sat.preprocess_tx_max_mutation_epoch",
    "sat.preprocess_tx_active",
    "sat.preprocess_tx_retained_completed",
    "sat.preprocess_tx_fail_closed_model_reconstruction_witness_missing",
    "sat.preprocess_tx_fail_closed_decompose_lrat_preflight_rejected",
    "sat.preprocess_tx_fail_closed_decompose_lrat_clamped_after_dry_run",
    "sat.preprocess_tx_fail_closed_other",
    "sat.preprocess_tx_rolled_back_other",
];
const PREPROCESS_TX_FMLA_OBLIGATION_REJECTION_FIELDS: &[&str] = &[
    "sat.preprocess_tx_fail_closed",
    "sat.preprocess_tx_rejected",
    "sat.preprocess_tx_proof_obligation_rejected",
    "sat.preprocess_tx_proof_obligation_pending",
    "sat.preprocess_tx_reconstruction_witness_missing",
    "sat.preprocess_tx_active",
    "sat.preprocess_tx_fail_closed_model_reconstruction_witness_missing",
    "sat.preprocess_tx_fail_closed_decompose_lrat_preflight_rejected",
    "sat.preprocess_tx_fail_closed_decompose_lrat_clamped_after_dry_run",
    "sat.preprocess_tx_fail_closed_other",
];
const PREPROCESS_TX_PROOF_DISPOSITION_FIELDS: &[&str] = &[
    "sat.preprocess_tx_proof_obligation_not_required",
    "sat.preprocess_tx_proof_obligation_satisfied",
    "sat.preprocess_tx_proof_obligation_rejected",
    "sat.preprocess_tx_proof_obligation_pending",
];
const PREPROCESS_TX_RECONSTRUCTION_DISPOSITION_FIELDS: &[&str] = &[
    "sat.preprocess_tx_reconstruction_witness_not_applicable",
    "sat.preprocess_tx_reconstruction_witness_present",
    "sat.preprocess_tx_reconstruction_witness_missing",
];

const TSV_COLUMNS: &[&str] = &[
    "suite",
    "track",
    "ai_class",
    "variant",
    "proof_mode",
    "proof_format",
    "jobs",
    "official_main_sequential",
    "instance",
    "benchmark",
    "path",
    "run_input",
    "expected",
    "actual",
    "verdict",
    "family",
    "category",
    "elapsed_s",
    "runtime_ms",
    "par2_s",
    "exit",
    "exit_code",
    "wrong",
    "invalid",
    "proof_status",
    "ay_lrat_status",
    "proof_checker_status",
    "external_proof_checker_verdict_artifact",
    "external_proof_checker_verdict_artifact_sha256",
    "external_proof_checker_verdict_artifact_schema",
    "external_proof_checker_verdict",
    "external_proof_checker_proof_out_path",
    "fmla_postcheck_admission_replay_status",
    "fmla_postcheck_admission_replay_artifact",
    "fmla_postcheck_admission_replay_artifact_sha256",
    "fmla_postcheck_admission_replay_materializer_records",
    "fmla_postcheck_admission_replay_external_checker_artifact_rows",
    "fmla_postcheck_admission_replay_preprocess_tx_committed",
    "fmla_learned_lrat_dry_run_artifact",
    "fmla_learned_lrat_dry_run_artifact_sha256",
    "fmla_learned_lrat_dry_run_artifact_schema",
    "fmla_main_lrat_authority_replay_env",
    "fmla_main_lrat_authority_replay_env_value",
    "fmla_main_lrat_authority_replay_env_value_sha256",
    "fmla_main_lrat_authority_replay_env_status",
    "proof_path",
    "proof_bytes",
    "proof_sha256",
    "model_status",
    "model_checker_artifact",
    "model_checker_artifact_sha256",
    "model_checker_artifact_schema",
    "model_checker_formula",
    "model_checker_stdout",
    "model_checker_command_json",
    "model_checker_exit_status",
    "proof_dir",
    "run_path",
    "timeout_s",
    "ay",
    "ay_sha256",
    "binary_path",
    "binary_sha256",
    "binary_size_bytes",
    "binary_mtime_epoch",
    "binary_executable",
    "stdout",
    "stderr",
];

/// Rust-owned SAT-COMP matrix preflight commands.
// clap subcommand enum: constructed once at CLI parse; boxing arg fields would
// break the derive and buys nothing at this scale.
#[allow(clippy::large_enum_variant)]
#[derive(Subcommand)]
pub(crate) enum SatCompMatrixCommand {
    /// Run generated SAT-COMP wrappers and write scoreboard artifacts.
    Run(SatCompMatrixRunOptions),
    /// Emit baseline/candidate evidence JSON from an existing score-bearing matrix.
    #[command(name = "evidence-summary")]
    EvidenceSummary(SatCompMatrixEvidenceSummaryOptions),
}

#[derive(Args, Clone, Debug)]
pub(crate) struct SatCompMatrixRunOptions {
    #[arg(long, default_value = "sat-main-2026-official-mirror")]
    suite: String,
    #[arg(long, default_value = "main")]
    track: String,
    #[arg(long, default_value = "regular")]
    ai_class: String,
    #[arg(long, default_value = "default")]
    variants: String,
    #[arg(long, default_value = "drat")]
    proof_format: String,
    #[arg(long, default_value = DEFAULT_SUBMISSION_ROOT)]
    submission_root: PathBuf,
    /// Run one explicit run.sh path instead of a generated root.
    #[arg(long)]
    run_sh: Option<PathBuf>,
    #[arg(long, default_value = DEFAULT_OUTPUT_DIR)]
    output: PathBuf,
    #[arg(long)]
    manifest: Option<PathBuf>,
    #[arg(long)]
    benchmarks_dir: Option<PathBuf>,
    /// Keep only manifest/directory rows with this exact family. May be repeated.
    #[arg(long = "filter-family")]
    filter_family: Vec<String>,
    /// Run one instance path.
    #[arg(long)]
    instance: Option<PathBuf>,
    #[arg(long, default_value = "unknown")]
    expected: String,
    #[arg(long, default_value = "ad-hoc")]
    family: String,
    #[arg(long, default_value = "ad-hoc")]
    category: String,
    #[arg(long)]
    timeout_sec: Option<f64>,
    #[arg(long)]
    limit: Option<usize>,
    #[arg(long)]
    soundness: bool,
    #[arg(long)]
    fail_on_wrong: bool,
    #[arg(long, default_value = "none")]
    proof_checker: String,
    #[arg(long)]
    require_total: Option<usize>,
    #[arg(long)]
    official_mirror_root: Option<PathBuf>,
    #[arg(long)]
    require_official_mirror: bool,
    #[arg(long)]
    allow_smoke: bool,
    /// Opt in to a checked two-pass Fmla Main/LRAT authority replay run.
    #[arg(long)]
    fmla_main_lrat_authority_replay_two_pass: bool,
}

#[derive(Args, Clone, Debug)]
pub(crate) struct SatCompMatrixEvidenceSummaryOptions {
    /// Existing SAT-COMP matrix scoreboard.json.
    #[arg(long)]
    scoreboard: PathBuf,
    /// Output path for the emitted evidence JSON.
    #[arg(long)]
    output: PathBuf,
    /// Scoreboard variant to summarize.
    #[arg(long, default_value = "default")]
    variant: String,
    /// Candidate mode represented by the stats artifacts.
    #[arg(long, value_enum)]
    candidate_mode: EvidenceCandidateMode,
    /// Per-instance stats JSON file or directory. May be repeated.
    #[arg(long = "stats-json")]
    stats_json: Vec<PathBuf>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, clap::ValueEnum)]
#[clap(rename_all = "kebab-case")]
enum EvidenceCandidateMode {
    Off,
    Current,
}

impl EvidenceCandidateMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::Off => "off",
            Self::Current => "current",
        }
    }
}

#[derive(Clone, Debug)]
struct Benchmark {
    path: PathBuf,
    expected: String,
    family: String,
    category: String,
    name: String,
}

#[derive(Clone, Debug)]
struct ParsedOutput {
    actual: String,
    invalid_reason: Option<String>,
    has_model_lines: bool,
}

#[derive(Clone, Debug, Default)]
struct ProofEvidence {
    proof_status: String,
    ay_lrat_status: String,
    proof_checker_status: String,
    external_artifact: String,
    external_artifact_sha256: String,
    external_artifact_schema: String,
    external_verdict: String,
    external_proof_out_path: String,
}

#[derive(Clone, Debug)]
struct ExternalCheckerRunEvidence {
    checker_path: PathBuf,
    checker_argv: Vec<String>,
    checker_exit_code: i32,
    checker_stdout: String,
    checker_stderr: String,
}

#[derive(Clone, Debug)]
struct RetainedFmlaLearnedLratDryRunArtifact {
    path: PathBuf,
    sha256: String,
    schema: String,
}

#[derive(Clone, Debug)]
struct FmlaMainLratAuthorityReplayHandoff {
    replay_artifact: PathBuf,
    replay_artifact_sha256: String,
}

#[derive(Clone, Debug, Default)]
struct FmlaPostcheckAdmissionEvidence {
    status: String,
    artifact: String,
    artifact_sha256: String,
    materializer_records: String,
    external_checker_artifact_rows: String,
    preprocess_tx_committed: String,
    learned_lrat_dry_run_artifact: String,
    learned_lrat_dry_run_artifact_sha256: String,
    learned_lrat_dry_run_artifact_schema: String,
    main_lrat_authority_replay_env: String,
    main_lrat_authority_replay_env_value: String,
    main_lrat_authority_replay_env_value_sha256: String,
    main_lrat_authority_replay_env_status: String,
}

#[derive(Clone, Debug)]
struct ModelEvidence {
    status: String,
    artifact: String,
    artifact_sha256: String,
    artifact_schema: String,
    formula: String,
    stdout: String,
    checker_command_json: String,
    checker_exit_status: String,
}

impl Default for ModelEvidence {
    fn default() -> Self {
        Self {
            status: "n/a".to_string(),
            artifact: String::new(),
            artifact_sha256: String::new(),
            artifact_schema: String::new(),
            formula: String::new(),
            stdout: String::new(),
            checker_command_json: String::new(),
            checker_exit_status: String::new(),
        }
    }
}

#[derive(Clone, Debug)]
struct Record {
    fields: BTreeMap<String, String>,
}

impl Record {
    fn get(&self, key: &str) -> &str {
        self.fields.get(key).map_or("", String::as_str)
    }

    fn truthy(&self, key: &str) -> bool {
        matches!(self.get(key), "1" | "true" | "True")
    }
}

#[derive(Default)]
struct Summary {
    total: usize,
    solved: usize,
    solved_sat: usize,
    solved_unsat: usize,
    expected_sat: usize,
    expected_unsat: usize,
    sat_model_valid: usize,
    sat_model_invalid: usize,
    unsat_proof_valid: usize,
    unsat_proof_invalid: usize,
    unknown: usize,
    timeout: usize,
    error: usize,
    wrong: usize,
    invalid: usize,
    par2_total: f64,
    par2_avg: f64,
    timeout_sec: f64,
    families: Option<BTreeMap<String, Summary>>,
}

pub(crate) fn run(cmd: SatCompMatrixCommand) -> Result<()> {
    match cmd {
        SatCompMatrixCommand::Run(opts) => run_matrix(&opts),
        SatCompMatrixCommand::EvidenceSummary(opts) => run_evidence_summary(&opts),
    }
}

fn run_matrix(opts: &SatCompMatrixRunOptions) -> Result<()> {
    if opts.fmla_main_lrat_authority_replay_two_pass
        && (opts.track != "main" || opts.proof_format != "lrat")
    {
        bail!(
            "valid Fmla Main/LRAT authority replay handoff required: \
             --fmla-main-lrat-authority-replay-two-pass only applies to \
             --track main --proof-format lrat (got --track {} --proof-format {})",
            opts.track,
            opts.proof_format
        );
    }
    let output_dir = absolute_path(&opts.output)?;
    fs::create_dir_all(&output_dir)
        .with_context(|| format!("creating output directory {}", output_dir.display()))?;

    let timeout_sec = opts
        .timeout_sec
        .unwrap_or_else(|| default_timeout_sec(&opts.suite));
    validate_limit_policy(opts)?;
    let mut benches = load_benchmarks(opts)?;
    apply_benchmark_filters(opts, &mut benches)?;
    if let Some(limit) = opts.limit {
        benches.truncate(limit);
    }
    check_official_mirror(opts, &benches)?;
    if let Some(required) = opts.require_total {
        if benches.len() != required {
            bail!(
                "suite {} has {} runnable benchmarks, expected {}",
                opts.suite,
                benches.len(),
                required
            );
        }
    }

    let variants = parse_variants(&opts.variants)?;
    let mut records_by_variant: BTreeMap<String, Vec<Record>> = BTreeMap::new();
    for variant in variants {
        let mut records = Vec::new();
        for bench in &benches {
            eprintln!("[satcomp-rust] {variant}: {}", bench.name);
            records.push(run_one(opts, bench, &variant, &output_dir, timeout_sec)?);
        }
        write_raw_tsv(
            &output_dir.join(format!("{variant}-raw.tsv")),
            records.as_slice(),
        )?;
        records_by_variant.insert(variant, records);
    }

    write_summary_outputs(&output_dir, &records_by_variant)?;
    let scoreboard = build_scoreboard(opts, &output_dir, &records_by_variant, timeout_sec);
    write_json_pretty(&output_dir.join("scoreboard.json"), &scoreboard)?;
    write_scoreboard_md(&output_dir.join("scoreboard.md"), &scoreboard)?;

    println!("raw/scoreboard output: {}", output_dir.display());
    println!(
        "summary jsonl: {}",
        output_dir.join("summary.jsonl").display()
    );
    println!("summary csv: {}", output_dir.join("summary.csv").display());
    println!(
        "scoreboard json: {}",
        output_dir.join("scoreboard.json").display()
    );
    println!(
        "scoreboard md: {}",
        output_dir.join("scoreboard.md").display()
    );

    if opts.fail_on_wrong {
        for (variant, records) in &records_by_variant {
            let summary = summarize_records(records, timeout_sec, true);
            if summary.wrong != 0 || summary.invalid != 0 {
                bail!(
                    "{variant} has wrong={} invalid={}",
                    summary.wrong,
                    summary.invalid
                );
            }
        }
    }

    Ok(())
}

fn run_evidence_summary(opts: &SatCompMatrixEvidenceSummaryOptions) -> Result<()> {
    let scoreboard_path = absolute_path(&opts.scoreboard)?;
    let output_path = absolute_path(&opts.output)?;
    let payload = build_evidence_summary(opts, &scoreboard_path)?;
    if let Some(parent) = output_path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("creating output directory {}", parent.display()))?;
    }
    write_json_pretty(&output_path, &payload)?;
    println!("evidence summary json: {}", output_path.display());
    Ok(())
}

fn build_evidence_summary(
    opts: &SatCompMatrixEvidenceSummaryOptions,
    scoreboard_path: &Path,
) -> Result<JsonValue> {
    let scoreboard = load_json_object(scoreboard_path)?;
    require_score_bearing_scoreboard(&scoreboard)?;

    let variants = scoreboard
        .get("variants")
        .and_then(JsonValue::as_object)
        .context("scoreboard missing variants object")?;
    let variant_data = variants.get(&opts.variant).with_context(|| {
        let known = variants.keys().cloned().collect::<Vec<_>>().join(", ");
        format!(
            "unknown evidence variant {:?}; known: {known}",
            opts.variant
        )
    })?;
    let summary = variant_data
        .get("summary")
        .and_then(JsonValue::as_object)
        .with_context(|| format!("variant {:?} missing summary", opts.variant))?;

    let rows = read_variant_raw_rows(
        variant_data,
        scoreboard_path.parent().unwrap_or(Path::new(".")),
    )?;
    require_raw_rows_match_summary(&rows, summary)?;
    require_summary_validation_counts_match(summary, &rows)?;
    require_score_bearing_row_validation(&rows)?;
    let expected_total = evidence_summary_expected_total(&scoreboard, rows.len())?;
    require_rows_inside_official_mirror(&rows, string_value(&scoreboard, "official_mirror_root"))?;

    let stats_paths = discover_evidence_stats_json(
        opts.stats_json.as_slice(),
        &scoreboard,
        &opts.variant,
        scoreboard_path.parent().unwrap_or(Path::new(".")),
    )?;
    if stats_paths.is_empty() {
        bail!("evidence summary requires at least one per-instance stats JSON artifact");
    }
    if stats_paths.len() != rows.len() {
        bail!(
            "evidence summary requires one stats JSON per scored row, got {} stats JSON artifact(s) for {} row(s)",
            stats_paths.len(),
            rows.len()
        );
    }
    let mut stats_docs = Vec::new();
    for path in &stats_paths {
        stats_docs.push(load_stats_json(path)?);
    }
    let counters = merge_stats_counters(&stats_docs);
    require_candidate_mode_counters(opts.candidate_mode, &counters)?;
    let totals = summarize_evidence_totals(summary, &rows);
    let corpus_fingerprint = string_value(&scoreboard, "corpus_fingerprint")
        .filter(|value| !value.is_empty())
        .unwrap_or_else(|| raw_rows_corpus_fingerprint(&rows));

    Ok(json!({
        "schema": STATS_JSON_SCHEMA,
        "mode": "dimacs-sat",
        "competition_jit": build_competition_jit_evidence(opts.candidate_mode, &counters)?,
        "counters": counters,
        "totals": totals,
        "satcomp_matrix": build_satcomp_matrix_provenance(
            &scoreboard,
            &corpus_fingerprint,
            &opts.variant,
            stats_docs.len(),
            expected_total,
        ),
    }))
}

fn run_one(
    opts: &SatCompMatrixRunOptions,
    bench: &Benchmark,
    variant: &str,
    output_dir: &Path,
    timeout_sec: f64,
) -> Result<Record> {
    if opts.fmla_main_lrat_authority_replay_two_pass
        && opts.track == "main"
        && opts.proof_format == "lrat"
        && benchmark_matches_fmla_equiv_chain_4_6_6(bench, &bench.path)
    {
        let authority_pass = run_one_attempt(opts, bench, variant, output_dir, timeout_sec, None)?;
        let proof_path = PathBuf::from(authority_pass.get("proof_path"));
        let handoff =
            fmla_main_lrat_authority_replay_handoff_from_record(&authority_pass, &proof_path)
                .with_context(|| {
                    format!(
                "valid Fmla Main/LRAT authority replay handoff required for two-pass instance {}",
                bench.name
            )
                })?;
        return run_one_attempt(
            opts,
            bench,
            variant,
            output_dir,
            timeout_sec,
            Some(&handoff),
        );
    }

    run_one_attempt(opts, bench, variant, output_dir, timeout_sec, None)
}

fn run_one_attempt(
    opts: &SatCompMatrixRunOptions,
    bench: &Benchmark,
    variant: &str,
    output_dir: &Path,
    timeout_sec: f64,
    authority_replay_handoff: Option<&FmlaMainLratAuthorityReplayHandoff>,
) -> Result<Record> {
    let (solver_root, run_path) = solver_root_and_run_path(opts, variant)?;
    if !run_path.is_file() {
        bail!(
            "run.sh not found for variant {variant}: {}",
            run_path.display()
        );
    }

    let safe_name = safe_case_name(&bench.name);
    let case_dir = output_dir.join("runs").join(variant).join(safe_name);
    fs::create_dir_all(&case_dir)
        .with_context(|| format!("creating case directory {}", case_dir.display()))?;

    let run_input = decompress_if_needed(&bench.path, &case_dir)?;
    let proof_path = case_dir.join("proof.out");
    remove_if_exists(&proof_path)?;
    if authority_replay_handoff.is_none() {
        remove_if_exists(&external_checker_verdict_artifact_path(&proof_path))?;
    }
    let stdout_path = case_dir.join("stdout.txt");
    let stderr_path = case_dir.join("stderr.txt");
    let fmla_learned_lrat_dry_run_artifact_path =
        benchmark_matches_fmla_equiv_chain_4_6_6(bench, &run_input)
            .then(|| case_dir.join(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_CANDIDATES[0]));
    if let Some(path) = fmla_learned_lrat_dry_run_artifact_path.as_ref() {
        remove_if_exists(path)?;
    }

    let start = Instant::now();
    let (exit_code, timed_out) = run_wrapper(
        &run_path,
        &solver_root,
        &run_input,
        &case_dir,
        &stdout_path,
        &stderr_path,
        fmla_learned_lrat_dry_run_artifact_path.as_deref(),
        authority_replay_handoff,
        &proof_path,
        timeout_sec,
    )?;
    let elapsed = if timed_out {
        timeout_sec
    } else {
        start.elapsed().as_secs_f64()
    };

    let strict_gate =
        opts.soundness || opts.fail_on_wrong || opts.fmla_main_lrat_authority_replay_two_pass;
    let strict_evidence = strict_gate && !timed_out;
    let parsed = parse_solver_output_file(&stdout_path, exit_code, strict_gate)?;
    let actual = if timed_out {
        "timeout".to_string()
    } else {
        parsed.actual.clone()
    };
    let wrong = matches!(bench.expected.as_str(), "sat" | "unsat")
        && matches!(actual.as_str(), "sat" | "unsat")
        && bench.expected != actual;
    let proof_mode = if opts.track == "main" { "main" } else { "none" };

    let mut model_status = "n/a".to_string();
    let mut proof_status = "n/a".to_string();
    let mut ay_lrat_status = "n/a".to_string();
    let mut proof_checker_status = "n/a".to_string();
    let mut external = ProofEvidence::default();
    let mut model_evidence = ModelEvidence::default();
    let mut fmla_postcheck_evidence = FmlaPostcheckAdmissionEvidence::default();
    let retained_fmla_learned_lrat_dry_run_artifact =
        if fmla_learned_lrat_dry_run_artifact_path.is_some() {
            find_retained_fmla_learned_lrat_dry_run_artifact(&case_dir, &stderr_path)?
        } else {
            None
        };
    let mut invalid = !timed_out && parsed.invalid_reason.is_some();

    if strict_evidence && actual == "sat" {
        let model_checker_artifact = case_dir.join(SAT_MODEL_CHECK_ARTIFACT);
        model_evidence = verify_model_with_ay(
            &solver_root,
            &run_input,
            &stdout_path,
            &model_checker_artifact,
            timeout_sec,
        );
        model_status.clone_from(&model_evidence.status);
        invalid |= model_evidence.status != "valid";
        if proof_path.exists() && proof_path.metadata()?.len() > 0 {
            proof_status = "unexpected".to_string();
            invalid = true;
        }
    } else if actual == "sat" {
        model_status = "unchecked".to_string();
    }

    if actual == "unsat" {
        if strict_evidence && parsed.has_model_lines {
            model_status = "unexpected".to_string();
            invalid = true;
        }
        if proof_mode == "main" && matches!(opts.proof_format.as_str(), "lrat" | "drat") {
            external = verify_lrat_proof(opts, &solver_root, &run_input, &proof_path, timeout_sec)?;
            proof_status.clone_from(&external.proof_status);
            ay_lrat_status.clone_from(&external.ay_lrat_status);
            proof_checker_status.clone_from(&external.proof_checker_status);
            // The Fmla learned-LRAT post-check admission replay is LRAT-specific
            // machinery; it does not apply under DRAT.
            if strict_evidence
                && opts.proof_format == "lrat"
                && proof_status == "valid"
                && benchmark_matches_fmla_equiv_chain_4_6_6(bench, &run_input)
            {
                let fmla_counters = fmla_postcheck_counters_from_stderr(&stderr_path)?;
                fmla_postcheck_evidence = run_fmla_postcheck_admission_replay(
                    &solver_root,
                    &run_input,
                    &proof_path,
                    &case_dir,
                    &external,
                    &fmla_counters,
                    retained_fmla_learned_lrat_dry_run_artifact.as_ref(),
                    timeout_sec,
                )?;
            }
        } else {
            proof_status = "unchecked".to_string();
        }
        if strict_evidence && proof_status != "valid" {
            invalid = true;
        }
    } else if actual != "sat" {
        if strict_evidence && parsed.has_model_lines {
            model_status = "unexpected".to_string();
            invalid = true;
        }
        if proof_path.exists() {
            if proof_path
                .metadata()
                .map(|meta| meta.len() > 0)
                .unwrap_or(false)
            {
                proof_status = STALE_NON_AUTHORITATIVE_PROOF_STATUS.to_string();
            }
            fs::remove_file(&proof_path)
                .with_context(|| format!("removing non-UNSAT proof {}", proof_path.display()))?;
        }
        if let Some(reason) = &parsed.invalid_reason {
            if proof_status == "n/a" {
                proof_status.clone_from(reason);
            }
        }
    }

    if parsed.invalid_reason.is_some() && proof_status == "n/a" {
        proof_status = parsed.invalid_reason.clone().unwrap_or_default();
    }
    if fmla_postcheck_evidence
        .learned_lrat_dry_run_artifact
        .is_empty()
    {
        if let Some(artifact) = retained_fmla_learned_lrat_dry_run_artifact.as_ref() {
            retain_fmla_learned_lrat_dry_run_artifact_evidence(
                &mut fmla_postcheck_evidence,
                artifact,
            );
        }
    }

    let solved = matches!(actual.as_str(), "sat" | "unsat") && !wrong && !invalid;
    let par2 = if solved { elapsed } else { 2.0 * timeout_sec };
    let official_main_sequential = opts.track == "main"
        && opts.ai_class == "regular"
        && variant == "default"
        && opts.proof_format == "lrat";
    let solver_binary = solver_binary_path(&solver_root);
    let run_prov = runtime_provenance(solver_binary.as_deref(), timeout_sec)?;
    let proof_bytes = file_size_if_exists(&proof_path)?;
    let proof_sha = if proof_bytes > 0 {
        sha256_file(&proof_path)?
    } else {
        String::new()
    };

    let mut fields = BTreeMap::new();
    insert(&mut fields, "suite", &opts.suite);
    insert(&mut fields, "track", &opts.track);
    insert(&mut fields, "ai_class", &opts.ai_class);
    insert(&mut fields, "variant", variant);
    insert(&mut fields, "proof_mode", proof_mode);
    insert(&mut fields, "proof_format", &opts.proof_format);
    insert(&mut fields, "jobs", "1");
    insert(
        &mut fields,
        "official_main_sequential",
        if official_main_sequential {
            "true"
        } else {
            "false"
        },
    );
    insert(&mut fields, "instance", &bench.name);
    insert(&mut fields, "benchmark", &path_string(&bench.path));
    insert(&mut fields, "path", &path_string(&bench.path));
    insert(&mut fields, "run_input", &path_string(&run_input));
    insert(&mut fields, "expected", &bench.expected);
    insert(&mut fields, "actual", &actual);
    insert(&mut fields, "verdict", satcomp_verdict(&actual));
    insert(&mut fields, "family", &bench.family);
    insert(&mut fields, "category", &bench.category);
    insert(&mut fields, "elapsed_s", &format!("{elapsed:.6}"));
    insert(
        &mut fields,
        "runtime_ms",
        &format!("{}", (elapsed * 1000.0).round() as u64),
    );
    insert(&mut fields, "par2_s", &format!("{par2:.6}"));
    insert(
        &mut fields,
        "exit",
        &exit_code.map_or_else(String::new, |code| code.to_string()),
    );
    insert(
        &mut fields,
        "exit_code",
        &exit_code.map_or_else(String::new, |code| code.to_string()),
    );
    insert(&mut fields, "wrong", if wrong { "1" } else { "0" });
    insert(&mut fields, "invalid", if invalid { "1" } else { "0" });
    insert(&mut fields, "proof_status", &proof_status);
    insert(&mut fields, "ay_lrat_status", &ay_lrat_status);
    insert(&mut fields, "proof_checker_status", &proof_checker_status);
    insert(
        &mut fields,
        "external_proof_checker_verdict_artifact",
        &external.external_artifact,
    );
    insert(
        &mut fields,
        "external_proof_checker_verdict_artifact_sha256",
        &external.external_artifact_sha256,
    );
    insert(
        &mut fields,
        "external_proof_checker_verdict_artifact_schema",
        &external.external_artifact_schema,
    );
    insert(
        &mut fields,
        "external_proof_checker_verdict",
        &external.external_verdict,
    );
    insert(
        &mut fields,
        "external_proof_checker_proof_out_path",
        &external.external_proof_out_path,
    );
    insert(
        &mut fields,
        "fmla_postcheck_admission_replay_status",
        &fmla_postcheck_evidence.status,
    );
    insert(
        &mut fields,
        "fmla_postcheck_admission_replay_artifact",
        &fmla_postcheck_evidence.artifact,
    );
    insert(
        &mut fields,
        "fmla_postcheck_admission_replay_artifact_sha256",
        &fmla_postcheck_evidence.artifact_sha256,
    );
    insert(
        &mut fields,
        "fmla_postcheck_admission_replay_materializer_records",
        &fmla_postcheck_evidence.materializer_records,
    );
    insert(
        &mut fields,
        "fmla_postcheck_admission_replay_external_checker_artifact_rows",
        &fmla_postcheck_evidence.external_checker_artifact_rows,
    );
    insert(
        &mut fields,
        "fmla_postcheck_admission_replay_preprocess_tx_committed",
        &fmla_postcheck_evidence.preprocess_tx_committed,
    );
    insert(
        &mut fields,
        "fmla_learned_lrat_dry_run_artifact",
        &fmla_postcheck_evidence.learned_lrat_dry_run_artifact,
    );
    insert(
        &mut fields,
        "fmla_learned_lrat_dry_run_artifact_sha256",
        &fmla_postcheck_evidence.learned_lrat_dry_run_artifact_sha256,
    );
    insert(
        &mut fields,
        "fmla_learned_lrat_dry_run_artifact_schema",
        &fmla_postcheck_evidence.learned_lrat_dry_run_artifact_schema,
    );
    insert(
        &mut fields,
        "fmla_main_lrat_authority_replay_env",
        &fmla_postcheck_evidence.main_lrat_authority_replay_env,
    );
    insert(
        &mut fields,
        "fmla_main_lrat_authority_replay_env_value",
        &fmla_postcheck_evidence.main_lrat_authority_replay_env_value,
    );
    insert(
        &mut fields,
        "fmla_main_lrat_authority_replay_env_value_sha256",
        &fmla_postcheck_evidence.main_lrat_authority_replay_env_value_sha256,
    );
    insert(
        &mut fields,
        "fmla_main_lrat_authority_replay_env_status",
        &fmla_postcheck_evidence.main_lrat_authority_replay_env_status,
    );
    insert(&mut fields, "proof_path", &path_string(&proof_path));
    insert(&mut fields, "proof_bytes", &proof_bytes.to_string());
    insert(&mut fields, "proof_sha256", &proof_sha);
    insert(&mut fields, "model_status", &model_status);
    insert(
        &mut fields,
        "model_checker_artifact",
        &model_evidence.artifact,
    );
    insert(
        &mut fields,
        "model_checker_artifact_sha256",
        &model_evidence.artifact_sha256,
    );
    insert(
        &mut fields,
        "model_checker_artifact_schema",
        &model_evidence.artifact_schema,
    );
    insert(
        &mut fields,
        "model_checker_formula",
        &model_evidence.formula,
    );
    insert(&mut fields, "model_checker_stdout", &model_evidence.stdout);
    insert(
        &mut fields,
        "model_checker_command_json",
        &model_evidence.checker_command_json,
    );
    insert(
        &mut fields,
        "model_checker_exit_status",
        &model_evidence.checker_exit_status,
    );
    insert(&mut fields, "proof_dir", &path_string(&case_dir));
    insert(&mut fields, "run_path", &path_string(&run_path));
    for (key, value) in run_prov {
        insert(&mut fields, &key, &value);
    }
    let binary_path = fields.get("binary_path").cloned().unwrap_or_default();
    let binary_sha256 = fields.get("binary_sha256").cloned().unwrap_or_default();
    insert(&mut fields, "ay", &binary_path);
    insert(&mut fields, "ay_sha256", &binary_sha256);
    insert(&mut fields, "stdout", &path_string(&stdout_path));
    insert(&mut fields, "stderr", &path_string(&stderr_path));

    Ok(Record { fields })
}

fn run_wrapper(
    run_path: &Path,
    solver_root: &Path,
    run_input: &Path,
    case_dir: &Path,
    stdout_path: &Path,
    stderr_path: &Path,
    fmla_learned_lrat_dry_run_artifact_path: Option<&Path>,
    authority_replay_handoff: Option<&FmlaMainLratAuthorityReplayHandoff>,
    proof_path: &Path,
    timeout_sec: f64,
) -> Result<(Option<i32>, bool)> {
    let stdout = File::create(stdout_path)
        .with_context(|| format!("creating stdout {}", stdout_path.display()))?;
    let stderr = File::create(stderr_path)
        .with_context(|| format!("creating stderr {}", stderr_path.display()))?;

    let mut command = Command::new(run_path);
    command
        .arg(run_input)
        .arg(case_dir)
        .current_dir(solver_root)
        .env(
            "STAREXEC_WALLCLOCK_LIMIT",
            format!("{}", timeout_sec.ceil() as u64 + 5),
        )
        .env("AY_SATCOMP_MATRIX", "1");
    if let Some(path) = fmla_learned_lrat_dry_run_artifact_path {
        command.env(
            "AY_SAT_FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT",
            path_string(path),
        );
    }
    if let Some(handoff) = authority_replay_handoff {
        debug_assert!(is_hex_sha256(&handoff.replay_artifact_sha256));
        command
            .env(
                FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_ENV,
                path_string(&handoff.replay_artifact),
            )
            .env(
                FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT_ENV,
                path_string(proof_path),
            );
    }
    let mut child = command
        .stdout(Stdio::from(stdout))
        .stderr(Stdio::from(stderr))
        .spawn()
        .with_context(|| format!("running {}", run_path.display()))?;

    let timeout = Duration::from_secs_f64(timeout_sec + 8.0);
    match child.wait_timeout(timeout)? {
        Some(status) => Ok((status.code(), false)),
        None => {
            let _ = child.kill();
            let _ = child.wait();
            Ok((None, true))
        }
    }
}

fn verify_model_with_ay(
    solver_root: &Path,
    cnf_path: &Path,
    stdout_path: &Path,
    artifact_path: &Path,
    timeout_sec: f64,
) -> ModelEvidence {
    let mut evidence = ModelEvidence::default();
    let Some(ay) = ay_checker_path(solver_root) else {
        evidence.status = "error:ay-checker-missing".to_string();
        return evidence;
    };
    let command = vec![
        path_string(&ay),
        "check".to_string(),
        "model".to_string(),
        path_string(cnf_path),
        path_string(stdout_path),
        "--json".to_string(),
    ];
    evidence.checker_command_json = serde_json::to_string(&command).unwrap_or_default();
    let args = command[1..].to_vec();
    let output = run_command_capture(
        &ay,
        args.as_slice(),
        solver_root,
        Duration::from_secs_f64((timeout_sec + 8.0).max(60.0)),
    );
    match output {
        Ok((exit_status, stdout, _stderr)) => {
            if let Some(code) = exit_status {
                evidence.checker_exit_status = code.to_string();
            }
            let payload = serde_json::from_str::<JsonValue>(&stdout);
            let status = payload
                .as_ref()
                .ok()
                .and_then(|payload| payload.get("model_status"))
                .and_then(JsonValue::as_str)
                .unwrap_or("")
                .trim();
            if recognized_model_status(status) {
                evidence.status = status.to_string();
                if let Ok(payload) = payload {
                    if let Err(err) = retain_model_checker_artifact(
                        &mut evidence,
                        artifact_path,
                        &payload,
                        &command,
                        exit_status,
                    ) {
                        evidence.status = format!("error:model-check-artifact-{err}");
                    }
                }
            } else {
                evidence.status = "error:unrecognized-model-check-output".to_string();
            }
            evidence
        }
        Err(err) => {
            evidence.status = format!("error:model-check-{err}");
            evidence
        }
    }
}

fn retain_model_checker_artifact(
    evidence: &mut ModelEvidence,
    artifact_path: &Path,
    payload: &JsonValue,
    command: &[String],
    exit_status: Option<i32>,
) -> Result<()> {
    if payload.get("schema").and_then(JsonValue::as_str) != Some(SAT_MODEL_CHECK_ARTIFACT_SCHEMA) {
        bail!("schema-mismatch");
    }
    let mut retained_payload = payload.clone();
    let Some(object) = retained_payload.as_object_mut() else {
        bail!("payload-not-object");
    };
    object.insert(
        "checker_command_json".to_string(),
        JsonValue::Array(command.iter().cloned().map(JsonValue::String).collect()),
    );
    object.insert("checker_exit_status".to_string(), json!(exit_status));
    let retained_stdout = serde_json::to_string(&retained_payload)? + "\n";
    if let Some(parent) = artifact_path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("creating model checker artifact dir {}", parent.display()))?;
    }
    fs::write(artifact_path, retained_stdout)
        .with_context(|| format!("writing model checker artifact {}", artifact_path.display()))?;
    evidence.artifact = path_string(artifact_path);
    evidence.artifact_sha256 = sha256_file(artifact_path)?;
    evidence.artifact_schema = SAT_MODEL_CHECK_ARTIFACT_SCHEMA.to_string();
    evidence.formula = payload
        .get("formula")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .to_string();
    evidence.stdout = payload
        .get("stdout")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .to_string();
    Ok(())
}

fn verify_lrat_proof(
    opts: &SatCompMatrixRunOptions,
    solver_root: &Path,
    cnf_path: &Path,
    proof_path: &Path,
    timeout_sec: f64,
) -> Result<ProofEvidence> {
    let mut evidence = ProofEvidence {
        proof_status: "n/a".to_string(),
        ay_lrat_status: "n/a".to_string(),
        proof_checker_status: "n/a".to_string(),
        ..ProofEvidence::default()
    };
    if !proof_path.is_file() {
        evidence.proof_status = "ay-missing".to_string();
        evidence.ay_lrat_status = "missing".to_string();
        evidence.proof_checker_status = "n/a".to_string();
        return Ok(evidence);
    }
    if proof_path.metadata()?.len() == 0 {
        evidence.proof_status = "ay-empty".to_string();
        evidence.ay_lrat_status = "empty".to_string();
        evidence.proof_checker_status = "n/a".to_string();
        return Ok(evidence);
    }

    let mut external_checker_run: Option<ExternalCheckerRunEvidence> = None;
    evidence.ay_lrat_status = match ay_checker_path(solver_root) {
        Some(ay) => {
            // Internal ay proof self-check, format-aware: `ay check drat|lrat`.
            // (The status field is named ay_lrat_status for historical reasons;
            // it records the internal ay proof-check verdict for either format.)
            let args = vec![
                "check".to_string(),
                opts.proof_format.clone(),
                path_string(cnf_path),
                path_string(proof_path),
            ];
            match run_command_capture(
                &ay,
                args.as_slice(),
                solver_root,
                proof_check_timeout(timeout_sec),
            ) {
                Ok((Some(0), _stdout, _stderr)) => "ok".to_string(),
                Ok((Some(_), _stdout, _stderr)) => "invalid".to_string(),
                Ok((None, _stdout, _stderr)) => "timeout".to_string(),
                Err(_) => "exec_error".to_string(),
            }
        }
        None => "missing".to_string(),
    };

    evidence.proof_checker_status = if let Some(checker) =
        resolve_external_proof_checker_path(&opts.proof_checker, &env::current_dir()?)
    {
        let args = vec![path_string(cnf_path), path_string(proof_path)];
        match run_command_capture(
            &checker,
            args.as_slice(),
            solver_root,
            proof_check_timeout(timeout_sec),
        ) {
            Ok((Some(0), stdout, stderr)) => {
                if proof_checker_output_is_verified(&stdout, &stderr) {
                    let checker_argv = vec![
                        path_string(&checker),
                        path_string(cnf_path),
                        path_string(proof_path),
                    ];
                    external_checker_run = Some(ExternalCheckerRunEvidence {
                        checker_path: checker,
                        checker_argv,
                        checker_exit_code: 0,
                        checker_stdout: stdout,
                        checker_stderr: stderr,
                    });
                    "ok".to_string()
                } else {
                    "invalid".to_string()
                }
            }
            Ok((Some(_), _stdout, _stderr)) => "invalid".to_string(),
            Ok((None, _stdout, _stderr)) => "timeout".to_string(),
            Err(_) => "exec_error".to_string(),
        }
    } else {
        "unchecked".to_string()
    };

    evidence.proof_status =
        if evidence.ay_lrat_status == "ok" && evidence.proof_checker_status == "ok" {
            "valid".to_string()
        } else if evidence.ay_lrat_status != "ok" {
            format!("ay-{}", evidence.ay_lrat_status)
        } else {
            format!("checker-{}", evidence.proof_checker_status)
        };

    if evidence.proof_status == "valid" {
        let Some(run) = external_checker_run.as_ref() else {
            bail!("valid UNSAT proof missing retained external checker run evidence");
        };
        write_external_checker_artifact(cnf_path, proof_path, run, &mut evidence)?;
    }
    Ok(evidence)
}

fn proof_check_timeout(timeout_sec: f64) -> Duration {
    Duration::from_secs_f64((timeout_sec + 8.0).max(60.0))
}

fn resolve_external_proof_checker_path(raw: &str, invocation_cwd: &Path) -> Option<PathBuf> {
    let trimmed = raw.trim();
    if trimmed.is_empty() || trimmed == "none" || trimmed == "auto" {
        return None;
    }
    let raw_path = Path::new(trimmed);
    if raw_path.file_name().is_some_and(|name| name == "ay") {
        return None;
    }
    let path = expand_home(raw_path);
    Some(if path.is_absolute() {
        path
    } else {
        invocation_cwd.join(path)
    })
}

fn write_external_checker_artifact(
    cnf_path: &Path,
    proof_path: &Path,
    run: &ExternalCheckerRunEvidence,
    evidence: &mut ProofEvidence,
) -> Result<()> {
    let artifact = external_checker_verdict_artifact_path(proof_path);
    let payload = json!({
        "schema": EXTERNAL_CHECKER_VERDICT_SCHEMA,
        "runtime_field": "external_proof_checker_verdict_artifact",
        "verdict": "VERIFIED_UNSAT",
        "artifact_path": path_string(&artifact),
        "checker_path": path_string(&run.checker_path),
        "checker_sha256": if run.checker_path.is_file() { sha256_file(&run.checker_path)? } else { String::new() },
        "checker_command": shell_join(&run.checker_argv),
        "checker_argv": run.checker_argv.clone(),
        "checker_exit_code": run.checker_exit_code,
        "checker_stdout": run.checker_stdout.clone(),
        "checker_stderr": run.checker_stderr.clone(),
        "proof_out_path": path_string(proof_path),
        "proof_out_sha256": sha256_file(proof_path)?,
        "checked_dimacs_path": path_string(cnf_path),
        "checked_dimacs_sha256": sha256_file(cnf_path)?,
    });
    write_json_pretty(&artifact, &payload)?;
    evidence.external_artifact = path_string(&artifact);
    evidence.external_artifact_sha256 = sha256_file(&artifact)?;
    evidence.external_artifact_schema = EXTERNAL_CHECKER_VERDICT_SCHEMA.to_string();
    evidence.external_verdict = "VERIFIED_UNSAT".to_string();
    evidence.external_proof_out_path = path_string(proof_path);
    Ok(())
}

fn run_fmla_postcheck_admission_replay(
    solver_root: &Path,
    cnf_path: &Path,
    proof_path: &Path,
    case_dir: &Path,
    external: &ProofEvidence,
    counters: &BTreeMap<String, String>,
    learned_artifact: Option<&RetainedFmlaLearnedLratDryRunArtifact>,
    timeout_sec: f64,
) -> Result<FmlaPostcheckAdmissionEvidence> {
    let mut evidence = FmlaPostcheckAdmissionEvidence::default();
    if external.ay_lrat_status != "ok"
        || external.proof_checker_status != "ok"
        || external.external_artifact.trim().is_empty()
        || external.external_artifact_sha256.trim().is_empty()
        || external.external_artifact_schema != EXTERNAL_CHECKER_VERDICT_SCHEMA
        || external.external_verdict != "VERIFIED_UNSAT"
        || external.external_proof_out_path.trim().is_empty()
    {
        return Ok(evidence);
    }

    if let Some(artifact) = learned_artifact {
        retain_fmla_learned_lrat_dry_run_artifact_evidence(&mut evidence, artifact);
    }

    let Some(ay) = ay_checker_path(solver_root) else {
        evidence.status = "ay-checker-missing".to_string();
        return Ok(evidence);
    };
    let replay_artifact = case_dir.join(FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_ARTIFACT);
    let summary_tsv = case_dir.join(FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_SUMMARY_TSV);
    let report = case_dir.join(FMLA_MAIN_LRAT_POSTCHECK_ADMISSION_REPLAY_REPORT);
    remove_if_exists(&replay_artifact)?;
    remove_if_exists(&summary_tsv)?;
    remove_if_exists(&report)?;

    let mut args = vec![
        "check".to_string(),
        "fmla-postcheck-admission".to_string(),
        "--dimacs".to_string(),
        path_string(cnf_path),
        "--proof-out".to_string(),
        path_string(proof_path),
        "--external-checker-artifact".to_string(),
        external.external_artifact.clone(),
        "--external-checker-artifact-sha256".to_string(),
        external.external_artifact_sha256.clone(),
        "--ay-lrat-status".to_string(),
        external.ay_lrat_status.clone(),
        "--proof-checker-status".to_string(),
        external.proof_checker_status.clone(),
        "--replay-artifact".to_string(),
        path_string(&replay_artifact),
        "--summary-tsv".to_string(),
        path_string(&summary_tsv),
        "--materializer-attempts".to_string(),
        fmla_counter_or_missing(counters, FMLA_MATERIALIZER_ATTEMPTS_COUNTER),
        "--materializer-proof-emit-records-seen".to_string(),
        fmla_counter_or_missing(counters, FMLA_MATERIALIZER_PROOF_EMIT_RECORDS_SEEN_COUNTER),
        "--materializer-records".to_string(),
        fmla_counter_or_missing(counters, FMLA_MATERIALIZER_RECORDS_COUNTER),
        "--materializer-fail-closed".to_string(),
        fmla_counter_or_missing(counters, FMLA_MATERIALIZER_FAIL_CLOSED_COUNTER),
        "--materializer-missing-runtime-records".to_string(),
        fmla_counter_or_missing(counters, FMLA_MATERIALIZER_MISSING_RUNTIME_RECORDS_COUNTER),
        "--preprocess-tx-fail-closed".to_string(),
        fmla_counter_or_missing(counters, FMLA_PREPROCESS_TX_FAIL_CLOSED_COUNTER),
        "--preprocess-tx-committed".to_string(),
        fmla_counter_or_missing(counters, FMLA_PREPROCESS_TX_COMMITTED_COUNTER),
        "--json".to_string(),
    ];
    if let Some(artifact) = learned_artifact {
        args.splice(
            10..10,
            [
                "--learned-lrat-dry-run-artifact".to_string(),
                path_string(&artifact.path),
            ],
        );
    }

    let output = run_command_capture(
        &ay,
        args.as_slice(),
        solver_root,
        Duration::from_secs_f64((timeout_sec + 8.0).max(60.0)),
    );
    match output {
        Ok((exit_status, stdout, _stderr)) => {
            if !stdout.trim().is_empty() {
                fs::write(&report, stdout).with_context(|| {
                    format!("writing Fmla admission report {}", report.display())
                })?;
            }
            if exit_status == Some(0) {
                if let Some(parsed) = parse_fmla_postcheck_summary_tsv(&summary_tsv)? {
                    evidence.status = parsed.status;
                    evidence.artifact = parsed.artifact;
                    evidence.artifact_sha256 = parsed.artifact_sha256;
                    evidence.materializer_records = parsed.materializer_records;
                    evidence.external_checker_artifact_rows = parsed.external_checker_artifact_rows;
                    evidence.preprocess_tx_committed = parsed.preprocess_tx_committed;
                    retain_fmla_main_lrat_authority_replay_handoff(&mut evidence, proof_path)?;
                }
            } else {
                evidence.status = exit_status
                    .map(|status| format!("rejected:{status}"))
                    .unwrap_or_else(|| "timeout".to_string());
            }
        }
        Err(err) => {
            evidence.status = format!("exec_error:{err}");
        }
    }
    Ok(evidence)
}

fn retain_fmla_main_lrat_authority_replay_handoff(
    evidence: &mut FmlaPostcheckAdmissionEvidence,
    proof_path: &Path,
) -> Result<()> {
    if evidence.status != "committed_checker_backed_admission"
        || evidence.artifact.trim().is_empty()
    {
        return Ok(());
    }
    let replay_artifact = evidence_path(evidence.artifact.trim());
    if !replay_artifact.is_file() {
        return Ok(());
    }
    let replay_sha256 = sha256_file(&replay_artifact)?;
    if evidence.artifact_sha256.trim().is_empty() || replay_sha256 != evidence.artifact_sha256 {
        return Ok(());
    }
    let payload = load_json_object(&replay_artifact)?;
    if !fmla_main_lrat_authority_replay_payload_authorizes_proof(
        &payload,
        proof_path,
        Some(&replay_artifact),
        Some(&replay_sha256),
    )? {
        return Ok(());
    }

    evidence.main_lrat_authority_replay_env =
        FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_ENV.to_string();
    evidence.main_lrat_authority_replay_env_value = path_string(&replay_artifact);
    evidence.main_lrat_authority_replay_env_value_sha256 = replay_sha256;
    evidence.main_lrat_authority_replay_env_status = "authorized_handoff".to_string();
    Ok(())
}

fn fmla_main_lrat_authority_replay_handoff_from_record(
    record: &Record,
    proof_path: &Path,
) -> Result<FmlaMainLratAuthorityReplayHandoff> {
    if record.get("fmla_main_lrat_authority_replay_env")
        != FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY_ENV
        || record.get("fmla_main_lrat_authority_replay_env_status") != "authorized_handoff"
    {
        bail!("row did not advertise an authorized Fmla Main/LRAT handoff");
    }
    let replay_artifact = PathBuf::from(record.get("fmla_main_lrat_authority_replay_env_value"));
    if !replay_artifact.is_file() {
        bail!(
            "Fmla Main/LRAT replay artifact is missing: {}",
            replay_artifact.display()
        );
    }
    let recorded_sha256 = record
        .get("fmla_main_lrat_authority_replay_env_value_sha256")
        .trim();
    if !is_hex_sha256(recorded_sha256) {
        bail!("Fmla Main/LRAT replay artifact sha256 is missing or malformed");
    }
    let observed_sha256 = sha256_file(&replay_artifact)?;
    if observed_sha256 != recorded_sha256 {
        bail!("Fmla Main/LRAT replay artifact sha256 drifted");
    }
    let payload = load_json_object(&replay_artifact)?;
    if !fmla_main_lrat_authority_replay_payload_authorizes_proof(
        &payload,
        proof_path,
        Some(&replay_artifact),
        Some(&observed_sha256),
    )? {
        bail!("Fmla Main/LRAT replay payload does not authorize the current proof.out");
    }
    Ok(FmlaMainLratAuthorityReplayHandoff {
        replay_artifact,
        replay_artifact_sha256: observed_sha256,
    })
}

fn fmla_main_lrat_authority_replay_payload_authorizes_proof(
    payload: &JsonValue,
    proof_path: &Path,
    replay_artifact: Option<&Path>,
    replay_artifact_sha256: Option<&str>,
) -> Result<bool> {
    let proof_obligation_rows = payload
        .get("proof_obligation_rows")
        .and_then(JsonValue::as_u64)
        .unwrap_or(0);
    if payload.get("schema").and_then(JsonValue::as_str)
        != Some("ay.fmla-main-lrat-postcheck-admission-replay/v1")
        || payload.get("status").and_then(JsonValue::as_str)
            != Some("committed_checker_backed_admission")
        || proof_obligation_rows == 0
        || payload
            .get("external_proof_checker_verdict_artifact_rows")
            .and_then(JsonValue::as_u64)
            != Some(proof_obligation_rows)
        || payload
            .get("learned_lrat_main_proof_authority_status")
            .and_then(JsonValue::as_str)
            != Some("authorized")
        || payload
            .get("learned_lrat_main_proof_authority_external_checker_verified")
            .and_then(JsonValue::as_bool)
            != Some(true)
        || payload
            .get("learned_lrat_main_proof_authority_proof_out_contains_lrat_fragment")
            .and_then(JsonValue::as_bool)
            != Some(true)
        || payload
            .get("learned_lrat_main_proof_authority_authorizes_main_proof_out")
            .and_then(JsonValue::as_bool)
            != Some(true)
        || payload
            .get("external_proof_checker_verdict")
            .and_then(JsonValue::as_str)
            != Some("VERIFIED_UNSAT")
        || payload.get("checker_exit_code").and_then(json_as_i64) != Some(0)
    {
        return Ok(false);
    }

    let payload_proof_path = payload
        .get("learned_lrat_main_proof_authority_proof_out_path")
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    if payload_proof_path.trim().is_empty()
        || !evidence_paths_match(payload_proof_path, &path_string(proof_path))
    {
        return Ok(false);
    }
    let expected_sha256 = payload
        .get("learned_lrat_main_proof_authority_proof_out_sha256")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .trim();
    if !is_hex_sha256(expected_sha256) {
        return Ok(false);
    }
    if !proof_path.is_file() || sha256_file(proof_path)? != expected_sha256 {
        return Ok(false);
    }
    if !fmla_main_lrat_authority_replay_external_checker_payload_valid(
        payload,
        replay_artifact,
        replay_artifact_sha256,
        &path_string(proof_path),
        expected_sha256,
    )? {
        return Ok(false);
    }
    Ok(true)
}

fn fmla_main_lrat_authority_replay_external_checker_payload_valid(
    payload: &JsonValue,
    replay_artifact: Option<&Path>,
    replay_artifact_sha256: Option<&str>,
    proof_path: &str,
    proof_sha256: &str,
) -> Result<bool> {
    let checker_artifact_path = payload
        .get("external_proof_checker_verdict_artifact")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .trim();
    if checker_artifact_path.is_empty()
        || payload
            .get("external_proof_checker_verdict_artifact_schema")
            .and_then(JsonValue::as_str)
            != Some(EXTERNAL_CHECKER_VERDICT_SCHEMA)
        || payload
            .get("external_proof_checker_verdict_artifact_runtime_field")
            .and_then(JsonValue::as_str)
            != Some("external_proof_checker_verdict_artifact")
        || payload
            .get("external_proof_checker_verdict_artifact_sha256")
            .and_then(JsonValue::as_str)
            .as_ref()
            .is_none_or(|sha| !is_hex_sha256(sha.trim()))
    {
        return Ok(false);
    }

    let checker_artifact = evidence_path(checker_artifact_path);
    if !checker_artifact.is_file() {
        return Ok(false);
    }
    let checker_artifact_sha256 = sha256_file(&checker_artifact)?;
    if payload
        .get("external_proof_checker_verdict_artifact_sha256")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .trim()
        != checker_artifact_sha256
    {
        return Ok(false);
    }
    let checker_payload = load_json_object(&checker_artifact)?;
    if checker_payload.get("schema").and_then(JsonValue::as_str)
        != Some(EXTERNAL_CHECKER_VERDICT_SCHEMA)
        || checker_payload
            .get("runtime_field")
            .and_then(JsonValue::as_str)
            != Some("external_proof_checker_verdict_artifact")
        || checker_payload.get("verdict").and_then(JsonValue::as_str) != Some("VERIFIED_UNSAT")
        || checker_payload
            .get("checker_exit_code")
            .and_then(json_as_i64)
            != Some(0)
        || checker_payload
            .get("proof_out_sha256")
            .and_then(JsonValue::as_str)
            != Some(proof_sha256)
        || !evidence_paths_match(
            checker_payload
                .get("proof_out_path")
                .and_then(JsonValue::as_str)
                .unwrap_or_default(),
            proof_path,
        )
        || !evidence_paths_match(
            checker_payload
                .get("artifact_path")
                .and_then(JsonValue::as_str)
                .unwrap_or_default(),
            checker_artifact_path,
        )
    {
        return Ok(false);
    }
    let replay_matches_checker = [
        ("external_proof_checker_path", "checker_path"),
        ("external_proof_checker_sha256", "checker_sha256"),
        ("external_proof_checker_command", "checker_command"),
        ("external_proof_checker_dimacs_path", "checked_dimacs_path"),
        (
            "external_proof_checker_dimacs_sha256",
            "checked_dimacs_sha256",
        ),
    ]
    .iter()
    .all(|(replay_key, checker_key)| {
        payload.get(*replay_key).and_then(JsonValue::as_str)
            == checker_payload
                .get(*checker_key)
                .and_then(JsonValue::as_str)
    });
    if !replay_matches_checker
        || payload.get("external_proof_checker_argv") != checker_payload.get("checker_argv")
        || payload
            .get("external_proof_checker_verdict_artifact")
            .and_then(JsonValue::as_str)
            .is_some_and(|path| {
                !evidence_paths_match(
                    path,
                    checker_payload
                        .get("artifact_path")
                        .and_then(JsonValue::as_str)
                        .unwrap_or_default(),
                )
            })
    {
        return Ok(false);
    }
    if let (Some(path), Some(sha256)) = (replay_artifact, replay_artifact_sha256) {
        if payload
            .get("artifact_path")
            .and_then(JsonValue::as_str)
            .is_some_and(|recorded| !evidence_paths_match(recorded, &path_string(path)))
            || payload
                .get("artifact_sha256")
                .and_then(JsonValue::as_str)
                .is_some_and(|recorded| recorded != sha256)
        {
            return Ok(false);
        }
    }
    Ok(true)
}

fn retain_fmla_learned_lrat_dry_run_artifact_evidence(
    evidence: &mut FmlaPostcheckAdmissionEvidence,
    artifact: &RetainedFmlaLearnedLratDryRunArtifact,
) {
    evidence.learned_lrat_dry_run_artifact = path_string(&artifact.path);
    evidence
        .learned_lrat_dry_run_artifact_sha256
        .clone_from(&artifact.sha256);
    evidence
        .learned_lrat_dry_run_artifact_schema
        .clone_from(&artifact.schema);
}

fn parse_fmla_postcheck_summary_tsv(
    summary_tsv: &Path,
) -> Result<Option<FmlaPostcheckAdmissionEvidence>> {
    if !summary_tsv.is_file() {
        return Ok(None);
    }
    let text = fs::read_to_string(summary_tsv)
        .with_context(|| format!("reading {}", summary_tsv.display()))?;
    let Some(line) = text.lines().next() else {
        return Ok(None);
    };
    if line.trim().is_empty() {
        return Ok(None);
    }
    let mut cells: Vec<&str> = line.split('\t').collect();
    while cells.len() < 6 {
        cells.push("");
    }
    Ok(Some(FmlaPostcheckAdmissionEvidence {
        status: cells[0].to_string(),
        artifact: cells[1].to_string(),
        artifact_sha256: cells[2].to_string(),
        materializer_records: cells[3].to_string(),
        external_checker_artifact_rows: cells[4].to_string(),
        preprocess_tx_committed: cells[5].to_string(),
        ..FmlaPostcheckAdmissionEvidence::default()
    }))
}

fn fmla_counter_or_missing(counters: &BTreeMap<String, String>, key: &str) -> String {
    counters
        .get(key)
        .filter(|value| !value.trim().is_empty())
        .cloned()
        .unwrap_or_else(|| "missing".to_string())
}

fn fmla_postcheck_counters_from_stderr(path: &Path) -> Result<BTreeMap<String, String>> {
    let mut counters = BTreeMap::new();
    if !path.is_file() {
        return Ok(counters);
    }
    let reader = BufReader::new(
        File::open(path).with_context(|| format!("opening stderr {}", path.display()))?,
    );
    for line in reader.lines() {
        let line = line?;
        let trimmed = line.trim();
        if !trimmed.starts_with('{') {
            continue;
        }
        let Ok(value) = serde_json::from_str::<JsonValue>(trimmed) else {
            continue;
        };
        let Some(object) = value.as_object() else {
            continue;
        };
        for &field in FMLA_POSTCHECK_COUNTER_FIELDS {
            if let Some(value) = object.get(field) {
                counters.insert(field.to_string(), value_string(value));
            }
        }
    }
    Ok(counters)
}

fn find_retained_fmla_learned_lrat_dry_run_artifact(
    case_dir: &Path,
    stderr_path: &Path,
) -> Result<Option<RetainedFmlaLearnedLratDryRunArtifact>> {
    let mut candidates: Vec<PathBuf> = FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_CANDIDATES
        .iter()
        .map(|file_name| case_dir.join(file_name))
        .collect();
    candidates.extend(fmla_learned_lrat_dry_run_artifact_path_fields(
        case_dir,
        stderr_path,
    )?);
    retained_fmla_learned_lrat_dry_run_artifact(case_dir, candidates.iter())
}

fn fmla_learned_lrat_dry_run_artifact_path_fields(
    case_dir: &Path,
    stderr_path: &Path,
) -> Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    if !stderr_path.is_file() {
        return Ok(paths);
    }
    let reader = BufReader::new(
        File::open(stderr_path)
            .with_context(|| format!("opening stderr {}", stderr_path.display()))?,
    );
    for line in reader.lines() {
        let line = line?;
        let trimmed = line.trim();
        if !trimmed.starts_with('{') {
            continue;
        }
        let Ok(value) = serde_json::from_str::<JsonValue>(trimmed) else {
            continue;
        };
        collect_fmla_learned_lrat_dry_run_paths(case_dir, &value, &mut paths);
    }
    Ok(paths)
}

fn collect_fmla_learned_lrat_dry_run_paths(
    case_dir: &Path,
    value: &JsonValue,
    paths: &mut Vec<PathBuf>,
) {
    for &field in FMLA_LEARNED_LRAT_DRY_RUN_ARTIFACT_PATH_FIELDS {
        if let Some(raw) = value.get(field).and_then(JsonValue::as_str) {
            paths.push(resolve_case_artifact_path(case_dir, raw));
        }
    }
    for field in ["fmla_learned_lrat_dry_run", "learned_lrat_dry_run"] {
        if let Some(object) = value.get(field).and_then(JsonValue::as_object) {
            for path_field in ["artifact", "artifact_path", "path"] {
                if let Some(raw) = object.get(path_field).and_then(JsonValue::as_str) {
                    paths.push(resolve_case_artifact_path(case_dir, raw));
                }
            }
        }
    }
}

fn resolve_case_artifact_path(case_dir: &Path, raw: &str) -> PathBuf {
    let path = PathBuf::from(raw);
    if path.is_absolute() {
        path
    } else {
        case_dir.join(path)
    }
}

fn retained_fmla_learned_lrat_dry_run_artifact<'a>(
    case_dir: &Path,
    candidates: impl IntoIterator<Item = &'a PathBuf>,
) -> Result<Option<RetainedFmlaLearnedLratDryRunArtifact>> {
    for candidate in candidates {
        if !candidate.is_file() || !path_is_retained_under_root(candidate, case_dir) {
            continue;
        }
        let Ok(payload) = load_json_object(candidate) else {
            continue;
        };
        if payload.get("schema").and_then(JsonValue::as_str)
            != Some(FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA)
        {
            continue;
        }
        return Ok(Some(RetainedFmlaLearnedLratDryRunArtifact {
            path: candidate.clone(),
            sha256: sha256_file(candidate)?,
            schema: FMLA_LEARNED_LRAT_DRY_RUN_PROOF_ARTIFACT_SCHEMA.to_string(),
        }));
    }
    Ok(None)
}

fn path_is_retained_under_root(path: &Path, root: &Path) -> bool {
    let Ok(path) = path.canonicalize() else {
        return false;
    };
    let Ok(root) = root.canonicalize() else {
        return false;
    };
    path.starts_with(root)
}

fn run_command_capture(
    program: &Path,
    args: &[String],
    cwd: &Path,
    timeout: Duration,
) -> Result<(Option<i32>, String, String)> {
    let mut child = Command::new(program)
        .args(args)
        .current_dir(cwd)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("running {}", program.display()))?;
    match child.wait_timeout(timeout)? {
        Some(status) => {
            let mut stdout = Vec::new();
            let mut stderr = Vec::new();
            if let Some(mut pipe) = child.stdout.take() {
                pipe.read_to_end(&mut stdout)?;
            }
            if let Some(mut pipe) = child.stderr.take() {
                pipe.read_to_end(&mut stderr)?;
            }
            Ok((
                status.code(),
                String::from_utf8_lossy(&stdout).to_string(),
                String::from_utf8_lossy(&stderr).to_string(),
            ))
        }
        None => {
            let _ = child.kill();
            let _ = child.wait();
            let mut stdout = Vec::new();
            let mut stderr = Vec::new();
            if let Some(mut pipe) = child.stdout.take() {
                pipe.read_to_end(&mut stdout)?;
            }
            if let Some(mut pipe) = child.stderr.take() {
                pipe.read_to_end(&mut stderr)?;
            }
            Ok((
                None,
                String::from_utf8_lossy(&stdout).to_string(),
                String::from_utf8_lossy(&stderr).to_string(),
            ))
        }
    }
}

fn parse_solver_output_file(
    path: &Path,
    exit_code: Option<i32>,
    strict: bool,
) -> Result<ParsedOutput> {
    let reader = BufReader::new(
        File::open(path).with_context(|| format!("opening stdout {}", path.display()))?,
    );
    let mut actual = "unknown".to_string();
    let mut status_count = 0usize;
    let mut invalid_reason: Option<String> = None;
    let mut has_model_lines = false;
    let mut status_seen = false;
    for (idx, line) in reader.lines().enumerate() {
        let line = line?;
        let line_no = idx + 1;
        if line.trim().is_empty() {
            continue;
        }
        if line == "c" || line.starts_with("c ") {
            continue;
        }
        if line.starts_with("v") {
            if strict && !status_seen {
                invalid_reason.get_or_insert_with(|| format!("model-before-status:{line_no}"));
            }
            has_model_lines = true;
            continue;
        }
        if let Some(verdict) = exact_status_line(&line) {
            status_count += 1;
            status_seen = true;
            actual = verdict.to_string();
            continue;
        }
        if line.starts_with("s ") {
            invalid_reason.get_or_insert_with(|| format!("malformed-status:{line_no}"));
        } else if strict {
            invalid_reason.get_or_insert_with(|| format!("junk-stdout:{line_no}"));
        }
    }
    if status_count == 0 {
        invalid_reason.get_or_insert_with(|| "missing-status".to_string());
    } else if status_count > 1 {
        invalid_reason.get_or_insert_with(|| "duplicate-status".to_string());
    }
    if strict && !exit_code_ok(&actual, exit_code) {
        invalid_reason.get_or_insert_with(|| {
            format!(
                "exit-code-mismatch:{}:{}",
                actual,
                exit_code.map_or_else(|| "timeout".to_string(), |code| code.to_string())
            )
        });
    }
    Ok(ParsedOutput {
        actual,
        invalid_reason,
        has_model_lines,
    })
}

fn exit_code_ok(actual: &str, exit_code: Option<i32>) -> bool {
    match actual {
        "sat" => exit_code == Some(10),
        "unsat" => exit_code == Some(20),
        "unknown" => matches!(exit_code, Some(0 | 30 | 124)),
        _ => true,
    }
}

fn exact_status_line(line: &str) -> Option<&'static str> {
    match line {
        "s SATISFIABLE" => Some("sat"),
        "s UNSATISFIABLE" => Some("unsat"),
        "s UNKNOWN" => Some("unknown"),
        _ => None,
    }
}

fn recognized_model_status(status: &str) -> bool {
    matches!(
        status,
        "valid" | "invalid" | "contradictory" | "missing" | "unterminated"
    ) || status.starts_with("malformed:")
        || status.starts_with("duplicate-terminator:")
        || status.starts_with("duplicate-assignment:")
        || status.starts_with("error:")
}

fn proof_checker_output_is_verified(stdout: &str, stderr: &str) -> bool {
    let lines = stdout.lines().collect::<Vec<_>>();
    let stdout_comment_or_verdict_only = lines.iter().all(|line| {
        line.is_empty()
            || *line == "c"
            || line.starts_with("c ")
            || matches!(
                normalized_proof_checker_verdict(line),
                "VERIFIED" | "s VERIFIED" | "s VERIFIED UNSAT"
            )
    });
    let verified = lines.iter().any(|line| {
        matches!(
            normalized_proof_checker_verdict(line),
            "VERIFIED" | "s VERIFIED" | "s VERIFIED UNSAT"
        )
    });
    let stderr_comment_only = stderr
        .lines()
        .all(|line| line.is_empty() || line == "c" || line.starts_with("c "));
    verified && stdout_comment_or_verdict_only && stderr_comment_only
}

fn shell_join(argv: &[String]) -> String {
    argv.iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(arg: &str) -> String {
    if !arg.is_empty()
        && arg.chars().all(|ch| {
            ch.is_ascii_alphanumeric() || matches!(ch, '/' | '.' | '_' | '-' | '+' | ':' | '=')
        })
    {
        arg.to_string()
    } else {
        format!("'{}'", arg.replace('\'', "'\"'\"'"))
    }
}

fn normalized_proof_checker_verdict(line: &str) -> &str {
    line.strip_prefix("c ").unwrap_or(line)
}

fn load_benchmarks(opts: &SatCompMatrixRunOptions) -> Result<Vec<Benchmark>> {
    if let Some(instance) = &opts.instance {
        let path = absolute_path(instance)?;
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("instance")
            .to_string();
        return Ok(vec![Benchmark {
            path,
            expected: normalize_expected(&opts.expected),
            family: opts.family.clone(),
            category: opts.category.clone(),
            name,
        }]);
    }

    if let Some(manifest) = &opts.manifest {
        return load_manifest(&absolute_path(manifest)?);
    }

    if let Some(benchmarks_dir) = &opts.benchmarks_dir {
        return load_benchmark_dir(&absolute_path(benchmarks_dir)?);
    }

    if opts.suite == "sat-main-2026-official-mirror" {
        let mirror_root = official_mirror_root(opts);
        if let Some(manifest) = find_official_mirror_manifest(&mirror_root)? {
            return load_manifest(&manifest);
        }
        if let Some(benchmarks_dir) = find_official_mirror_benchmarks_dir(&mirror_root) {
            return load_benchmark_dir(&benchmarks_dir);
        }
        bail!(
            "SAT-COMP 2026 official mirror inputs not found under {}",
            mirror_root.display()
        );
    }

    bail!("--manifest, --benchmarks-dir, or --instance is required for Rust SAT matrix preflight")
}

fn apply_benchmark_filters(
    opts: &SatCompMatrixRunOptions,
    benches: &mut Vec<Benchmark>,
) -> Result<()> {
    let family_filters = normalized_filter_values(&opts.filter_family, "--filter-family")?;
    if !family_filters.is_empty() {
        benches.retain(|bench| {
            family_filters
                .iter()
                .any(|family| bench.family.trim() == family.as_str())
        });
    }
    Ok(())
}

fn normalized_filter_values(raw: &[String], flag: &str) -> Result<Vec<String>> {
    let mut values = Vec::new();
    for value in raw {
        let value = value.trim();
        if value.is_empty() {
            bail!("{flag} must not be empty");
        }
        values.push(value.to_string());
    }
    values.sort();
    values.dedup();
    Ok(values)
}

fn load_benchmark_dir(path: &Path) -> Result<Vec<Benchmark>> {
    let mut benches = Vec::new();
    collect_benchmarks_from_dir(path, &mut benches)?;
    benches.sort_by(|left, right| left.name.cmp(&right.name));
    Ok(benches)
}

fn collect_benchmarks_from_dir(path: &Path, benches: &mut Vec<Benchmark>) -> Result<()> {
    let entries = fs::read_dir(path)
        .with_context(|| format!("reading benchmark directory {}", path.display()))?;
    for entry in entries {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_benchmarks_from_dir(&path, benches)?;
            continue;
        }
        if !path.is_file() || !is_dimacs_path(&path) {
            continue;
        }
        let name = path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("instance")
            .to_string();
        benches.push(Benchmark {
            path: absolute_path(&path)?,
            expected: "unknown".to_string(),
            family: "unknown".to_string(),
            category: "unknown".to_string(),
            name,
        });
    }
    Ok(())
}

// SAT-COMP benchmark names use lowercase `.cnf`/`.cnf.xz` by contract; the
// double suffix does not fit `Path::extension` and exact matching is intended.
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn is_dimacs_path(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    name.ends_with(".cnf") || name.ends_with(".cnf.xz")
}

fn load_manifest(path: &Path) -> Result<Vec<Benchmark>> {
    let text =
        fs::read_to_string(path).with_context(|| format!("reading manifest {}", path.display()))?;
    let mut lines = text.lines();
    let Some(header_line) = lines.next() else {
        return Ok(Vec::new());
    };
    let headers = parse_csv_line(header_line);
    let mut benches = Vec::new();
    for line in lines {
        if line.trim().is_empty() {
            continue;
        }
        let values = parse_csv_line(line);
        let get = |name: &str| -> String {
            headers
                .iter()
                .position(|header| header == name)
                .and_then(|idx| values.get(idx))
                .cloned()
                .unwrap_or_default()
        };
        let raw_path = first_non_empty(&[get("local_path"), get("path")]);
        if raw_path.is_empty() {
            continue;
        }
        let bench_path = absolute_path(Path::new(&raw_path))?;
        if !bench_path.exists() {
            continue;
        }
        let name = bench_path
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("instance")
            .to_string();
        benches.push(Benchmark {
            path: bench_path,
            expected: normalize_expected(&first_non_empty(&[get("result"), get("expected")])),
            family: first_non_empty(&[get("family"), "unknown".to_string()]),
            category: first_non_empty(&[get("category"), "unknown".to_string()]),
            name,
        });
    }
    Ok(benches)
}

fn parse_csv_line(line: &str) -> Vec<String> {
    let mut fields = Vec::new();
    let mut current = String::new();
    let mut chars = line.chars().peekable();
    let mut in_quotes = false;
    while let Some(ch) = chars.next() {
        match ch {
            '"' if in_quotes && chars.peek() == Some(&'"') => {
                current.push('"');
                let _ = chars.next();
            }
            '"' => in_quotes = !in_quotes,
            ',' if !in_quotes => {
                fields.push(current.clone());
                current.clear();
            }
            _ => current.push(ch),
        }
    }
    fields.push(current);
    fields
}

fn check_official_mirror(opts: &SatCompMatrixRunOptions, benches: &[Benchmark]) -> Result<()> {
    let required = opts.require_official_mirror || opts.suite == "sat-main-2026-official-mirror";
    if !required {
        return Ok(());
    }
    let root = official_mirror_root(opts);
    if !root.is_dir() {
        bail!("official mirror root not found: {}", root.display());
    }
    let root = root.canonicalize()?;
    for bench in benches {
        let bench_path = bench.path.canonicalize()?;
        if !bench_path.starts_with(&root) {
            bail!(
                "benchmark outside official mirror: {}",
                bench.path.display()
            );
        }
    }
    Ok(())
}

fn validate_limit_policy(opts: &SatCompMatrixRunOptions) -> Result<()> {
    let Some(limit) = opts.limit else {
        return Ok(());
    };
    if limit == 0 {
        bail!("--limit must be positive");
    }
    let official = opts.require_official_mirror || opts.suite == "sat-main-2026-official-mirror";
    if official && !opts.allow_smoke {
        bail!("official mirror gate must not use --limit unless --allow-smoke is set");
    }
    Ok(())
}

fn official_mirror_root(opts: &SatCompMatrixRunOptions) -> PathBuf {
    if let Some(root) = &opts.official_mirror_root {
        return root.clone();
    }
    if let Ok(root) = env::var("SATCOMP_OFFICIAL_MIRROR") {
        return PathBuf::from(root);
    }
    home_dir().join(DEFAULT_OFFICIAL_MIRROR_ROOT)
}

fn find_official_mirror_manifest(root: &Path) -> Result<Option<PathBuf>> {
    for candidate in OFFICIAL_MIRROR_MANIFEST_CANDIDATES {
        let manifest = root.join(candidate);
        if manifest.is_file() {
            return Ok(Some(manifest));
        }
    }

    let mut matches = Vec::new();
    collect_official_mirror_manifest_matches(root, &mut matches)?;
    matches.sort();
    if matches.len() == 1 {
        Ok(matches.pop())
    } else {
        Ok(None)
    }
}

fn collect_official_mirror_manifest_matches(root: &Path, matches: &mut Vec<PathBuf>) -> Result<()> {
    if !root.is_dir() {
        return Ok(());
    }
    for entry in fs::read_dir(root).with_context(|| format!("reading {}", root.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_official_mirror_manifest_matches(&path, matches)?;
        } else if path.file_name().and_then(|name| name.to_str()) == Some("manifest.csv")
            && official_mirror_manifest_path_matches(&path)
        {
            matches.push(path);
        }
    }
    Ok(())
}

fn official_mirror_manifest_path_matches(path: &Path) -> bool {
    let mut has_sat = false;
    let mut has_2026 = false;
    for part in path
        .components()
        .filter_map(|component| component.as_os_str().to_str())
    {
        let lower = part.to_ascii_lowercase();
        if lower == "sat" {
            has_sat = true;
        }
        if matches!(lower.as_str(), "2026" | "satcomp2026" | "satcomp2026-main") {
            has_2026 = true;
        }
    }
    has_sat && has_2026
}

fn find_official_mirror_benchmarks_dir(root: &Path) -> Option<PathBuf> {
    for candidate in OFFICIAL_MIRROR_DIR_CANDIDATES {
        let directory = root.join(candidate);
        if directory.is_dir() {
            return Some(directory);
        }
    }
    root.is_dir().then(|| root.to_path_buf())
}

fn parse_variants(raw: &str) -> Result<Vec<String>> {
    let variants: Vec<_> = raw
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToString::to_string)
        .collect();
    if variants.is_empty() {
        bail!("--variants must name at least one variant");
    }
    Ok(variants)
}

fn solver_root_and_run_path(
    opts: &SatCompMatrixRunOptions,
    variant: &str,
) -> Result<(PathBuf, PathBuf)> {
    if let Some(run_sh) = &opts.run_sh {
        let run_path = absolute_path(run_sh)?;
        let root = run_path.parent().unwrap_or(Path::new(".")).to_path_buf();
        return Ok((root, run_path));
    }
    let root = absolute_path(&opts.submission_root)?
        .join(format!("ay-{}-{}-{}", opts.track, opts.ai_class, variant));
    Ok((root.clone(), root.join("run.sh")))
}

fn decompress_if_needed(path: &Path, case_dir: &Path) -> Result<PathBuf> {
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("input.cnf");
    let (tool, output_name) = if let Some(stripped) = name.strip_suffix(".xz") {
        (Some("xz"), stripped)
    } else if let Some(stripped) = name.strip_suffix(".gz") {
        (Some("gzip"), stripped)
    } else if let Some(stripped) = name.strip_suffix(".bz2") {
        (Some("bzip2"), stripped)
    } else {
        (None, name)
    };
    let output_path = case_dir.join(output_name);
    if let Some(tool) = tool {
        let output = File::create(&output_path)
            .with_context(|| format!("creating decompressed {}", output_path.display()))?;
        let child = Command::new(tool)
            .arg("-dc")
            .arg(path)
            .stdout(Stdio::from(output))
            .stderr(Stdio::piped())
            .spawn()
            .with_context(|| format!("running {tool} -dc {}", path.display()))?;
        let output = child.wait_with_output()?;
        if !output.status.success() {
            let _ = fs::remove_file(&output_path);
            bail!(
                "{tool} -dc failed for {}: {}",
                path.display(),
                String::from_utf8_lossy(&output.stderr)
            );
        }
    } else {
        fs::copy(path, &output_path)
            .with_context(|| format!("copying {} to {}", path.display(), output_path.display()))?;
    }
    Ok(output_path)
}

fn summarize_records(records: &[Record], timeout_sec: f64, include_families: bool) -> Summary {
    let mut summary = Summary {
        total: records.len(),
        timeout_sec,
        ..Summary::default()
    };
    for row in records {
        let solved = row_solved(row);
        if solved {
            summary.solved += 1;
            match row.get("actual") {
                "sat" => summary.solved_sat += 1,
                "unsat" => summary.solved_unsat += 1,
                _ => {}
            }
        }
        match row.get("expected") {
            "sat" => summary.expected_sat += 1,
            "unsat" => summary.expected_unsat += 1,
            _ => {}
        }
        match row.get("actual") {
            "unknown" => summary.unknown += 1,
            "timeout" => summary.timeout += 1,
            "error" => summary.error += 1,
            _ => {}
        }
        summary.wrong += usize::from(row.truthy("wrong"));
        summary.invalid += usize::from(row.truthy("invalid"));
        summary.par2_total += row.get("par2_s").parse::<f64>().unwrap_or(0.0);
    }
    let validation = validation_counts_from_rows(records);
    summary.sat_model_valid = validation.sat_model_valid;
    summary.sat_model_invalid = validation.sat_model_invalid;
    summary.unsat_proof_valid = validation.unsat_proof_valid;
    summary.unsat_proof_invalid = validation.unsat_proof_invalid;
    summary.par2_total = round3(summary.par2_total);
    summary.par2_avg = if summary.total == 0 {
        0.0
    } else {
        round3(summary.par2_total / summary.total as f64)
    };
    if include_families {
        let mut grouped: BTreeMap<String, Vec<Record>> = BTreeMap::new();
        for row in records {
            grouped
                .entry(row.get("family").to_string())
                .or_default()
                .push(row.clone());
        }
        summary.families = Some(
            grouped
                .into_iter()
                .map(|(family, rows)| (family, summarize_records(&rows, timeout_sec, false)))
                .collect(),
        );
    }
    summary
}

fn build_scoreboard(
    opts: &SatCompMatrixRunOptions,
    output_dir: &Path,
    records_by_variant: &BTreeMap<String, Vec<Record>>,
    timeout_sec: f64,
) -> JsonValue {
    let mut variants = serde_json::Map::new();
    for (variant, records) in records_by_variant {
        variants.insert(
            variant.clone(),
            json!({
                "run_path": records.first().map(|row| row.get("run_path")).unwrap_or(""),
                "raw_tsv": path_string(&output_dir.join(format!("{variant}-raw.tsv"))),
                "summary": summary_json(&summarize_records(records, timeout_sec, true)),
            }),
        );
    }
    json!({
        "schema": "ay.satcomp-matrix-scoreboard/v2-rust",
        "suite": opts.suite,
        "track": opts.track,
        "ai_class": opts.ai_class,
        "submission_root": path_string(&opts.submission_root),
        "benchmark_source": if opts.require_official_mirror || opts.suite == "sat-main-2026-official-mirror" { "official-mirror" } else { "custom" },
        "official_mirror_required": opts.require_official_mirror || opts.suite == "sat-main-2026-official-mirror",
        "official_mirror_root": path_string(&official_mirror_root(opts)),
        "timeout_sec": timeout_sec,
        "expected_total": opts.require_total,
        "require_total": opts.require_total,
        "filter_family": opts.filter_family,
        "limited": opts.limit.is_some(),
        "allow_smoke": opts.allow_smoke,
        "soundness": opts.soundness,
        "fail_on_wrong": opts.fail_on_wrong,
        "proof_checker": opts.proof_checker,
        "manifest": opts.manifest.as_ref().map(|path| path_string(path)),
        "source_commit": git_head(),
        "source_dirty": git_dirty(),
        "output_dir": path_string(output_dir),
        "variants": variants,
    })
}

fn summary_json(summary: &Summary) -> JsonValue {
    let families = summary.families.as_ref().map(|families| {
        let mut value = serde_json::Map::new();
        for (family, summary) in families {
            value.insert(family.clone(), summary_json(summary));
        }
        JsonValue::Object(value)
    });
    json!({
        "total": summary.total,
        "solved": summary.solved,
        "solved_sat": summary.solved_sat,
        "solved_unsat": summary.solved_unsat,
        "expected_sat": summary.expected_sat,
        "expected_unsat": summary.expected_unsat,
        "sat_model_valid": summary.sat_model_valid,
        "sat_model_invalid": summary.sat_model_invalid,
        "unsat_proof_valid": summary.unsat_proof_valid,
        "unsat_proof_invalid": summary.unsat_proof_invalid,
        "unknown": summary.unknown,
        "timeout": summary.timeout,
        "error": summary.error,
        "wrong": summary.wrong,
        "invalid": summary.invalid,
        "disqualified": summary.wrong != 0 || summary.invalid != 0,
        "par2_total": summary.par2_total,
        "par2_avg": summary.par2_avg,
        "timeout_sec": summary.timeout_sec,
        "families": families,
    })
}

fn require_score_bearing_scoreboard(scoreboard: &JsonValue) -> Result<()> {
    let mut errors = Vec::new();
    if string_value(scoreboard, "suite").as_deref() != Some("sat-main-2026-official-mirror") {
        errors.push(format!(
            "evidence summary requires suite 'sat-main-2026-official-mirror', got {:?}",
            scoreboard.get("suite")
        ));
    }
    if string_value(scoreboard, "benchmark_source").as_deref() != Some("official-mirror") {
        errors.push(format!(
            "evidence summary requires benchmark_source 'official-mirror', got {:?}",
            scoreboard.get("benchmark_source")
        ));
    }
    if scoreboard
        .get("official_mirror_required")
        .and_then(JsonValue::as_bool)
        != Some(true)
    {
        errors.push("evidence summary requires official_mirror_required=true".to_string());
    }
    if string_value(scoreboard, "official_mirror_root")
        .map(|value| value.trim().is_empty())
        .unwrap_or(true)
    {
        errors.push("evidence summary requires official_mirror_root".to_string());
    }
    if scoreboard.get("limited").and_then(JsonValue::as_bool) != Some(false) {
        errors.push("score-bearing evidence summary must not use --limit".to_string());
    }
    if scoreboard.get("source_dirty").and_then(JsonValue::as_bool) == Some(true) {
        errors.push("score-bearing evidence summary requires source_dirty=false".to_string());
    }
    let soundness = scoreboard
        .get("soundness")
        .and_then(JsonValue::as_bool)
        .unwrap_or(false);
    let fail_on_wrong = scoreboard
        .get("fail_on_wrong")
        .and_then(JsonValue::as_bool)
        .unwrap_or(false);
    if !soundness && !fail_on_wrong {
        errors.push(
            "score-bearing evidence summary requires --soundness or --fail-on-wrong".to_string(),
        );
    }
    let proof_checker = string_value(scoreboard, "proof_checker").unwrap_or_default();
    let checker_name = Path::new(&proof_checker)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("");
    if proof_checker.trim().is_empty()
        || proof_checker == "auto"
        || proof_checker == "none"
        || checker_name == "ay"
    {
        errors.push(
            "score-bearing evidence summary requires an explicit external LRAT proof checker"
                .to_string(),
        );
    }
    if errors.is_empty() {
        Ok(())
    } else {
        bail!("{}", errors.join("; "))
    }
}

fn read_variant_raw_rows(variant_data: &JsonValue, scoreboard_dir: &Path) -> Result<Vec<Record>> {
    let raw_tsv = variant_data
        .get("raw_tsv")
        .and_then(JsonValue::as_str)
        .context("evidence summary requires the variant raw_tsv artifact")?;
    let Some(raw_path) = resolve_reported_path(raw_tsv, scoreboard_dir) else {
        bail!("evidence summary requires the variant raw_tsv artifact");
    };
    if !raw_path.is_file() {
        bail!("evidence summary requires the variant raw_tsv artifact");
    }
    read_tsv_records(&raw_path)
}

fn read_tsv_records(path: &Path) -> Result<Vec<Record>> {
    let reader = BufReader::new(
        File::open(path).with_context(|| format!("opening raw TSV {}", path.display()))?,
    );
    let mut lines = reader.lines();
    let Some(header) = lines.next() else {
        return Ok(Vec::new());
    };
    let headers: Vec<String> = header?.split('\t').map(ToString::to_string).collect();
    let mut rows = Vec::new();
    for line in lines {
        let line = line?;
        if line.trim().is_empty() {
            continue;
        }
        let values: Vec<&str> = line.split('\t').collect();
        let mut fields = BTreeMap::new();
        for (idx, header) in headers.iter().enumerate() {
            fields.insert(
                header.clone(),
                values.get(idx).copied().unwrap_or_default().to_string(),
            );
        }
        rows.push(Record { fields });
    }
    Ok(rows)
}

fn require_raw_rows_match_summary(
    rows: &[Record],
    summary: &serde_json::Map<String, JsonValue>,
) -> Result<()> {
    let Some(total) = summary.get("total").and_then(json_as_i64) else {
        bail!("evidence summary requires variant summary total");
    };
    if total <= 0 {
        bail!("evidence summary requires positive variant summary total, got {total}");
    }
    if rows.len() != total as usize {
        bail!(
            "evidence summary raw_tsv row count does not match variant summary total: {} row(s) vs total={total}",
            rows.len()
        );
    }
    Ok(())
}

fn validation_counts_from_rows(rows: &[Record]) -> Summary {
    let mut summary = Summary::default();
    for row in rows {
        match row.get("actual").trim().to_ascii_lowercase().as_str() {
            "sat" => {
                if row.get("model_status").trim().eq_ignore_ascii_case("valid") {
                    summary.sat_model_valid += 1;
                } else {
                    summary.sat_model_invalid += 1;
                }
            }
            "unsat" => {
                if row.get("proof_status").trim().eq_ignore_ascii_case("valid")
                    && row.get("ay_lrat_status").trim().eq_ignore_ascii_case("ok")
                    && row
                        .get("proof_checker_status")
                        .trim()
                        .eq_ignore_ascii_case("ok")
                {
                    summary.unsat_proof_valid += 1;
                } else {
                    summary.unsat_proof_invalid += 1;
                }
            }
            _ => {}
        }
    }
    summary
}

fn validation_count_fields(summary: &Summary) -> [(&'static str, usize); 4] {
    [
        ("sat_model_valid", summary.sat_model_valid),
        ("sat_model_invalid", summary.sat_model_invalid),
        ("unsat_proof_valid", summary.unsat_proof_valid),
        ("unsat_proof_invalid", summary.unsat_proof_invalid),
    ]
}

fn require_summary_validation_counts_match(
    summary: &serde_json::Map<String, JsonValue>,
    rows: &[Record],
) -> Result<()> {
    let expected = validation_counts_from_rows(rows);
    let mut mismatched = Vec::new();
    for (field, expected_value) in validation_count_fields(&expected) {
        let Some(value) = summary.get(field) else {
            continue;
        };
        match json_as_i64(value) {
            Some(actual) if actual >= 0 && actual as usize == expected_value => {}
            Some(actual) if actual >= 0 => mismatched.push(format!(
                "{field}={actual} does not match raw TSV count {expected_value}"
            )),
            _ => mismatched.push(format!("{field} is not a nonnegative integer: {value:?}")),
        }
    }

    let mut errors = Vec::new();
    errors.extend(mismatched);
    if errors.is_empty() {
        Ok(())
    } else {
        bail!("{}", errors.join("; "))
    }
}

fn require_score_bearing_row_validation(rows: &[Record]) -> Result<()> {
    let required_columns = [
        "actual",
        "wrong",
        "invalid",
        "proof_status",
        "ay_lrat_status",
        "proof_checker_status",
        "external_proof_checker_verdict_artifact",
        "external_proof_checker_verdict_artifact_sha256",
        "external_proof_checker_verdict_artifact_schema",
        "external_proof_checker_verdict",
        "external_proof_checker_proof_out_path",
        "proof_path",
        "proof_bytes",
        "proof_sha256",
        "model_status",
        "model_checker_artifact",
        "model_checker_artifact_sha256",
        "model_checker_artifact_schema",
        "model_checker_formula",
        "model_checker_stdout",
        "model_checker_command_json",
        "model_checker_exit_status",
        "binary_path",
        "binary_sha256",
        "binary_size_bytes",
        "binary_executable",
        "ay",
        "ay_sha256",
    ];
    let mut errors = Vec::new();
    for (idx, row) in rows.iter().enumerate() {
        let row_no = idx + 1;
        let instance = first_non_empty(&[
            row.get("instance").to_string(),
            row.get("path").to_string(),
            format!("row {row_no}"),
        ]);
        let missing: Vec<_> = required_columns
            .iter()
            .filter(|column| !row.fields.contains_key(**column))
            .copied()
            .collect();
        if !missing.is_empty() {
            errors.push(format!(
                "score-bearing row {row_no} ({instance}) missing validation columns: {}",
                missing.join(", ")
            ));
            continue;
        }
        if parse_i64(row.get("wrong")) != Some(0) {
            errors.push(format!(
                "score-bearing row {row_no} ({instance}) has wrong={:?}",
                row.get("wrong")
            ));
        }
        if parse_i64(row.get("invalid")) != Some(0) {
            errors.push(format!(
                "score-bearing row {row_no} ({instance}) has invalid={:?}",
                row.get("invalid")
            ));
        }
        require_binary_provenance_row(row_no, &instance, row, &mut errors);
        match row.get("actual").trim().to_ascii_lowercase().as_str() {
            "sat" => {
                require_non_unsat_no_proof_authority(row_no, &instance, row, &mut errors);
                if !row.get("model_status").trim().eq_ignore_ascii_case("valid") {
                    errors.push(format!(
                        "score-bearing SAT row {row_no} ({instance}) requires model_status=valid, got {:?}",
                        row.get("model_status")
                    ));
                }
                require_sat_model_evidence_row(row_no, &instance, row, &mut errors);
            }
            "unsat" => require_unsat_evidence_row(row_no, &instance, row, &mut errors),
            _ => require_non_unsat_no_proof_authority(row_no, &instance, row, &mut errors),
        }
        errors.extend(fmla_reconstructed_model_validation_gate_errors(
            row_no, &instance, row,
        ));
        errors.extend(fmla_preprocess_transaction_gate_errors(
            row_no, &instance, row,
        ));
    }
    if errors.is_empty() {
        Ok(())
    } else {
        bail!("{}", errors.join("; "))
    }
}

fn require_binary_provenance_row(
    row_no: usize,
    instance: &str,
    row: &Record,
    errors: &mut Vec<String>,
) {
    let binary_path = row.get("binary_path").trim();
    let binary_sha256 = row.get("binary_sha256").trim();
    if binary_path.is_empty() {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) requires binary_path"
        ));
        return;
    }
    if !is_hex_sha256(binary_sha256) {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) requires binary_sha256 to be a 64-character hex SHA256, got {binary_sha256:?}"
        ));
    }
    if row.get("ay").trim() != binary_path {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) requires ay to match binary_path"
        ));
    }
    if row.get("ay_sha256").trim() != binary_sha256 {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) requires ay_sha256 to match binary_sha256"
        ));
    }
    if parse_i64(row.get("binary_size_bytes")).unwrap_or(0) <= 0 {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) requires positive binary_size_bytes, got {:?}",
            row.get("binary_size_bytes")
        ));
    }
    if parse_i64(row.get("binary_executable")) != Some(1) {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) requires binary_executable=1, got {:?}",
            row.get("binary_executable")
        ));
    }
    let path = evidence_path(binary_path);
    if !path.is_file() {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) binary_path missing: {binary_path}"
        ));
    } else if sha256_file(&path)
        .map(|sha| sha != binary_sha256)
        .unwrap_or(true)
    {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) binary_sha256 mismatch"
        ));
    }
}

fn require_non_unsat_no_proof_authority(
    row_no: usize,
    instance: &str,
    row: &Record,
    errors: &mut Vec<String>,
) {
    let actual = row.get("actual").trim();
    let proof_status = row.get("proof_status").trim();
    if proof_status.eq_ignore_ascii_case("valid") {
        errors.push(format!(
            "score-bearing non-UNSAT row {row_no} ({instance}) actual={actual:?} must not record proof_status=valid"
        ));
    }
    if row.get("ay_lrat_status").trim().eq_ignore_ascii_case("ok") {
        errors.push(format!(
            "score-bearing non-UNSAT row {row_no} ({instance}) actual={actual:?} must not record ay_lrat_status=ok"
        ));
    }
    if row
        .get("proof_checker_status")
        .trim()
        .eq_ignore_ascii_case("ok")
    {
        errors.push(format!(
            "score-bearing non-UNSAT row {row_no} ({instance}) actual={actual:?} must not record proof_checker_status=ok"
        ));
    }
    if non_unsat_row_records_external_checker_authority(row) {
        errors.push(format!(
            "score-bearing non-UNSAT row {row_no} ({instance}) actual={actual:?} must not record external proof checker authority"
        ));
    }
    if non_unsat_row_retains_proof_out(row) {
        if proof_status != STALE_NON_AUTHORITATIVE_PROOF_STATUS {
            errors.push(format!(
                "score-bearing non-UNSAT row {row_no} ({instance}) retained proof.out must be marked {STALE_NON_AUTHORITATIVE_PROOF_STATUS}, got {proof_status:?}"
            ));
        }
        errors.push(format!(
            "score-bearing non-UNSAT row {row_no} ({instance}) retained proof.out is stale/non-authoritative and cannot be used for evidence"
        ));
    }
}

fn non_unsat_row_records_external_checker_authority(row: &Record) -> bool {
    [
        "external_proof_checker_verdict_artifact",
        "external_proof_checker_verdict_artifact_sha256",
        "external_proof_checker_verdict_artifact_schema",
        "external_proof_checker_verdict",
        "external_proof_checker_proof_out_path",
    ]
    .iter()
    .any(|field| {
        let value = row.get(field).trim();
        !value.is_empty() && !value.eq_ignore_ascii_case("n/a")
    })
}

fn non_unsat_row_retains_proof_out(row: &Record) -> bool {
    if parse_i64(row.get("proof_bytes")).unwrap_or(0) > 0 {
        return true;
    }
    if !row.get("proof_sha256").trim().is_empty() {
        return true;
    }
    if !row
        .get("external_proof_checker_proof_out_path")
        .trim()
        .is_empty()
    {
        return true;
    }
    let proof_path = row.get("proof_path").trim();
    if proof_path.is_empty()
        || Path::new(proof_path)
            .file_name()
            .and_then(|name| name.to_str())
            != Some("proof.out")
    {
        return false;
    }
    evidence_path(proof_path)
        .metadata()
        .map(|metadata| metadata.is_file() && metadata.len() > 0)
        .unwrap_or(false)
}

fn require_sat_model_evidence_row(
    row_no: usize,
    instance: &str,
    row: &Record,
    errors: &mut Vec<String>,
) {
    let artifact = row.get("model_checker_artifact").trim();
    let artifact_sha256 = row.get("model_checker_artifact_sha256").trim();
    if artifact.is_empty() {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) requires model_checker_artifact"
        ));
    } else {
        let artifact_path = evidence_path(artifact);
        if !artifact_path.is_file() {
            errors.push(format!(
                "score-bearing SAT row {row_no} ({instance}) model_checker_artifact missing: {artifact}"
            ));
        } else {
            if sha256_file(&artifact_path)
                .map(|sha| sha != artifact_sha256)
                .unwrap_or(true)
            {
                errors.push(format!(
                    "score-bearing SAT row {row_no} ({instance}) model_checker_artifact_sha256 mismatch"
                ));
            }
            require_sat_model_artifact_payload(row_no, instance, row, &artifact_path, errors);
        }
    }
    if !is_hex_sha256(artifact_sha256) {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) requires model_checker_artifact_sha256 to be a 64-character hex SHA256, got {artifact_sha256:?}"
        ));
    }
    if row.get("model_checker_artifact_schema") != SAT_MODEL_CHECK_ARTIFACT_SCHEMA {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact_schema mismatch"
        ));
    }
    for field in ["model_checker_formula", "model_checker_stdout"] {
        let value = row.get(field).trim();
        if value.is_empty() {
            errors.push(format!(
                "score-bearing SAT row {row_no} ({instance}) requires {field}"
            ));
        } else if !evidence_path(value).is_file() {
            errors.push(format!(
                "score-bearing SAT row {row_no} ({instance}) {field} missing: {value}"
            ));
        }
    }
    if parse_i64(row.get("model_checker_exit_status")) != Some(0) {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) requires model_checker_exit_status=0, got {:?}",
            row.get("model_checker_exit_status")
        ));
    }
    require_sat_model_checker_command(row_no, instance, row, errors);
}

fn require_sat_model_artifact_payload(
    row_no: usize,
    instance: &str,
    row: &Record,
    artifact_path: &Path,
    errors: &mut Vec<String>,
) {
    let Ok(payload) = load_json_object(artifact_path) else {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact is not valid JSON"
        ));
        return;
    };
    if payload.get("schema").and_then(JsonValue::as_str) != Some(SAT_MODEL_CHECK_ARTIFACT_SCHEMA) {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact schema mismatch"
        ));
    }
    if payload.get("model_status").and_then(JsonValue::as_str) != Some("valid") {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact requires model_status=valid"
        ));
    }
    for (field, payload_field) in [
        ("model_checker_formula", "formula"),
        ("model_checker_stdout", "stdout"),
    ] {
        let expected = row.get(field).trim();
        let observed = payload
            .get(payload_field)
            .and_then(JsonValue::as_str)
            .unwrap_or_default()
            .trim();
        if !expected.is_empty() && observed != expected {
            errors.push(format!(
                "score-bearing SAT row {row_no} ({instance}) {field} does not match retained artifact"
            ));
        }
    }
    let payload_exit = payload.get("checker_exit_status").and_then(json_as_i64);
    match payload_exit {
        Some(0) => {}
        Some(observed) => errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact requires checker_exit_status=0, got {observed}"
        )),
        None => errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact requires checker_exit_status"
        )),
    }
    if let (Some(expected), Some(observed)) = (
        parse_i64(row.get("model_checker_exit_status")),
        payload_exit,
    ) {
        if observed != expected {
            errors.push(format!(
                "score-bearing SAT row {row_no} ({instance}) model_checker_artifact checker_exit_status does not match raw TSV"
            ));
        }
    }
    match payload
        .get("checker_command_json")
        .and_then(json_string_array)
    {
        Some(command) => {
            if !sat_model_checker_command_shape_is_valid(&command) {
                errors.push(format!(
                    "score-bearing SAT row {row_no} ({instance}) model_checker_artifact checker_command_json must invoke ay check model <formula> <stdout> --json"
                ));
            }
            let raw = row.get("model_checker_command_json").trim();
            if !raw.is_empty() {
                if let Ok(expected) = serde_json::from_str::<Vec<String>>(raw) {
                    if command != expected {
                        errors.push(format!(
                            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact checker_command_json does not match raw TSV"
                        ));
                    }
                }
            }
        }
        None => errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_artifact requires checker_command_json argv list"
        )),
    }
}

fn require_sat_model_checker_command(
    row_no: usize,
    instance: &str,
    row: &Record,
    errors: &mut Vec<String>,
) {
    let raw = row.get("model_checker_command_json").trim();
    if raw.is_empty() {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) requires model_checker_command_json"
        ));
        return;
    }
    let command: Vec<String> = match serde_json::from_str(raw) {
        Ok(command) => command,
        Err(err) => {
            errors.push(format!(
                "score-bearing SAT row {row_no} ({instance}) model_checker_command_json invalid JSON: {err}"
            ));
            return;
        }
    };
    if !sat_model_checker_command_shape_is_valid(&command) {
        errors.push(format!(
            "score-bearing SAT row {row_no} ({instance}) model_checker_command_json must invoke ay check model <formula> <stdout> --json"
        ));
        return;
    }
    for (field, index) in [
        ("model_checker_formula", 3usize),
        ("model_checker_stdout", 4usize),
    ] {
        let expected = row.get(field).trim();
        if !expected.is_empty() && command.get(index).map(String::as_str) != Some(expected) {
            errors.push(format!(
                "score-bearing SAT row {row_no} ({instance}) model_checker_command_json {field} argument mismatch"
            ));
        }
    }
}

fn sat_model_checker_command_shape_is_valid(command: &[String]) -> bool {
    command.len() == 6
        && !command[0].trim().is_empty()
        && command[1] == "check"
        && command[2] == "model"
        && command[5] == "--json"
}

fn json_string_array(value: &JsonValue) -> Option<Vec<String>> {
    value
        .as_array()?
        .iter()
        .map(|part| part.as_str().map(ToString::to_string))
        .collect()
}

fn require_unsat_evidence_row(
    row_no: usize,
    instance: &str,
    row: &Record,
    errors: &mut Vec<String>,
) {
    if !row.get("proof_status").trim().eq_ignore_ascii_case("valid") {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires proof_status=valid, got {:?}",
            row.get("proof_status")
        ));
    }
    if !row.get("ay_lrat_status").trim().eq_ignore_ascii_case("ok") {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires ay_lrat_status=ok, got {:?}",
            row.get("ay_lrat_status")
        ));
    }
    if !row
        .get("proof_checker_status")
        .trim()
        .eq_ignore_ascii_case("ok")
    {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires proof_checker_status=ok, got {:?}",
            row.get("proof_checker_status")
        ));
    }
    let artifact = row.get("external_proof_checker_verdict_artifact").trim();
    let artifact_sha256 = row
        .get("external_proof_checker_verdict_artifact_sha256")
        .trim();
    let mut artifact_path_for_payload: Option<PathBuf> = None;
    if artifact.is_empty() {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires external_proof_checker_verdict_artifact"
        ));
    } else {
        let artifact_path = evidence_path(artifact);
        if !artifact_path.is_file() {
            errors.push(format!(
                "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact missing: {artifact}"
            ));
        } else if sha256_file(&artifact_path)
            .map(|sha| sha != artifact_sha256)
            .unwrap_or(true)
        {
            errors.push(format!(
                "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact sha256 mismatch"
            ));
            artifact_path_for_payload = Some(artifact_path);
        } else {
            artifact_path_for_payload = Some(artifact_path);
        }
    }
    if !is_hex_sha256(artifact_sha256) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires external_proof_checker_verdict_artifact_sha256 to be a 64-character hex SHA256, got {artifact_sha256:?}"
        ));
    }
    if row.get("external_proof_checker_verdict_artifact_schema") != EXTERNAL_CHECKER_VERDICT_SCHEMA
    {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact schema mismatch"
        ));
    }
    if row.get("external_proof_checker_verdict") != "VERIFIED_UNSAT" {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires external_proof_checker_verdict=VERIFIED_UNSAT"
        ));
    }
    let proof_out = row.get("external_proof_checker_proof_out_path").trim();
    if proof_out.is_empty()
        || Path::new(proof_out)
            .file_name()
            .and_then(|name| name.to_str())
            != Some("proof.out")
    {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker proof_out path must name proof.out"
        ));
    }
    if parse_i64(row.get("proof_bytes")).unwrap_or(0) <= 0 {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires positive proof_bytes, got {:?}",
            row.get("proof_bytes")
        ));
    }
    if row.get("proof_path").trim().is_empty() {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires proof_path"
        ));
    }
    let proof_sha = row.get("proof_sha256").trim();
    if !is_hex_sha256(proof_sha) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) requires proof_sha256 to be a 64-character hex SHA256, got {proof_sha:?}"
        ));
    }
    if let Some(artifact_path) = artifact_path_for_payload {
        require_external_checker_artifact_payload(row_no, instance, row, &artifact_path, errors);
    }
}

fn require_external_checker_artifact_payload(
    row_no: usize,
    instance: &str,
    row: &Record,
    artifact_path: &Path,
    errors: &mut Vec<String>,
) {
    let Ok(payload) = load_json_object(artifact_path) else {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact is not valid JSON"
        ));
        return;
    };
    if payload.get("schema").and_then(JsonValue::as_str) != Some(EXTERNAL_CHECKER_VERDICT_SCHEMA) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact schema mismatch"
        ));
    }
    if payload.get("runtime_field").and_then(JsonValue::as_str)
        != Some("external_proof_checker_verdict_artifact")
    {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact runtime_field mismatch"
        ));
    }
    if payload.get("verdict").and_then(JsonValue::as_str) != Some("VERIFIED_UNSAT") {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact requires verdict=VERIFIED_UNSAT"
        ));
    }

    require_artifact_path_matches_row(
        row_no,
        instance,
        "external checker verdict artifact artifact_path",
        payload.get("artifact_path").and_then(JsonValue::as_str),
        row.get("external_proof_checker_verdict_artifact"),
        errors,
    );
    let payload_proof_out = payload
        .get("proof_out_path")
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    require_artifact_path_matches_row(
        row_no,
        instance,
        "external checker verdict artifact proof_out_path",
        Some(payload_proof_out),
        row.get("external_proof_checker_proof_out_path"),
        errors,
    );
    require_artifact_path_matches_row(
        row_no,
        instance,
        "external checker verdict artifact proof_out_path",
        Some(payload_proof_out),
        row.get("proof_path"),
        errors,
    );

    let payload_proof_sha = payload
        .get("proof_out_sha256")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .trim();
    let proof_sha = row.get("proof_sha256").trim();
    if payload_proof_sha.is_empty() {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact requires proof_out_sha256"
        ));
    } else if !proof_sha.is_empty() && payload_proof_sha != proof_sha {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact proof_out_sha256 does not match proof_sha256"
        ));
    }
    if !payload_proof_out.trim().is_empty() {
        let proof_path = evidence_path(payload_proof_out);
        if proof_path.is_file()
            && sha256_file(&proof_path)
                .map(|sha| sha != payload_proof_sha)
                .unwrap_or(true)
        {
            errors.push(format!(
                "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact proof_out_sha256 does not match retained proof.out"
            ));
        }
    }

    let checked_dimacs_path = payload
        .get("checked_dimacs_path")
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    require_artifact_path_matches_row(
        row_no,
        instance,
        "external checker verdict artifact checked_dimacs_path",
        Some(checked_dimacs_path),
        row.get("path"),
        errors,
    );
    let checked_dimacs_sha = payload
        .get("checked_dimacs_sha256")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .trim();
    if checked_dimacs_sha.is_empty() {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact requires checked_dimacs_sha256"
        ));
    } else if !checked_dimacs_path.trim().is_empty() {
        let checked_dimacs = evidence_path(checked_dimacs_path);
        if checked_dimacs.is_file()
            && sha256_file(&checked_dimacs)
                .map(|sha| sha != checked_dimacs_sha)
                .unwrap_or(true)
        {
            errors.push(format!(
                "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact checked_dimacs_sha256 does not match retained DIMACS"
            ));
        }
    }

    if payload.get("checker_exit_code").and_then(json_as_i64) != Some(0) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact requires checker_exit_code=0"
        ));
    }
    let checker_stdout = payload
        .get("checker_stdout")
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    let checker_stderr = payload
        .get("checker_stderr")
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    if !proof_checker_output_is_verified(checker_stdout, checker_stderr) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact checker_stdout/checker_stderr do not contain a clean VERIFIED verdict"
        ));
    }

    match payload.get("checker_argv").and_then(json_string_array) {
        Some(argv) => require_external_checker_argv_matches_payload(
            row_no,
            instance,
            row,
            &payload,
            &argv,
            errors,
        ),
        None => errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact requires checker_argv"
        )),
    }
}

fn require_artifact_path_matches_row(
    row_no: usize,
    instance: &str,
    label: &str,
    observed: Option<&str>,
    expected: &str,
    errors: &mut Vec<String>,
) {
    let observed = observed.unwrap_or_default().trim();
    let expected = expected.trim();
    if observed.is_empty() {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) {label} is missing"
        ));
    } else if !expected.is_empty() && !evidence_paths_match(observed, expected) {
        errors.push(format!(
            "score-bearing row {row_no} ({instance}) {label} does not match raw TSV"
        ));
    }
}

fn require_external_checker_argv_matches_payload(
    row_no: usize,
    instance: &str,
    row: &Record,
    payload: &JsonValue,
    argv: &[String],
    errors: &mut Vec<String>,
) {
    if argv.len() != 3 || argv[0].trim().is_empty() {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact checker_argv must be [checker, dimacs, proof.out]"
        ));
        return;
    }
    let checker_path = payload
        .get("checker_path")
        .and_then(JsonValue::as_str)
        .unwrap_or_default();
    if !checker_path.is_empty() && !evidence_paths_match(&argv[0], checker_path) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact checker_argv[0] does not match checker_path"
        ));
    }
    let checked_dimacs = payload
        .get("checked_dimacs_path")
        .and_then(JsonValue::as_str)
        .unwrap_or_else(|| row.get("path"));
    if !evidence_paths_match(&argv[1], checked_dimacs) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact checker_argv[1] does not match checked_dimacs_path"
        ));
    }
    let proof_out = payload
        .get("proof_out_path")
        .and_then(JsonValue::as_str)
        .unwrap_or_else(|| row.get("external_proof_checker_proof_out_path"));
    if !evidence_paths_match(&argv[2], proof_out) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact checker_argv[2] does not match proof_out_path"
        ));
    }
    let command = payload
        .get("checker_command")
        .and_then(JsonValue::as_str)
        .unwrap_or_default()
        .trim();
    if command.is_empty() {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact requires checker_command"
        ));
    } else if command != shell_join(argv) {
        errors.push(format!(
            "score-bearing UNSAT row {row_no} ({instance}) external checker verdict artifact checker_command does not match checker_argv"
        ));
    }
}

fn fmla_reconstructed_model_validation_gate_errors(
    row_no: usize,
    instance: &str,
    row: &Record,
) -> Vec<String> {
    if !row_matches_fmla_equiv_chain_4_6_6(row) {
        return Vec::new();
    }
    if !row.get("actual").trim().eq_ignore_ascii_case("sat") {
        return Vec::new();
    }

    let prefix = format!("score-bearing FmlaEquivChain_4_6_6 SAT row {row_no} ({instance})");
    let missing: Vec<_> = FMLA_RECONSTRUCTED_MODEL_REQUIRED_VALID_PACKET_FIELDS
        .iter()
        .filter(|field| row.get(field).trim().is_empty())
        .copied()
        .collect();
    let mut invalid = Vec::new();

    for field in [
        "reconstructed_original_dimacs_model_stdout_present",
        "reconstructed_original_dimacs_model_stdout_matches_solver_stdout",
        "reconstructed_original_dimacs_model_verdict_written",
    ] {
        if parse_i64(row.get(field)) != Some(1) {
            invalid.push(format!("{field}={:?}", row.get(field)));
        }
    }

    if parse_i64(row.get("reconstructed_original_dimacs_model_checker_exit_code")) != Some(0) {
        invalid.push(format!(
            "reconstructed_original_dimacs_model_checker_exit_code={:?}",
            row.get("reconstructed_original_dimacs_model_checker_exit_code")
        ));
    }

    let packet_status = row
        .get("reconstructed_original_dimacs_model_packet_status")
        .trim()
        .to_ascii_lowercase();
    if packet_status != "valid" {
        invalid.push(format!(
            "reconstructed_original_dimacs_model_packet_status={packet_status:?}"
        ));
    }

    for field in FMLA_RECONSTRUCTED_MODEL_SHA256_FIELDS {
        let value = row.get(field).trim();
        if !value.is_empty() && !is_hex_sha256(value) {
            invalid.push(format!(
                "{field} must be a 64-character hex SHA256, got {value:?}"
            ));
        }
    }

    let solver_stdout_sha256 = row
        .get("reconstructed_original_dimacs_model_solver_stdout_sha256")
        .trim();
    let reconstructed_stdout_sha256 = row
        .get("reconstructed_original_dimacs_model_stdout_sha256")
        .trim();
    if !solver_stdout_sha256.is_empty()
        && !reconstructed_stdout_sha256.is_empty()
        && solver_stdout_sha256 != reconstructed_stdout_sha256
    {
        invalid.push(
            "reconstructed_original_dimacs_model_solver_stdout_sha256 must match reconstructed_original_dimacs_model_stdout_sha256"
                .to_string(),
        );
    }

    let packet_reason = row
        .get("reconstructed_original_dimacs_model_packet_invalid_reason")
        .trim();
    if !packet_reason.is_empty() {
        invalid.push(format!(
            "reconstructed_original_dimacs_model_packet_invalid_reason={packet_reason:?}"
        ));
    }

    let reconstruction_source =
        row.get("reconstructed_original_dimacs_model_reconstruction_source");
    if !reconstruction_source.is_empty()
        && (!reconstruction_source.contains("finalize_sat_model")
            || !reconstruction_source.contains("emit_dimacs_sat_model"))
    {
        invalid.push(
            "reconstructed_original_dimacs_model_reconstruction_source must name finalize_sat_model and emit_dimacs_sat_model"
                .to_string(),
        );
    }

    let command_raw = row
        .get("reconstructed_original_dimacs_model_check_command")
        .trim();
    if !command_raw.is_empty() {
        match serde_json::from_str::<JsonValue>(command_raw) {
            Ok(JsonValue::Array(parts)) => {
                let mut command = Vec::new();
                let mut non_string = false;
                for part in parts {
                    if let Some(text) = part.as_str() {
                        command.push(text.to_string());
                    } else {
                        non_string = true;
                    }
                }
                if non_string {
                    invalid.push(
                        "reconstructed_original_dimacs_model_check_command must be a JSON string list"
                            .to_string(),
                    );
                } else {
                    validate_fmla_reconstructed_model_command(row, &command, &mut invalid);
                }
            }
            Ok(_) => invalid.push(
                "reconstructed_original_dimacs_model_check_command must be a JSON string list"
                    .to_string(),
            ),
            Err(err) => invalid.push(format!(
                "reconstructed_original_dimacs_model_check_command invalid JSON: {err}"
            )),
        }
    }

    let mut errors = Vec::new();
    if !missing.is_empty() {
        errors.push(format!(
            "{prefix} requires W132 original-DIMACS reconstructed-model validation packet; missing fields: {}",
            missing.join(", ")
        ));
    }
    if !invalid.is_empty() {
        errors.push(format!(
            "{prefix} has invalid W132 original-DIMACS reconstructed-model validation packet fields: {}",
            invalid.join("; ")
        ));
    }
    errors
}

fn validate_fmla_reconstructed_model_command(
    row: &Record,
    command: &[String],
    invalid: &mut Vec<String>,
) {
    if command.len() < 2 || !evidence_paths_match(&command[1], FMLA_RECONSTRUCTED_MODEL_CHECKER) {
        invalid.push(
            "reconstructed_original_dimacs_model_check_command must invoke the W132 reconstructed-model checker"
                .to_string(),
        );
    }

    let missing_flags: Vec<_> = FMLA_RECONSTRUCTED_MODEL_REQUIRED_COMMAND_FLAGS
        .iter()
        .filter(|flag| !command.iter().any(|part| part == **flag))
        .copied()
        .collect();
    if !missing_flags.is_empty() {
        invalid.push(format!(
            "reconstructed_original_dimacs_model_check_command missing flags: {}",
            missing_flags.join(", ")
        ));
    }

    for (flag, field) in [
        (
            "--original-dimacs",
            "reconstructed_original_dimacs_model_original_path",
        ),
        (
            "--check-reconstructed-model",
            "reconstructed_original_dimacs_model_stdout",
        ),
        (
            "--verdict-out",
            "reconstructed_original_dimacs_model_verdict",
        ),
    ] {
        let expected = row.get(field).trim();
        let observed_values = command_flag_values(command, flag);
        if observed_values.is_empty() || observed_values.iter().any(|value| value.is_none()) {
            invalid.push(format!(
                "reconstructed_original_dimacs_model_check_command {flag} is missing its value"
            ));
        } else if observed_values.len() > 1 {
            invalid.push(format!(
                "reconstructed_original_dimacs_model_check_command has duplicate {flag} flags"
            ));
        } else {
            let observed = observed_values[0].unwrap_or_default();
            if !expected.is_empty() && !evidence_paths_match(observed, expected) {
                invalid.push(format!(
                    "reconstructed_original_dimacs_model_check_command {flag}={observed:?} does not match {field}={expected:?}"
                ));
            }
        }
    }
}

fn fmla_preprocess_transaction_gate_errors(
    row_no: usize,
    instance: &str,
    row: &Record,
) -> Vec<String> {
    if !row_exercises_fmla_destructive_preprocessing(row) {
        return Vec::new();
    }

    let prefix = format!("score-bearing FmlaEquivChain_4_6_6 row {row_no} ({instance})");
    let mut missing = Vec::new();
    let mut invalid = Vec::new();
    let mut values = BTreeMap::new();
    for field in PREPROCESS_TX_COUNTER_FIELDS {
        let text = row.get(field).trim();
        if text.is_empty() || text.eq_ignore_ascii_case("missing") {
            missing.push(*field);
            continue;
        }
        let Some(value) = parse_f64(text) else {
            invalid.push(format!("{field}={text}"));
            continue;
        };
        if !value.is_finite() || value < 0.0 {
            invalid.push(format!("{field}={text}"));
            continue;
        }
        values.insert(*field, value);
    }

    let mut errors = Vec::new();
    if !missing.is_empty() {
        errors.push(format!(
            "{prefix} missing required preprocess transaction counters: {}",
            missing.join(", ")
        ));
    }
    if !invalid.is_empty() {
        errors.push(format!(
            "{prefix} has invalid preprocess transaction counters: {}",
            invalid.join(", ")
        ));
    }
    if !missing.is_empty() || !invalid.is_empty() {
        return errors;
    }

    let started = values
        .get("sat.preprocess_tx_started")
        .copied()
        .unwrap_or(0.0);
    if started <= 0.0 {
        errors.push(format!(
            "{prefix} requires sat.preprocess_tx_started > 0 when destructive preprocessing counters are active"
        ));
    }

    let proof_dispositions: f64 = PREPROCESS_TX_PROOF_DISPOSITION_FIELDS
        .iter()
        .map(|field| values.get(field).copied().unwrap_or(0.0))
        .sum();
    if started > 0.0 && proof_dispositions <= 0.0 {
        errors.push(format!(
            "{prefix} has no preprocess transaction proof-obligation disposition"
        ));
    }

    let reconstruction_dispositions: f64 = PREPROCESS_TX_RECONSTRUCTION_DISPOSITION_FIELDS
        .iter()
        .map(|field| values.get(field).copied().unwrap_or(0.0))
        .sum();
    if started > 0.0 && reconstruction_dispositions <= 0.0 {
        errors.push(format!(
            "{prefix} has no preprocess transaction model-reconstruction disposition"
        ));
    }

    let unsafe_values: BTreeMap<_, _> = PREPROCESS_TX_FMLA_OBLIGATION_REJECTION_FIELDS
        .iter()
        .filter_map(|field| {
            let value = values.get(field).copied().unwrap_or(0.0);
            (value != 0.0).then_some((*field, value))
        })
        .collect();
    if !unsafe_values.is_empty() {
        errors.push(format!(
            "{prefix} has pending/rejected/missing preprocess transaction obligations: {}",
            format_counter_values(&unsafe_values)
        ));
    }

    errors
}

fn evidence_summary_expected_total(scoreboard: &JsonValue, row_count: usize) -> Result<usize> {
    match scoreboard.get("expected_total") {
        None | Some(JsonValue::Null) => Ok(row_count),
        Some(JsonValue::String(value)) if value.trim().is_empty() => Ok(row_count),
        Some(value) => {
            let Some(total) = json_as_i64(value) else {
                bail!(
                    "evidence summary requires positive expected_total when present, got {value:?}"
                );
            };
            if total <= 0 {
                bail!(
                    "evidence summary requires positive expected_total when present, got {value:?}"
                );
            }
            if total as usize != row_count {
                bail!(
                    "evidence summary expected_total does not match scored row count: {total} != {row_count}"
                );
            }
            Ok(total as usize)
        }
    }
}

fn require_rows_inside_official_mirror(rows: &[Record], root: Option<String>) -> Result<()> {
    let Some(root) = root else {
        bail!("evidence summary requires official_mirror_root");
    };
    let root = expand_home(Path::new(root.trim()));
    let mut errors = Vec::new();
    for row in rows {
        let raw_path = row.get("path");
        if raw_path.trim().is_empty() || !reported_path_is_inside_root(raw_path, &root) {
            let instance =
                first_non_empty(&[row.get("instance").to_string(), "unknown".to_string()]);
            errors.push(format!(
                "score-bearing row outside official mirror: {instance}"
            ));
        }
    }
    if errors.is_empty() {
        Ok(())
    } else {
        bail!("{}", errors.join("; "))
    }
}

fn discover_evidence_stats_json(
    raw_paths: &[PathBuf],
    scoreboard: &JsonValue,
    variant: &str,
    scoreboard_dir: &Path,
) -> Result<Vec<PathBuf>> {
    let mut paths = Vec::new();
    for raw in raw_paths {
        let path = absolute_path(raw)?;
        if path.is_dir() {
            collect_stats_json(&path, &mut paths)?;
        } else {
            paths.push(path);
        }
    }
    if !paths.is_empty() {
        paths.sort();
        return Ok(paths);
    }
    let Some(output_dir) = string_value(scoreboard, "output_dir")
        .and_then(|raw| resolve_reported_path(&raw, scoreboard_dir))
    else {
        return Ok(Vec::new());
    };
    let run_dir = output_dir.join("runs").join(variant);
    if run_dir.is_dir() {
        collect_stats_json(&run_dir, &mut paths)?;
    }
    paths.sort();
    Ok(paths)
}

fn collect_stats_json(dir: &Path, paths: &mut Vec<PathBuf>) -> Result<()> {
    for entry in fs::read_dir(dir).with_context(|| format!("reading {}", dir.display()))? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            collect_stats_json(&path, paths)?;
        } else if path.extension().is_some_and(|ext| ext == "json")
            && path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.starts_with("stats"))
        {
            paths.push(path);
        }
    }
    Ok(())
}

fn load_stats_json(path: &Path) -> Result<JsonValue> {
    let value = load_json_object(path)?;
    if value.get("schema").and_then(JsonValue::as_str) != Some(STATS_JSON_SCHEMA) {
        bail!(
            "{path}: expected {STATS_JSON_SCHEMA:?} stats JSON",
            path = path.display()
        );
    }
    Ok(value)
}

fn merge_stats_counters(docs: &[JsonValue]) -> BTreeMap<String, i64> {
    let mut counters: BTreeMap<String, i64> = SAT_REQUIRED_EVIDENCE_COUNTERS
        .iter()
        .map(|counter| ((*counter).to_string(), 0))
        .collect();
    for doc in docs {
        let mut raw_counter_keys = std::collections::BTreeSet::new();
        if let Some(raw_counters) = doc.get("counters").and_then(JsonValue::as_object) {
            for (key, value) in raw_counters {
                raw_counter_keys.insert(key.clone());
                if let Some(parsed) = json_as_i64(value) {
                    *counters.entry(key.clone()).or_insert(0) += parsed;
                }
            }
        }
        if let Some(application_counter) = doc
            .get("competition_jit")
            .and_then(|value| value.get("application_counter"))
            .and_then(JsonValue::as_object)
        {
            let key = application_counter.get("key").and_then(JsonValue::as_str);
            let value = application_counter.get("value").and_then(json_as_i64);
            if let (Some(key), Some(value)) = (key, value) {
                if !raw_counter_keys.contains(key) {
                    *counters.entry(key.to_string()).or_insert(0) += value;
                }
            }
        }
    }
    counters
}

fn require_candidate_mode_counters(
    mode: EvidenceCandidateMode,
    counters: &BTreeMap<String, i64>,
) -> Result<()> {
    let helper_applications = *counters.get(SAT_NATIVE_HELPER_COUNTER).unwrap_or(&0);
    let conflict_applications = *counters.get(SAT_CONFLICT_ANALYSIS_COUNTER).unwrap_or(&0);
    match mode {
        EvidenceCandidateMode::Off => {
            if helper_applications != 0 {
                bail!("off-mode evidence expected {SAT_NATIVE_HELPER_COUNTER}=0, got {helper_applications}");
            }
        }
        EvidenceCandidateMode::Current => {
            let mut errors = Vec::new();
            if helper_applications <= 0 {
                errors.push(format!(
                    "current-mode evidence summary requires {SAT_NATIVE_HELPER_COUNTER:?} > 0, got {helper_applications}"
                ));
            }
            if conflict_applications <= 0 {
                errors.push(format!(
                    "current-mode evidence summary requires {SAT_CONFLICT_ANALYSIS_COUNTER:?} > 0, got {conflict_applications}"
                ));
            }
            if helper_applications > 0
                && conflict_applications > 0
                && helper_applications < conflict_applications
            {
                errors.push(format!(
                    "current-mode evidence summary: {SAT_NATIVE_HELPER_COUNTER:?} must cover {SAT_CONFLICT_ANALYSIS_COUNTER:?}, got {helper_applications} < {conflict_applications}"
                ));
            }
            if !errors.is_empty() {
                bail!("{}", errors.join("; "));
            }
        }
    }
    Ok(())
}

fn build_competition_jit_evidence(
    mode: EvidenceCandidateMode,
    counters: &BTreeMap<String, i64>,
) -> Result<JsonValue> {
    let applications = *counters.get(SAT_NATIVE_HELPER_COUNTER).unwrap_or(&0);
    if mode == EvidenceCandidateMode::Off && applications != 0 {
        bail!("off-mode evidence expected {SAT_NATIVE_HELPER_COUNTER}=0, got {applications}");
    }
    let native_dispatch = mode == EvidenceCandidateMode::Current && applications > 0;
    Ok(json!({
        "schema_version": 1,
        "track": "sat",
        "artifact_id": SAT_NATIVE_HELPER_ARTIFACT,
        "artifact": SAT_NATIVE_HELPER_ARTIFACT,
        "candidate_mode": mode.as_str(),
        "application_counter": {
            "key": SAT_NATIVE_HELPER_COUNTER,
            "value": applications,
        },
        "requested_mode": mode.as_str(),
        "native_dispatch": native_dispatch,
        "fail_closed": mode == EvidenceCandidateMode::Current && !native_dispatch,
    }))
}

fn summarize_evidence_totals(
    summary: &serde_json::Map<String, JsonValue>,
    rows: &[Record],
) -> JsonValue {
    let mut proof_failures = 0i64;
    let mut witness_failures = 0i64;
    let mut crashes = 0i64;
    for row in rows {
        let row_invalid = parse_i64(row.get("invalid")).unwrap_or(0) != 0;
        let proof_failed =
            row_status_failed(row.get("proof_status"), &["", "n/a", "valid", "unchecked"]);
        let witness_failed =
            row_status_failed(row.get("model_status"), &["", "n/a", "valid", "unchecked"]);
        let mut crashed = row.get("actual").trim().eq_ignore_ascii_case("error");
        if let Some(exit_code) = parse_i64(row.get("exit_code")) {
            if !matches!(exit_code, 0 | 10 | 20 | 30 | 124) {
                crashed = true;
            }
        }
        if proof_failed {
            proof_failures += 1;
        }
        if witness_failed {
            witness_failures += 1;
        }
        if crashed {
            crashes += 1;
        }
        if row_invalid && !(proof_failed || witness_failed || crashed) {
            proof_failures += 1;
        }
    }
    let summary_invalid = summary.get("invalid").and_then(json_as_i64).unwrap_or(0);
    if rows.is_empty() && summary_invalid != 0 {
        proof_failures = summary_invalid;
    }
    proof_failures = proof_failures.max((summary_invalid - witness_failures - crashes).max(0));
    crashes = crashes.max(summary.get("error").and_then(json_as_i64).unwrap_or(0));
    let validation = validation_counts_from_rows(rows);
    json!({
        "solved": summary.get("solved").and_then(json_as_i64).unwrap_or(0),
        "par2": summary.get("par2_total").and_then(json_as_f64).unwrap_or(0.0),
        "wrong_answers": summary.get("wrong").and_then(json_as_i64).unwrap_or(0),
        "sat_model_valid": validation.sat_model_valid,
        "sat_model_invalid": validation.sat_model_invalid,
        "unsat_proof_valid": validation.unsat_proof_valid,
        "unsat_proof_invalid": validation.unsat_proof_invalid,
        "proof_failures": proof_failures,
        "witness_failures": witness_failures,
        "crashes": crashes,
    })
}

fn build_satcomp_matrix_provenance(
    scoreboard: &JsonValue,
    corpus_fingerprint: &str,
    variant: &str,
    stats_json_count: usize,
    expected_total: usize,
) -> JsonValue {
    let mut run_identity = serde_json::Map::new();
    for key in [
        "suite",
        "track",
        "ai_class",
        "timeout_sec",
        "proof_checker",
        "official_mirror_root",
    ] {
        if let Some(value) = scoreboard.get(key) {
            run_identity.insert(key.to_string(), value.clone());
        }
    }
    run_identity.insert(
        "soundness".to_string(),
        JsonValue::Bool(
            scoreboard
                .get("soundness")
                .and_then(JsonValue::as_bool)
                .unwrap_or(false),
        ),
    );
    run_identity.insert("expected_total".to_string(), json!(expected_total));
    for key in ["manifest", "benchmarks_dir", "require_total"] {
        if let Some(value) = scoreboard.get(key) {
            if !value.is_null() {
                run_identity.insert(key.to_string(), value.clone());
            }
        }
    }
    json!({
        "schema_version": SATCOMP_MATRIX_EVIDENCE_SCHEMA,
        "suite": scoreboard.get("suite").cloned().unwrap_or(JsonValue::Null),
        "benchmark_source": scoreboard.get("benchmark_source").cloned().unwrap_or(JsonValue::Null),
        "official_mirror_required": scoreboard.get("official_mirror_required").and_then(JsonValue::as_bool).unwrap_or(false),
        "official_mirror_root": string_value(scoreboard, "official_mirror_root").unwrap_or_default(),
        "limited": scoreboard.get("limited").and_then(JsonValue::as_bool).unwrap_or(false),
        "allow_smoke": scoreboard.get("allow_smoke").and_then(JsonValue::as_bool).unwrap_or(false),
        "corpus_fingerprint": corpus_fingerprint,
        "run_identity": JsonValue::Object(run_identity),
        "variant": variant,
        "source_commit": scoreboard.get("source_commit").cloned().unwrap_or(JsonValue::Null),
        "scoreboard_output_dir": scoreboard.get("output_dir").cloned().unwrap_or(JsonValue::Null),
        "stats_json_count": stats_json_count,
    })
}

fn write_summary_outputs(
    output_dir: &Path,
    records_by_variant: &BTreeMap<String, Vec<Record>>,
) -> Result<()> {
    let mut all = Vec::new();
    for records in records_by_variant.values() {
        all.extend(records.iter().cloned());
    }
    write_raw_tsv(&output_dir.join("summary.csv"), &all)?;
    let mut jsonl = File::create(output_dir.join("summary.jsonl"))?;
    for row in &all {
        let mut object = serde_json::Map::new();
        for &column in TSV_COLUMNS {
            object.insert(
                column.to_string(),
                JsonValue::String(row.get(column).to_string()),
            );
        }
        writeln!(jsonl, "{}", JsonValue::Object(object))?;
    }
    Ok(())
}

fn write_raw_tsv(path: &Path, records: &[Record]) -> Result<()> {
    let delimiter = if path.extension().is_some_and(|ext| ext == "csv") {
        ","
    } else {
        "\t"
    };
    let mut file = File::create(path).with_context(|| format!("creating {}", path.display()))?;
    writeln!(file, "{}", TSV_COLUMNS.join(delimiter))?;
    for row in records {
        let values: Vec<String> = TSV_COLUMNS
            .iter()
            .map(|column| escape_cell(row.get(column), delimiter))
            .collect();
        writeln!(file, "{}", values.join(delimiter))?;
    }
    Ok(())
}

fn write_scoreboard_md(path: &Path, scoreboard: &JsonValue) -> Result<()> {
    let variants = scoreboard
        .get("variants")
        .and_then(JsonValue::as_object)
        .context("scoreboard variants missing")?;
    let mut lines = vec![
        "# SAT-COMP Wrapper Scoreboard".to_string(),
        String::new(),
        format!("Suite: `{}`", scoreboard["suite"].as_str().unwrap_or("")),
        format!(
            "Run root: `{}`",
            scoreboard["submission_root"].as_str().unwrap_or("")
        ),
        format!(
            "Timeout: `{}s`",
            scoreboard["timeout_sec"].as_f64().unwrap_or(0.0)
        ),
        String::new(),
        markdown_table(
            &[
                "variant",
                "total",
                "solved",
                "SAT",
                "UNSAT",
                "wrong",
                "invalid",
                "PAR-2 total",
                "PAR-2 avg",
                "disqualified",
            ],
            variants
                .iter()
                .map(|(variant, data)| {
                    let s = &data["summary"];
                    vec![
                        variant.clone(),
                        value_string(&s["total"]),
                        value_string(&s["solved"]),
                        format!(
                            "{}/{}",
                            value_string(&s["solved_sat"]),
                            value_string(&s["expected_sat"])
                        ),
                        format!(
                            "{}/{}",
                            value_string(&s["solved_unsat"]),
                            value_string(&s["expected_unsat"])
                        ),
                        value_string(&s["wrong"]),
                        value_string(&s["invalid"]),
                        format!("{:.3}", s["par2_total"].as_f64().unwrap_or(0.0)),
                        format!("{:.3}", s["par2_avg"].as_f64().unwrap_or(0.0)),
                        if s["disqualified"].as_bool().unwrap_or(false) {
                            "yes".to_string()
                        } else {
                            "no".to_string()
                        },
                    ]
                })
                .collect(),
        ),
    ];
    for (variant, data) in variants {
        let Some(families) = data["summary"]["families"].as_object() else {
            continue;
        };
        let rows = families
            .iter()
            .map(|(family, s)| {
                vec![
                    family.clone(),
                    value_string(&s["total"]),
                    value_string(&s["solved"]),
                    format!(
                        "{}/{}",
                        value_string(&s["solved_sat"]),
                        value_string(&s["expected_sat"])
                    ),
                    format!(
                        "{}/{}",
                        value_string(&s["solved_unsat"]),
                        value_string(&s["expected_unsat"])
                    ),
                    value_string(&s["wrong"]),
                    value_string(&s["invalid"]),
                    format!("{:.3}", s["par2_avg"].as_f64().unwrap_or(0.0)),
                ]
            })
            .collect();
        lines.extend([
            String::new(),
            format!("## Family Split: {variant}"),
            String::new(),
            markdown_table(
                &[
                    "family",
                    "total",
                    "solved",
                    "SAT",
                    "UNSAT",
                    "wrong",
                    "invalid",
                    "PAR-2 avg",
                ],
                rows,
            ),
        ]);
    }
    fs::write(path, lines.join("\n") + "\n")?;
    Ok(())
}

fn markdown_table(headers: &[&str], rows: Vec<Vec<String>>) -> String {
    let mut lines = vec![
        format!("| {} |", headers.join(" | ")),
        format!("| {} |", vec!["---"; headers.len()].join(" | ")),
    ];
    for row in rows {
        lines.push(format!("| {} |", row.join(" | ")));
    }
    lines.join("\n")
}

fn runtime_provenance(path: Option<&Path>, timeout_sec: f64) -> Result<BTreeMap<String, String>> {
    let mut fields = BTreeMap::new();
    fields.insert("timeout_s".to_string(), format!("{timeout_sec:.6}"));
    fields.insert(
        "binary_path".to_string(),
        path.map(path_string).unwrap_or_default(),
    );
    fields.insert(
        "binary_sha256".to_string(),
        if let Some(path) = path.filter(|path| path.is_file()) {
            sha256_file(path)?
        } else {
            "unavailable".to_string()
        },
    );
    let metadata = path.and_then(|path| fs::metadata(path).ok());
    fields.insert(
        "binary_size_bytes".to_string(),
        metadata
            .as_ref()
            .map_or(String::new(), |meta| meta.len().to_string()),
    );
    fields.insert(
        "binary_mtime_epoch".to_string(),
        metadata
            .as_ref()
            .and_then(|meta| meta.modified().ok())
            .and_then(|mtime| mtime.duration_since(std::time::UNIX_EPOCH).ok())
            .map_or(String::new(), |duration| duration.as_secs().to_string()),
    );
    fields.insert(
        "binary_executable".to_string(),
        if path.is_some_and(Path::is_file) {
            "1"
        } else {
            "0"
        }
        .to_string(),
    );
    Ok(fields)
}

fn solver_binary_path(solver_root: &Path) -> Option<PathBuf> {
    let local = solver_root.join("ay");
    local.is_file().then_some(local)
}

fn ay_checker_path(solver_root: &Path) -> Option<PathBuf> {
    if let Some(local) = solver_binary_path(solver_root) {
        return Some(local);
    }
    env::current_exe().ok().filter(|path| path.is_file())
}

fn external_checker_verdict_artifact_path(proof_path: &Path) -> PathBuf {
    proof_path
        .parent()
        .unwrap_or(Path::new("."))
        .join(EXTERNAL_CHECKER_VERDICT_ARTIFACT)
}

fn sha256_file(path: &Path) -> Result<String> {
    let mut hasher = Sha256::new();
    let mut file = File::open(path).with_context(|| format!("opening {}", path.display()))?;
    let mut buffer = vec![0u8; 1024 * 1024];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn write_json_pretty(path: &Path, value: &JsonValue) -> Result<()> {
    fs::write(path, serde_json::to_string_pretty(value)? + "\n")
        .with_context(|| format!("writing {}", path.display()))
}

fn load_json_object(path: &Path) -> Result<JsonValue> {
    let value: JsonValue = serde_json::from_str(
        &fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?,
    )
    .with_context(|| format!("parsing JSON {}", path.display()))?;
    if !value.is_object() {
        bail!("{}: expected JSON object", path.display());
    }
    Ok(value)
}

fn git_head() -> String {
    Command::new("git")
        .args(["rev-parse", "HEAD"])
        .output()
        .ok()
        .filter(|output| output.status.success())
        .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string())
        .unwrap_or_else(|| "unknown".to_string())
}

fn git_dirty() -> bool {
    Command::new("git")
        .args(["status", "--porcelain", "--untracked-files=no"])
        .output()
        .map(|output| !String::from_utf8_lossy(&output.stdout).trim().is_empty())
        .unwrap_or(true)
}

fn row_solved(row: &Record) -> bool {
    matches!(row.get("actual"), "sat" | "unsat") && !row.truthy("wrong") && !row.truthy("invalid")
}

fn satcomp_verdict(actual: &str) -> &'static str {
    match actual {
        "sat" => "SATISFIABLE",
        "unsat" => "UNSATISFIABLE",
        "unknown" | "timeout" => "UNKNOWN",
        _ => "NO_VERDICT",
    }
}

fn normalize_expected(raw: &str) -> String {
    match raw.trim().to_ascii_lowercase().as_str() {
        "sat" => "sat".to_string(),
        "unsat" => "unsat".to_string(),
        _ => "unknown".to_string(),
    }
}

fn default_timeout_sec(suite: &str) -> f64 {
    if suite == "sat-main-2026-official-mirror" {
        5000.0
    } else {
        20.0
    }
}

fn file_size_if_exists(path: &Path) -> Result<u64> {
    match fs::metadata(path) {
        Ok(meta) => Ok(meta.len()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(0),
        Err(err) => Err(err).with_context(|| format!("reading metadata {}", path.display())),
    }
}

fn remove_if_exists(path: &Path) -> Result<()> {
    match fs::remove_file(path) {
        Ok(()) => Ok(()),
        Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
        Err(err) => Err(err).with_context(|| format!("removing {}", path.display())),
    }
}

fn safe_case_name(name: &str) -> String {
    name.replace(['/', ' '], "_")
}

fn first_non_empty(values: &[String]) -> String {
    values
        .iter()
        .find(|value| !value.trim().is_empty())
        .cloned()
        .unwrap_or_default()
}

fn string_value(value: &JsonValue, key: &str) -> Option<String> {
    value.get(key).and_then(|value| match value {
        JsonValue::String(text) => Some(text.clone()),
        JsonValue::Null => None,
        other => Some(value_string(other)),
    })
}

fn json_as_i64(value: &JsonValue) -> Option<i64> {
    match value {
        JsonValue::Number(number) => number
            .as_i64()
            .or_else(|| number.as_f64().map(|v| v as i64)),
        JsonValue::String(text) => parse_i64(text),
        JsonValue::Bool(value) => Some(i64::from(*value)),
        _ => None,
    }
}

fn json_as_f64(value: &JsonValue) -> Option<f64> {
    match value {
        JsonValue::Number(number) => number.as_f64(),
        JsonValue::String(text) => parse_f64(text),
        JsonValue::Bool(value) => Some(f64::from(u8::from(*value))),
        _ => None,
    }
}

fn parse_i64(value: &str) -> Option<i64> {
    let value = value.trim();
    if value.is_empty() {
        return None;
    }
    value
        .parse::<i64>()
        .ok()
        .or_else(|| value.parse::<f64>().ok().map(|value| value as i64))
}

fn parse_f64(value: &str) -> Option<f64> {
    let value = value.trim();
    if value.is_empty() {
        None
    } else {
        value.parse::<f64>().ok()
    }
}

fn row_matches_fmla_equiv_chain_4_6_6(row: &Record) -> bool {
    ["instance", "benchmark", "path", "run_input"]
        .iter()
        .any(|field| row.get(field).contains(FMLA_EQUIV_CHAIN_4_6_6_MARKER))
}

fn benchmark_matches_fmla_equiv_chain_4_6_6(bench: &Benchmark, run_input: &Path) -> bool {
    bench.name.contains(FMLA_EQUIV_CHAIN_4_6_6_MARKER)
        || bench
            .path
            .to_string_lossy()
            .contains(FMLA_EQUIV_CHAIN_4_6_6_MARKER)
        || run_input
            .to_string_lossy()
            .contains(FMLA_EQUIV_CHAIN_4_6_6_MARKER)
}

fn row_counter_f64(row: &Record, key: &str) -> Option<f64> {
    let text = row.get(key).trim();
    if text.is_empty() || text.eq_ignore_ascii_case("missing") {
        None
    } else {
        parse_f64(text)
    }
}

fn row_has_positive_counter(row: &Record, key: &str) -> bool {
    row_counter_f64(row, key).is_some_and(|value| value > 0.0)
}

fn row_exercises_fmla_destructive_preprocessing(row: &Record) -> bool {
    row_matches_fmla_equiv_chain_4_6_6(row)
        && (DESTRUCTIVE_TRANSFORM_ACTIVITY_COUNTER_FIELDS
            .iter()
            .any(|field| row_has_positive_counter(row, field))
            || row_has_positive_counter(row, "sat.preprocess_tx_started")
            || row_has_positive_counter(row, "sat.preprocess_tx_committed"))
}

fn format_counter_values(values: &BTreeMap<&str, f64>) -> String {
    values
        .iter()
        .map(|(key, value)| format!("{key}={}", format_counter_value(*value)))
        .collect::<Vec<_>>()
        .join(", ")
}

fn format_counter_value(value: f64) -> String {
    if value.fract() == 0.0 && value >= i64::MIN as f64 && value <= i64::MAX as f64 {
        (value as i64).to_string()
    } else {
        value.to_string()
    }
}

fn command_flag_values<'a>(command: &'a [String], flag: &str) -> Vec<Option<&'a str>> {
    let mut values = Vec::new();
    for (index, part) in command.iter().enumerate() {
        if part != flag {
            continue;
        }
        values.push(command.get(index + 1).map(String::as_str));
    }
    values
}

fn is_hex_sha256(value: &str) -> bool {
    value.len() == 64 && value.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn evidence_path(raw: &str) -> PathBuf {
    let path = expand_home(Path::new(raw));
    if path.is_absolute() {
        path
    } else {
        repo_root().join(path)
    }
}

fn evidence_paths_match(left: &str, right: &str) -> bool {
    if left == right {
        return true;
    }
    normalize_evidence_path(left) == normalize_evidence_path(right)
}

fn normalize_evidence_path(raw: &str) -> PathBuf {
    let path = evidence_path(raw);
    let mut normalized = PathBuf::new();
    for component in path.components() {
        match component {
            Component::CurDir => {}
            Component::ParentDir => {
                normalized.pop();
            }
            Component::Normal(part) => normalized.push(part),
            Component::RootDir | Component::Prefix(_) => normalized.push(component.as_os_str()),
        }
    }
    normalized
}

fn resolve_reported_path(raw: &str, base_dir: &Path) -> Option<PathBuf> {
    if raw.trim().is_empty() {
        return None;
    }
    let path = PathBuf::from(raw);
    if path.is_absolute() {
        return Some(path);
    }
    let repo_path = repo_root().join(&path);
    if repo_path.exists() {
        Some(repo_path)
    } else {
        Some(base_dir.join(path))
    }
}

fn reported_path_is_inside_root(raw: &str, root: &Path) -> bool {
    let path = evidence_path(raw);
    let root = expand_home(root);
    let Ok(path) = path.canonicalize() else {
        return false;
    };
    let Ok(root) = root.canonicalize() else {
        return false;
    };
    path.starts_with(root)
}

fn raw_rows_corpus_fingerprint(rows: &[Record]) -> String {
    let mut sorted = rows.to_vec();
    sorted.sort_by(|left, right| {
        (left.get("path"), left.get("instance")).cmp(&(right.get("path"), right.get("instance")))
    });
    let mut hasher = Sha256::new();
    for row in sorted {
        let line = [
            row.get("path"),
            row.get("expected"),
            row.get("family"),
            row.get("category"),
            row.get("instance"),
        ]
        .join("\t")
            + "\n";
        hasher.update(line.as_bytes());
    }
    format!("sha256:{:x}", hasher.finalize())
}

fn row_status_failed(status: &str, allowed: &[&str]) -> bool {
    let token = status.trim().to_ascii_lowercase();
    !allowed.iter().any(|allowed| *allowed == token)
}

fn expand_home(path: &Path) -> PathBuf {
    let raw = path.to_string_lossy();
    if raw == "~" {
        home_dir()
    } else if let Some(rest) = raw.strip_prefix("~/") {
        home_dir().join(rest)
    } else {
        path.to_path_buf()
    }
}

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .unwrap_or(Path::new("."))
        .to_path_buf()
}

fn insert(fields: &mut BTreeMap<String, String>, key: &str, value: &str) {
    fields.insert(key.to_string(), value.to_string());
}

fn absolute_path(path: &Path) -> Result<PathBuf> {
    if path.is_absolute() {
        Ok(path.to_path_buf())
    } else {
        Ok(env::current_dir()?.join(path))
    }
}

fn path_string(path: &Path) -> String {
    path.to_string_lossy().to_string()
}

fn home_dir() -> PathBuf {
    env::var_os("HOME").map_or_else(|| PathBuf::from("."), PathBuf::from)
}

fn round3(value: f64) -> f64 {
    (value * 1000.0).round() / 1000.0
}

fn value_string(value: &JsonValue) -> String {
    if let Some(value) = value.as_i64() {
        value.to_string()
    } else if let Some(value) = value.as_u64() {
        value.to_string()
    } else if let Some(value) = value.as_f64() {
        format!("{value:.3}")
    } else if let Some(value) = value.as_str() {
        value.to_string()
    } else {
        value.to_string()
    }
}

fn escape_cell(value: &str, delimiter: &str) -> String {
    let cleaned = value.replace(['\t', '\n', '\r'], " ");
    if delimiter == "," && (cleaned.contains(',') || cleaned.contains('"')) {
        format!("\"{}\"", cleaned.replace('"', "\"\""))
    } else {
        cleaned
    }
}

#[cfg(test)]
mod tests;
