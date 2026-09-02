// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ay launch-gate` command for public launch evidence gates.

use anyhow::{bail, Context, Result};
use clap::{Args, ValueEnum};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::ffi::OsString;
use std::fs;
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Output, Stdio};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
enum LaunchMode {
    DryRun,
    MetadataOnly,
}

impl LaunchMode {
    fn as_str(self) -> &'static str {
        match self {
            Self::DryRun => "dry-run",
            Self::MetadataOnly => "metadata-only",
        }
    }
}

/// Arguments for `ay launch-gate`.
#[derive(Args)]
#[command(after_help = "\
The native gate preserves the blocker names and exit policy of the original
shell release-readiness gate. It exits 0 only when evidence gate failures,
and launch blockers are all zero. Advisory checks are reported in the
transcript and summary JSON, but advisory failures do not make the native gate
exit non-zero.

Artifact-path options also accept the matching AY_RELEASE_GATE_* environment
variables (the legacy AY_HN_GATE_* names are still accepted), for example
AY_RELEASE_GATE_BENCHMARK_SUMMARY, AY_RELEASE_GATE_DOWNSTREAM_SUMMARY,
AY_RELEASE_GATE_RELEASE_MANIFEST, AY_RELEASE_GATE_RELEASE_MANIFEST_VERIFICATION,
AY_RELEASE_GATE_DEPENDENCY_PINS,
AY_RELEASE_GATE_PROOF_CLI_EVIDENCE, AY_RELEASE_GATE_PROOF_CLI_LOG,
AY_RELEASE_GATE_PROOF_ALETHE_REPLAY_SUMMARY, AY_RELEASE_GATE_PROOF_LEAN_REPLAY_SUMMARY,
AY_RELEASE_GATE_PROOF_CHC_REPLAY_SUMMARY, AY_RELEASE_GATE_PUBLIC_MIRROR_EVIDENCE,
AY_RELEASE_GATE_CHECK_PUBLIC_MIRROR, and AY_RELEASE_GATE_SUMMARY_JSON.

Use --list-shell-delegations to print the remaining shell, Python, and cargo
delegations without running the gate.

The native command validates launch evidence; it does not synthesize the full
packet by itself. Generate benchmark evidence with scripts/launch_benchmark_packet.sh,
downstream evidence with `ay consumer-smoke run --json`, release evidence
with ay release generate-manifest and ay release verify-manifest,
and proof evidence with ay z3-audit or the legacy proof replay packet producers.
The public_mirror blocker is publication evidence only: a missing or stale
public mirror is not classified as a solver blocker.")]
pub(crate) struct HnGateArgs {
    /// Repository root to check.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// ay binary passed to launch benchmark packet checks.
    #[arg(long, default_value = "./target/release/ay")]
    ay: PathBuf,

    /// Reference solver passed to benchmark packet checks.
    #[arg(long, default_value = "z3")]
    reference_solver: String,

    /// Fast packet wiring mode.
    #[arg(long, value_enum, default_value_t = LaunchMode::DryRun)]
    launch_mode: LaunchMode,

    /// Output directory for launch packet fast mode.
    #[arg(long)]
    out_dir: Option<PathBuf>,

    /// Real launch packet summary.json to validate.
    #[arg(long)]
    benchmark_summary: Option<PathBuf>,

    /// ay consumer-smoke run --json output to validate.
    #[arg(long)]
    downstream_summary: Option<PathBuf>,

    /// Fetch current HEAD from the public ay mirror.
    #[arg(long)]
    check_public_mirror: bool,

    /// Write public-mirror JSON evidence to PATH.
    #[arg(long)]
    public_mirror_evidence: Option<PathBuf>,

    /// ay-public-release-pins/v1 JSON to validate instead of running the Python no-fetch check.
    #[arg(long)]
    dependency_pins: Option<PathBuf>,

    /// ay-release-manifest/v1 JSON to validate.
    #[arg(long)]
    release_manifest: Option<PathBuf>,

    /// ay-release-manifest-verification/v1 JSON to validate.
    #[arg(long)]
    release_manifest_verification: Option<PathBuf>,

    /// Validate legacy ay-proof-cli-verify/v1 JSON proof evidence.
    #[arg(long)]
    proof_cli_evidence: Option<PathBuf>,

    /// Optional log path named by --proof-cli-evidence.
    #[arg(long)]
    proof_cli_log: Option<PathBuf>,

    /// Validate ay-proof-external-replay/v1 Alethe replay JSON.
    #[arg(long)]
    proof_alethe_replay_summary: Option<PathBuf>,

    /// Validate ay-proof-lean-replay/v1 Lean replay JSON.
    #[arg(long)]
    proof_lean_replay_summary: Option<PathBuf>,

    /// Validate ay-chc-certificate-replay/v1 replay JSON.
    #[arg(long)]
    proof_chc_replay_summary: Option<PathBuf>,

    /// Write machine-readable gate summary JSON to PATH.
    #[arg(long)]
    summary_json: Option<PathBuf>,

    /// Run targeted cargo Z3 CLI compatibility tests.
    #[arg(long)]
    run_z3_cli_tests: bool,

    /// Print remaining shell/script delegated checks and exit.
    #[arg(long)]
    list_shell_delegations: bool,
}

#[derive(Clone)]
struct ResolvedArgs {
    repo_root: PathBuf,
    ay: PathBuf,
    reference_solver: String,
    launch_mode: LaunchMode,
    out_dir: Option<PathBuf>,
    benchmark_summary: Option<PathBuf>,
    downstream_summary: Option<PathBuf>,
    check_public_mirror: bool,
    public_mirror_evidence: Option<PathBuf>,
    dependency_pins: Option<PathBuf>,
    release_manifest: Option<PathBuf>,
    release_manifest_verification: Option<PathBuf>,
    proof_cli_evidence: Option<PathBuf>,
    proof_cli_log: Option<PathBuf>,
    proof_alethe_replay_summary: Option<PathBuf>,
    proof_lean_replay_summary: Option<PathBuf>,
    proof_chc_replay_summary: Option<PathBuf>,
    summary_json: Option<PathBuf>,
    run_z3_cli_tests: bool,
}

#[derive(Clone)]
struct Blocker {
    name: String,
    evidence: String,
    command: String,
    finding: String,
}

#[derive(Clone)]
struct TargetedSmokeCheck {
    id: String,
    required: bool,
    status: String,
    solver_timeout_ms: u64,
    wall_timeout_ms: u64,
    cases_total: usize,
    cases_passed: usize,
    cases_failed: usize,
    cases: Vec<TargetedSmokeCase>,
}

#[derive(Clone)]
struct TargetedSmokeCase {
    id: String,
    path: String,
    expected_verdict: bool,
    expected_result: String,
    expected_certificate: String,
    command: Vec<String>,
    exit_code: Option<i32>,
    timed_out: bool,
    duration_ms: u64,
    stdout_predicates: TargetedSmokeStdoutPredicates,
    status: String,
    finding: Option<String>,
}

#[derive(Clone)]
struct TargetedSmokeStdoutPredicates {
    has_unsat_line: bool,
    first_non_empty_line_is_unsat: bool,
    has_unsafe_certificate: bool,
    has_unknown_line: bool,
    has_timeout_reason: bool,
}

#[derive(Clone, Copy)]
struct ChcBmcRustHornCaseSpec {
    id: &'static str,
    path: &'static str,
    expected_verdict: bool,
    expected_result: &'static str,
    expected_certificate: &'static str,
}

const CHC_BMC_RUST_HORN_SMOKE_ID: &str = "chc_bmc_rust_horn_smoke";
const CHC_BMC_RUST_HORN_SOLVER_TIMEOUT_MS: u64 = 12_000;
const CHC_BMC_RUST_HORN_WALL_TIMEOUT_MS: u64 = 15_000;
const CHC_BMC_RUST_HORN_CASES: &[ChcBmcRustHornCaseSpec] = &[
    ChcBmcRustHornCaseSpec {
        id: "bmc-3-unsafe",
        path: "benchmarks/chc-comp/chc-comp25-repo/rust-horn/bmc-3-test-bmc-3-unsafe_000.smt2",
        expected_verdict: false,
        expected_result: "unsat",
        expected_certificate: "UNSAFE",
    },
    ChcBmcRustHornCaseSpec {
        id: "bmc-1-unsafe",
        path: "benchmarks/chc-comp/chc-comp25-repo/rust-horn/bmc-1-test-bmc-1-unsafe_000.smt2",
        expected_verdict: false,
        expected_result: "unsat",
        expected_certificate: "UNSAFE",
    },
];

#[derive(Clone, Copy)]
struct ShellDelegationStatus {
    scope: &'static str,
    check: &'static str,
    command: &'static str,
    native_gap: &'static str,
}

const LAUNCH_GATE_SHELL_DELEGATIONS: &[ShellDelegationStatus] = &[
    ShellDelegationStatus {
        scope: "runtime-gate",
        check: "doc_reality",
        command: "bash scripts/check_doc_reality.sh",
        native_gap: "doc-reality policy is still implemented in the shell script",
    },
    ShellDelegationStatus {
        scope: "runtime-gate",
        check: "public_release_pins_no_fetch_fallback",
        command: "ay release verify-public-pins --no-fetch",
        native_gap:
            "fallback only when --dependency-pins / AY_RELEASE_GATE_DEPENDENCY_PINS is absent",
    },
    ShellDelegationStatus {
        scope: "optional-runtime-gate",
        check: "z3_cli_compat_tests",
        command: "cargo test -p ay --test group_cli z3_compat_args",
        native_gap:
            "optional --run-z3-cli-tests delegates to cargo; no in-process native test runner",
    },
];

impl Blocker {
    fn id(&self) -> String {
        blocker_id(&self.name, &self.evidence, &self.command, &self.finding)
    }
}

fn blocker_id(name: &str, evidence: &str, command: &str, finding: &str) -> String {
    if name != "proof_external_replay" {
        return name.to_string();
    }

    if evidence.contains("smt-alethe")
        || command.contains("--alethe")
        || finding.contains("SMT Alethe")
    {
        return "proof_external_replay.alethe".to_string();
    }

    if evidence.contains("lean-proof")
        || evidence.contains("lean")
        || command.contains("lean")
        || finding.contains("Lean4 proof replay")
    {
        return "proof_external_replay.lean".to_string();
    }

    name.to_string()
}

struct GateState {
    evidence_gate_failures: usize,
    advisory_failures: usize,
    blockers: Vec<Blocker>,
    targeted_smokes: Vec<TargetedSmokeCheck>,
}

impl GateState {
    fn new() -> Self {
        Self {
            evidence_gate_failures: 0,
            advisory_failures: 0,
            blockers: Vec::new(),
            targeted_smokes: Vec::new(),
        }
    }

    fn add_blocker(&mut self, name: &str, evidence: &str, command: &str, finding: String) {
        self.blockers.push(Blocker {
            name: name.to_string(),
            evidence: evidence.to_string(),
            command: command.to_string(),
            finding,
        });
    }
}

pub(crate) fn run(args: &HnGateArgs) -> Result<i32> {
    if args.list_shell_delegations {
        print_launch_gate_shell_delegations();
        return Ok(0);
    }

    let args = resolve_args(args)?;
    let mut state = GateState::new();

    println!("=== Release Readiness Gate ===");
    println!("repo_root={}", args.repo_root.display());
    println!("launch_mode={}", args.launch_mode.as_str());
    let checklist = args.repo_root.join("the development design notes");
    if checklist.is_file() {
        println!("packet_checklist=the development design notes");
    }
    println!();

    run_evidence_gate(
        &args.repo_root,
        &mut state,
        "doc_reality",
        &["bash", "scripts/check_doc_reality.sh"],
    )?;
    check_public_release_pins_no_fetch(&args, &mut state)?;
    let proof_audit_ay = proof_audit_command_binary(&args)?;
    let proof_summary_json = proof_audit_summary_json_path();
    let _proof_summary_json_cleanup = TempPathCleanup::new(proof_summary_json.clone());
    let _ = fs::remove_file(&proof_summary_json);
    let proof_args = proof_audit_args(&args, &proof_audit_ay, &proof_summary_json);
    let proof_argv = proof_args.iter().map(String::as_str).collect::<Vec<_>>();
    let proof_output = run_evidence_gate_capture_allow_failure(
        &args.repo_root,
        &mut state,
        "proof_evidence_summary",
        &proof_argv,
    )?;
    print_proof_matrix_compat_disclosures();

    if args.benchmark_summary.is_none() {
        run_native_launch_packet_fast(&args, &mut state)?;
    } else {
        println!(
            "[evidence] SKIP  launch_packet_{}: --benchmark-summary supplied; validating existing summary instead",
            args.launch_mode.as_str()
        );
        println!();
    }

    run_downstream_smoke_inventory_advisory(&args.repo_root, &mut state);
    if args.run_z3_cli_tests {
        run_evidence_gate(
            &args.repo_root,
            &mut state,
            "z3_cli_compat_tests",
            &[
                "cargo",
                "test",
                "-p",
                "ay",
                "--test",
                "group_cli",
                "z3_compat_args",
            ],
        )?;
    } else {
        println!("[advisory] Z3 CLI compatibility tests are outside the launch-gate default.");
        println!("[advisory] To execute them through this gate, pass --run-z3-cli-tests.");
        quote_command(&[
            "cargo",
            "test",
            "-p",
            "ay",
            "--test",
            "group_cli",
            "z3_compat_args",
        ]);
        println!();
    }

    println!("=== Required Launch Blocker Checks ===");
    check_chc_bmc_rust_horn_smoke(&args, &mut state)?;
    check_compatibility_matrix(&args, &mut state);
    check_benchmark_summary(&args, &mut state);
    check_proof_summary(&args, &mut state, &proof_output, &proof_summary_json);
    check_downstream_summary(&args, &mut state);
    check_public_mirror(&args, &mut state)?;
    check_release_manifest(&args, &mut state);
    check_release_manifest_verification(&args, &mut state);
    check_auflia_completeness(&args, &mut state);
    println!();

    if let Some(path) = &args.summary_json {
        match write_summary_json(&args, &state, path) {
            Ok(()) => println!("gate_summary_json={}", path.display()),
            Err(error) => {
                eprintln!(
                    "launch-gate: failed to write summary JSON: {}",
                    path.display()
                );
                eprintln!("{error:#}");
                state.evidence_gate_failures += 1;
            }
        }
    }

    println!("=== Gate Summary ===");
    println!("evidence_gate_failures={}", state.evidence_gate_failures);
    println!("advisory_failures={}", state.advisory_failures);
    println!("launch_blockers={}", state.blockers.len());

    print_missing_evidence_summary(&state);

    if state.evidence_gate_failures != 0 || !state.blockers.is_empty() {
        println!("launch-gate: FAIL release readiness is blocked");
        return Ok(1);
    }

    println!("launch-gate: PASS release readiness blockers are clear");
    Ok(0)
}

fn proof_audit_summary_json_path() -> PathBuf {
    let millis = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_millis())
        .unwrap_or(0);
    env::temp_dir().join(format!(
        "ay-launch-gate-proof-audit-{}-{millis}.json",
        std::process::id()
    ))
}

struct TempPathCleanup {
    path: PathBuf,
}

impl TempPathCleanup {
    fn new(path: PathBuf) -> Self {
        Self { path }
    }
}

impl Drop for TempPathCleanup {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

fn run_native_launch_packet_fast(args: &ResolvedArgs, state: &mut GateState) -> Result<()> {
    let check = format!("launch_packet_{}", args.launch_mode.as_str());
    println!("[evidence] START {check}");
    let mode = match args.launch_mode {
        LaunchMode::DryRun => crate::cmd_launch_packet::FastPacketMode::DryRun,
        LaunchMode::MetadataOnly => crate::cmd_launch_packet::FastPacketMode::MetadataOnly,
    };
    let config = crate::cmd_launch_packet::FastPacketConfig {
        repo_root: args.repo_root.clone(),
        ay: resolve_repo_path(&args.repo_root, &args.ay),
        timeout: "30".to_string(),
        runs: 1,
        reference_solver: args.reference_solver.clone(),
        out_dir: args
            .out_dir
            .as_ref()
            .map(|path| resolve_repo_path(&args.repo_root, path)),
        requested_evals: Vec::new(),
        excluded_evals: vec!["sat-par2-dev".to_string()],
        mode,
        progress_every: 1,
    };
    match crate::cmd_launch_packet::write_fast_packet(config) {
        Ok(out_dir) => {
            println!("packet_dir={}", out_dir.display());
            println!("[evidence] PASS  {check}");
        }
        Err(error) => {
            eprintln!("[evidence] FAIL  {check}");
            eprintln!("{error:#}");
            state.evidence_gate_failures += 1;
        }
    }
    println!();
    Ok(())
}

fn proof_audit_args(
    args: &ResolvedArgs,
    proof_audit_ay: &Path,
    summary_json: &Path,
) -> Vec<String> {
    vec![
        proof_audit_ay.display().to_string(),
        "z3-audit".to_string(),
        "--scope".to_string(),
        "full-replacement".to_string(),
        "--repo-root".to_string(),
        args.repo_root.display().to_string(),
        "--ay".to_string(),
        proof_audit_ay.display().to_string(),
        "--reference-cache".to_string(),
        args.repo_root
            .join("tests/z3-audit/reference-cache.json")
            .display()
            .to_string(),
        "--summary-json".to_string(),
        summary_json.display().to_string(),
    ]
}

fn print_proof_matrix_compat_disclosures() {
    println!("=== Proof Evidence Matrix Compatibility Disclosures ===");
    println!("{}", proof_sat_model_differential_disclosure_row());
    println!();
}

fn proof_sat_model_differential_disclosure_row() -> String {
    format!(
        "{:<12} | {:<30} | {:<39} | {}",
        "SKIPPED",
        "SAT model/differential",
        "ay gate solver / scripts/soundness_gate.sh",
        "Not a proof surface; the legacy integration filter matches 0 tests."
    )
}

fn print_missing_evidence_summary(state: &GateState) {
    for line in missing_evidence_summary_lines(state) {
        println!("{line}");
    }
}

fn missing_evidence_summary_lines(state: &GateState) -> Vec<String> {
    let mut lines = vec!["=== Missing Evidence For Z3 Skeptics ===".to_string()];
    if state.blockers.is_empty() {
        lines.push("none".to_string());
        return lines;
    }

    for blocker in &state.blockers {
        lines.push(format!("- {}", blocker.name));
        lines.push(format!("  evidence: {}", blocker.evidence));
        lines.push(format!("  command: {}", blocker.command));
        lines.push(format!("  finding: {}", blocker.finding));
    }
    lines
}

fn resolve_args(args: &HnGateArgs) -> Result<ResolvedArgs> {
    let repo_root = match &args.repo_root {
        Some(path) => path.clone(),
        None => default_repo_root().context("resolve default repo root")?,
    };
    if !repo_root.is_dir() {
        bail!("repo root does not exist: {}", repo_root.display());
    }
    let repo_root = fs::canonicalize(&repo_root)
        .with_context(|| format!("canonicalize repo root {}", repo_root.display()))?;

    Ok(ResolvedArgs {
        repo_root,
        ay: args.ay.clone(),
        reference_solver: args.reference_solver.clone(),
        launch_mode: args.launch_mode,
        out_dir: args.out_dir.clone(),
        benchmark_summary: path_arg_or_env(
            &args.benchmark_summary,
            "AY_RELEASE_GATE_BENCHMARK_SUMMARY",
        ),
        downstream_summary: path_arg_or_env(
            &args.downstream_summary,
            "AY_RELEASE_GATE_DOWNSTREAM_SUMMARY",
        ),
        check_public_mirror: args.check_public_mirror
            || env_bool("AY_RELEASE_GATE_CHECK_PUBLIC_MIRROR")?,
        public_mirror_evidence: path_arg_or_env(
            &args.public_mirror_evidence,
            "AY_RELEASE_GATE_PUBLIC_MIRROR_EVIDENCE",
        ),
        dependency_pins: path_arg_or_env(&args.dependency_pins, "AY_RELEASE_GATE_DEPENDENCY_PINS"),
        release_manifest: path_arg_or_env(
            &args.release_manifest,
            "AY_RELEASE_GATE_RELEASE_MANIFEST",
        ),
        release_manifest_verification: path_arg_or_env(
            &args.release_manifest_verification,
            "AY_RELEASE_GATE_RELEASE_MANIFEST_VERIFICATION",
        ),
        proof_cli_evidence: path_arg_or_env(
            &args.proof_cli_evidence,
            "AY_RELEASE_GATE_PROOF_CLI_EVIDENCE",
        ),
        proof_cli_log: path_arg_or_env(&args.proof_cli_log, "AY_RELEASE_GATE_PROOF_CLI_LOG"),
        proof_alethe_replay_summary: path_arg_or_env(
            &args.proof_alethe_replay_summary,
            "AY_RELEASE_GATE_PROOF_ALETHE_REPLAY_SUMMARY",
        ),
        proof_lean_replay_summary: path_arg_or_env(
            &args.proof_lean_replay_summary,
            "AY_RELEASE_GATE_PROOF_LEAN_REPLAY_SUMMARY",
        ),
        proof_chc_replay_summary: path_arg_or_env(
            &args.proof_chc_replay_summary,
            "AY_RELEASE_GATE_PROOF_CHC_REPLAY_SUMMARY",
        ),
        summary_json: path_arg_or_env(&args.summary_json, "AY_RELEASE_GATE_SUMMARY_JSON"),
        run_z3_cli_tests: args.run_z3_cli_tests,
    })
}

fn print_launch_gate_shell_delegations() {
    println!("=== Native Launch Gate Shell Delegations ===");
    println!("scope\tcheck\tcommand\tnative_gap");
    for row in LAUNCH_GATE_SHELL_DELEGATIONS {
        println!(
            "{}\t{}\t{}\t{}",
            row.scope, row.check, row.command, row.native_gap
        );
    }
    println!(
        "blocker-guidance\tcompatibility_matrix\t{}\tno single native producer for doc-reality plus z3 CLI compatibility evidence",
        compatibility_command()
    );
    println!(
        "blocker-guidance\tproof_inventory\t{}\tproof inventory producer is native z3-audit but still documents shell transcript capture",
        proof_full_gate_command()
    );
    println!(
        "blocker-guidance\tproof_cli_verify\t{}\tproof CLI evidence producer is native z3-audit but still documents shell transcript capture",
        proof_cli_command()
    );
    println!(
        "blocker-guidance\tproof_external_replay_alethe\t{}\tSMT Alethe replay producer is native z3-audit plus external checker and shell transcript capture",
        proof_alethe_replay_command()
    );
    println!(
        "blocker-guidance\tproof_external_replay_lean\t{}\tLean replay evidence producer still requires shell setup and external lean",
        proof_lean_replay_command()
    );
    println!(
        "blocker-guidance\tproof_chc_replay\t{}\tCHC certificate replay evidence producer still requires shell setup and external z3 replay",
        proof_chc_replay_command()
    );
    println!(
        "blocker-guidance\tbenchmark_summary\t{}\tbenchmark packet production is still script-based",
        benchmark_command()
    );
    println!(
        "blocker-guidance\tdownstream_smoke\t{}\tconsumer smoke orchestration is native; per-consumer leaf smoke commands still execute external repo scripts",
        downstream_command("/tmp/ay-consumer-smoke.json")
    );
    println!(
        "blocker-guidance\trelease_manifest\t{}\trelease manifest production is native; final build still delegates to cargo",
        release_manifest_command("release-manifest.json")
    );
    println!(
        "blocker-guidance\trelease_manifest_verification\t{}\trelease manifest verification is native; version replay still executes the release binary",
        release_manifest_verification_command(
            "release-manifest.json",
            "release-manifest-verification.json"
        )
    );
    println!(
        "blocker-guidance\tauflia_target\t{}\tAUFLIA target evidence still depends on benchmark download script and cargo soundness test",
        auflia_command()
    );
}

fn check_public_release_pins_no_fetch(args: &ResolvedArgs, state: &mut GateState) -> Result<()> {
    let Some(path) = &args.dependency_pins else {
        let ay_exe = env::current_exe()
            .unwrap_or_else(|_| PathBuf::from("ay"))
            .to_string_lossy()
            .into_owned();
        return run_evidence_gate(
            &args.repo_root,
            state,
            "public_release_pins_no_fetch",
            &[
                ay_exe.as_str(),
                "release",
                "verify-public-pins",
                "--no-fetch",
            ],
        );
    };

    println!("[evidence] START public_release_pins_no_fetch");
    let resolved = resolve_repo_path(&args.repo_root, path);
    let command = [
        "ay".to_string(),
        "launch-gate".to_string(),
        "--dependency-pins".to_string(),
        path.display().to_string(),
    ];
    let command_refs = command.iter().map(String::as_str).collect::<Vec<_>>();
    quote_command(&command_refs);

    let reasons = match read_json(&resolved) {
        Ok(value) => public_release_pins_evidence_reasons(&value, &args.repo_root),
        Err(error) => vec![error],
    };
    if reasons.is_empty() {
        println!(
            "[evidence] PASS  public_release_pins_no_fetch: supplied dependency pins evidence is valid"
        );
    } else {
        eprintln!(
            "[evidence] FAIL  public_release_pins_no_fetch: {}",
            reasons.join("; ")
        );
        state.evidence_gate_failures += 1;
    }
    println!();
    Ok(())
}

fn public_release_pins_evidence_reasons(evidence: &Value, repo_root: &Path) -> Vec<String> {
    let mut reasons = Vec::new();
    expect_string(
        evidence,
        "schema",
        "ay-public-release-pins/v1",
        &mut reasons,
    );
    expect_string(evidence, "status", "pass", &mut reasons);
    if value_at(evidence, &["errors"]).is_some_and(|errors| !is_empty_value(errors)) {
        reasons.push("errors is not empty".to_string());
    }

    let head = current_head(repo_root);
    match (
        value_at(evidence, &["source", "ay_commit"]).and_then(Value::as_str),
        head.as_deref(),
    ) {
        (Some(commit), Some(head)) if commit == head => {}
        (Some(commit), Some(head)) => {
            reasons.push(format!(
                "source.ay_commit={commit:?} does not match HEAD {head:?}"
            ));
        }
        (None, _) => reasons.push("source.ay_commit is missing".to_string()),
        (_, None) => reasons.push("cannot resolve current git HEAD".to_string()),
    }
    if value_at(evidence, &["source", "lockfile"]).and_then(Value::as_str) != Some("Cargo.lock") {
        reasons.push("source.lockfile is not Cargo.lock".to_string());
    }
    if value_at(evidence, &["source", "cargo_wrapper"]).and_then(Value::as_str)
        != Some("cargo_wrapper.toml")
    {
        reasons.push("source.cargo_wrapper is not cargo_wrapper.toml".to_string());
    }
    if value_at(evidence, &["source", "public_fetch_checked"])
        .and_then(Value::as_bool)
        .is_none()
    {
        reasons.push("source.public_fetch_checked is not a boolean".to_string());
    }
    let manifests = value_at(evidence, &["source", "manifests"]).and_then(Value::as_array);
    if manifests.is_none_or(|items| items.is_empty()) {
        reasons.push("source.manifests is empty".to_string());
    }

    let external_codegen_url = crate::cmd_release::external_codegen_url();
    // Pin evidence historically records the legacy underscore slug for
    // external-codegen-ir; keep the exact-match expectation on that spelling.
    let external_codegen_ir_url = crate::cmd_release::external_codegen_ir_url()
        .replace("/external-codegen-ir", "/external_codegen_ir");
    check_release_pin_component(
        evidence,
        "EXTERNAL_CODEGEN",
        &external_codegen_url,
        true,
        &mut reasons,
    );
    check_release_pin_component(
        evidence,
        "ExternalCodegenIr",
        &external_codegen_ir_url,
        false,
        &mut reasons,
    );
    check_release_pin_auto_bump(
        evidence,
        "external_codegen-codegen",
        &external_codegen_url,
        "listed",
        "manifest-rev",
        true,
        &mut reasons,
    );
    check_release_pin_auto_bump(
        evidence,
        "external_codegen_ir",
        &external_codegen_ir_url,
        "exempt",
        "lockfile-only",
        false,
        &mut reasons,
    );

    reasons
}

fn check_release_pin_component(
    evidence: &Value,
    name: &str,
    expected_url: &str,
    rev_must_match_commit: bool,
    reasons: &mut Vec<String>,
) {
    let Some(pin) = evidence
        .get("pins")
        .and_then(Value::as_array)
        .and_then(|pins| {
            pins.iter()
                .find(|pin| pin.get("name").and_then(Value::as_str) == Some(name))
        })
    else {
        reasons.push(format!("pins missing {name}"));
        return;
    };

    if pin.get("url").and_then(Value::as_str) != Some(expected_url) {
        reasons.push(format!(
            "pins.{name}.url={:?}, expected {expected_url:?}",
            pin.get("url")
        ));
    }
    let commit = pin.get("commit").and_then(Value::as_str).unwrap_or("");
    if !lower_full_commit_hex(commit) {
        reasons.push(format!("pins.{name}.commit is not a lowercase full commit"));
    }
    let rev = pin.get("rev");
    if rev_must_match_commit {
        if rev.and_then(Value::as_str) != Some(commit) {
            reasons.push(format!("pins.{name}.rev does not match commit"));
        }
    } else if !matches!(rev, None | Some(Value::Null)) {
        reasons.push(format!("pins.{name}.rev is not null"));
    }
    let packages = pin.get("packages").and_then(Value::as_array);
    if packages.is_none_or(|items| items.is_empty()) {
        reasons.push(format!("pins.{name}.packages is empty"));
    }
    let component_version = pin.get("component_version").and_then(Value::as_str);
    if component_version.is_none_or(str::is_empty) {
        reasons.push(format!("pins.{name}.component_version is missing"));
    }
    let package_versions = pin.get("package_versions").and_then(Value::as_object);
    if package_versions.is_none_or(|items| items.is_empty()) {
        reasons.push(format!("pins.{name}.package_versions is empty"));
    }
}

fn check_release_pin_auto_bump(
    evidence: &Value,
    dependency: &str,
    expected_url: &str,
    expected_status: &str,
    expected_bump_method: &str,
    rev_must_match_pin: bool,
    reasons: &mut Vec<String>,
) {
    let Some(row) = evidence
        .get("auto_bump")
        .and_then(Value::as_array)
        .and_then(|rows| {
            rows.iter().find(|row| {
                row.get("dependency").and_then(Value::as_str) == Some(dependency)
                    && row.get("url").and_then(Value::as_str) == Some(expected_url)
            })
        })
    else {
        reasons.push(format!("auto_bump missing {dependency} {expected_url}"));
        return;
    };

    if row.get("status").and_then(Value::as_str) != Some(expected_status) {
        reasons.push(format!(
            "auto_bump.{dependency}.status={:?}, expected {expected_status:?}",
            row.get("status")
        ));
    }
    if row.get("bump_method").and_then(Value::as_str) != Some(expected_bump_method) {
        reasons.push(format!(
            "auto_bump.{dependency}.bump_method={:?}, expected {expected_bump_method:?}",
            row.get("bump_method")
        ));
    }
    if rev_must_match_pin {
        let pin_commit = release_pin_commit(evidence, expected_url);
        if row.get("rev").and_then(Value::as_str) != pin_commit {
            reasons.push(format!(
                "auto_bump.{dependency}.rev does not match release pin commit"
            ));
        }
    } else if !matches!(row.get("rev"), None | Some(Value::Null)) {
        reasons.push(format!("auto_bump.{dependency}.rev is not null"));
    }
    let updates = row.get("updates").and_then(Value::as_array);
    if updates.is_none_or(|items| !items.iter().any(|item| item.as_str() == Some("Cargo.lock"))) {
        reasons.push(format!(
            "auto_bump.{dependency}.updates does not include Cargo.lock"
        ));
    }
}

fn release_pin_commit<'a>(evidence: &'a Value, expected_url: &str) -> Option<&'a str> {
    evidence
        .get("pins")
        .and_then(Value::as_array)?
        .iter()
        .find(|pin| pin.get("url").and_then(Value::as_str) == Some(expected_url))?
        .get("commit")
        .and_then(Value::as_str)
}

fn lower_full_commit_hex(commit: &str) -> bool {
    full_commit_hex(commit)
        && commit
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

fn proof_audit_command_binary(args: &ResolvedArgs) -> Result<PathBuf> {
    let requested = resolve_repo_path(&args.repo_root, &args.ay);
    if requested.is_file() && supports_z3_audit_subcommand(&requested, &args.repo_root) {
        if current_head(&args.repo_root).is_none()
            || ay_binary_matches_current_head(&requested, &args.repo_root)
        {
            return Ok(args.ay.clone());
        }
    }
    env::current_exe().context("resolve current executable for native proof audit")
}

fn supports_z3_audit_subcommand(ay: &Path, repo_root: &Path) -> bool {
    let Ok(output) = ProcessCommand::new(ay)
        .args(["z3-audit", "--help"])
        .current_dir(repo_root)
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
    else {
        return false;
    };
    if !output.status.success() {
        return false;
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    stdout.contains("--scope") && stdout.contains("full-replacement")
}

fn ay_binary_matches_current_head(ay: &Path, repo_root: &Path) -> bool {
    let Some(head) = current_head(repo_root) else {
        return false;
    };
    let Some(build_commit) = ay_binary_build_commit(ay, repo_root) else {
        return false;
    };
    if build_commit.ends_with("-dirty") {
        return false;
    }
    build_commit_matches_head(build_commit.as_str(), head.as_str())
}

fn build_commit_matches_head(build_commit: &str, head: &str) -> bool {
    build_commit.len() >= 12
        && build_commit.bytes().all(|byte| byte.is_ascii_hexdigit())
        && head.starts_with(build_commit)
}

fn ay_binary_build_commit(ay: &Path, repo_root: &Path) -> Option<String> {
    let output = ProcessCommand::new(ay)
        .arg("--version")
        .current_dir(repo_root)
        .stdin(Stdio::null())
        .stderr(Stdio::null())
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    parse_build_commit(&String::from_utf8_lossy(&output.stdout))
}

fn parse_build_commit(version_output: &str) -> Option<String> {
    version_output
        .lines()
        .find_map(|line| line.trim().strip_prefix("build.commit="))
        .map(str::trim)
        .filter(|commit| !commit.is_empty())
        .map(str::to_string)
}

fn default_repo_root() -> Result<PathBuf> {
    let cwd = env::current_dir().context("resolve current directory as repo root")?;
    if let Some(repo_root) = find_launch_gate_repo_root(&cwd) {
        return Ok(repo_root);
    }
    if let Ok(exe) = env::current_exe() {
        if let Some(parent) = exe.parent() {
            if let Some(repo_root) = find_launch_gate_repo_root(parent) {
                return Ok(repo_root);
            }
        }
    }
    Ok(cwd)
}

fn find_launch_gate_repo_root(start: &Path) -> Option<PathBuf> {
    // Identify the AY workspace root by its permanent markers. The historical
    // marker `scripts/release_gate.sh` was the original shell gate, now
    // superseded by this native `ay launch-gate` command and removed from the
    // tree, so it can no longer be relied on. The workspace manifest plus the
    // `crates/ay` package directory uniquely identify the repo root.
    for path in start.ancestors() {
        if path.join("Cargo.toml").is_file() && path.join("crates/ay").is_dir() {
            return Some(path.to_path_buf());
        }
    }
    None
}

/// Resolve `AY_RELEASE_GATE_<SUFFIX>` to its legacy `AY_HN_GATE_<SUFFIX>`
/// spelling, which remains accepted for backward compatibility.
fn legacy_gate_env_name(name: &str) -> Option<String> {
    name.strip_prefix("AY_RELEASE_GATE_")
        .map(|suffix| format!("AY_HN_GATE_{suffix}"))
}

fn path_arg_or_env(arg: &Option<PathBuf>, name: &str) -> Option<PathBuf> {
    arg.clone()
        .or_else(|| non_empty_env_path(name))
        .or_else(|| legacy_gate_env_name(name).and_then(|legacy| non_empty_env_path(&legacy)))
}

fn non_empty_env_path(name: &str) -> Option<PathBuf> {
    env::var_os(name).and_then(|value| {
        if value.is_empty() {
            None
        } else {
            Some(PathBuf::from(value))
        }
    })
}

fn env_bool(name: &str) -> Result<bool> {
    let raw = match env::var_os(name) {
        Some(raw) => raw,
        None => match legacy_gate_env_name(name).and_then(env::var_os) {
            Some(raw) => raw,
            None => return Ok(false),
        },
    };
    if raw.is_empty() {
        return Ok(false);
    }
    let value = raw.to_string_lossy().to_ascii_lowercase();
    match value.as_str() {
        "true" | "1" | "yes" | "on" => Ok(true),
        "false" | "0" | "no" | "off" => Ok(false),
        _ => bail!("{name} must be true or false"),
    }
}

fn run_evidence_gate(
    repo_root: &Path,
    state: &mut GateState,
    name: &str,
    argv: &[&str],
) -> Result<()> {
    println!("[evidence] START {name}");
    quote_command(argv);
    let status = match ProcessCommand::new(argv[0])
        .args(&argv[1..])
        .current_dir(repo_root)
        .status()
    {
        Ok(status) => status,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            // Shell semantics: a missing command is exit 127 and one counted
            // evidence-gate failure, never an aborted gate run — the remaining
            // gates still execute and the summary JSON is still written.
            eprintln!(
                "[evidence] FAIL  {name} exit=127 (command not found: {})",
                argv[0]
            );
            state.evidence_gate_failures += 1;
            println!();
            return Ok(());
        }
        Err(error) => {
            return Err(error).with_context(|| format!("run evidence gate {name}"));
        }
    };
    if status.success() {
        println!("[evidence] PASS  {name}");
    } else {
        let code = status
            .code()
            .map_or_else(|| "signal".to_string(), |code| code.to_string());
        eprintln!("[evidence] FAIL  {name} exit={code}");
        state.evidence_gate_failures += 1;
    }
    println!();
    Ok(())
}

fn run_evidence_gate_capture_allow_failure(
    repo_root: &Path,
    state: &mut GateState,
    name: &str,
    argv: &[&str],
) -> Result<String> {
    run_evidence_gate_capture_inner(repo_root, state, name, argv, false)
}

fn run_evidence_gate_capture_inner(
    repo_root: &Path,
    state: &mut GateState,
    name: &str,
    argv: &[&str],
    fail_closes: bool,
) -> Result<String> {
    println!("[evidence] START {name}");
    quote_command(argv);
    let output = match ProcessCommand::new(argv[0])
        .args(&argv[1..])
        .current_dir(repo_root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()
    {
        Ok(output) => output,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            // Shell semantics: a missing command is exit 127; the gate run
            // continues and downstream parsing of the (empty) captured output
            // stays fail-closed.
            if fail_closes {
                eprintln!(
                    "[evidence] FAIL  {name} exit=127 (command not found: {})",
                    argv[0]
                );
                state.evidence_gate_failures += 1;
            } else {
                eprintln!(
                    "[evidence] INFO  {name} exit=127 (command not found: {}; parsed as fail-closed inventory)",
                    argv[0]
                );
            }
            println!();
            return Ok(String::new());
        }
        Err(error) => {
            return Err(error).with_context(|| format!("run evidence gate {name}"));
        }
    };
    io::stdout().write_all(&output.stdout)?;
    io::stderr().write_all(&output.stderr)?;
    let combined = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    if output.status.success() {
        println!("[evidence] PASS  {name}");
    } else {
        let code = output
            .status
            .code()
            .map_or_else(|| "signal".to_string(), |code| code.to_string());
        if fail_closes {
            eprintln!("[evidence] FAIL  {name} exit={code}");
            state.evidence_gate_failures += 1;
        } else {
            eprintln!("[evidence] INFO  {name} exit={code} (parsed as fail-closed inventory)");
        }
    }
    println!();
    Ok(combined)
}

fn quote_command(argv: &[&str]) {
    print!("$");
    for arg in argv {
        print!(" {}", quote_arg(arg));
    }
    println!();
}

fn quote_arg(arg: &str) -> String {
    if arg
        .bytes()
        .all(|byte| byte.is_ascii_alphanumeric() || b"@%_+=:,./-".contains(&byte))
    {
        return arg.to_string();
    }
    let escaped = arg.replace('\'', "'\\''");
    format!("'{escaped}'")
}

fn command_string(argv: &[String]) -> String {
    argv.iter()
        .map(|arg| quote_arg(arg))
        .collect::<Vec<_>>()
        .join(" ")
}

struct TimedProcessOutput {
    output: Option<Output>,
    timed_out: bool,
    duration_ms: u64,
    error: Option<String>,
}

fn check_chc_bmc_rust_horn_smoke(args: &ResolvedArgs, state: &mut GateState) -> Result<()> {
    println!("[blocker-check] START {CHC_BMC_RUST_HORN_SMOKE_ID}");
    let mut cases = Vec::new();
    for spec in CHC_BMC_RUST_HORN_CASES {
        cases.push(run_chc_bmc_rust_horn_case(args, *spec)?);
    }

    let cases_passed = cases.iter().filter(|case| case.status == "pass").count();
    let cases_failed = cases.len().saturating_sub(cases_passed);
    let status = if cases_failed == 0 { "pass" } else { "fail" };
    let first_failed_command = cases
        .iter()
        .find(|case| case.status == "fail")
        .map(|case| command_string(&case.command));
    let failure_summary = cases
        .iter()
        .filter_map(|case| {
            case.finding
                .as_ref()
                .map(|finding| format!("{}: {finding}", case.id))
        })
        .collect::<Vec<_>>();

    state.targeted_smokes.push(TargetedSmokeCheck {
        id: CHC_BMC_RUST_HORN_SMOKE_ID.to_string(),
        required: true,
        status: status.to_string(),
        solver_timeout_ms: CHC_BMC_RUST_HORN_SOLVER_TIMEOUT_MS,
        wall_timeout_ms: CHC_BMC_RUST_HORN_WALL_TIMEOUT_MS,
        cases_total: CHC_BMC_RUST_HORN_CASES.len(),
        cases_passed,
        cases_failed,
        cases,
    });

    if cases_failed == 0 {
        println!("[blocker-check] PASS {CHC_BMC_RUST_HORN_SMOKE_ID}: both rust-horn BMC unsafe canaries returned UNSAFE");
    } else {
        let command = first_failed_command
            .unwrap_or_else(|| chc_bmc_rust_horn_command_display(CHC_BMC_RUST_HORN_CASES[0]));
        let finding = format!(
            "expected exit 0 with first non-empty line unsat and UNSAFE certificate; {}",
            failure_summary.join("; ")
        );
        eprintln!("[blocker-check] FAIL {CHC_BMC_RUST_HORN_SMOKE_ID}: {finding}");
        state.add_blocker(
            CHC_BMC_RUST_HORN_SMOKE_ID,
            "targeted_smokes.chc_bmc_rust_horn_smoke",
            &command,
            finding,
        );
    }
    println!();
    Ok(())
}

fn run_chc_bmc_rust_horn_case(
    args: &ResolvedArgs,
    spec: ChcBmcRustHornCaseSpec,
) -> Result<TargetedSmokeCase> {
    let command = chc_bmc_rust_horn_command(args, spec);
    let command_refs = command.iter().map(String::as_str).collect::<Vec<_>>();
    println!(
        "[blocker-check] CASE {CHC_BMC_RUST_HORN_SMOKE_ID}: {}",
        spec.id
    );
    quote_command(&command_refs);

    let fixture = args.repo_root.join(spec.path);
    let run = if fixture.is_file() {
        run_process_with_wall_timeout(
            &resolve_repo_path(&args.repo_root, &args.ay),
            &command_refs[1..],
            &args.repo_root,
            Duration::from_millis(CHC_BMC_RUST_HORN_WALL_TIMEOUT_MS),
        )
    } else {
        TimedProcessOutput {
            output: None,
            timed_out: false,
            duration_ms: 0,
            error: Some(format!("fixture is missing: {}", spec.path)),
        }
    };

    if let Some(output) = &run.output {
        io::stdout().write_all(&output.stdout)?;
        io::stderr().write_all(&output.stderr)?;
    }

    let stdout = run
        .output
        .as_ref()
        .map(|output| String::from_utf8_lossy(&output.stdout).into_owned())
        .unwrap_or_default();
    let predicates = TargetedSmokeStdoutPredicates {
        has_unsat_line: stdout_has_exact_line(&stdout, spec.expected_result),
        first_non_empty_line_is_unsat: stdout_first_non_empty_line_is(
            &stdout,
            spec.expected_result,
        ),
        has_unsafe_certificate: stdout.contains(";; AY CHC Certificate: UNSAFE"),
        has_unknown_line: stdout_has_exact_line(&stdout, "unknown"),
        has_timeout_reason: stdout.contains("(:reason-unknown \"timeout\")"),
    };
    let exit_code = run.output.as_ref().and_then(|output| output.status.code());
    let mut reasons = Vec::new();
    if exit_code != Some(0) {
        reasons.push(format!("exit_code={exit_code:?}, expected 0"));
    }
    if run.timed_out {
        reasons.push(format!(
            "wall timeout fired at {CHC_BMC_RUST_HORN_WALL_TIMEOUT_MS}ms"
        ));
    }
    if let Some(error) = &run.error {
        reasons.push(error.clone());
    }
    if !predicates.first_non_empty_line_is_unsat {
        reasons.push(format!(
            "stdout first non-empty line is not {:?}",
            spec.expected_result
        ));
    }
    if !predicates.has_unsafe_certificate {
        reasons.push(format!(
            "stdout is missing CHC certificate marker {:?}",
            spec.expected_certificate
        ));
    }
    if predicates.has_unknown_line {
        reasons.push("stdout contains exact line \"unknown\"".to_string());
    }
    if predicates.has_timeout_reason {
        reasons.push("stdout contains timeout reason".to_string());
    }

    let status = if reasons.is_empty() { "pass" } else { "fail" };
    let finding = (!reasons.is_empty()).then(|| reasons.join("; "));
    if let Some(finding) = &finding {
        eprintln!("[blocker-check] FAIL  {}: {finding}", spec.id);
    } else {
        println!("[blocker-check] PASS  {}", spec.id);
    }

    Ok(TargetedSmokeCase {
        id: spec.id.to_string(),
        path: spec.path.to_string(),
        expected_verdict: spec.expected_verdict,
        expected_result: spec.expected_result.to_string(),
        expected_certificate: spec.expected_certificate.to_string(),
        command,
        exit_code,
        timed_out: run.timed_out,
        duration_ms: run.duration_ms,
        stdout_predicates: predicates,
        status: status.to_string(),
        finding,
    })
}

fn run_process_with_wall_timeout(
    program: &Path,
    argv: &[&str],
    repo_root: &Path,
    wall_timeout: Duration,
) -> TimedProcessOutput {
    let start = Instant::now();
    let mut child = match ProcessCommand::new(program)
        .args(argv)
        .current_dir(repo_root)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(error) => {
            return TimedProcessOutput {
                output: None,
                timed_out: false,
                duration_ms: duration_millis(start.elapsed()),
                error: Some(format!("spawn failed: {error}")),
            };
        }
    };

    let deadline = start + wall_timeout;
    let mut timed_out = false;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) if Instant::now() >= deadline => {
                timed_out = true;
                let _ = child.kill();
                break;
            }
            Ok(None) => thread::sleep(Duration::from_millis(20)),
            Err(error) => {
                let _ = child.kill();
                return TimedProcessOutput {
                    output: child.wait_with_output().ok(),
                    timed_out: false,
                    duration_ms: duration_millis(start.elapsed()),
                    error: Some(format!("wait failed: {error}")),
                };
            }
        }
    }

    match child.wait_with_output() {
        Ok(output) => TimedProcessOutput {
            output: Some(output),
            timed_out,
            duration_ms: duration_millis(start.elapsed()),
            error: None,
        },
        Err(error) => TimedProcessOutput {
            output: None,
            timed_out,
            duration_ms: duration_millis(start.elapsed()),
            error: Some(format!("collect output failed: {error}")),
        },
    }
}

fn duration_millis(duration: Duration) -> u64 {
    duration.as_millis().min(u64::MAX as u128) as u64
}

fn stdout_has_exact_line(stdout: &str, expected: &str) -> bool {
    stdout
        .lines()
        .any(|line| line.trim_end_matches('\r') == expected)
}

fn stdout_first_non_empty_line_is(stdout: &str, expected: &str) -> bool {
    stdout
        .lines()
        .map(|line| line.trim_end_matches('\r'))
        .find(|line| !line.trim().is_empty())
        .is_some_and(|line| line == expected)
}

fn chc_bmc_rust_horn_command(args: &ResolvedArgs, spec: ChcBmcRustHornCaseSpec) -> Vec<String> {
    vec![
        args.ay.display().to_string(),
        "solve".to_string(),
        "--chc".to_string(),
        "--timeout".to_string(),
        CHC_BMC_RUST_HORN_SOLVER_TIMEOUT_MS.to_string(),
        spec.path.to_string(),
    ]
}

fn chc_bmc_rust_horn_command_display(spec: ChcBmcRustHornCaseSpec) -> String {
    command_string(&[
        "./target/release/ay".to_string(),
        "solve".to_string(),
        "--chc".to_string(),
        "--timeout".to_string(),
        CHC_BMC_RUST_HORN_SOLVER_TIMEOUT_MS.to_string(),
        spec.path.to_string(),
    ])
}

fn resolve_repo_path(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    }
}

fn current_head(repo_root: &Path) -> Option<String> {
    git_output(repo_root, &["rev-parse", "HEAD"])
}

fn git_output(repo_root: &Path, args: &[&str]) -> Option<String> {
    let output = ProcessCommand::new("git")
        .args(args)
        .current_dir(repo_root)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn check_compatibility_matrix(args: &ResolvedArgs, state: &mut GateState) {
    let doc = args.repo_root.join("the development design notes");
    let command = compatibility_command();
    let Ok(text) = fs::read_to_string(&doc) else {
        state.add_blocker(
            "compatibility_matrix",
            "the development design notes",
            &command,
            "the development design notes is missing".to_string(),
        );
        return;
    };
    let non_ready = non_ready_compatibility_rows(&text);
    if non_ready.is_empty() {
        println!("[blocker-check] PASS compatibility_matrix: all matrix rows are Ready");
    } else {
        state.add_blocker(
            "compatibility_matrix",
            "the development design notes",
            &command,
            format!("non-Ready Z3 compatibility rows: {}", non_ready.join("; ")),
        );
    }
}

fn non_ready_compatibility_rows(text: &str) -> Vec<String> {
    compatibility_matrix_lines(text)
        .into_iter()
        .filter_map(parse_markdown_row)
        .filter_map(|cells| {
            if cells.len() < 2 || is_markdown_header_cell(&cells[0]) {
                return None;
            }
            let status = cells[1].as_str();
            if status == "Ready" {
                None
            } else {
                Some(format!("{}={}", cells[0], cells[1]))
            }
        })
        .collect()
}

fn compatibility_matrix_lines(text: &str) -> Vec<&str> {
    let mut scoped = Vec::new();
    let mut in_launch_scope = false;
    let mut saw_launch_scope = false;

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed == "## Release-Gated Compatibility Surface" {
            saw_launch_scope = true;
            in_launch_scope = true;
            continue;
        }
        if saw_launch_scope && in_launch_scope && trimmed.starts_with("## ") {
            break;
        }
        if in_launch_scope {
            scoped.push(line);
        }
    }

    if saw_launch_scope {
        scoped
    } else {
        text.lines().collect()
    }
}

fn parse_markdown_row(line: &str) -> Option<Vec<String>> {
    if !line.starts_with('|') {
        return None;
    }
    let cells = line
        .trim()
        .trim_matches('|')
        .split('|')
        .map(str::trim)
        .map(str::to_string)
        .collect::<Vec<_>>();
    if cells.is_empty() || cells[0].chars().all(|ch| ch == '-') {
        return None;
    }
    Some(cells)
}

fn is_markdown_header_cell(cell: &str) -> bool {
    matches!(
        cell,
        "Surface"
            | "Logic or family"
            | "Status"
            | "Z3-style flag or parameter"
            | "Unsupported Z3 option"
            | "SMT-LIB command sequence"
    )
}

fn check_auflia_completeness(args: &ResolvedArgs, state: &mut GateState) {
    let doc = args.repo_root.join("the development design notes");
    let command = auflia_command();
    let Ok(text) = fs::read_to_string(&doc) else {
        state.add_blocker(
            "auflia_completeness",
            "the development design notes",
            &command,
            "the development design notes is missing".to_string(),
        );
        return;
    };
    let rows = parse_auflia_rows(&text);
    if rows.is_empty() {
        state.add_blocker(
            "auflia_completeness",
            "the development design notes",
            &command,
            "no AUFLIA row is marked Ready in the development design notes".to_string(),
        );
        return;
    }
    let not_ready = rows
        .iter()
        .filter(|(_, status)| status != "Ready")
        .map(|(name, status)| format!("{name}={status}"))
        .collect::<Vec<_>>();
    if not_ready.is_empty() {
        println!("[blocker-check] PASS auflia_completeness: AUFLIA row is Ready");
    } else {
        state.add_blocker(
            "auflia_completeness",
            "the development design notes",
            &command,
            not_ready.join("; "),
        );
    }
}

fn parse_auflia_rows(text: &str) -> Vec<(String, String)> {
    text.lines()
        .filter_map(parse_markdown_row)
        .filter_map(|cells| {
            if cells.len() < 2 || is_markdown_header_cell(&cells[0]) {
                return None;
            }
            if cells[0].to_ascii_uppercase().contains("AUFLIA") {
                Some((cells[0].clone(), cells[1].clone()))
            } else {
                None
            }
        })
        .collect()
}

fn check_benchmark_summary(args: &ResolvedArgs, state: &mut GateState) {
    let command = benchmark_command();
    let Some(summary_path) = &args.benchmark_summary else {
        state.add_blocker(
            "benchmark_packet",
            "evals/launch-packets/<run>/summary.json and provenance.txt",
            &command,
            "no real launch packet summary supplied; pass --benchmark-summary evals/launch-packets/<run>/summary.json".to_string(),
        );
        return;
    };
    let resolved = resolve_repo_path(&args.repo_root, summary_path);
    match read_json(&resolved) {
        Ok(value) => {
            let reasons = benchmark_summary_reasons(&value, &resolved, &args.repo_root);
            if reasons.is_empty() {
                println!("[blocker-check] PASS benchmark_packet: supplied launch packet summary is run evidence");
            } else {
                state.add_blocker(
                    "benchmark_packet",
                    &summary_path.display().to_string(),
                    &command,
                    reasons.join("; "),
                );
            }
        }
        Err(error) => state.add_blocker(
            "benchmark_packet",
            &summary_path.display().to_string(),
            &command,
            error,
        ),
    }
}

fn benchmark_summary_reasons(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
) -> Vec<String> {
    let mut reasons = Vec::new();
    expect_string(
        summary,
        "schema",
        "ay-launch-benchmark-packet/v1",
        &mut reasons,
    );
    expect_string(summary, "mode", "run", &mut reasons);
    expect_bool(summary, "benchmarks_executed", true, &mut reasons);
    expect_bool(summary, "packet_complete", true, &mut reasons);
    expect_i64(summary, "failure_count", 0, &mut reasons);
    if eval_ids(summary).is_empty() {
        reasons.push("summary has no eval rows".to_string());
    }
    check_benchmark_eval_scope(summary, &mut reasons);
    let raw_sha256s = check_benchmark_raw_artifacts(summary, summary_path, repo_root, &mut reasons);

    let indexed_artifact_paths =
        check_benchmark_artifact_index(summary, summary_path, repo_root, &mut reasons);
    check_benchmark_raw_hash_index(summary, raw_sha256s.as_ref(), &mut reasons);
    check_benchmark_self_validation(summary, &mut reasons);
    check_benchmark_provenance(
        summary,
        summary_path,
        repo_root,
        indexed_artifact_paths.as_ref(),
        &mut reasons,
    );
    check_benchmark_provenance_text(summary, summary_path, repo_root, &mut reasons);
    reasons
}

fn check_benchmark_eval_scope(summary: &Value, reasons: &mut Vec<String>) {
    let eval_ids = eval_ids(summary);
    if eval_ids.is_empty() {
        return;
    }
    let present = eval_ids.iter().map(String::as_str).collect::<BTreeSet<_>>();
    let required = [
        "smt-local-suite",
        "smt-smtcomp-qf-lia",
        "smt-smtcomp-qf-lra",
        "smt-smtcomp-qf-bv",
        "smt-smtcomp-qf-abv",
        "chccomp-2025-extra-small-lia",
        "z3-perf-cliffs",
    ];
    let missing = required
        .iter()
        .copied()
        .filter(|eval_id| !present.contains(eval_id))
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        reasons.push(format!(
            "missing required non-SAT launch evals: {}",
            missing.join(", ")
        ));
    }

    let out_of_scope = eval_ids
        .iter()
        .filter(|eval_id| {
            eval_id.as_str() == "sat-par2-dev"
                || eval_id.starts_with("sat-")
                || eval_id.starts_with("pb-")
                || eval_id.starts_with("jit-")
        })
        .cloned()
        .collect::<Vec<_>>();
    if !out_of_scope.is_empty() {
        reasons.push(format!(
            "out-of-scope evals present: {}",
            out_of_scope.join(", ")
        ));
    }

    if summary.get("launch_scope").and_then(Value::as_str) != Some("subset") {
        reasons.push(format!(
            "launch_scope={:?}, expected standard non-SAT 'subset'",
            summary.get("launch_scope")
        ));
    }
}

fn check_benchmark_raw_artifacts(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    reasons: &mut Vec<String>,
) -> Option<BTreeMap<String, String>> {
    let Some(rows) = summary.get("evals").and_then(Value::as_array) else {
        reasons
            .push("summary.evals is missing; planned_evals are not benchmark evidence".to_string());
        if summary.get("totals").and_then(Value::as_object).is_none() {
            reasons.push("totals is missing".to_string());
        }
        return None;
    };
    let mut raw_sha256s = BTreeMap::new();
    let mut raw_item_count = 0_u64;
    for row in rows {
        let eval_id = row
            .get("eval_id")
            .and_then(Value::as_str)
            .unwrap_or("<unknown eval>");
        let Some(results_json) = row.get("results_json").and_then(Value::as_str) else {
            reasons.push(format!("{eval_id}.results_json is missing"));
            continue;
        };
        let Some(path) = resolve_artifact_path(summary_path, repo_root, results_json) else {
            reasons.push(format!(
                "raw result artifact not found for {eval_id}: {results_json}"
            ));
            continue;
        };
        if !path.exists() {
            reasons.push(format!(
                "raw result artifact not found for {eval_id}: {results_json}"
            ));
            continue;
        }
        if path.file_stem().and_then(|stem| stem.to_str()) != Some(eval_id) {
            reasons.push(format!(
                "{eval_id}.results_json points at {:?}",
                path.file_name().and_then(|name| name.to_str())
            ));
        }
        match sha256_file_hex(&path) {
            Ok(sha256) => {
                raw_sha256s.insert(eval_id.to_string(), sha256);
            }
            Err(error) => reasons.push(format!("{eval_id}.results_json cannot be hashed: {error}")),
        }
        match read_json(&path) {
            Ok(raw) => match raw.get("items").and_then(Value::as_array) {
                Some(items) if !items.is_empty() => raw_item_count += items.len() as u64,
                _ => reasons.push(format!(
                    "raw result JSON for {eval_id} has no benchmark items"
                )),
            },
            Err(error) => reasons.push(format!(
                "cannot read raw result JSON for {eval_id}: {error}"
            )),
        }
    }

    let Some(totals) = summary.get("totals").and_then(Value::as_object) else {
        reasons.push("totals is missing".to_string());
        return Some(raw_sha256s);
    };
    if totals.get("evals").and_then(Value::as_u64) != Some(rows.len() as u64) {
        reasons.push(format!(
            "totals.evals={:?}, expected {}",
            totals.get("evals"),
            rows.len()
        ));
    }
    if totals.get("benchmarks").and_then(Value::as_u64) != Some(raw_item_count) {
        reasons.push(format!(
            "totals.benchmarks={:?}, expected raw item count {raw_item_count}",
            totals.get("benchmarks")
        ));
    }

    Some(raw_sha256s)
}

fn check_benchmark_artifact_index(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    reasons: &mut Vec<String>,
) -> Option<BTreeSet<PathBuf>> {
    let Some(index) = summary.get("artifact_index").and_then(Value::as_object) else {
        reasons.push("artifact_index is missing".to_string());
        return None;
    };
    if index.get("schema").and_then(Value::as_str) != Some("ay-launch-benchmark-artifact-index/v1")
    {
        reasons.push(format!(
            "artifact_index.schema={:?}, expected 'ay-launch-benchmark-artifact-index/v1'",
            index.get("schema")
        ));
    }
    if !matches!(
        index.get("hash_algorithm").and_then(Value::as_str),
        None | Some("sha256")
    ) {
        reasons.push(format!(
            "artifact_index.hash_algorithm={:?}",
            index.get("hash_algorithm")
        ));
    }
    if index.get("missing_count").and_then(Value::as_i64) != Some(0) {
        reasons.push(format!(
            "artifact_index.missing_count={:?}, expected 0",
            index.get("missing_count")
        ));
    }

    let artifacts = match index.get("artifacts").and_then(Value::as_array) {
        Some(artifacts) if !artifacts.is_empty() => artifacts,
        _ => {
            reasons.push("artifact_index.artifacts is empty".to_string());
            return Some(BTreeSet::new());
        }
    };
    if index.get("artifact_count").and_then(Value::as_u64) != Some(artifacts.len() as u64) {
        reasons.push(format!(
            "artifact_index.artifact_count={:?}, expected {}",
            index.get("artifact_count"),
            artifacts.len()
        ));
    }
    let mut present_roles = BTreeSet::new();
    let mut indexed_paths = BTreeSet::new();
    for (row_index, artifact) in artifacts.iter().enumerate() {
        let label = format!("artifact_index.artifacts[{row_index}]");
        if artifact.get("exists").and_then(Value::as_bool) != Some(true) {
            reasons.push(format!("{label}.exists is not true"));
        }
        if let Some(role) = artifact.get("role").and_then(Value::as_str) {
            present_roles.insert(role.to_string());
        }
        if let Some(raw_path) = artifact.get("path").and_then(Value::as_str) {
            if let Some(path) = resolve_artifact_path(summary_path, repo_root, raw_path) {
                if path.exists() {
                    indexed_paths.insert(path.canonicalize().unwrap_or(path));
                }
            }
        }
        check_artifact_sha256_row(artifact, summary_path, repo_root, &label, reasons);
    }
    let required_sidecars = BTreeSet::from([
        "commands_log",
        "input_inventory_jsonl",
        "planned_evals_tsv",
        "provenance_json",
        "provenance_txt",
        "summary_md",
    ]);
    let missing_sidecars = required_sidecars
        .difference(&present_roles.iter().map(String::as_str).collect())
        .copied()
        .collect::<Vec<_>>();
    if !missing_sidecars.is_empty() {
        reasons.push(format!(
            "artifact_index missing required sidecar roles: {}",
            missing_sidecars.join(", ")
        ));
    }

    let indexed_raw_count = index.get("raw_result_count").and_then(Value::as_u64);
    if let Some(raw_hashes) = summary
        .get("raw_artifact_sha256s")
        .and_then(Value::as_object)
    {
        if indexed_raw_count != Some(raw_hashes.len() as u64) {
            reasons.push(format!(
                "artifact_index.raw_result_count={:?}, expected {}",
                index.get("raw_result_count"),
                raw_hashes.len()
            ));
        }
        if summary.get("raw_artifact_count").and_then(Value::as_u64)
            != Some(raw_hashes.len() as u64)
        {
            reasons.push(format!(
                "raw_artifact_count={:?}, expected {}",
                summary.get("raw_artifact_count"),
                raw_hashes.len()
            ));
        }
        if index.get("raw_result_sha256s") != summary.get("raw_artifact_sha256s") {
            reasons.push(
                "artifact_index.raw_result_sha256s does not match raw_artifact_sha256s".to_string(),
            );
        }
    }
    Some(indexed_paths)
}

fn check_benchmark_raw_hash_index(
    summary: &Value,
    raw_sha256s: Option<&BTreeMap<String, String>>,
    reasons: &mut Vec<String>,
) {
    let Some(raw_sha256s) = raw_sha256s else {
        return;
    };
    let raw_json = Value::Object(
        raw_sha256s
            .iter()
            .map(|(key, value)| (key.clone(), Value::String(value.clone())))
            .collect(),
    );
    if summary.get("raw_artifact_sha256s") != Some(&raw_json) {
        reasons.push("raw_artifact_sha256s does not match raw result artifacts".to_string());
    }
    if summary.get("raw_artifact_count").and_then(Value::as_u64) != Some(raw_sha256s.len() as u64) {
        reasons.push(format!(
            "raw_artifact_count={:?}, expected {}",
            summary.get("raw_artifact_count"),
            raw_sha256s.len()
        ));
    }

    let Some(index) = summary.get("artifact_index").and_then(Value::as_object) else {
        return;
    };
    if index.get("raw_result_count").and_then(Value::as_u64) != Some(raw_sha256s.len() as u64) {
        reasons.push(format!(
            "artifact_index.raw_result_count={:?}, expected {}",
            index.get("raw_result_count"),
            raw_sha256s.len()
        ));
    }
    if index.get("raw_result_sha256s") != Some(&raw_json) {
        reasons.push(
            "artifact_index.raw_result_sha256s does not match raw result artifacts".to_string(),
        );
    }

    let indexed_raw = index
        .get("artifacts")
        .and_then(Value::as_array)
        .map(|artifacts| {
            artifacts
                .iter()
                .filter(|artifact| {
                    artifact.get("role").and_then(Value::as_str) == Some("raw_results_json")
                })
                .filter_map(|artifact| {
                    let eval_id = artifact.get("eval_id").and_then(Value::as_str)?;
                    let sha256 = artifact.get("sha256").and_then(Value::as_str)?;
                    Some((eval_id.to_string(), sha256.to_string()))
                })
                .collect::<BTreeMap<_, _>>()
        })
        .unwrap_or_default();
    if &indexed_raw != raw_sha256s {
        reasons.push(
            "artifact_index raw_results_json rows do not match raw result artifacts".to_string(),
        );
    }
}

fn check_benchmark_self_validation(summary: &Value, reasons: &mut Vec<String>) {
    let Some(self_validation) = summary.get("self_validation").and_then(Value::as_object) else {
        reasons.push("self_validation is missing".to_string());
        return;
    };
    if self_validation.get("schema").and_then(Value::as_str)
        != Some("ay-launch-benchmark-self-validation/v1")
    {
        reasons.push(format!(
            "self_validation.schema={:?}, expected 'ay-launch-benchmark-self-validation/v1'",
            self_validation.get("schema")
        ));
    }
    if self_validation.get("status").and_then(Value::as_str) != Some("pass") {
        reasons.push(format!(
            "self_validation.status={:?}, expected 'pass'",
            self_validation.get("status")
        ));
    }
    match self_validation.get("checks").and_then(Value::as_object) {
        Some(checks) if !checks.is_empty() => {
            let failed = checks
                .iter()
                .filter_map(|(name, passed)| (passed.as_bool() != Some(true)).then_some(name))
                .cloned()
                .collect::<Vec<_>>();
            if !failed.is_empty() {
                reasons.push(format!(
                    "self_validation failed checks: {}",
                    failed.join(", ")
                ));
            }
        }
        _ => reasons.push("self_validation.checks is empty".to_string()),
    }
    if self_validation.get("errors") != Some(&Value::Array(Vec::new())) {
        reasons.push(format!(
            "self_validation.errors={:?}, expected []",
            self_validation.get("errors")
        ));
    }
}

fn check_benchmark_provenance(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    indexed_artifact_paths: Option<&BTreeSet<PathBuf>>,
    reasons: &mut Vec<String>,
) {
    if summary.get("git_clean").and_then(Value::as_bool) != Some(true) {
        reasons.push("git_clean is not true".to_string());
    }
    let current_head = current_head(repo_root);
    if let Some(head) = current_head.as_deref() {
        if summary.get("git_commit").and_then(Value::as_str) != Some(head) {
            reasons.push(format!(
                "git_commit={:?} does not match current HEAD={head}",
                summary.get("git_commit")
            ));
        }
    }

    let Some(provenance_json) = summary.get("provenance_json").and_then(Value::as_str) else {
        reasons.push("provenance_json is missing".to_string());
        return;
    };
    let Some(provenance_path) = resolve_artifact_path(summary_path, repo_root, provenance_json)
    else {
        reasons.push(format!("provenance_json not found: {provenance_json}"));
        return;
    };
    if !provenance_path.exists() {
        reasons.push(format!("provenance_json not found: {provenance_json}"));
        return;
    }
    if let Some(indexed_paths) = indexed_artifact_paths.filter(|paths| !paths.is_empty()) {
        let resolved_provenance = provenance_path
            .canonicalize()
            .unwrap_or_else(|_| provenance_path.clone());
        if !indexed_paths.contains(&resolved_provenance) {
            reasons.push("provenance_json is not listed in artifact_index".to_string());
        }
    }
    let provenance = match read_json(&provenance_path) {
        Ok(value) => value,
        Err(error) => {
            reasons.push(format!("cannot read provenance_json: {error}"));
            return;
        }
    };

    if provenance.get("schema").and_then(Value::as_str) != Some("ay-launch-benchmark-provenance/v1")
    {
        reasons.push(format!(
            "provenance_json.schema={:?}, expected 'ay-launch-benchmark-provenance/v1'",
            provenance.get("schema")
        ));
    }
    if provenance.get("mode") != summary.get("mode") {
        reasons.push(format!(
            "provenance_json.mode={:?} does not match summary mode={:?}",
            provenance.get("mode"),
            summary.get("mode")
        ));
    }

    let provenance_repo = provenance.get("repo").and_then(Value::as_object);
    match provenance_repo {
        Some(repo) => {
            if repo.get("clean").and_then(Value::as_bool) != Some(true) {
                reasons.push("provenance_json.repo.clean is not true".to_string());
            }
            if repo
                .get("git_status_short")
                .and_then(Value::as_array)
                .is_some_and(|rows| !rows.is_empty())
            {
                reasons.push("provenance_json.repo.git_status_short is not clean".to_string());
            }
            if let Some(head) = current_head.as_deref() {
                if repo.get("commit").and_then(Value::as_str) != Some(head) {
                    reasons.push(format!(
                        "provenance_json.repo.commit={:?} does not match current HEAD={head}",
                        repo.get("commit")
                    ));
                }
            }
        }
        None => reasons.push("provenance_json.repo is not an object".to_string()),
    }

    check_benchmark_provenance_selection(&provenance, summary, reasons);
    check_benchmark_provenance_ay(&provenance, current_head.as_deref(), reasons);
}

fn check_benchmark_provenance_text(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    reasons: &mut Vec<String>,
) {
    let provenance_path = summary_path.with_file_name("provenance.txt");
    let Ok(text) = fs::read_to_string(&provenance_path) else {
        reasons.push("provenance.txt is missing next to summary.json".to_string());
        return;
    };

    let mut git_commit: Option<String> = None;
    let mut launch_scope: Option<String> = None;
    let mut requested_evals = Vec::new();
    let mut excluded_evals = Vec::new();
    let mut dirty_lines = Vec::new();
    let mut in_status = false;

    for raw in text.lines() {
        let line = raw.trim_end();
        if let Some(value) = line.strip_prefix("git_commit=") {
            git_commit = Some(value.trim().to_string());
            in_status = false;
            continue;
        }
        if let Some(value) = line.strip_prefix("launch_scope=") {
            launch_scope = Some(value.trim().to_string());
            in_status = false;
            continue;
        }
        if let Some(value) = line.strip_prefix("requested_evals=") {
            requested_evals = value
                .trim()
                .split(',')
                .filter(|part| !part.is_empty())
                .map(str::to_string)
                .collect();
            in_status = false;
            continue;
        }
        if let Some(value) = line.strip_prefix("excluded_evals=") {
            excluded_evals = value
                .trim()
                .split(',')
                .filter(|part| !part.is_empty())
                .map(str::to_string)
                .collect();
            in_status = false;
            continue;
        }
        if line == "git_status_short:" {
            in_status = true;
            continue;
        }
        if in_status {
            if line.trim().is_empty() {
                in_status = false;
            } else {
                dirty_lines.push(line.to_string());
            }
        }
    }

    match git_commit.as_deref() {
        Some(commit) if !commit.is_empty() => {
            if let Some(head) = current_head(repo_root) {
                if commit != head {
                    reasons.push(format!(
                        "git_commit={commit} does not match current HEAD={head}"
                    ));
                }
            }
        }
        _ => reasons.push("provenance.txt lacks git_commit".to_string()),
    }

    let summary_launch_scope = summary.get("launch_scope").and_then(Value::as_str);
    match launch_scope.as_deref() {
        None => reasons.push("provenance.txt lacks launch_scope".to_string()),
        Some(scope) if summary_launch_scope.is_some() && Some(scope) != summary_launch_scope => {
            reasons.push(format!(
                "provenance launch_scope={scope:?} does not match summary launch_scope={summary_launch_scope:?}"
            ));
        }
        _ => {}
    }

    if !requested_evals.is_empty() {
        reasons.push(
            "provenance requested_evals is present; broad gate requires full non-SAT packet, not an explicit eval subset"
                .to_string(),
        );
    }

    let excluded = excluded_evals
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let expected = BTreeSet::from(["sat-par2-dev"]);
    if !excluded.is_empty() && excluded != expected {
        reasons.push(
            "provenance excluded_evals must be exactly sat-par2-dev for this non-SAT gate"
                .to_string(),
        );
    }
    if summary_launch_scope == Some("subset") && excluded != expected {
        reasons.push(
            "launch_scope='subset' is accepted only for the standard non-SAT packet excluding sat-par2-dev"
                .to_string(),
        );
    }
    if !dirty_lines.is_empty() {
        reasons.push("provenance git_status_short is not clean".to_string());
    }
}

fn check_benchmark_provenance_selection(
    provenance: &Value,
    summary: &Value,
    reasons: &mut Vec<String>,
) {
    let Some(selection) = provenance.get("selection").and_then(Value::as_object) else {
        reasons.push("provenance_json.selection is not an object".to_string());
        return;
    };
    let launch_scope = summary.get("launch_scope").and_then(Value::as_str);
    if selection.get("launch_scope").and_then(Value::as_str) != launch_scope {
        reasons.push(format!(
            "provenance_json.selection.launch_scope={:?} does not match summary launch_scope={launch_scope:?}",
            selection.get("launch_scope")
        ));
    }
    if selection
        .get("requested_evals")
        .and_then(Value::as_array)
        .is_some_and(|rows| !rows.is_empty())
    {
        reasons.push("provenance_json.selection.requested_evals is present".to_string());
    }
    let excluded = selection
        .get("excluded_evals")
        .and_then(Value::as_array)
        .map(|rows| {
            rows.iter()
                .filter_map(|row| row.get("eval_id").and_then(Value::as_str))
                .collect::<BTreeSet<_>>()
        })
        .unwrap_or_default();
    let expected = BTreeSet::from(["sat-par2-dev"]);
    if launch_scope == Some("subset") && excluded != expected {
        reasons.push(
            "provenance_json.selection.excluded_evals must be exactly sat-par2-dev for this non-SAT gate"
                .to_string(),
        );
    }
}

fn check_benchmark_provenance_ay(
    provenance: &Value,
    current_head: Option<&str>,
    reasons: &mut Vec<String>,
) {
    let Some(ay) = provenance
        .get("tools")
        .and_then(|tools| tools.get("ay"))
        .and_then(Value::as_object)
    else {
        reasons.push("provenance_json.tools.ay is missing".to_string());
        return;
    };

    if let Some(sha256) = ay.get("sha256").and_then(Value::as_str) {
        if !is_lower_sha256(sha256) {
            reasons
                .push("provenance_json.tools.ay.sha256 is not lowercase hex SHA-256".to_string());
        }
    }

    let version_lines = ay
        .get("version")
        .and_then(|version| version.get("output"))
        .and_then(Value::as_array)
        .map(|rows| rows.iter().filter_map(Value::as_str).collect::<Vec<_>>())
        .unwrap_or_default();
    let build_commit = version_lines
        .iter()
        .find_map(|line| line.strip_prefix("build.commit="))
        .map(str::trim);
    let Some(build_commit) = build_commit else {
        reasons.push("provenance_json.tools.ay.version.output lacks build.commit".to_string());
        return;
    };
    if build_commit.contains("-dirty") {
        reasons.push(format!(
            "provenance_json.tools.ay build.commit is dirty: {build_commit:?}"
        ));
    }
    if let Some(head) = current_head {
        let clean_build_commit = build_commit.trim_end_matches("-dirty");
        if !head.starts_with(clean_build_commit) {
            reasons.push(format!(
                "provenance_json.tools.ay build.commit={build_commit:?} does not match current HEAD={head}"
            ));
        }
    }
}

fn check_proof_summary(
    args: &ResolvedArgs,
    state: &mut GateState,
    _proof_output: &str,
    proof_summary_json: &Path,
) {
    match read_json(proof_summary_json) {
        Ok(summary) => match proof_findings_from_summary_json(&summary) {
            Ok(findings) => {
                check_proof_findings(args, state, findings);
            }
            Err(error) => {
                state.add_blocker(
                    "proof_inventory",
                    &proof_summary_json.display().to_string(),
                    &proof_full_gate_command(),
                    error,
                );
            }
        },
        Err(error) => {
            state.add_blocker(
                "proof_inventory",
                &proof_summary_json.display().to_string(),
                &proof_full_gate_command(),
                format!("z3-audit summary JSON is missing or unreadable: {error}"),
            );
        }
    }
}

fn check_proof_findings(
    args: &ResolvedArgs,
    state: &mut GateState,
    findings: Vec<(String, String, String)>,
) {
    if findings.is_empty() {
        println!(
            "[blocker-check] PASS proof_coverage: z3-audit proof inventory has no fail/warn rows"
        );
        return;
    }

    for (status, surface, note) in findings {
        if status == "GATE-SKIP"
            || (status == "fail"
                && (surface.contains("DIMACS DRAT") || surface.contains("ay-sat proof")))
        {
            state.add_blocker(
                "proof_checked_gate",
                "z3-audit-proof.log",
                &proof_full_gate_command(),
                format!("{surface} is not checked by the default proof gate: {note}"),
            );
        } else if status == "SEPARATE" && surface.contains("CLI") && surface.contains("DRAT") {
            check_proof_cli_evidence(state, args, &surface, &note);
        } else if matches!(status.as_str(), "SEPARATE" | "UNSUPPORTED")
            && surface.contains("Alethe")
        {
            check_proof_alethe_replay_summary(
                state,
                args,
                &surface,
                &note,
                args.proof_alethe_replay_summary.as_ref(),
            );
        } else if status == "UNSUPPORTED" && surface.contains("Lean") {
            check_proof_lean_replay_summary(
                state,
                args,
                &surface,
                &note,
                args.proof_lean_replay_summary.as_ref(),
            );
        } else if status == "POLICY" && surface.contains("CHC") {
            check_proof_chc_replay_summary(
                state,
                args,
                &surface,
                &note,
                args.proof_chc_replay_summary.as_ref(),
            );
        } else {
            state.add_blocker(
                "proof_coverage",
                "z3-audit-summary.json",
                &proof_full_gate_command(),
                format!("{surface}={status}: {note}"),
            );
        }
    }
}

fn proof_findings_from_summary_json(
    summary: &Value,
) -> Result<Vec<(String, String, String)>, String> {
    if summary.get("schema").and_then(Value::as_str) != Some("ay-z3-replacement-audit/v1") {
        return Err("z3-audit summary JSON has the wrong schema".to_string());
    }
    if summary.get("scope").and_then(Value::as_str) != Some("full-replacement") {
        return Err(format!(
            "z3-audit summary JSON must have scope=\"full-replacement\", got {:?}",
            summary.get("scope")
        ));
    }
    let full_replacement_ready = summary
        .get("full_replacement_ready")
        .and_then(Value::as_bool)
        .ok_or_else(|| {
            "z3-audit summary JSON is missing boolean full_replacement_ready".to_string()
        })?;
    let scoped_cli_ready = summary
        .get("scoped_cli_ready")
        .and_then(Value::as_bool)
        .ok_or_else(|| "z3-audit summary JSON is missing boolean scoped_cli_ready".to_string())?;

    let mut findings = Vec::new();
    if !full_replacement_ready {
        findings.push((
            "fail".to_string(),
            "z3-audit full_replacement_ready".to_string(),
            "full_replacement_ready must be true".to_string(),
        ));
    }
    if !scoped_cli_ready {
        findings.push((
            "fail".to_string(),
            "z3-audit scoped_cli_ready".to_string(),
            "scoped_cli_ready must be true".to_string(),
        ));
    }
    if summary.get("verdict").and_then(Value::as_str) != Some("pass") {
        findings.push((
            "fail".to_string(),
            "z3-audit summary verdict".to_string(),
            format!("verdict must be pass, got {:?}", summary.get("verdict")),
        ));
    }
    match summary.get("failed").and_then(Value::as_u64) {
        Some(0) => {}
        Some(failed) => findings.push((
            "fail".to_string(),
            "z3-audit summary failed count".to_string(),
            format!("failed must be 0, got {failed}"),
        )),
        None => {
            return Err("z3-audit summary JSON is missing numeric failed count".to_string());
        }
    }
    match summary.get("proof_failed").and_then(Value::as_u64) {
        Some(0) => {}
        Some(failed) => findings.push((
            "fail".to_string(),
            "z3-audit proof inventory failed count".to_string(),
            format!("proof_failed must be 0, got {failed}"),
        )),
        None => {
            return Err("z3-audit summary JSON is missing numeric proof_failed count".to_string());
        }
    }

    let rows = summary
        .get("proof_inventory")
        .and_then(Value::as_array)
        .ok_or_else(|| "z3-audit summary JSON is missing proof_inventory rows".to_string())?;
    if rows.is_empty() {
        return Err("z3-audit summary JSON has an empty proof_inventory".to_string());
    }
    findings.extend(rows.iter().filter_map(|row| {
        let status = row.get("status").and_then(Value::as_str)?;
        if status == "pass" {
            return None;
        }
        let surface = row.get("surface").and_then(Value::as_str)?;
        let finding = row
            .get("finding")
            .and_then(Value::as_str)
            .unwrap_or("missing proof finding");
        let status = if matches!(status, "fail" | "warn") {
            format!("z3-audit-{status}")
        } else {
            status.to_string()
        };
        Some((status, surface.to_string(), finding.to_string()))
    }));
    Ok(findings)
}

fn check_proof_cli_evidence(state: &mut GateState, args: &ResolvedArgs, surface: &str, note: &str) {
    let Some(path) = args.proof_cli_evidence.as_ref() else {
        state.add_blocker(
            "proof_cli_verify",
            "z3-cli-proof-verify.json",
            &proof_cli_command(),
            format!("{surface} is not checked in the default proof inventory: {note}; run the command for native audit evidence, or pass --proof-cli-evidence z3-cli-proof-verify.json for a legacy ay-proof-cli-verify/v1 packet"),
        );
        return;
    };
    let resolved = resolve_repo_path(&args.repo_root, path);
    match read_json(&resolved) {
        Ok(value) => {
            let reasons = proof_cli_evidence_reasons(
                &value,
                &resolved,
                &args.repo_root,
                args.proof_cli_log.as_deref(),
            );
            if reasons.is_empty() {
                println!("[blocker-check] PASS proof_cli_verify: supplied CLI proof evidence shows targeted test passed");
            } else {
                state.add_blocker(
                    "proof_cli_verify",
                    &path.display().to_string(),
                    &proof_cli_command(),
                    reasons.join("; "),
                );
            }
        }
        Err(error) => state.add_blocker(
            "proof_cli_verify",
            &path.display().to_string(),
            &proof_cli_command(),
            error,
        ),
    }
}

fn proof_cli_evidence_reasons(
    evidence: &Value,
    evidence_path: &Path,
    repo_root: &Path,
    proof_cli_log: Option<&Path>,
) -> Vec<String> {
    let mut reasons = Vec::new();
    expect_string(evidence, "schema", "ay-proof-cli-verify/v1", &mut reasons);
    expect_string(evidence, "status", "pass", &mut reasons);
    expect_string(
        evidence,
        "surface",
        "CLI DRAT/LRAT post-solve",
        &mut reasons,
    );
    if let Some(head) = current_head(repo_root) {
        if evidence.get("ay_commit").and_then(Value::as_str) != Some(head.as_str()) {
            reasons.push(format!(
                "ay_commit={:?} does not match current HEAD={head}",
                evidence.get("ay_commit")
            ));
        }
    } else if evidence
        .get("ay_commit")
        .and_then(Value::as_str)
        .is_none_or(str::is_empty)
    {
        reasons.push("ay_commit is missing".to_string());
    }

    let expected_command = json!([
        "cargo",
        "test",
        "-p",
        "ay",
        "--test",
        "group_cli",
        "verify_proof_8771"
    ]);
    if evidence.get("command") != Some(&expected_command) {
        reasons.push("command does not match targeted CLI proof cargo test".to_string());
    }

    let result = evidence.get("result");
    check_proof_cli_result(result, &mut reasons);
    check_errors_empty(evidence, "evidence", &mut reasons);

    let Some(log) = evidence.get("log").and_then(Value::as_object) else {
        reasons.push("log is missing".to_string());
        return reasons;
    };
    let raw_log_path = log.get("path").and_then(Value::as_str);
    let log_path = match raw_log_path {
        Some(path) if !path.is_empty() => resolve_artifact_path(evidence_path, repo_root, path),
        _ => {
            reasons.push("log.path is missing".to_string());
            None
        }
    };
    if let (Some(expected), Some(actual)) = (proof_cli_log, log_path.as_ref()) {
        let expected = resolve_repo_path(repo_root, expected);
        if !paths_equivalent(actual, &expected) {
            reasons.push("log.path does not match --proof-cli-log".to_string());
        }
    }
    if let (Some(raw_path), Some(path)) = (raw_log_path, log_path.as_ref()) {
        if !path.is_file() {
            reasons.push(format!("log.path not found: {raw_path}"));
        } else {
            match sha256_file_hex(path) {
                Ok(actual)
                    if log.get("sha256").and_then(Value::as_str) != Some(actual.as_str()) =>
                {
                    reasons.push("log.sha256 does not match log.path".to_string());
                }
                Ok(_) => {}
                Err(error) => reasons.push(format!("log.sha256 cannot be checked: {error}")),
            }
            check_proof_cli_log_text(path, result, &mut reasons);
        }
    }

    reasons
}

fn check_proof_cli_result(result: Option<&Value>, reasons: &mut Vec<String>) {
    let Some(result) = result else {
        reasons.push("result is missing".to_string());
        return;
    };
    if !result.is_object() {
        reasons.push("result is missing".to_string());
        return;
    }
    if result.get("checked").and_then(Value::as_bool) != Some(true) {
        reasons.push("result.checked is not true".to_string());
    }
    if result.get("exit_code").and_then(Value::as_i64) != Some(0) {
        reasons.push(format!(
            "result.exit_code={:?}, expected 0",
            result.get("exit_code")
        ));
    }
    if result.get("test_filter").and_then(Value::as_str) != Some("verify_proof_8771") {
        reasons.push("result.test_filter must be verify_proof_8771".to_string());
    }
    if result.get("failures").and_then(Value::as_i64) != Some(0) {
        reasons.push(format!(
            "result.failures={:?}, expected 0",
            result.get("failures")
        ));
    }
}

fn check_proof_cli_log_text(path: &Path, result: Option<&Value>, reasons: &mut Vec<String>) {
    let Ok(text) = fs::read_to_string(path) else {
        reasons.push(format!("log is unreadable: {}", path.display()));
        return;
    };
    if !text.contains("verify_proof_8771") {
        reasons.push("log does not mention verify_proof_8771".to_string());
    }
    let targeted_pass_count = text
        .lines()
        .filter(|line| is_verify_proof_8771_ok_line(line))
        .count() as i64;
    if targeted_pass_count == 0 {
        reasons.push("log does not show any verify_proof_8771 test passing".to_string());
    }
    let cargo_summary = parse_passing_cargo_test_summary(&text);
    let Some(cargo_summary) = cargo_summary else {
        reasons.push("log does not contain a parseable passing cargo test result".to_string());
        compare_proof_cli_result_counts(result, None, targeted_pass_count, reasons);
        return;
    };
    if cargo_summary.passed_tests <= 0 {
        reasons.push("log does not report any passed tests".to_string());
    }
    if targeted_pass_count > cargo_summary.passed_tests {
        reasons.push("log has more targeted passing tests than total passed tests".to_string());
    }
    compare_proof_cli_result_counts(result, Some(cargo_summary), targeted_pass_count, reasons);
    if !text.contains("test result: ok.") {
        reasons.push("log does not contain a passing cargo test result".to_string());
    }
    if !text.contains("0 failed") {
        reasons.push("log does not report 0 failed tests".to_string());
    }
    if text.contains("test result: FAILED")
        || text.contains("FAILED")
        || text.contains("panicked at")
    {
        reasons.push("log contains cargo failure text".to_string());
    }
}

fn is_verify_proof_8771_ok_line(line: &str) -> bool {
    let line = line.trim();
    line.starts_with("test ")
        && line.contains("verify_proof_8771")
        && line.contains(" ... ")
        && line.ends_with(" ok")
}

#[derive(Clone, Copy)]
struct CargoTestSummary {
    passed_tests: i64,
    failed_tests: i64,
    ignored_tests: i64,
    measured_tests: i64,
    filtered_out: i64,
}

fn parse_passing_cargo_test_summary(text: &str) -> Option<CargoTestSummary> {
    text.lines().find_map(|line| {
        let line = line.trim();
        let rest = line.strip_prefix("test result: ok.")?.trim();
        let mut summary = CargoTestSummary {
            passed_tests: -1,
            failed_tests: -1,
            ignored_tests: -1,
            measured_tests: -1,
            filtered_out: -1,
        };
        for part in rest
            .split(';')
            .map(str::trim)
            .filter(|part| !part.is_empty())
        {
            let mut words = part.split_whitespace();
            let Some(first) = words.next() else {
                continue;
            };
            let Ok(count) = first.parse::<i64>() else {
                continue;
            };
            let Some(label) = words.next() else {
                continue;
            };
            match label {
                "passed" => summary.passed_tests = count,
                "failed" => summary.failed_tests = count,
                "ignored" => summary.ignored_tests = count,
                "measured" => summary.measured_tests = count,
                "filtered" if words.next() == Some("out") => {
                    summary.filtered_out = count;
                }
                _ => {}
            }
        }
        (summary.passed_tests >= 0
            && summary.failed_tests >= 0
            && summary.ignored_tests >= 0
            && summary.measured_tests >= 0
            && summary.filtered_out >= 0)
            .then_some(summary)
    })
}

fn compare_proof_cli_result_counts(
    result: Option<&Value>,
    summary: Option<CargoTestSummary>,
    targeted_pass_count: i64,
    reasons: &mut Vec<String>,
) {
    let Some(result) = result.and_then(Value::as_object) else {
        return;
    };
    if result.get("targeted_pass_count").and_then(Value::as_i64) != Some(targeted_pass_count) {
        reasons.push(format!(
            "result.targeted_pass_count={:?}, expected {targeted_pass_count}",
            result.get("targeted_pass_count")
        ));
    }
    let Some(summary) = summary else {
        return;
    };
    for (key, expected) in [
        ("passed_tests", summary.passed_tests),
        ("failed_tests", summary.failed_tests),
        ("ignored_tests", summary.ignored_tests),
        ("measured_tests", summary.measured_tests),
        ("filtered_out", summary.filtered_out),
    ] {
        if result.get(key).and_then(Value::as_i64) != Some(expected) {
            reasons.push(format!(
                "result.{key}={:?}, expected {expected}",
                result.get(key)
            ));
        }
    }
}

fn paths_equivalent(left: &Path, right: &Path) -> bool {
    if let (Ok(left), Ok(right)) = (left.canonicalize(), right.canonicalize()) {
        left == right
    } else {
        left == right
    }
}

fn check_proof_alethe_replay_summary(
    state: &mut GateState,
    args: &ResolvedArgs,
    surface: &str,
    note: &str,
    path: Option<&PathBuf>,
) {
    let Some(path) = path else {
        state.add_blocker(
            "proof_external_replay",
            "smt-alethe-external-replay.json",
            &proof_alethe_replay_command(),
            format!("{surface} has no supplied external replay summary: {note}; run the command for native audit evidence, or pass --proof-alethe-replay-summary smt-alethe-external-replay.json with schema ay-proof-external-replay/v1 for a legacy replay packet"),
        );
        return;
    };
    let resolved = resolve_repo_path(&args.repo_root, path);
    match read_json(&resolved) {
        Ok(value) => {
            let reasons = proof_alethe_replay_reasons(&value, &resolved, &args.repo_root, surface);
            if reasons.is_empty() {
                println!("[blocker-check] PASS proof_external_replay: supplied SMT Alethe replay summary is current");
            } else {
                state.add_blocker(
                    "proof_external_replay",
                    &path.display().to_string(),
                    &proof_alethe_replay_command(),
                    reasons.join("; "),
                );
            }
        }
        Err(error) => state.add_blocker(
            "proof_external_replay",
            &path.display().to_string(),
            &proof_alethe_replay_command(),
            error,
        ),
    }
}

fn check_proof_lean_replay_summary(
    state: &mut GateState,
    args: &ResolvedArgs,
    surface: &str,
    note: &str,
    path: Option<&PathBuf>,
) {
    let Some(path) = path else {
        state.add_blocker(
            "proof_external_replay",
            "lean-proof-replay.json",
            &proof_lean_replay_command(),
            format!("{surface} has no supplied Lean replay summary: {note}; pass --proof-lean-replay-summary lean-proof-replay.json with schema ay-proof-lean-replay/v1 after replaying the Lean proof artifact"),
        );
        return;
    };
    let resolved = resolve_repo_path(&args.repo_root, path);
    match read_json(&resolved) {
        Ok(value) => {
            let reasons = proof_lean_replay_reasons(&value, &resolved, &args.repo_root, surface);
            if reasons.is_empty() {
                println!("[blocker-check] PASS proof_external_replay: supplied Lean replay summary is current");
            } else {
                state.add_blocker(
                    "proof_external_replay",
                    &path.display().to_string(),
                    &proof_lean_replay_command(),
                    reasons.join("; "),
                );
            }
        }
        Err(error) => state.add_blocker(
            "proof_external_replay",
            &path.display().to_string(),
            &proof_lean_replay_command(),
            error,
        ),
    }
}

fn check_proof_chc_replay_summary(
    state: &mut GateState,
    args: &ResolvedArgs,
    surface: &str,
    note: &str,
    path: Option<&PathBuf>,
) {
    let Some(path) = path else {
        state.add_blocker(
            "proof_chc_replay",
            "chc-certificate-replay.json",
            &proof_chc_replay_command(),
            format!("{surface} has no supplied CHC certificate replay summary: {note}; pass --proof-chc-replay-summary chc-certificate-replay.json with schema ay-chc-certificate-replay/v1 after replaying the certificate obligations"),
        );
        return;
    };
    let resolved = resolve_repo_path(&args.repo_root, path);
    match read_json(&resolved) {
        Ok(value) => {
            let reasons = proof_chc_replay_reasons(&value, &resolved, &args.repo_root, surface);
            if reasons.is_empty() {
                println!("[blocker-check] PASS proof_chc_replay: supplied CHC certificate replay summary is current");
            } else {
                state.add_blocker(
                    "proof_chc_replay",
                    &path.display().to_string(),
                    &proof_chc_replay_command(),
                    reasons.join("; "),
                );
            }
        }
        Err(error) => state.add_blocker(
            "proof_chc_replay",
            &path.display().to_string(),
            &proof_chc_replay_command(),
            error,
        ),
    }
}

fn proof_alethe_replay_reasons(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    surface: &str,
) -> Vec<String> {
    let mut reasons =
        proof_replay_common_reasons(summary, "ay-proof-external-replay/v1", surface, repo_root);
    check_empty_failure_kind(summary, &mut reasons);
    check_ay_binary(summary, summary_path, repo_root, &mut reasons);
    check_artifact_sha256(summary, summary_path, repo_root, "proof", &mut reasons);
    check_artifact_sha256(summary, summary_path, repo_root, "log", &mut reasons);
    reasons
}

fn proof_lean_replay_reasons(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    surface: &str,
) -> Vec<String> {
    let mut reasons =
        proof_replay_common_reasons(summary, "ay-proof-lean-replay/v1", surface, repo_root);
    // Trust: rebrand proof_replay->clean. Back-compat: accept the new canonical
    // 'clean' format AND the legacy 'lean4'/'proof_replay' aliases.
    if !matches!(
        summary.get("proof_format").and_then(Value::as_str),
        Some("clean" | "lean4" | "proof_replay")
    ) {
        reasons.push(format!(
            "proof_format={:?}, expected 'clean' (or legacy 'lean4'/'proof_replay')",
            summary.get("proof_format")
        ));
    }
    check_artifact_sha256(summary, summary_path, repo_root, "proof", &mut reasons);
    check_artifact_sha256(summary, summary_path, repo_root, "log", &mut reasons);
    if summary.get("problem").is_some() {
        check_artifact_sha256(summary, summary_path, repo_root, "problem", &mut reasons);
    }
    reasons
}

fn proof_chc_replay_reasons(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    _surface: &str,
) -> Vec<String> {
    let mut reasons = proof_replay_common_reasons(
        summary,
        "ay-chc-certificate-replay/v1",
        "CHC certificates",
        repo_root,
    );
    check_empty_failure_kind(summary, &mut reasons);
    if summary.get("diagnostic_only").and_then(Value::as_bool) == Some(true) {
        reasons.push("diagnostic_only is true".to_string());
    }
    let verdict = summary.get("verdict").and_then(Value::as_str);
    if !matches!(verdict, Some("safe" | "unsafe")) {
        reasons.push(format!(
            "verdict={:?}, expected 'safe' or 'unsafe'",
            summary.get("verdict")
        ));
    }
    for label in ["problem", "certificate", "run_log", "replay_log"] {
        check_artifact_sha256(summary, summary_path, repo_root, label, &mut reasons);
    }
    check_chc_obligations(summary, summary_path, repo_root, verdict, &mut reasons);
    reasons
}

fn proof_replay_common_reasons(
    summary: &Value,
    schema: &str,
    surface: &str,
    repo_root: &Path,
) -> Vec<String> {
    let mut reasons = Vec::new();
    expect_string(summary, "schema", schema, &mut reasons);
    expect_string(summary, "status", "pass", &mut reasons);
    expect_string(summary, "surface", surface, &mut reasons);
    if let Some(head) = current_head(repo_root) {
        if summary.get("ay_commit").and_then(Value::as_str) != Some(head.as_str()) {
            reasons.push(format!(
                "ay_commit={:?} does not match current HEAD={head}",
                summary.get("ay_commit")
            ));
        }
    } else if summary
        .get("ay_commit")
        .and_then(Value::as_str)
        .is_none_or(str::is_empty)
    {
        reasons.push("ay_commit is missing".to_string());
    }

    match summary.get("checker") {
        Some(checker) if checker.is_object() => {
            if checker
                .get("name")
                .and_then(Value::as_str)
                .is_none_or(str::is_empty)
            {
                reasons.push("checker.name is missing".to_string());
            }
            if checker
                .get("version")
                .and_then(Value::as_str)
                .is_none_or(str::is_empty)
            {
                reasons.push("checker.version is missing".to_string());
            }
            if checker.get("external").and_then(Value::as_bool) != Some(true) {
                reasons.push("checker.external is not true".to_string());
            }
        }
        _ => reasons.push("checker is not an object".to_string()),
    }

    if summary.get("command").is_none_or(is_empty_value) {
        reasons.push("command is missing".to_string());
    }
    check_replay_result(summary.get("result"), "result", &mut reasons);
    check_errors_empty(summary, "summary", &mut reasons);
    reasons
}

fn check_empty_failure_kind(summary: &Value, reasons: &mut Vec<String>) {
    match summary.get("failure_kind") {
        None | Some(Value::Null) => {}
        Some(Value::String(text)) if text.is_empty() => {}
        Some(Value::String(text)) => reasons.push(format!("failure_kind={text:?}")),
        Some(_) => reasons.push("failure_kind is not a string".to_string()),
    }
}

fn check_ay_binary(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    reasons: &mut Vec<String>,
) {
    let Some(ay_binary) = summary.get("ay_binary") else {
        reasons.push("ay_binary is missing".to_string());
        return;
    };
    if !ay_binary.is_object() {
        reasons.push("ay_binary is missing".to_string());
        return;
    }
    check_artifact_sha256_row(ay_binary, summary_path, repo_root, "ay_binary", reasons);
    if ay_binary
        .get("version_output")
        .and_then(Value::as_str)
        .is_none_or(str::is_empty)
    {
        reasons.push("ay_binary.version_output is missing".to_string());
    }
    if ay_binary.get("version_exit_code").and_then(Value::as_i64) != Some(0) {
        reasons.push(format!(
            "ay_binary.version_exit_code={:?}",
            ay_binary.get("version_exit_code")
        ));
    }
    let build_commit = ay_binary.get("build_commit").and_then(Value::as_str);
    if build_commit.is_none_or(str::is_empty) {
        reasons.push("ay_binary.build_commit is missing".to_string());
    } else if let Some(build_commit) = build_commit {
        let clean = build_commit.strip_suffix("-dirty").unwrap_or(build_commit);
        if ay_binary.get("dirty").and_then(Value::as_bool) != Some(false) {
            reasons.push(format!(
                "ay_binary.dirty={:?}, expected false",
                ay_binary.get("dirty")
            ));
        }
        if build_commit.ends_with("-dirty") {
            reasons.push(format!("ay_binary.build_commit is dirty: {build_commit:?}"));
        }
        if let Some(head) = current_head(repo_root) {
            if !head.starts_with(clean) {
                reasons.push(format!(
                    "ay_binary.build_commit={build_commit:?} does not match current HEAD={head}"
                ));
            }
        }
    }
    if ay_binary.get("matches_git_head").and_then(Value::as_bool) != Some(true) {
        reasons.push("ay_binary.matches_git_head is not true".to_string());
    }
}

fn check_replay_result(result: Option<&Value>, label: &str, reasons: &mut Vec<String>) {
    let Some(result) = result else {
        reasons.push(format!("{label} is not an object"));
        return;
    };
    if !result.is_object() {
        reasons.push(format!("{label} is not an object"));
        return;
    }
    if result.get("checked").and_then(Value::as_bool) != Some(true) {
        reasons.push(format!("{label}.checked is not true"));
    }
    if result.get("exit_code").and_then(Value::as_i64) != Some(0) {
        reasons.push(format!("{label}.exit_code={:?}", result.get("exit_code")));
    }
    if result.get("failures").and_then(Value::as_i64).unwrap_or(0) != 0 {
        reasons.push(format!("{label}.failures={:?}", result.get("failures")));
    }
    if let Some(status) = result.get("status") {
        if status.as_str() != Some("pass") {
            reasons.push(format!("{label}.status={status:?}, expected 'pass'"));
        }
    }
}

fn check_artifact_sha256(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    label: &str,
    reasons: &mut Vec<String>,
) {
    match summary.get(label) {
        Some(row) => check_artifact_sha256_row(row, summary_path, repo_root, label, reasons),
        None => reasons.push(format!("{label} is missing")),
    }
}

fn check_artifact_sha256_row(
    row: &Value,
    summary_path: &Path,
    repo_root: &Path,
    label: &str,
    reasons: &mut Vec<String>,
) {
    let Some(row) = row.as_object() else {
        reasons.push(format!("{label} is missing"));
        return;
    };
    let raw_path = row.get("path").and_then(Value::as_str);
    let artifact_path = match raw_path {
        Some(path) if !path.is_empty() => resolve_artifact_path(summary_path, repo_root, path),
        _ => {
            reasons.push(format!("{label}.path is missing"));
            None
        }
    };

    if let (Some(raw_path), Some(path)) = (raw_path, artifact_path.as_ref()) {
        if !path.exists() {
            reasons.push(format!("{label}.path not found: {raw_path}"));
        }
    }

    let expected_hash = row.get("sha256").and_then(Value::as_str);
    let Some(expected_hash) = expected_hash else {
        reasons.push(format!("{label}.sha256 is missing"));
        return;
    };
    if !is_lower_sha256(expected_hash) {
        reasons.push(format!("{label}.sha256 is not lowercase hex SHA-256"));
        return;
    }
    if let (Some(raw_path), Some(path)) = (raw_path, artifact_path) {
        if path.exists() {
            match sha256_file_hex(&path) {
                Ok(actual) if actual != expected_hash => {
                    reasons.push(format!("{label}.sha256 does not match {raw_path}"));
                }
                Ok(_) => {}
                Err(error) => reasons.push(format!("{label}.sha256 cannot be checked: {error}")),
            }
            if let Some(recorded_size) = row.get("size_bytes") {
                let actual_size = fs::metadata(&path).map(|metadata| metadata.len()).ok();
                if let Some(actual_size) = actual_size {
                    if recorded_size.as_u64() != Some(actual_size) {
                        reasons.push(format!(
                            "{label}.size_bytes={recorded_size:?}, expected {actual_size}"
                        ));
                    }
                }
            }
        }
    }
}

fn resolve_artifact_path(summary_path: &Path, repo_root: &Path, raw_path: &str) -> Option<PathBuf> {
    let path = Path::new(raw_path);
    if path.is_absolute() {
        return Some(path.to_path_buf());
    }
    let parent = summary_path.parent()?;
    let candidates = [parent.join(path), repo_root.join(path)];
    candidates
        .iter()
        .find(|candidate| candidate.exists())
        .cloned()
        .or_else(|| Some(candidates[0].clone()))
}

fn check_chc_obligations(
    summary: &Value,
    summary_path: &Path,
    repo_root: &Path,
    verdict: Option<&str>,
    reasons: &mut Vec<String>,
) {
    let required_kinds: &[&str] = match verdict {
        Some("safe") => &["initiation", "consecution", "safety"],
        Some("unsafe") => &["trace-validity"],
        _ => &[],
    };
    let Some(obligations) = summary.get("obligations").and_then(Value::as_array) else {
        reasons.push("obligations is empty".to_string());
        return;
    };
    if obligations.is_empty() {
        reasons.push("obligations is empty".to_string());
        return;
    }
    let mut seen_kinds = Vec::new();
    for (index, obligation) in obligations.iter().enumerate() {
        let label = format!("obligations[{index}]");
        let Some(obligation) = obligation.as_object() else {
            reasons.push(format!("{label} is not an object"));
            continue;
        };
        if obligation
            .get("name")
            .and_then(Value::as_str)
            .is_none_or(str::is_empty)
        {
            reasons.push(format!("{label}.name is missing"));
        }
        match obligation.get("kind").and_then(Value::as_str) {
            Some(kind @ ("initiation" | "consecution" | "safety" | "trace-validity")) => {
                seen_kinds.push(kind.to_string());
            }
            other => reasons.push(format!("{label}.kind={other:?}")),
        }
        if obligation.get("checker_command").is_none_or(is_empty_value) {
            reasons.push(format!("{label}.checker_command is missing"));
        }
        match obligation.get("query") {
            Some(query) => check_artifact_sha256_row(
                query,
                summary_path,
                repo_root,
                &format!("{label}.query"),
                reasons,
            ),
            None => reasons.push(format!("{label}.query is missing")),
        }
        let result_label = format!("{label}.result");
        check_replay_result(obligation.get("result"), &result_label, reasons);
        if let Some(result) = obligation.get("result") {
            if result.get("status").and_then(Value::as_str) != Some("pass") {
                reasons.push(format!(
                    "{result_label}.status={:?}, expected 'pass'",
                    result.get("status")
                ));
            }
        }
    }
    let missing = required_kinds
        .iter()
        .copied()
        .filter(|kind| !seen_kinds.iter().any(|seen| seen == kind))
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        reasons.push(format!(
            "missing CHC replay obligation kinds: {}",
            missing.join(", ")
        ));
    }
}

fn check_downstream_summary(args: &ResolvedArgs, state: &mut GateState) {
    let Some(summary_path) = &args.downstream_summary else {
        let command = downstream_command("/tmp/ay-consumer-smoke.json");
        state.add_blocker(
            "downstream_smoke",
            "/tmp/ay-consumer-smoke.json",
            &command,
            "no consumer smoke JSON supplied; pass --downstream-summary /path/to/ay-consumer-smoke.json".to_string(),
        );
        return;
    };
    let summary_path_display = summary_path.display().to_string();
    let command = downstream_command(&summary_path_display);
    let resolved = resolve_repo_path(&args.repo_root, summary_path);
    match read_json(&resolved) {
        Ok(value) => {
            let reasons = validate_downstream_summary(&args.repo_root, &resolved, &value);
            if reasons.is_empty() {
                println!(
                    "[blocker-check] PASS downstream_smoke: consumer smoke JSON has no failures or skips"
                );
            } else {
                state.add_blocker(
                    "downstream_smoke",
                    &summary_path_display,
                    &command,
                    reasons.join("; "),
                );
            }
        }
        Err(error) => state.add_blocker("downstream_smoke", &summary_path_display, &command, error),
    }
}

const DOWNSTREAM_SMOKE_SCHEMA_PATH: &str =
    "crates/ay/schemas/downstream-smoke-evidence.schema.json";
const DOWNSTREAM_SMOKE_SCHEMA_ID: &str =
    "https://github.com/alabsystems/ay/blob/main/crates/ay/schemas/downstream-smoke-evidence.schema.json";

pub(crate) fn validate_downstream_summary(
    repo_root: &Path,
    summary_path: &Path,
    data: &Value,
) -> Vec<String> {
    let schema_reasons = validate_downstream_summary_schema(repo_root, data);
    if !schema_reasons.is_empty() {
        return schema_reasons;
    }

    let mut reasons = Vec::new();
    let required_consumers = downstream_inventory_consumers(repo_root, &mut reasons);

    if data.get("tool").and_then(Value::as_str) != Some("ay-consumer-smoke-check") {
        reasons.push(format!(
            "tool={:?}, expected 'ay-consumer-smoke-check'",
            data.get("tool")
        ));
    }

    validate_downstream_evidence(data, &mut reasons);
    let current_head = validate_downstream_ay(repo_root, data, &mut reasons);
    validate_downstream_run_shape(data, &mut reasons);
    validate_downstream_inventory(repo_root, data, &required_consumers, &mut reasons);
    validate_downstream_tools(data, &mut reasons);
    validate_downstream_consumers(
        repo_root,
        summary_path,
        data,
        &required_consumers,
        current_head.as_deref(),
        &mut reasons,
    );

    reasons
}

fn validate_downstream_summary_schema(repo_root: &Path, data: &Value) -> Vec<String> {
    let mut reasons = Vec::new();
    let schema_path = repo_root.join(DOWNSTREAM_SMOKE_SCHEMA_PATH);
    let schema = match read_json(&schema_path) {
        Ok(schema) => schema,
        Err(error) => {
            reasons.push(format!(
                "downstream smoke schema validation failed: cannot load {DOWNSTREAM_SMOKE_SCHEMA_PATH}: {error}"
            ));
            return reasons;
        }
    };
    if schema.get("$id").and_then(Value::as_str) != Some(DOWNSTREAM_SMOKE_SCHEMA_ID) {
        reasons.push(format!(
            "downstream smoke schema validation failed: {DOWNSTREAM_SMOKE_SCHEMA_PATH}.$id={:?}, expected {DOWNSTREAM_SMOKE_SCHEMA_ID:?}",
            schema.get("$id")
        ));
        return reasons;
    }

    let mut path = Vec::new();
    validate_required_downstream_schema_value(&schema, &schema, data, &mut path, &mut reasons);

    let Some(consumer_schema) = value_at(&schema, &["$defs", "consumerEvidence"]) else {
        reasons.push(format!(
            "downstream smoke schema validation failed: {DOWNSTREAM_SMOKE_SCHEMA_PATH} missing $defs.consumerEvidence"
        ));
        return reasons;
    };
    let Some(consumers) = data.get("consumers").and_then(Value::as_object) else {
        return reasons;
    };
    path.push("consumers".to_string());
    for (name, row) in consumers {
        path.push(name.clone());
        validate_required_downstream_schema_value(
            &schema,
            consumer_schema,
            row,
            &mut path,
            &mut reasons,
        );
        path.pop();
    }
    path.pop();

    reasons
}

fn validate_required_downstream_schema_value(
    schema_root: &Value,
    schema_node: &Value,
    data: &Value,
    path: &mut Vec<String>,
    reasons: &mut Vec<String>,
) {
    let Some(schema_node) = resolve_downstream_schema_ref(schema_root, schema_node, path, reasons)
    else {
        return;
    };
    if let Some(expected_type) = schema_node.get("type").and_then(Value::as_str) {
        if !downstream_schema_type_matches(expected_type, data) {
            reasons.push(format!(
                "downstream smoke schema validation failed: {} has type {}, expected {expected_type}",
                downstream_schema_path(path),
                downstream_json_type(data)
            ));
            return;
        }
    }
    if let Some(expected) = schema_node.get("const") {
        if data != expected {
            reasons.push(format!(
                "downstream smoke schema validation failed: {}={data:?}, expected const {expected:?}",
                downstream_schema_path(path)
            ));
        }
    }
    if let Some(allowed) = schema_node.get("enum").and_then(Value::as_array) {
        if !allowed.iter().any(|value| value == data) {
            reasons.push(format!(
                "downstream smoke schema validation failed: {}={data:?}, expected one of {allowed:?}",
                downstream_schema_path(path)
            ));
        }
    }
    if let Some(min_length) = schema_node.get("minLength").and_then(Value::as_u64) {
        if data
            .as_str()
            .is_some_and(|value| value.len() < min_length as usize)
        {
            reasons.push(format!(
                "downstream smoke schema validation failed: {} length is less than {min_length}",
                downstream_schema_path(path)
            ));
        }
    }
    if let Some(minimum) = schema_node.get("minimum").and_then(Value::as_i64) {
        if downstream_integer_less_than(data, minimum) {
            reasons.push(format!(
                "downstream smoke schema validation failed: {}={data:?} is less than {minimum}",
                downstream_schema_path(path)
            ));
        }
    }

    let Some(required_value) = schema_node.get("required") else {
        return;
    };
    let Some(required) = required_value.as_array() else {
        reasons.push(format!(
            "downstream smoke schema validation failed: {DOWNSTREAM_SMOKE_SCHEMA_PATH} {}.required is not an array",
            downstream_schema_path(path)
        ));
        return;
    };
    let Some(data_object) = data.as_object() else {
        reasons.push(format!(
            "downstream smoke schema validation failed: {} is not an object",
            downstream_schema_path(path)
        ));
        return;
    };
    let properties = schema_node.get("properties").and_then(Value::as_object);
    for required_key in required {
        let Some(required_key) = required_key.as_str() else {
            reasons.push(format!(
                "downstream smoke schema validation failed: {DOWNSTREAM_SMOKE_SCHEMA_PATH} {}.required contains a non-string entry",
                downstream_schema_path(path)
            ));
            continue;
        };
        let Some(child) = data_object.get(required_key) else {
            path.push(required_key.to_string());
            reasons.push(format!(
                "downstream smoke schema validation failed: {} is required by {DOWNSTREAM_SMOKE_SCHEMA_PATH}",
                downstream_schema_path(path)
            ));
            path.pop();
            continue;
        };
        if let Some(child_schema) = properties.and_then(|properties| properties.get(required_key)) {
            path.push(required_key.to_string());
            validate_required_downstream_schema_value(
                schema_root,
                child_schema,
                child,
                path,
                reasons,
            );
            path.pop();
        }
    }
}

fn resolve_downstream_schema_ref<'a>(
    schema_root: &'a Value,
    schema_node: &'a Value,
    path: &[String],
    reasons: &mut Vec<String>,
) -> Option<&'a Value> {
    let Some(reference) = schema_node.get("$ref").and_then(Value::as_str) else {
        return Some(schema_node);
    };
    if reference == "#/$defs/consumerEvidence" {
        return value_at(schema_root, &["$defs", "consumerEvidence"]);
    }
    reasons.push(format!(
        "downstream smoke schema validation failed: unsupported schema reference {reference:?} at {}",
        downstream_schema_path(path)
    ));
    None
}

fn downstream_schema_type_matches(expected_type: &str, value: &Value) -> bool {
    match expected_type {
        "object" => value.is_object(),
        "array" => value.is_array(),
        "string" => value.is_string(),
        "boolean" => value.is_boolean(),
        "integer" => value
            .as_number()
            .is_some_and(|number| number.is_i64() || number.is_u64()),
        "number" => value.is_number(),
        _ => false,
    }
}

fn downstream_integer_less_than(value: &Value, minimum: i64) -> bool {
    let Some(number) = value.as_number() else {
        return false;
    };
    if let Some(value) = number.as_i64() {
        value < minimum
    } else {
        number
            .as_u64()
            .is_some_and(|value| minimum > 0 && value < minimum as u64)
    }
}

fn downstream_json_type(value: &Value) -> &'static str {
    match value {
        Value::Null => "null",
        Value::Bool(_) => "boolean",
        Value::Number(number) if number.is_i64() || number.is_u64() => "integer",
        Value::Number(_) => "number",
        Value::String(_) => "string",
        Value::Array(_) => "array",
        Value::Object(_) => "object",
    }
}

fn downstream_schema_path(path: &[String]) -> String {
    if path.is_empty() {
        "<root>".to_string()
    } else {
        path.join(".")
    }
}

fn downstream_int_value(value: Option<&Value>) -> Option<i64> {
    value.and_then(|value| {
        value
            .as_i64()
            .or_else(|| value.as_u64().and_then(|item| i64::try_from(item).ok()))
    })
}

fn resolve_existing_artifact(repo_root: &Path, base_dir: &Path, raw_path: &str) -> Option<PathBuf> {
    if raw_path.is_empty() {
        return None;
    }
    let path = PathBuf::from(raw_path);
    let candidates = if path.is_absolute() {
        vec![path]
    } else {
        vec![base_dir.join(&path), repo_root.join(&path)]
    };
    candidates.into_iter().find(|candidate| candidate.exists())
}

#[derive(Clone)]
struct DownstreamInventoryConsumer {
    name: String,
    local_dir: String,
    smoke_script: String,
    tracking_state: String,
    note: String,
}

fn run_downstream_smoke_inventory_advisory(repo_root: &Path, state: &mut GateState) {
    println!("[advisory] START downstream_smoke_inventory");
    println!("source=the development design notes");
    let mut reasons = Vec::new();
    let rows = downstream_inventory_rows(repo_root, &mut reasons);
    if reasons.is_empty() {
        println!("consumer-smoke-check: smoke consumers from the development design notes");
        for row in rows {
            println!(
                "  {:<12} {} path={} script={} state={} note={}",
                row.name,
                downstream_inventory_path_status(&row.local_dir),
                downstream_inventory_display_path(&row.local_dir),
                row.smoke_script,
                row.tracking_state,
                row.note
            );
        }
        println!("[advisory] PASS  downstream_smoke_inventory");
    } else {
        eprintln!(
            "[advisory] FAIL  downstream_smoke_inventory {}",
            reasons.join("; ")
        );
        state.advisory_failures += 1;
    }
    println!();
}

fn downstream_inventory_path_status(raw_path: &str) -> &'static str {
    if downstream_inventory_resolved_path(raw_path).is_some_and(|path| path.exists()) {
        "PRESENT"
    } else {
        "MISSING"
    }
}

fn downstream_inventory_display_path(raw_path: &str) -> String {
    downstream_inventory_resolved_path(raw_path)
        .unwrap_or_else(|| PathBuf::from(raw_path))
        .display()
        .to_string()
}

fn downstream_inventory_resolved_path(raw_path: &str) -> Option<PathBuf> {
    if let Some(rest) = raw_path.strip_prefix("$HOME/") {
        return env::var_os("HOME").map(|home| PathBuf::from(home).join(rest));
    }
    if let Some(rest) = raw_path.strip_prefix("~/") {
        return env::var_os("HOME").map(|home| PathBuf::from(home).join(rest));
    }
    if raw_path.is_empty() || raw_path == "-" {
        return None;
    }
    Some(PathBuf::from(raw_path))
}

fn downstream_inventory_consumers(repo_root: &Path, reasons: &mut Vec<String>) -> Vec<String> {
    downstream_inventory_rows(repo_root, reasons)
        .into_iter()
        .map(|row| row.name)
        .collect()
}

fn downstream_inventory_rows(
    repo_root: &Path,
    reasons: &mut Vec<String>,
) -> Vec<DownstreamInventoryConsumer> {
    let inventory_path = repo_root.join("the development design notes");
    let Ok(text) = fs::read_to_string(&inventory_path) else {
        reasons.push("the development design notes is missing".to_string());
        return Vec::new();
    };
    text.lines()
        .filter_map(|raw| {
            let line = raw.trim();
            if line.is_empty() || line.starts_with('#') || line.starts_with("name\t") {
                return None;
            }
            let fields = raw.split('\t').collect::<Vec<_>>();
            let name = fields.first()?.trim();
            let local_dir = fields.get(1).map_or("", |field| field.trim());
            let smoke_script = fields.get(6)?.trim();
            if name.is_empty() || smoke_script.is_empty() || smoke_script == "-" {
                None
            } else {
                Some(DownstreamInventoryConsumer {
                    name: name.to_string(),
                    local_dir: local_dir.to_string(),
                    smoke_script: smoke_script.to_string(),
                    tracking_state: fields.get(7).map_or("", |field| field.trim()).to_string(),
                    note: fields.get(8).map_or("", |field| field.trim()).to_string(),
                })
            }
        })
        .collect()
}

/// Read a boolean evidence field, accepting a canonical key and falling back to
/// a legacy alias. New (post-rename) smoke artifacts emit the canonical key,
/// while pre-rename artifacts emit the legacy spelling; both must validate.
fn aliased_evidence_bool(
    evidence: &serde_json::Map<String, Value>,
    canonical: &str,
    legacy: &str,
) -> Option<bool> {
    evidence
        .get(canonical)
        .and_then(Value::as_bool)
        .or_else(|| evidence.get(legacy).and_then(Value::as_bool))
}

fn validate_downstream_evidence(data: &Value, reasons: &mut Vec<String>) {
    let Some(evidence) = data.get("evidence").and_then(Value::as_object) else {
        reasons.push("evidence is missing or not an object".to_string());
        return;
    };
    for key in [
        "launch_candidate",
        "inventory_complete",
        "summary_counts_match",
        "all_executed_logs_verified",
        "ay_head_stable",
        "ay_worktree_clean",
        "all_consumers_clean",
        "all_consumers_have_commit",
    ] {
        if evidence.get(key).and_then(Value::as_bool) != Some(true) {
            reasons.push(format!("evidence.{key} is not true"));
        }
    }
    // Accept canonical verification_consumer_deductive_checks_clean_origin_main, falling back to the
    // legacy quantifier_consumer_certificate_consumer_clean_origin_main alias for pre-rename artifacts.
    if aliased_evidence_bool(
        evidence,
        "verification_consumer_deductive_checks_clean_origin_main",
        "quantifier_consumer_certificate_consumer_clean_origin_main",
    ) != Some(true)
    {
        reasons.push(
            "evidence.verification_consumer_deductive_checks_clean_origin_main is not true \
             (legacy alias evidence.quantifier_consumer_certificate_consumer_clean_origin_main is not true)"
                .to_string(),
        );
    }
    if evidence.get("partial").and_then(Value::as_bool) != Some(false) {
        reasons.push("evidence.partial is not false".to_string());
    }
    // Require the canonical model_checker_consumer_first_failure_mode. The legacy
    // zani_first_failure_mode alias is no longer recognized.
    if evidence
        .get("model_checker_consumer_first_failure_mode")
        .and_then(Value::as_bool)
        != Some(false)
    {
        reasons.push("evidence.model_checker_consumer_first_failure_mode is not false".to_string());
    }
    if evidence.get("scope").and_then(Value::as_str) != Some("full_inventory") {
        reasons.push(format!(
            "evidence.scope={:?}, expected 'full_inventory'",
            evidence.get("scope")
        ));
    }
}

fn validate_downstream_ay(
    repo_root: &Path,
    data: &Value,
    reasons: &mut Vec<String>,
) -> Option<String> {
    let Some(ay) = data.get("ay").and_then(Value::as_object) else {
        reasons.push("ay is missing or not an object".to_string());
        return None;
    };
    let ay_commit = ay.get("commit").and_then(Value::as_str).unwrap_or("");
    if ay_commit.is_empty() {
        reasons.push("ay.commit is missing".to_string());
    } else if ay_commit.len() < 7 {
        reasons.push(format!(
            "ay.commit={ay_commit:?} is too short to identify the checked AY HEAD"
        ));
    }

    let current_head = current_head(repo_root);
    if let Some(head) = &current_head {
        let mut accepted_commits = BTreeSet::from([head.clone()]);
        if let Some(short) = git_output(repo_root, &["rev-parse", "--short", "HEAD"]) {
            accepted_commits.insert(short);
        }
        if !ay_commit.is_empty() && !accepted_commits.contains(ay_commit) {
            reasons.push(format!(
                "ay.commit={ay_commit:?} does not identify current HEAD={head}"
            ));
        }
        for key in ["commit_full", "commit_end", "commit_full_end"] {
            if ay.get(key).and_then(Value::as_str) != Some(head.as_str()) {
                reasons.push(format!(
                    "ay.{key}={:?} does not match current HEAD={head}",
                    ay.get(key)
                ));
            }
        }
    } else {
        for key in ["commit_full", "commit_end", "commit_full_end"] {
            if ay.get(key).and_then(Value::as_str).unwrap_or("").is_empty() {
                reasons.push(format!("ay.{key} is missing"));
            }
        }
    }
    for key in ["git_status_short", "git_status_short_end"] {
        if ay.get(key).and_then(Value::as_str) != Some("") {
            reasons.push(format!("ay.{key} is not clean"));
        }
    }
    current_head
}

fn validate_downstream_run_shape(data: &Value, reasons: &mut Vec<String>) {
    let overall = data.get("overall").unwrap_or(&Value::Null);
    if overall.get("status").and_then(Value::as_str) != Some("PASS") {
        reasons.push(format!("overall.status={:?}", overall.get("status")));
    }
    if overall.get("exit_code").and_then(Value::as_i64) != Some(0) {
        reasons.push(format!("overall.exit_code={:?}", overall.get("exit_code")));
    }
    if data.get("mode").and_then(Value::as_str) != Some("full") {
        reasons.push(format!("mode={:?}, expected 'full'", data.get("mode")));
    }
    if !matches!(data.get("selected_consumers").and_then(Value::as_array), Some(items) if items.is_empty())
    {
        reasons.push(format!(
            "selected_consumers={:?}, expected full inventory []",
            data.get("selected_consumers")
        ));
    }
    let unprocessed = data
        .get("unprocessed_consumers")
        .and_then(Value::as_array)
        .cloned()
        .unwrap_or_default();
    if !unprocessed.is_empty() {
        reasons.push(format!(
            "unprocessed_consumers={:?}, expected []",
            data.get("unprocessed_consumers")
        ));
    }
}

fn validate_downstream_inventory(
    repo_root: &Path,
    data: &Value,
    required_consumers: &[String],
    reasons: &mut Vec<String>,
) {
    let Some(inventory) = data.get("inventory").and_then(Value::as_object) else {
        reasons.push("inventory is missing or not an object".to_string());
        return;
    };
    let smoke_consumers = inventory
        .get("smoke_consumers")
        .and_then(Value::as_array)
        .map(|rows| {
            rows.iter()
                .filter_map(Value::as_str)
                .map(str::to_string)
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    if smoke_consumers != required_consumers {
        reasons.push(
            "inventory.smoke_consumers does not match the development design notes".to_string(),
        );
    }
    if inventory
        .get("smoke_consumer_count")
        .and_then(Value::as_u64)
        != Some(required_consumers.len() as u64)
    {
        reasons.push(format!(
            "inventory.smoke_consumer_count={:?}, expected {}",
            inventory.get("smoke_consumer_count"),
            required_consumers.len()
        ));
    }
    let Some(inventory_path_raw) = inventory.get("path").and_then(Value::as_str) else {
        reasons.push("inventory.path is missing".to_string());
        return;
    };
    let Some(inventory_path) = resolve_existing_artifact(repo_root, repo_root, inventory_path_raw)
    else {
        reasons.push(format!("inventory.path not found: {inventory_path_raw}"));
        return;
    };
    if inventory_path != repo_root.join("the development design notes") {
        reasons.push(format!(
            "inventory.path={inventory_path_raw:?}, expected the development design notes"
        ));
    }
    match inventory.get("sha256").and_then(Value::as_str) {
        Some(hash) if is_lower_sha256(hash) => {
            if let Ok(actual) = sha256_file_hex(&inventory_path) {
                if hash != actual {
                    reasons.push(
                        "inventory.sha256 does not match the development design notes".to_string(),
                    );
                }
            }
        }
        Some(_) => reasons.push("inventory.sha256 is not lowercase hex SHA-256".to_string()),
        None => reasons.push("inventory.sha256 is missing".to_string()),
    }
}

fn validate_downstream_tools(data: &Value, reasons: &mut Vec<String>) {
    let Some(tools) = data.get("tools").and_then(Value::as_object) else {
        reasons.push("tools is missing or not an object".to_string());
        return;
    };
    for tool in ["git", "cargo", "rustc", "z3"] {
        if tools
            .get(tool)
            .and_then(Value::as_str)
            .unwrap_or("")
            .is_empty()
        {
            reasons.push(format!("tools.{tool} is missing"));
        }
    }
}

fn validate_downstream_consumers(
    repo_root: &Path,
    summary_path: &Path,
    data: &Value,
    required_consumers: &[String],
    current_head: Option<&str>,
    reasons: &mut Vec<String>,
) {
    let summary = data.get("summary").unwrap_or(&Value::Null);
    if downstream_int_value(summary.get("failed")) != Some(0) {
        reasons.push(format!("summary.failed={:?}", summary.get("failed")));
    }
    if downstream_int_value(summary.get("skipped")) != Some(0) {
        reasons.push(format!("summary.skipped={:?}", summary.get("skipped")));
    }

    let Some(consumers) = data.get("consumers").and_then(Value::as_object) else {
        reasons.push("no consumers recorded".to_string());
        return;
    };
    if consumers.is_empty() {
        reasons.push("no consumers recorded".to_string());
    }

    let missing_inventory_consumers = required_consumers
        .iter()
        .filter(|name| !consumers.contains_key(name.as_str()))
        .cloned()
        .collect::<Vec<_>>();
    if !missing_inventory_consumers.is_empty() {
        reasons.push(format!(
            "inventory smoke consumer evidence is missing: {}",
            missing_inventory_consumers.join(", ")
        ));
    }

    let mut status_counts = BTreeMap::from([("PASS", 0_u64), ("FAIL", 0), ("SKIP", 0)]);
    for row in consumers.values() {
        if let Some(status) = row.get("status").and_then(Value::as_str) {
            if let Some(count) = status_counts.get_mut(status) {
                *count += 1;
            }
        }
    }
    for (summary_key, status) in [("passed", "PASS"), ("failed", "FAIL"), ("skipped", "SKIP")] {
        if summary.get(summary_key).and_then(Value::as_u64) != status_counts.get(status).copied() {
            reasons.push(format!(
                "summary.{summary_key}={:?}, expected {} {status} rows",
                summary.get(summary_key),
                status_counts.get(status).copied().unwrap_or_default()
            ));
        }
    }

    // Trust: rebrand quantifier_consumer->verification-consumer, certificate_consumer->deductive-checks. Back-compat: accept
    // EITHER the canonical new name OR the legacy alias so older evidence keeps
    // validating; only flag a consumer missing when neither name is present.
    for (canonical, alias) in [
        ("verification-consumer", "quantifier_consumer"),
        ("deductive-checks", "certificate_consumer"),
    ] {
        if !consumers.contains_key(canonical) && !consumers.contains_key(alias) {
            reasons.push(format!("{canonical} consumer evidence is missing"));
        }
    }

    for (name, row) in consumers {
        let Some(row) = row.as_object() else {
            reasons.push(format!("{name} consumer evidence is not an object"));
            continue;
        };
        if row.get("status").and_then(Value::as_str) != Some("PASS") {
            reasons.push(format!("{name}.status={:?}", row.get("status")));
        }
        if row
            .get("commit")
            .and_then(Value::as_str)
            .unwrap_or("")
            .is_empty()
        {
            reasons.push(format!("{name}.commit is missing"));
        }
        if !matches!(
            row.get("git_status").and_then(Value::as_str),
            Some("clean" | "")
        ) {
            reasons.push(format!("{name}.git_status={:?}", row.get("git_status")));
        }
        if row.get("status").and_then(Value::as_str) == Some("PASS") {
            validate_downstream_pass_row_refs(name, row, current_head, reasons);
            validate_downstream_pass_row_log(repo_root, summary_path, name, row, reasons);
        }
        // Trust: rebrand quantifier_consumer->verification-consumer, certificate_consumer->deductive-checks. Back-compat:
        // match EITHER the new canonical name OR the legacy alias.
        if matches!(
            name.as_str(),
            "verification-consumer"
                | "quantifier_consumer"
                | "deductive-checks"
                | "certificate_consumer"
        ) {
            if row.get("temp_worktree").and_then(Value::as_bool) != Some(true) {
                reasons.push(format!("{name}.temp_worktree is not true"));
            }
            if row.get("worktree_ref").and_then(Value::as_str) != Some("origin/main") {
                reasons.push(format!("{name}.worktree_ref={:?}", row.get("worktree_ref")));
            }
        }
    }
}

fn validate_downstream_pass_row_refs(
    name: &str,
    row: &serde_json::Map<String, Value>,
    current_head: Option<&str>,
    reasons: &mut Vec<String>,
) {
    for key in ["ay_commit_full_before", "ay_commit_full_after"] {
        let value = row.get(key).and_then(Value::as_str).unwrap_or("");
        if let Some(head) = current_head {
            if value != head {
                reasons.push(format!(
                    "{name}.{key}={value:?} does not match current HEAD={head}"
                ));
            }
        } else if value.is_empty() {
            reasons.push(format!("{name}.{key} is missing"));
        }
    }
    for key in ["ay_worktree_status_before", "ay_worktree_status_after"] {
        if row.get(key).and_then(Value::as_str) != Some("clean") {
            reasons.push(format!("{name}.{key}={:?}, expected 'clean'", row.get(key)));
        }
    }
    for key in ["ay_git_status_short_before", "ay_git_status_short_after"] {
        if row.get(key).and_then(Value::as_str) != Some("") {
            reasons.push(format!("{name}.{key} is not clean"));
        }
    }
}

fn validate_downstream_pass_row_log(
    repo_root: &Path,
    summary_path: &Path,
    name: &str,
    row: &serde_json::Map<String, Value>,
    reasons: &mut Vec<String>,
) {
    let command = row.get("command").and_then(Value::as_str).unwrap_or("");
    if command.is_empty() {
        reasons.push(format!("{name}.command is missing"));
    }
    let log_path_raw = row.get("log_path").and_then(Value::as_str).unwrap_or("");
    let log_path = if log_path_raw.is_empty() {
        reasons.push(format!("{name}.log_path is missing"));
        None
    } else {
        match resolve_existing_artifact(
            repo_root,
            summary_path.parent().unwrap_or(repo_root),
            log_path_raw,
        ) {
            Some(path) => Some(path),
            None => {
                reasons.push(format!("{name}.log_path not found: {log_path_raw}"));
                None
            }
        }
    };
    let log_sha256 = row.get("log_sha256").and_then(Value::as_str).unwrap_or("");
    if log_sha256.is_empty() {
        reasons.push(format!("{name}.log_sha256 is missing"));
    } else if !is_lower_sha256(log_sha256) {
        reasons.push(format!("{name}.log_sha256 is not lowercase hex SHA-256"));
    } else if let Some(log_path) = &log_path {
        match sha256_file_hex(log_path) {
            Ok(actual) if actual != log_sha256 => {
                reasons.push(format!("{name}.log_sha256 does not match log_path"));
            }
            Err(error) => reasons.push(format!("{name}.log_path unreadable: {error}")),
            _ => {}
        }
    }
    if !command.is_empty() {
        if let Some(log_path) = &log_path {
            if let Ok(text) = fs::read_to_string(log_path) {
                let mut lines = text.lines();
                match (lines.next(), lines.next()) {
                    (Some(consumer), Some(log_command)) => {
                        if consumer != format!("consumer={name}") {
                            reasons.push(format!("{name}.log consumer header does not match row"));
                        }
                        if log_command != format!("command={command}") {
                            reasons.push(format!("{name}.log command header does not match row"));
                        }
                    }
                    _ => reasons.push(format!(
                        "{name}.log_path is missing consumer/command header"
                    )),
                }
            }
        }
    }
}

fn check_public_mirror(args: &ResolvedArgs, state: &mut GateState) -> Result<()> {
    let blocker_evidence = args
        .public_mirror_evidence
        .clone()
        .unwrap_or_else(|| PathBuf::from("public_ay_commit.json"));
    let command = public_mirror_command(&blocker_evidence);
    let Some(head) = current_head(&args.repo_root).filter(|head| !head.is_empty()) else {
        state.add_blocker(
            "public_mirror",
            &blocker_evidence.display().to_string(),
            "git rev-parse HEAD",
            "cannot resolve current private HEAD".to_string(),
        );
        return Ok(());
    };
    if !args.check_public_mirror {
        state.add_blocker(
            "public_mirror",
            &blocker_evidence.display().to_string(),
            &command,
            "network check not enabled; rerun with --check-public-mirror".to_string(),
        );
        return Ok(());
    }

    let (resolved, remove_after_check) = match &args.public_mirror_evidence {
        Some(evidence) => {
            let resolved = resolve_repo_path(&args.repo_root, evidence);
            if let Some(parent) = resolved.parent() {
                fs::create_dir_all(parent).with_context(|| {
                    format!("create public mirror evidence dir {}", parent.display())
                })?;
            }
            (resolved, false)
        }
        None => {
            let path = temporary_public_mirror_evidence_path();
            if let Some(parent) = path.parent() {
                fs::create_dir_all(parent).with_context(|| {
                    format!("create public mirror evidence dir {}", parent.display())
                })?;
            }
            (path, true)
        }
    };
    println!("[evidence] START public_ay_commit_fetch");
    quote_command(&["git", "fetch", "--depth", "1", PUBLIC_AY_URL, &head]);
    let (code, evidence) = verify_public_mirror_commit(&head)?;
    let mut evidence_bytes = serde_json::to_vec_pretty(&evidence)?;
    evidence_bytes.push(b'\n');
    fs::write(&resolved, &evidence_bytes)
        .with_context(|| format!("write public mirror evidence {}", resolved.display()))?;
    io::stdout().write_all(&evidence_bytes)?;
    if code == 0 {
        println!("[evidence] PASS  public_ay_commit_fetch");
    } else {
        eprintln!("[evidence] FAIL  public_ay_commit_fetch exit={code}");
        state.evidence_gate_failures += 1;
        let detail = public_mirror_failure_detail(&resolved, &head);
        state.add_blocker(
            "public_mirror",
            &blocker_evidence.display().to_string(),
            &command,
            detail,
        );
    }
    if remove_after_check {
        fs::remove_file(&resolved).ok();
    }
    println!();
    Ok(())
}

const PUBLIC_AY_URL: &str = "https://github.com/alabsystems/ay.git";
const PUBLIC_AY_REF: &str = "refs/heads/main";
const PUBLIC_COMMIT_EVIDENCE_SCHEMA: &str = "ay-public-commit-evidence/v1";

fn public_mirror_command(evidence_path: &Path) -> String {
    format!(
        "./target/release/ay launch-gate --check-public-mirror --public-mirror-evidence {}",
        evidence_path.display()
    )
}

fn verify_public_mirror_commit(commit: &str) -> Result<(i32, Value)> {
    let mut evidence = public_mirror_base_evidence(commit);
    if !full_commit_hex(commit) {
        evidence["failure_kind"] = json!("invalid-commit");
        evidence["error"] = json!("commit must be a full 40-hex object id");
        return Ok((2, evidence));
    }
    if !command_available("git") {
        evidence["failure_kind"] = json!("missing-git");
        evidence["error"] = json!("git is required for public commit verification");
        return Ok((1, evidence));
    }

    let workdir = temporary_public_mirror_workdir()?;
    let cleanup = TempDirCleanup::new(workdir.clone());
    let init = run_public_git(["init", "-q"], &workdir)?;
    if !init.status.success() {
        evidence["failure_kind"] = json!("git-init-failed");
        evidence["error"] = json!(process_detail(&init));
        return Ok((1, evidence));
    }

    let fetch_args = ["fetch", "--depth", "1", PUBLIC_AY_URL, commit];
    let fetch = run_public_git(fetch_args, &workdir)?;
    evidence["fetch_command"] = json!(["git", "fetch", "--depth", "1", PUBLIC_AY_URL, commit]);
    evidence["fetch_exit"] = json!(fetch.status.code().unwrap_or(1));
    if !fetch.status.success() {
        let ls_remote = record_public_ref_check(&mut evidence, &workdir, commit)?;
        evidence["failure_kind"] = json!("public-object-not-fetchable");
        evidence["error"] = json!(process_detail(&fetch));
        let ref_commit = evidence.get("ref_commit").and_then(Value::as_str);
        evidence["mirror_action"] =
            public_mirror_action(commit, "public-object-not-fetchable", ref_commit);
        if !ls_remote.status.success() {
            evidence["ref_error"] = json!(process_detail(&ls_remote));
        }
        drop(cleanup);
        return Ok((1, evidence));
    }

    let rev_parse = run_public_git(["rev-parse", "FETCH_HEAD"], &workdir)?;
    evidence["rev_parse_exit"] = json!(rev_parse.status.code().unwrap_or(1));
    if !rev_parse.status.success() {
        evidence["failure_kind"] = json!("fetch-head-unreadable");
        evidence["error"] = json!(process_detail(&rev_parse));
        return Ok((1, evidence));
    }
    let fetched_commit = String::from_utf8_lossy(&rev_parse.stdout)
        .trim()
        .to_string();
    evidence["fetched_commit"] = json!(fetched_commit);
    if !fetched_commit.eq_ignore_ascii_case(commit) {
        evidence["failure_kind"] = json!("fetched-commit-mismatch");
        evidence["error"] = json!(format!(
            "FETCH_HEAD resolved to {fetched_commit}, expected {commit}"
        ));
        return Ok((1, evidence));
    }
    evidence["fetchable"] = json!(true);

    let ls_remote = record_public_ref_check(&mut evidence, &workdir, commit)?;
    if !ls_remote.status.success() {
        evidence["failure_kind"] = json!("public-ref-not-advertised");
        evidence["error"] = json!(process_detail(&ls_remote));
        evidence["mirror_action"] = public_mirror_action(commit, "public-ref-not-advertised", None);
        return Ok((1, evidence));
    }
    let ref_commit = evidence
        .get("ref_commit")
        .and_then(Value::as_str)
        .map(str::to_string);
    let Some(ref_commit) = ref_commit else {
        evidence["failure_kind"] = json!("public-ref-not-advertised");
        evidence["error"] = json!(format!(
            "public ref {PUBLIC_AY_REF} not found in ls-remote output"
        ));
        evidence["mirror_action"] = public_mirror_action(commit, "public-ref-not-advertised", None);
        return Ok((1, evidence));
    };
    if !ref_commit.eq_ignore_ascii_case(commit) {
        evidence["failure_kind"] = json!("public-ref-mismatch");
        evidence["error"] = json!(format!(
            "public ref {PUBLIC_AY_REF} resolves to {ref_commit}, expected {commit}"
        ));
        evidence["mirror_action"] =
            public_mirror_action(commit, "public-ref-mismatch", Some(&ref_commit));
        return Ok((1, evidence));
    }

    evidence["status"] = json!("pass");
    evidence["failure_kind"] = Value::Null;
    evidence["ref_matches_commit"] = json!(true);
    Ok((0, evidence))
}

fn public_mirror_base_evidence(commit: &str) -> Value {
    json!({
        "schema": PUBLIC_COMMIT_EVIDENCE_SCHEMA,
        "status": "fail",
        "commit": commit,
        "expected_commit": commit,
        "fetchable": false,
        "failure_kind": Value::Null,
        "git_env": public_git_env_evidence(),
        "public_ref": PUBLIC_AY_REF,
        "ref_checked": false,
        "ref_matches_commit": false,
        "url": PUBLIC_AY_URL,
    })
}

fn public_git_env_evidence() -> Value {
    json!({
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_TERMINAL_PROMPT": "0",
    })
}

fn run_public_git<const N: usize>(args: [&str; N], cwd: &Path) -> Result<Output> {
    ProcessCommand::new("git")
        .args(args)
        .current_dir(cwd)
        .env("GIT_CONFIG_GLOBAL", "/dev/null")
        .env("GIT_CONFIG_NOSYSTEM", "1")
        .env("GIT_TERMINAL_PROMPT", "0")
        .output()
        .context("run native public mirror git check")
}

fn record_public_ref_check(evidence: &mut Value, workdir: &Path, commit: &str) -> Result<Output> {
    let output = run_public_git(
        ["ls-remote", "--exit-code", PUBLIC_AY_URL, PUBLIC_AY_REF],
        workdir,
    )?;
    evidence["ls_remote_command"] = json!([
        "git",
        "ls-remote",
        "--exit-code",
        PUBLIC_AY_URL,
        PUBLIC_AY_REF
    ]);
    evidence["ls_remote_exit"] = json!(output.status.code().unwrap_or(1));
    evidence["ref_checked"] = json!(true);
    if output.status.success() {
        if let Some(ref_commit) =
            parse_ls_remote_commit(&String::from_utf8_lossy(&output.stdout), PUBLIC_AY_REF)
        {
            evidence["ref_commit"] = json!(ref_commit);
            evidence["ref_matches_commit"] = json!(ref_commit.eq_ignore_ascii_case(commit));
        }
    }
    Ok(output)
}

fn public_mirror_action(commit: &str, failure_kind: &str, ref_commit: Option<&str>) -> Value {
    let publish_refspec = format!("{commit}:{PUBLIC_AY_REF}");
    let handoff_shell_command = "./target/release/ay launch-gate --check-public-mirror --public-mirror-evidence ay-public-commit-evidence.json".to_string();
    let summary = match failure_kind {
        "public-object-not-fetchable" => {
            "Publish the exact private commit object to the public ay remote and make the public launch ref resolve to it."
        }
        "public-ref-mismatch" => {
            "The commit object is public, but the public launch ref points at a different commit."
        }
        "public-ref-not-advertised" => {
            "Create or advertise the public launch ref at the required commit."
        }
        _ => "Resolve the public mirror verification failure.",
    };
    let mut action = json!({
        "failure_kind": failure_kind,
        "summary": summary,
        "example_publish_command": ["git", "push", PUBLIC_AY_URL, publish_refspec],
        "handoff_shell_command": handoff_shell_command,
        "verify_command": [
            "./target/release/ay",
            "launch-gate",
            "--check-public-mirror",
            "--public-mirror-evidence",
            "ay-public-commit-evidence.json"
        ],
        "publish_permission": {
            "checked": false,
            "required": true,
            "required_access": "write",
            "required_actor": format!("maintainer with write access to {PUBLIC_AY_URL}"),
            "required_url": PUBLIC_AY_URL,
            "status": "not-checked",
        },
        "required_actor": format!("maintainer with write access to {PUBLIC_AY_URL}"),
        "required_commit": commit,
        "required_ref": PUBLIC_AY_REF,
        "required_url": PUBLIC_AY_URL,
    });
    if let Some(ref_commit) = ref_commit {
        action["current_ref_commit"] = json!(ref_commit);
    }
    action
}

fn parse_ls_remote_commit(output: &str, public_ref: &str) -> Option<String> {
    let peeled_ref = format!("{public_ref}^{{}}");
    let mut direct_match = None;
    for line in output.lines() {
        let mut parts = line.split_whitespace();
        let Some(commit) = parts.next() else {
            continue;
        };
        let Some(reference) = parts.next() else {
            continue;
        };
        if reference == peeled_ref {
            return Some(commit.to_string());
        }
        if reference == public_ref {
            direct_match = Some(commit.to_string());
        }
    }
    direct_match
}

fn process_detail(output: &Output) -> String {
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let detail = if stderr.trim().is_empty() {
        stdout.trim()
    } else {
        stderr.trim()
    };
    if detail.is_empty() {
        format!("git exited {}", output.status.code().unwrap_or(1))
    } else {
        detail.to_string()
    }
}

fn full_commit_hex(commit: &str) -> bool {
    commit.len() == 40 && commit.bytes().all(|byte| byte.is_ascii_hexdigit())
}

fn command_available(command: &str) -> bool {
    ProcessCommand::new(command)
        .arg("--version")
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok()
}

fn temporary_public_mirror_workdir() -> Result<PathBuf> {
    let mut path = env::temp_dir();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    path.push(format!(
        "ay-public-commit-work.{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&path).with_context(|| {
        format!(
            "create temporary public mirror work directory {}",
            path.display()
        )
    })?;
    Ok(path)
}

struct TempDirCleanup {
    path: PathBuf,
}

impl TempDirCleanup {
    fn new(path: PathBuf) -> Self {
        Self { path }
    }
}

impl Drop for TempDirCleanup {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn temporary_public_mirror_evidence_path() -> PathBuf {
    let mut path = env::temp_dir();
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    path.push(format!("ay-public-commit.{nanos}.json"));
    path
}

fn public_mirror_failure_detail(output_path: &Path, head: &str) -> String {
    let fallback = format!("current HEAD {head} is not fetchable from the public mirror");
    let Ok(evidence) = read_json(output_path) else {
        return fallback;
    };
    let mut parts = vec![fallback];
    if let Some(failure_kind) = evidence.get("failure_kind").and_then(Value::as_str) {
        if !failure_kind.is_empty() {
            parts.push(format!("failure_kind={failure_kind}"));
        }
    }
    if let Some(error) = evidence.get("error").and_then(Value::as_str) {
        if !error.is_empty() {
            parts.push(format!("error={error}"));
        }
    }
    if let Some(action) = evidence.get("mirror_action").and_then(Value::as_object) {
        if let Some(summary) = action.get("summary").and_then(Value::as_str) {
            if !summary.is_empty() {
                parts.push(format!("mirror_action={summary}"));
            }
        }
        if let Some(publish) = string_array(action.get("example_publish_command")) {
            parts.push(format!("publish_command={}", shell_join(&publish)));
        }
        if let Some(handoff) = action.get("handoff_shell_command").and_then(Value::as_str) {
            if !handoff.is_empty() {
                parts.push(format!("handoff_command={handoff}"));
            }
        }
        if let Some(verify) = string_array(action.get("verify_command")) {
            parts.push(format!("verify_command={}", shell_join(&verify)));
        }
        if let Some(permission) = action.get("publish_permission").and_then(Value::as_object) {
            let access = permission
                .get("required_access")
                .and_then(Value::as_str)
                .filter(|value| !value.is_empty())
                .unwrap_or("<unknown>");
            let status = permission
                .get("status")
                .and_then(Value::as_str)
                .filter(|value| !value.is_empty())
                .unwrap_or("<unknown>");
            if access != "<unknown>" || status != "<unknown>" {
                parts.push(format!("publish_permission={access}/{status}"));
            }
        }
    }
    parts
        .into_iter()
        .map(|part| part.replace(['\t', '\n'], " "))
        .collect::<Vec<_>>()
        .join("; ")
}

fn string_array(value: Option<&Value>) -> Option<Vec<String>> {
    value.and_then(Value::as_array).and_then(|items| {
        items
            .iter()
            .map(|item| item.as_str().map(str::to_string))
            .collect::<Option<Vec<_>>>()
    })
}

fn shell_join(items: &[String]) -> String {
    items
        .iter()
        .map(|item| {
            if !item.is_empty()
                && item
                    .bytes()
                    .all(|byte| byte.is_ascii_alphanumeric() || b"@%_+=:,./-".contains(&byte))
            {
                item.clone()
            } else {
                format!("'{}'", item.replace('\'', "'\"'\"'"))
            }
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn check_release_manifest(args: &ResolvedArgs, state: &mut GateState) {
    let evidence = args
        .release_manifest
        .clone()
        .unwrap_or_else(|| PathBuf::from("release-manifest.json"));
    let command = release_manifest_command(&evidence.display().to_string());
    let Some(manifest_path) = &args.release_manifest else {
        state.add_blocker(
            "release_manifest",
            "release-manifest.json",
            &command,
            "no release manifest supplied; pass --release-manifest release-manifest.json"
                .to_string(),
        );
        return;
    };
    let resolved = resolve_repo_path(&args.repo_root, manifest_path);
    if !resolved.is_file() {
        state.add_blocker(
            "release_manifest",
            &manifest_path.display().to_string(),
            &command,
            format!("release manifest not found: {}", manifest_path.display()),
        );
        return;
    }
    match read_json(&resolved) {
        Ok(value) => {
            let reasons = release_manifest_reasons(&value, &args.repo_root);
            if reasons.is_empty() {
                println!(
                    "[blocker-check] PASS release_manifest: supplied release manifest is current"
                );
            } else {
                state.add_blocker(
                    "release_manifest",
                    &manifest_path.display().to_string(),
                    &command,
                    reasons.join("; "),
                );
            }
        }
        Err(error) => state.add_blocker(
            "release_manifest",
            &manifest_path.display().to_string(),
            &command,
            error,
        ),
    }
}

fn release_manifest_reasons(manifest: &Value, repo_root: &Path) -> Vec<String> {
    let mut reasons = Vec::new();
    expect_string(manifest, "schema", "ay-release-manifest/v1", &mut reasons);
    expect_string(manifest, "status", "pass", &mut reasons);
    expect_string(manifest, "channel", "public", &mut reasons);

    let private = value_at(manifest, &["private"]);
    let manifest_commit = value_at(manifest, &["private", "ay_commit"]).and_then(Value::as_str);
    if private.is_none() {
        reasons.push("private is missing".to_string());
    }
    if let Some(head) = current_head(repo_root) {
        if manifest_commit != Some(head.as_str()) {
            reasons.push(format!(
                "private.ay_commit={manifest_commit:?} does not match current HEAD={head}"
            ));
        }
    } else if manifest_commit.is_none_or(str::is_empty) {
        reasons.push("private.ay_commit is missing".to_string());
    }

    let public = value_at(manifest, &["public"]);
    if public.is_none() {
        reasons.push("public is missing".to_string());
    }
    let public_commit = value_at(manifest, &["public", "ay_commit"]).and_then(Value::as_str);
    if value_at(manifest, &["public", "commit_synced"]).and_then(Value::as_bool) != Some(true) {
        reasons.push("public.commit_synced is not true".to_string());
    }
    if value_at(manifest, &["public", "mirror_handoff_status"]).and_then(Value::as_str)
        != Some("synced")
    {
        reasons.push(format!(
            "public.mirror_handoff_status={:?}, expected 'synced'",
            value_at(manifest, &["public", "mirror_handoff_status"])
        ));
    }
    if public_commit != manifest_commit {
        reasons.push(format!(
            "public.ay_commit={public_commit:?} does not match private.ay_commit={manifest_commit:?}"
        ));
    }
    check_public_release_evidence(manifest, manifest_commit, &mut reasons);

    let release = value_at(manifest, &["release"]);
    if release.is_none() {
        reasons.push("release is missing".to_string());
    }
    if value_at(manifest, &["release", "channel"]).and_then(Value::as_str) != Some("public") {
        reasons.push(format!(
            "release.channel={:?}, expected 'public'",
            value_at(manifest, &["release", "channel"])
        ));
    }
    if value_at(manifest, &["release", "public_release_ready"]).and_then(Value::as_bool)
        != Some(true)
    {
        reasons.push("release.public_release_ready is not true".to_string());
    }
    if value_at(manifest, &["release", "public_mirror_synced"]).and_then(Value::as_bool)
        != Some(true)
    {
        reasons.push("release.public_mirror_synced is not true".to_string());
    }
    if value_at(manifest, &["release", "public_mirror_handoff_status"]).and_then(Value::as_str)
        != Some("synced")
    {
        reasons.push(format!(
            "release.public_mirror_handoff_status={:?}, expected 'synced'",
            value_at(manifest, &["release", "public_mirror_handoff_status"])
        ));
    }
    if value_at(manifest, &["release", "public_mirror_commit"]).and_then(Value::as_str)
        != manifest_commit
    {
        reasons.push(format!(
            "release.public_mirror_commit={:?} does not match private.ay_commit={manifest_commit:?}",
            value_at(manifest, &["release", "public_mirror_commit"])
        ));
    }
    check_blocked_handoff(manifest, &mut reasons);

    if value_at(manifest, &["dependencies", "status"]).and_then(Value::as_str) != Some("pass") {
        reasons.push(format!(
            "dependencies.status={:?}, expected 'pass'",
            value_at(manifest, &["dependencies", "status"])
        ));
    }
    if value_at(manifest, &["dependencies", "pins"]).is_none_or(is_empty_value) {
        reasons.push("dependencies.pins is empty".to_string());
    }

    if value_at(manifest, &["build", "binary_version_output"]).is_none_or(is_empty_value) {
        reasons.push("build.binary_version_output is missing".to_string());
    }
    if value_at(manifest, &["build", "command"]).is_none_or(is_empty_value) {
        reasons.push("build.command is missing".to_string());
    }
    if value_at(manifest, &["build", "artifact_path"]).is_none_or(is_empty_value) {
        reasons.push("build.artifact_path is missing".to_string());
    }

    check_launch_gates(manifest, &mut reasons);
    check_launch_gate_summaries(manifest, &mut reasons);
    check_checks_object(manifest, &mut reasons);
    check_errors_empty(manifest, "manifest", &mut reasons);

    reasons
}

fn check_public_release_evidence(
    manifest: &Value,
    manifest_commit: Option<&str>,
    reasons: &mut Vec<String>,
) {
    let Some(public_evidence) = value_at(manifest, &["public", "evidence"]) else {
        reasons.push("public.evidence is missing".to_string());
        return;
    };
    if !public_evidence.is_object() {
        reasons.push("public.evidence is missing".to_string());
        return;
    }
    expect_string(
        public_evidence,
        "schema",
        "ay-public-commit-evidence/v1",
        reasons,
    );
    expect_string(public_evidence, "status", "pass", reasons);
    if value_at(public_evidence, &["failure_kind"])
        .and_then(Value::as_str)
        .is_some_and(|value| !value.is_empty())
    {
        reasons.push(format!(
            "public.evidence.failure_kind={:?}, expected None",
            value_at(public_evidence, &["failure_kind"])
        ));
    }
    if value_at(public_evidence, &["fetchable"]).and_then(Value::as_bool) != Some(true) {
        reasons.push("public.evidence.fetchable is not true".to_string());
    }
    if value_at(public_evidence, &["ref_matches_commit"]).and_then(Value::as_bool) != Some(true) {
        reasons.push("public.evidence.ref_matches_commit is not true".to_string());
    }
    for key in ["commit", "expected_commit", "fetched_commit", "ref_commit"] {
        let actual = public_evidence.get(key).and_then(Value::as_str);
        if actual != manifest_commit {
            reasons.push(format!(
                "public.evidence.{key}={actual:?} does not match private.ay_commit={manifest_commit:?}"
            ));
        }
    }

    let public_url = public_evidence.get("url").and_then(Value::as_str);
    let public_ref = public_evidence.get("public_ref").and_then(Value::as_str);
    if public_url.is_none_or(str::is_empty) {
        reasons.push("public.evidence.url is missing".to_string());
    } else if value_at(manifest, &["public", "ay_url"]).and_then(Value::as_str) != public_url {
        reasons.push(format!(
            "public.ay_url={:?} does not match public.evidence.url={public_url:?}",
            value_at(manifest, &["public", "ay_url"])
        ));
    }
    if public_ref.is_none_or(str::is_empty) {
        reasons.push("public.evidence.public_ref is missing".to_string());
    } else if value_at(manifest, &["public", "ay_ref"]).and_then(Value::as_str) != public_ref {
        reasons.push(format!(
            "public.ay_ref={:?} does not match public.evidence.public_ref={public_ref:?}",
            value_at(manifest, &["public", "ay_ref"])
        ));
    }

    let expected_git_env = json!({
        "GIT_CONFIG_GLOBAL": "/dev/null",
        "GIT_CONFIG_NOSYSTEM": "1",
        "GIT_TERMINAL_PROMPT": "0",
    });
    if public_evidence.get("git_env") != Some(&expected_git_env) {
        reasons.push(
            "public.evidence.git_env does not match sanitized verifier environment".to_string(),
        );
    }

    if let (Some(public_url), Some(manifest_commit)) = (public_url, manifest_commit) {
        if !public_url.is_empty() && !manifest_commit.is_empty() {
            let expected_fetch =
                json!(["git", "fetch", "--depth", "1", public_url, manifest_commit]);
            if public_evidence.get("fetch_command") != Some(&expected_fetch) {
                reasons.push(
                    "public.evidence.fetch_command does not fetch the private commit from the public URL"
                        .to_string(),
                );
            }
        }
    }
    if let (Some(public_url), Some(public_ref)) = (public_url, public_ref) {
        if !public_url.is_empty() && !public_ref.is_empty() {
            let mut expected_refs = vec![Value::String(public_ref.to_string())];
            if public_ref.starts_with("refs/tags/") {
                expected_refs.push(Value::String(format!("{public_ref}^{{}}")));
            }
            let mut expected_ls_remote = vec![
                Value::String("git".to_string()),
                Value::String("ls-remote".to_string()),
                Value::String("--exit-code".to_string()),
                Value::String(public_url.to_string()),
            ];
            expected_ls_remote.extend(expected_refs);
            if public_evidence.get("ls_remote_command") != Some(&Value::Array(expected_ls_remote)) {
                reasons.push(
                    "public.evidence.ls_remote_command does not check the public launch ref"
                        .to_string(),
                );
            }
        }
    }

    check_publish_attempt(
        public_evidence,
        public_url,
        public_ref,
        manifest_commit,
        reasons,
    );
}

fn check_publish_attempt(
    public_evidence: &Value,
    public_url: Option<&str>,
    public_ref: Option<&str>,
    manifest_commit: Option<&str>,
    reasons: &mut Vec<String>,
) {
    let Some(publish_attempt) = public_evidence.get("publish_attempt") else {
        return;
    };
    if publish_attempt.is_null() {
        return;
    }
    let Some(publish_attempt) = publish_attempt.as_object() else {
        reasons.push("public.evidence.publish_attempt must be an object when present".to_string());
        return;
    };
    if let (Some(public_url), Some(public_ref), Some(manifest_commit)) =
        (public_url, public_ref, manifest_commit)
    {
        if !public_url.is_empty() && !public_ref.is_empty() && !manifest_commit.is_empty() {
            let expected_publish = json!([
                "git",
                "push",
                public_url,
                format!("{manifest_commit}:{public_ref}")
            ]);
            if publish_attempt.get("command") != Some(&expected_publish) {
                reasons.push(
                    "public.evidence.publish_attempt.command does not publish the private commit to the public ref"
                        .to_string(),
                );
            }
        }
    }
    let status = publish_attempt.get("status").and_then(Value::as_str);
    if !matches!(status, Some("pass" | "fail" | "skipped")) {
        reasons.push(format!(
            "public.evidence.publish_attempt.status={status:?}, expected pass, fail, or skipped"
        ));
    }
    if status == Some("pass") {
        if publish_attempt.get("exit_code").and_then(Value::as_i64) != Some(0) {
            reasons.push(
                "public.evidence.publish_attempt.exit_code must be 0 when status is pass"
                    .to_string(),
            );
        }
        if public_evidence.get("status").and_then(Value::as_str) != Some("pass") {
            reasons.push(
                "public.evidence.publish_attempt pass cannot replace sanitized public evidence pass"
                    .to_string(),
            );
        }
    }
    if status == Some("fail") {
        match publish_attempt.get("exit_code").and_then(Value::as_i64) {
            Some(code) if code != 0 => {}
            _ => reasons.push(
                "public.evidence.publish_attempt.exit_code must be nonzero when status is fail"
                    .to_string(),
            ),
        }
    }
}

fn check_blocked_handoff(manifest: &Value, reasons: &mut Vec<String>) {
    if value_at(manifest, &["release", "blocked_handoff", "required"]).and_then(Value::as_bool)
        != Some(false)
    {
        reasons.push("release.blocked_handoff.required is not false".to_string());
    }
    if value_at(manifest, &["release", "blocked_handoff", "complete"]).and_then(Value::as_bool)
        != Some(false)
    {
        reasons.push("release.blocked_handoff.complete is not false".to_string());
    }
    if value_at(
        manifest,
        &["release", "blocked_handoff", "public_release_blocking"],
    )
    .and_then(Value::as_bool)
        != Some(false)
    {
        reasons.push("release.blocked_handoff.public_release_blocking is not false".to_string());
    }
    if value_at(manifest, &["release", "blocked_handoff", "status"]).and_then(Value::as_str)
        != Some("synced")
    {
        reasons.push(format!(
            "release.blocked_handoff.status={:?}, expected 'synced'",
            value_at(manifest, &["release", "blocked_handoff", "status"])
        ));
    }
}

fn check_launch_gates(manifest: &Value, reasons: &mut Vec<String>) {
    let Some(launch_gates) = value_at(manifest, &["launch_gates"]).and_then(Value::as_array) else {
        reasons.push("launch_gates is empty".to_string());
        return;
    };
    if launch_gates.is_empty() {
        reasons.push("launch_gates is empty".to_string());
        return;
    }
    for gate in launch_gates {
        let Some(gate) = gate.as_object() else {
            reasons.push("launch_gates contains a non-object entry".to_string());
            continue;
        };
        let label = gate
            .get("name")
            .or_else(|| gate.get("path"))
            .and_then(Value::as_str)
            .unwrap_or("<unknown>");
        if gate.get("exists").and_then(Value::as_bool) != Some(true) {
            reasons.push(format!("launch gate status path is missing: {label}"));
        }
        if gate.get("outcome").and_then(Value::as_str) != Some("pass") {
            reasons.push(format!(
                "launch gate {label} outcome={:?}, expected 'pass'",
                gate.get("outcome")
            ));
        }
    }
}

fn check_launch_gate_summaries(manifest: &Value, reasons: &mut Vec<String>) {
    let Some(summaries) = value_at(manifest, &["launch_gate_summaries"]) else {
        return;
    };
    let Some(summaries) = summaries.as_array() else {
        reasons.push("launch_gate_summaries contains a non-object entry".to_string());
        return;
    };
    for summary in summaries {
        let Some(summary) = summary.as_object() else {
            reasons.push("launch_gate_summaries contains a non-object entry".to_string());
            continue;
        };
        let label = summary
            .get("name")
            .or_else(|| summary.get("path"))
            .and_then(Value::as_str)
            .unwrap_or("<unknown>");
        if summary.get("exists").and_then(Value::as_bool) != Some(true) {
            reasons.push(format!("launch gate summary path is missing: {label}"));
        }
        if summary.get("schema").and_then(Value::as_str) != Some("ay-release-gate-summary/v1") {
            reasons.push(format!(
                "launch gate summary {label} schema={:?}, expected 'ay-release-gate-summary/v1'",
                summary.get("schema")
            ));
        }
        if summary.get("status").and_then(Value::as_str) != Some("pass") {
            reasons.push(format!(
                "launch gate summary {label} status={:?}, expected 'pass'",
                summary.get("status")
            ));
        }
        if summary
            .get("evidence_gate_failures")
            .and_then(Value::as_i64)
            != Some(0)
        {
            reasons.push(format!(
                "launch gate summary {label} evidence_gate_failures={:?}, expected 0",
                summary.get("evidence_gate_failures")
            ));
        }
        if summary.get("launch_blocker_count").and_then(Value::as_i64) != Some(0) {
            reasons.push(format!(
                "launch gate summary {label} launch_blocker_count={:?}, expected 0",
                summary.get("launch_blocker_count")
            ));
        }
    }
}

fn check_checks_object(manifest: &Value, reasons: &mut Vec<String>) {
    let Some(checks) = value_at(manifest, &["checks"]).and_then(Value::as_object) else {
        reasons.push("checks is empty".to_string());
        return;
    };
    if checks.is_empty() {
        reasons.push("checks is empty".to_string());
        return;
    }
    let failed_checks = checks
        .iter()
        .filter_map(|(key, value)| (value.as_bool() != Some(true)).then_some(key.clone()))
        .collect::<Vec<_>>();
    if !failed_checks.is_empty() {
        reasons.push(format!("failed checks: {}", failed_checks.join(", ")));
    }
}

fn check_errors_empty(value: &Value, label: &str, reasons: &mut Vec<String>) {
    match value.get("errors") {
        Some(Value::Array(items)) if !items.is_empty() => {
            let rendered = items.iter().map(Value::to_string).collect::<Vec<_>>();
            reasons.push(format!("{label} errors: {}", rendered.join("; ")));
        }
        Some(Value::Array(_)) | None | Some(Value::Null) => {}
        Some(other) => reasons.push(format!("{label} errors is not a list: {other:?}")),
    }
}

fn is_empty_value(value: &Value) -> bool {
    match value {
        Value::Null => true,
        Value::String(text) => text.is_empty(),
        Value::Array(items) => items.is_empty(),
        Value::Object(items) => items.is_empty(),
        Value::Bool(_) | Value::Number(_) => false,
    }
}

fn is_lower_sha256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
}

fn sha256_file_hex(path: &Path) -> std::result::Result<String, String> {
    let bytes = fs::read(path).map_err(|error| format!("read {}: {error}", path.display()))?;
    let digest = Sha256::digest(&bytes);
    Ok(hex_digest(&digest))
}

fn hex_digest(bytes: &[u8]) -> String {
    use std::fmt::Write as _;

    bytes
        .iter()
        .fold(String::with_capacity(bytes.len() * 2), |mut out, byte| {
            write!(&mut out, "{byte:02x}").expect("write to String");
            out
        })
}

fn check_release_manifest_verification(args: &ResolvedArgs, state: &mut GateState) {
    let Some(path) = &args.release_manifest_verification else {
        if let Some(manifest_path) = &args.release_manifest {
            let output_path = PathBuf::from("ay-release-manifest-verification.json");
            let command = release_manifest_verification_command(
                &manifest_path.display().to_string(),
                &output_path.display().to_string(),
            );
            state.add_blocker(
                "release_manifest_verification",
                &output_path.display().to_string(),
                &command,
                format!(
                    "no release manifest verification supplied for {}; pass --release-manifest-verification ay-release-manifest-verification.json",
                    manifest_path.display()
                ),
            );
        }
        return;
    };
    let command = release_manifest_verification_command(
        &args.release_manifest.as_ref().map_or_else(
            || "release-manifest.json".to_string(),
            |path| path.display().to_string(),
        ),
        &path.display().to_string(),
    );
    let Some(manifest_path) = &args.release_manifest else {
        state.add_blocker(
            "release_manifest_verification",
            &path.display().to_string(),
            &command,
            "release manifest verification supplied without --release-manifest".to_string(),
        );
        return;
    };
    let resolved = resolve_repo_path(&args.repo_root, path);
    let resolved_manifest = resolve_repo_path(&args.repo_root, manifest_path);
    if !resolved.is_file() {
        state.add_blocker(
            "release_manifest_verification",
            &path.display().to_string(),
            &command,
            format!(
                "release manifest verification not found: {}",
                path.display()
            ),
        );
        return;
    }
    if !resolved_manifest.is_file() {
        state.add_blocker(
            "release_manifest_verification",
            &path.display().to_string(),
            &command,
            format!(
                "release manifest verification cannot be checked because release manifest is missing: {}",
                manifest_path.display()
            ),
        );
        return;
    }
    let verification = match read_json(&resolved) {
        Ok(value) => value,
        Err(error) => {
            state.add_blocker(
                "release_manifest_verification",
                &path.display().to_string(),
                &command,
                error,
            );
            return;
        }
    };
    let manifest = match read_json(&resolved_manifest) {
        Ok(value) => value,
        Err(error) => {
            state.add_blocker(
                "release_manifest_verification",
                &path.display().to_string(),
                &command,
                error,
            );
            return;
        }
    };

    let reasons = release_manifest_verification_reasons(
        &verification,
        &manifest,
        &resolved_manifest,
        &args.repo_root,
    );
    if reasons.is_empty() {
        println!(
            "[blocker-check] PASS release_manifest_verification: release artifact verification summary is complete"
        );
    } else {
        state.add_blocker(
            "release_manifest_verification",
            &path.display().to_string(),
            &command,
            reasons.join("; "),
        );
    }
}

const REQUIRED_RELEASE_VERIFICATION_CHECKS: &[&str] = &[
    "manifest_schema",
    "manifest_status_pass",
    "manifest_checks_all_true",
    "public_channel",
    "public_release_ready",
    "private_commit_full_hex",
    "public_commit_matches_private",
    "public_evidence_pass",
    "public_evidence_location",
    "public_evidence_git_env_sanitized",
    "public_evidence_fetch_command",
    "public_evidence_ls_remote_command",
    "dependency_evidence_pass",
    "dependency_public_fetch_checked",
    "dependency_EXTERNAL_CODEGEN_public_url",
    "dependency_EXTERNAL_CODEGEN_commit_full_hex",
    "dependency_EXTERNAL_CODEGEN_component_version_present",
    "dependency_EXTERNAL_CODEGEN_package_versions_present",
    "dependency_ExternalCodegenIr_public_url",
    "dependency_ExternalCodegenIr_commit_full_hex",
    "dependency_ExternalCodegenIr_component_version_present",
    "dependency_ExternalCodegenIr_package_versions_present",
    "binary_build_commit_matches_private",
    "binary_version_output_mentions_build_commit",
    "artifact_path_available",
    "artifact_exists",
    "artifact_sha256_matches_manifest",
    "artifact_size_matches_manifest",
    "artifact_version_matches_manifest",
];

fn release_manifest_verification_reasons(
    verification: &Value,
    manifest: &Value,
    manifest_path: &Path,
    repo_root: &Path,
) -> Vec<String> {
    let mut reasons = Vec::new();
    expect_string(
        verification,
        "schema",
        "ay-release-manifest-verification/v1",
        &mut reasons,
    );
    expect_string(verification, "status", "pass", &mut reasons);

    match verification.get("checks").and_then(Value::as_object) {
        Some(checks) if !checks.is_empty() => {
            let failed_checks = checks
                .iter()
                .filter_map(|(key, value)| (value.as_bool() != Some(true)).then_some(key.clone()))
                .collect::<Vec<_>>();
            if !failed_checks.is_empty() {
                reasons.push(format!(
                    "failed verification checks: {}",
                    failed_checks.join(", ")
                ));
            }
            let missing_or_false = REQUIRED_RELEASE_VERIFICATION_CHECKS
                .iter()
                .copied()
                .filter(|key| checks.get(*key).and_then(Value::as_bool) != Some(true))
                .collect::<Vec<_>>();
            if !missing_or_false.is_empty() {
                reasons.push(format!(
                    "missing required verification checks: {}",
                    missing_or_false.join(", ")
                ));
            }
        }
        _ => reasons.push("checks is empty".to_string()),
    }

    if let Some(errors) = verification.get("errors") {
        match errors {
            Value::Array(items) if !items.is_empty() => {
                let rendered = items.iter().map(Value::to_string).collect::<Vec<_>>();
                reasons.push(format!("verification errors: {}", rendered.join("; ")));
            }
            Value::Array(_) | Value::Null => {}
            _ => reasons.push(format!("verification errors is not a list: {errors:?}")),
        }
    }

    let private_commit = value_at(manifest, &["private", "ay_commit"]);
    let public_commit = value_at(manifest, &["public", "ay_commit"]);
    let manifest_record = value_at(verification, &["manifest"]);
    let recorded_path = value_at(verification, &["manifest", "path"]);
    match recorded_path {
        None => reasons.push("verification.manifest.path is missing".to_string()),
        Some(value) => {
            let recorded = value.as_str().unwrap_or_default();
            if !path_matches_recorded_manifest(recorded, manifest_path, repo_root) {
                reasons.push(format!(
                    "verification.manifest.path={value:?} does not resolve to {:?}",
                    manifest_path.display().to_string()
                ));
            }
        }
    }
    compare_value(
        manifest_record.and_then(|value| value.get("channel")),
        manifest.get("channel"),
        "verification.manifest.channel",
        "manifest channel",
        &mut reasons,
    );
    compare_value(
        manifest_record.and_then(|value| value.get("claim_status")),
        value_at(manifest, &["release", "claim_status"]),
        "verification.manifest.claim_status",
        "release.claim_status",
        &mut reasons,
    );
    compare_value(
        manifest_record.and_then(|value| value.get("private_commit")),
        private_commit,
        "verification.manifest.private_commit",
        "private.ay_commit",
        &mut reasons,
    );
    compare_value(
        manifest_record.and_then(|value| value.get("public_mirror_commit")),
        public_commit,
        "verification.manifest.public_mirror_commit",
        "public.ay_commit",
        &mut reasons,
    );

    match value_at(verification, &["artifact"]) {
        Some(artifact) if artifact.is_object() => {
            compare_value(
                artifact.get("sha256"),
                value_at(manifest, &["build", "artifact_sha256"]),
                "verification.artifact.sha256",
                "build.artifact_sha256",
                &mut reasons,
            );
            compare_value(
                artifact.get("size_bytes"),
                value_at(manifest, &["build", "artifact_size_bytes"]),
                "verification.artifact.size_bytes",
                "build.artifact_size_bytes",
                &mut reasons,
            );
            if artifact.get("version_returncode").and_then(Value::as_i64) != Some(0) {
                reasons.push(format!(
                    "verification.artifact.version_returncode={:?}, expected 0",
                    artifact.get("version_returncode")
                ));
            }
            compare_value(
                artifact.get("version_stdout"),
                value_at(manifest, &["build", "binary_version_output"]),
                "verification.artifact.version_stdout",
                "build.binary_version_output",
                &mut reasons,
            );
        }
        _ => reasons.push("verification.artifact is missing".to_string()),
    }

    reasons
}

fn value_at<'a>(value: &'a Value, path: &[&str]) -> Option<&'a Value> {
    let mut current = value;
    for key in path {
        current = current.get(*key)?;
    }
    Some(current)
}

fn compare_value(
    actual: Option<&Value>,
    expected: Option<&Value>,
    actual_label: &str,
    expected_label: &str,
    reasons: &mut Vec<String>,
) {
    if actual != expected {
        reasons.push(format!(
            "{actual_label}={actual:?} does not match {expected_label}={expected:?}"
        ));
    }
}

fn path_matches_recorded_manifest(recorded: &str, manifest_path: &Path, repo_root: &Path) -> bool {
    if recorded.is_empty() {
        return false;
    }
    let recorded_path = Path::new(recorded);
    let mut candidates = vec![recorded_path.to_path_buf()];
    if !recorded_path.is_absolute() {
        candidates.push(repo_root.join(recorded_path));
        if let Some(parent) = manifest_path.parent() {
            candidates.push(parent.join(recorded_path));
        }
    }
    let expected = manifest_path
        .canonicalize()
        .unwrap_or_else(|_| manifest_path.to_path_buf());
    for candidate in candidates {
        if candidate
            .canonicalize()
            .is_ok_and(|resolved| resolved == expected)
        {
            return true;
        }
    }
    recorded == manifest_path.to_string_lossy()
}

fn read_json(path: &Path) -> std::result::Result<Value, String> {
    let text = fs::read_to_string(path).map_err(|error| {
        format!(
            "JSON file not found or unreadable: {}: {error}",
            path.display()
        )
    })?;
    serde_json::from_str(&text).map_err(|error| format!("cannot read JSON: {error}"))
}

fn expect_string(value: &Value, key: &str, expected: &str, reasons: &mut Vec<String>) {
    if value.get(key).and_then(Value::as_str) != Some(expected) {
        reasons.push(format!("{key}={:?}, expected {expected:?}", value.get(key)));
    }
}

fn expect_bool(value: &Value, key: &str, expected: bool, reasons: &mut Vec<String>) {
    if value.get(key).and_then(Value::as_bool) != Some(expected) {
        reasons.push(format!("{key}={:?}, expected {expected}", value.get(key)));
    }
}

fn expect_i64(value: &Value, key: &str, expected: i64, reasons: &mut Vec<String>) {
    if value.get(key).and_then(Value::as_i64) != Some(expected) {
        reasons.push(format!("{key}={:?}, expected {expected}", value.get(key)));
    }
}

fn eval_ids(value: &Value) -> Vec<String> {
    value
        .get("evals")
        .and_then(Value::as_array)
        .map(|rows| {
            rows.iter()
                .filter_map(|row| row.get("eval_id").and_then(Value::as_str))
                .map(str::to_string)
                .collect()
        })
        .unwrap_or_default()
}

fn write_summary_json(args: &ResolvedArgs, state: &GateState, path: &Path) -> Result<()> {
    let targeted_smokes = state
        .targeted_smokes
        .iter()
        .map(|check| (check.id.clone(), targeted_smoke_check_json(check)))
        .collect::<serde_json::Map<_, _>>();
    let summary = json!({
        "schema": "ay-release-gate-summary/v1",
        "status": if state.evidence_gate_failures == 0 && state.blockers.is_empty() { "pass" } else { "fail" },
        "generated_at_utc": now_utc_rfc3339(),
        "repo_root": args.repo_root,
        "launch_mode": args.launch_mode.as_str(),
        "evidence_gate_failures": state.evidence_gate_failures,
        "advisory_failures": state.advisory_failures,
        "launch_blocker_count": state.blockers.len(),
        "packet_checklist": {
            "path": "the development design notes",
            "exists": args.repo_root.join("the development design notes").exists(),
        },
        "targeted_smokes": targeted_smokes,
        "blockers": state.blockers.iter().map(|blocker| {
            json!({
                "id": blocker.id(),
                "name": blocker.name,
                "evidence": blocker.evidence,
                "command": blocker.command,
                "finding": blocker.finding,
            })
        }).collect::<Vec<_>>(),
    });
    let resolved = resolve_repo_path(&args.repo_root, path);
    if let Some(parent) = resolved.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("create summary JSON parent {}", parent.display()))?;
    }
    let mut bytes = serde_json::to_vec_pretty(&summary)?;
    bytes.push(b'\n');
    fs::write(&resolved, bytes)
        .with_context(|| format!("write summary JSON {}", resolved.display()))?;
    Ok(())
}

fn targeted_smoke_check_json(check: &TargetedSmokeCheck) -> Value {
    json!({
        "required": check.required,
        "status": &check.status,
        "solver_timeout_ms": check.solver_timeout_ms,
        "wall_timeout_ms": check.wall_timeout_ms,
        "cases_total": check.cases_total,
        "cases_passed": check.cases_passed,
        "cases_failed": check.cases_failed,
        "cases": check.cases.iter().map(|case| {
            json!({
                "id": &case.id,
                "path": &case.path,
                "expected_verdict": case.expected_verdict,
                "expected_result": &case.expected_result,
                "expected_certificate": &case.expected_certificate,
                "command": &case.command,
                "exit_code": case.exit_code,
                "timed_out": case.timed_out,
                "duration_ms": case.duration_ms,
                "stdout_predicates": {
                    "has_unsat_line": case.stdout_predicates.has_unsat_line,
                    "first_non_empty_line_is_unsat": case.stdout_predicates.first_non_empty_line_is_unsat,
                    "has_unsafe_certificate": case.stdout_predicates.has_unsafe_certificate,
                    "has_unknown_line": case.stdout_predicates.has_unknown_line,
                    "has_timeout_reason": case.stdout_predicates.has_timeout_reason,
                },
                "status": &case.status,
                "finding": &case.finding,
            })
        }).collect::<Vec<_>>(),
    })
}

fn now_utc_rfc3339() -> String {
    let seconds = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_secs() as i64;
    let days = seconds.div_euclid(86_400);
    let seconds_of_day = seconds.rem_euclid(86_400);
    let (year, month, day) = civil_from_days(days);
    let hour = seconds_of_day / 3_600;
    let minute = (seconds_of_day % 3_600) / 60;
    let second = seconds_of_day % 60;
    format!("{year:04}-{month:02}-{day:02}T{hour:02}:{minute:02}:{second:02}Z")
}

fn civil_from_days(days_since_unix_epoch: i64) -> (i64, i64, i64) {
    let z = days_since_unix_epoch + 719_468;
    let era = if z >= 0 { z } else { z - 146_096 } / 146_097;
    let doe = z - era * 146_097;
    let yoe = (doe - doe / 1_460 + doe / 36_524 - doe / 146_096) / 365;
    let year = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let day = doy - (153 * mp + 2) / 5 + 1;
    let month = mp + if mp < 10 { 3 } else { -9 };
    let year = year + if month <= 2 { 1 } else { 0 };
    (year, month, day)
}

fn compatibility_command() -> String {
    "bash scripts/check_doc_reality.sh && cargo test -p ay --test group_cli z3_compat_args"
        .to_string()
}

fn proof_full_gate_command() -> String {
    "DRAT_TRIM=/path/to/drat-trim ./target/release/ay z3-audit --scope full-replacement --summary-json z3-audit-proof.json 2>&1 | tee z3-audit-proof.log"
        .to_string()
}

fn proof_cli_command() -> String {
    "./target/release/ay z3-audit --scope full-replacement --summary-json z3-audit-proof.json 2>&1 | tee z3-audit-proof.log".to_string()
}

fn proof_alethe_replay_command() -> String {
    "AY_PACKET_DIR=${AY_PACKET_DIR:-/tmp/ay-proof-replay}; ./target/release/ay z3-audit --scope full-replacement --proof-work-dir \"${AY_PACKET_DIR}\" --alethe-problem tests/fixtures/proof/smt_alethe_qf_uf_transitivity_not_eq.smt2 --alethe-checker carcara --summary-json \"${AY_PACKET_DIR}/z3-audit-alethe.json\" 2>&1 | tee \"${AY_PACKET_DIR}/z3-audit-alethe.log\"".to_string()
}

fn proof_lean_replay_command() -> String {
    "set -o pipefail; AY_PACKET_DIR=${AY_PACKET_DIR:-/tmp/ay-lean-replay} && mkdir -p \"${AY_PACKET_DIR}\" && lean \"${AY_PACKET_DIR}/lean-proof.lean4\" 2>&1 | tee \"${AY_PACKET_DIR}/lean-proof-replay.log\"".to_string()
}

fn proof_chc_replay_command() -> String {
    "set -o pipefail; AY_PACKET_DIR=${AY_PACKET_DIR:-/tmp/ay-chc-replay} && mkdir -p \"${AY_PACKET_DIR}\" && AY_CHC_RUN_DIR=$(umask 077 && mktemp -d \"${AY_PACKET_DIR}/chc-run.XXXXXXXXXX\") && chmod 700 \"${AY_CHC_RUN_DIR}\" && AY_CHC_CERTIFICATE=\"${AY_CHC_RUN_DIR}/chc-certificate.smt2\" && ./target/release/ay solve --chc --stats-json --proof \"${AY_CHC_CERTIFICATE}\" benchmarks/chc/counter_safe_chccomp.smt2 2>&1 | tee \"${AY_CHC_RUN_DIR}/chc-certificate-run.log\" && set -- \"${AY_CHC_CERTIFICATE}\".chc-obligations-* && test \"$#\" -eq 1 && test -d \"$1\" && AY_CHC_OBLIGATIONS_DIR=$1 && set -- \"${AY_CHC_OBLIGATIONS_DIR}\"/*.smt2 && test \"$#\" -gt 0 && test -f \"$1\" && : > \"${AY_CHC_RUN_DIR}/chc-certificate-replay.log\" && (for AY_CHC_OBLIGATION in \"$@\"; do AY_CHC_REPLAY_OUTPUT=$(z3 \"${AY_CHC_OBLIGATION}\" 2>&1) || { AY_CHC_REPLAY_STATUS=$?; printf '%s\\n' \"${AY_CHC_REPLAY_OUTPUT}\" | tee -a \"${AY_CHC_RUN_DIR}/chc-certificate-replay.log\"; exit \"${AY_CHC_REPLAY_STATUS}\"; }; printf '%s\\n' \"${AY_CHC_REPLAY_OUTPUT}\" | tee -a \"${AY_CHC_RUN_DIR}/chc-certificate-replay.log\" || exit 1; AY_CHC_REPLAY_VERDICT=$(printf '%s\\n' \"${AY_CHC_REPLAY_OUTPUT}\" | awk 'NF { print; exit }') || exit 1; test \"${AY_CHC_REPLAY_VERDICT}\" = unsat || exit 1; done)".to_string()
}

fn benchmark_command() -> String {
    "bash scripts/launch_benchmark_packet.sh --ay ./target/release/ay --timeout 30 --reference-solver z3 --exclude-eval sat-par2-dev".to_string()
}

fn downstream_command(json_path: &str) -> String {
    format!(
        "./target/release/ay consumer-smoke run --full --temp-worktree verification-consumer,deductive-checks --worktree-ref origin/main --fetch-worktree-ref --json {json_path}"
    )
}

fn release_manifest_command(output_path: &str) -> String {
    let build_command = "RUSTC_WRAPPER= CARGO_NET_GIT_FETCH_WITH_CLI=true CARGO_INCREMENTAL=0 CARGO_TARGET_DIR=$AY_RELEASE_TARGET_DIR AY_SOURCE_GIT_COMMIT=$AY_RELEASE_COMMIT AY_SOURCE_GIT_COMMIT_SHORT=$AY_RELEASE_COMMIT_SHORT AY_SOURCE_GIT_DIRTY=false cargo build --release -p ay --locked";
    format!(
        "AY_RELEASE_COMMIT=\"$(git rev-parse HEAD)\" && \
         AY_RELEASE_COMMIT_SHORT=\"$(git rev-parse --short=12 HEAD)\" && \
         AY_RELEASE_TARGET_DIR=\"${{AY_RELEASE_TARGET_DIR:-${{AY_PACKET_DIR:-$PWD}}/target-release}}\" && \
         test -z \"$(git status --short --untracked-files=no)\" && \
         RUSTC_WRAPPER= CARGO_NET_GIT_FETCH_WITH_CLI=true CARGO_INCREMENTAL=0 CARGO_TARGET_DIR=\"$AY_RELEASE_TARGET_DIR\" AY_SOURCE_GIT_COMMIT=\"$AY_RELEASE_COMMIT\" AY_SOURCE_GIT_COMMIT_SHORT=\"$AY_RELEASE_COMMIT_SHORT\" AY_SOURCE_GIT_DIRTY=false cargo build --release -p ay --locked && \
         ay_bin=\"$AY_RELEASE_TARGET_DIR/release/ay\" && \
         test -x \"$ay_bin\" && \
         \"$ay_bin\" release verify-public-pins --json > ay-dependency-pins.json && \
         \"$ay_bin\" --version > ay-version.txt && \
         grep -Fx \"build.commit=$AY_RELEASE_COMMIT_SHORT\" ay-version.txt && \
         printf 'release-manifest-inputs: PASS\\n' > release-manifest-inputs.log && \
         \"$ay_bin\" release generate-manifest --channel public --private-commit \"$AY_RELEASE_COMMIT\" --public-evidence ay-public-commit-evidence.json --dependency-pins ay-dependency-pins.json --build-command \"{build_command}\" --artifact-path \"$ay_bin\" --binary-version-file ay-version.txt --launch-gate-status release_manifest_inputs=release-manifest-inputs.log --output \"{output_path}\""
    )
}

fn release_manifest_verification_command(manifest_path: &str, output_path: &str) -> String {
    format!(
        "AY_RELEASE_TARGET_DIR=\"${{AY_RELEASE_TARGET_DIR:-${{AY_PACKET_DIR:-$PWD}}/target-release}}\" && ay_bin=\"$AY_RELEASE_TARGET_DIR/release/ay\" && test -x \"$ay_bin\" && \"$ay_bin\" release verify-manifest --manifest \"{manifest_path}\" --artifact \"$ay_bin\" --run-version > \"{output_path}\""
    )
}

fn auflia_command() -> String {
    "scripts/download_smtcomp_benchmarks.sh --logic QF_AUFLIA && ./target/release/ay bench run smt-smtcomp-qf-auflia --ay ./target/release/ay --timeout 30 --reference-solver z3 -o \"${AY_PACKET_DIR:-/tmp}/qf-auflia-results.json\" && cargo test -p ay --test group_soundness auflia".to_string()
}

trait OsStringExt {
    fn is_empty(&self) -> bool;
}

impl OsStringExt for OsString {
    fn is_empty(&self) -> bool {
        self.as_os_str().is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    // Unix-only test helpers: `write_fake_ay_script` writes a `#!/bin/sh`
    // stub and chmods it via PermissionsExt, which does not exist on
    // Windows. Gate the import, the helper, and its two consumer tests so
    // the bin test target compiles on Windows (found 2026-07-14 by the
    // experimental-feature compile lane).
    #[cfg(unix)]
    use std::os::unix::fs::PermissionsExt;
    use tempfile::TempDir;

    fn repo_root_for_tests() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .expect("crate lives under repo/crates/ay")
            .to_path_buf()
    }

    fn resolved_args_for_ay(repo_root: &Path, ay: PathBuf) -> ResolvedArgs {
        ResolvedArgs {
            repo_root: repo_root.to_path_buf(),
            ay,
            reference_solver: "z3".to_string(),
            launch_mode: LaunchMode::DryRun,
            out_dir: None,
            benchmark_summary: None,
            downstream_summary: None,
            check_public_mirror: false,
            public_mirror_evidence: None,
            dependency_pins: None,
            release_manifest: None,
            release_manifest_verification: None,
            proof_cli_evidence: None,
            proof_cli_log: None,
            proof_alethe_replay_summary: None,
            proof_lean_replay_summary: None,
            proof_chc_replay_summary: None,
            summary_json: None,
            run_z3_cli_tests: false,
        }
    }

    #[cfg(unix)]
    fn write_fake_ay_script(dir: &Path, build_commit: &str) -> PathBuf {
        let path = dir.join("fake-ay");
        fs::write(
            &path,
            format!(
                "#!/bin/sh\n\
                 if [ \"$1\" = \"z3-audit\" ] && [ \"$2\" = \"--help\" ]; then\n\
                   printf '%s\\n' 'Usage: ay z3-audit --scope full-replacement'\n\
                   exit 0\n\
                 fi\n\
                 if [ \"$1\" = \"--version\" ]; then\n\
                   printf '%s\\n' 'ay fake'\n\
                   printf '%s\\n' 'build.commit={build_commit}'\n\
                   exit 0\n\
                 fi\n\
                 exit 0\n"
            ),
        )
        .expect("write fake ay");
        let mut permissions = fs::metadata(&path).expect("fake ay metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(&path, permissions).expect("chmod fake ay");
        path
    }

    #[test]
    fn native_launch_gate_default_repo_root_can_start_inside_repo() {
        let repo_root = repo_root_for_tests();
        let nested = repo_root.join("crates/ay/src");

        assert_eq!(find_launch_gate_repo_root(&nested), Some(repo_root));
    }

    #[cfg(unix)]
    #[test]
    fn proof_audit_binary_uses_requested_current_head_binary() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");
        let temp = TempDir::new().expect("temp fake ay");
        let fake_ay = write_fake_ay_script(temp.path(), &head[..12]);
        let args = resolved_args_for_ay(&repo_root, fake_ay.clone());

        let selected = proof_audit_command_binary(&args).expect("select proof audit binary");

        assert_eq!(selected, fake_ay);
    }

    #[cfg(unix)]
    #[test]
    fn proof_audit_binary_rejects_stale_dirty_and_too_short_build_commits() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");
        assert!(build_commit_matches_head(&head[..12], &head));
        assert!(!build_commit_matches_head(&head[..11], &head));
        assert!(!build_commit_matches_head("not-a-sha", &head));

        for build_commit in ["000000000000", &format!("{}-dirty", &head[..12])] {
            let temp = TempDir::new().expect("temp fake ay");
            let fake_ay = write_fake_ay_script(temp.path(), build_commit);
            let args = resolved_args_for_ay(&repo_root, fake_ay.clone());

            let selected = proof_audit_command_binary(&args).expect("select proof audit binary");

            assert_ne!(
                selected, fake_ay,
                "stale or dirty build commit {build_commit} must not be used for proof audit"
            );
        }
    }

    #[test]
    fn proof_audit_args_request_full_replacement_json() {
        let repo_root = repo_root_for_tests();
        let args = resolved_args_for_ay(&repo_root, PathBuf::from("./target/release/ay"));
        let summary_json = Path::new("/tmp/ay-launch-gate-proof-audit-test.json");

        let argv = proof_audit_args(&args, &args.ay, summary_json);

        assert!(argv
            .windows(2)
            .any(|pair| pair == ["--scope", "full-replacement"]));
        assert!(argv.windows(2).any(|pair| pair
            == [
                "--summary-json",
                "/tmp/ay-launch-gate-proof-audit-test.json"
            ]));
        assert!(argv.windows(2).any(|pair| pair[0] == "--reference-cache"
            && pair[1].ends_with("tests/z3-audit/reference-cache.json")));
        assert!(
            !argv
                .iter()
                .any(|arg| arg == "--write-reference-cache" || arg == "--generate-reference-cache"),
            "launch gate must not mutate baseline references while auditing"
        );
        assert!(
            !argv.iter().any(|arg| arg == "--inventory-only"),
            "launch gate must consume executed full-replacement proof evidence, not inventory-only rows"
        );
    }

    #[test]
    fn chc_replay_guidance_isolates_each_emission_before_globbing() {
        let command = proof_chc_replay_command();

        assert!(command.contains("mktemp -d \"${AY_PACKET_DIR}/chc-run.XXXXXXXXXX\""));
        assert!(command.contains("chmod 700 \"${AY_CHC_RUN_DIR}\""));
        assert!(command.contains("solve --chc --stats-json --proof \"${AY_CHC_CERTIFICATE}\""));
        assert!(command.contains("\"${AY_CHC_CERTIFICATE}\".chc-obligations-*"));
        assert!(command.contains("test \"$#\" -eq 1 && test -d \"$1\""));
        assert!(command.contains("\"${AY_CHC_OBLIGATIONS_DIR}\"/*.smt2"));
        assert!(command.contains("for AY_CHC_OBLIGATION in \"$@\""));
        assert!(command.contains("z3 \"${AY_CHC_OBLIGATION}\""));
        assert!(command.contains("test \"${AY_CHC_REPLAY_VERDICT}\" = unsat || exit 1"));
        assert!(!command.contains("z3 \"$@\""));
        assert!(
            !command.contains("\"${AY_PACKET_DIR}\"/chc-obligations"),
            "replay guidance must not inspect a shared stale obligation directory: {command}"
        );
    }

    fn public_release_pins_fixture(head: &str) -> Value {
        let llvm_commit = "1111111111111111111111111111111111111111";
        let external_codegen_ir_commit = "2222222222222222222222222222222222222222";
        let external_codegen_url = crate::cmd_release::external_codegen_url();
        let external_codegen_ir_url = crate::cmd_release::external_codegen_ir_url()
            .replace("/external-codegen-ir", "/external_codegen_ir");
        json!({
            "schema": "ay-public-release-pins/v1",
            "status": "pass",
            "source": {
                "ay_commit": head,
                "lockfile": "Cargo.lock",
                "cargo_wrapper": "cargo_wrapper.toml",
                "manifests": ["Cargo.toml", "crates/ay-jit/Cargo.toml"],
                "public_fetch_checked": false,
            },
            "pins": [
                {
                    "name": "EXTERNAL_CODEGEN",
                    "url": external_codegen_url.clone(),
                    "commit": llvm_commit,
                    "rev": llvm_commit,
                    "packages": ["external_codegen-codegen"],
                    "component_version": "0.1.0",
                    "package_versions": {"external_codegen-codegen": "0.1.0"},
                },
                {
                    "name": "ExternalCodegenIr",
                    "url": external_codegen_ir_url.clone(),
                    "commit": external_codegen_ir_commit,
                    "rev": null,
                    "packages": ["external_codegen_ir"],
                    "component_version": "0.1.0",
                    "package_versions": {"external_codegen_ir": "0.1.0"},
                },
            ],
            "auto_bump": [
                {
                    "dependency": "external_codegen-codegen",
                    "url": external_codegen_url.clone(),
                    "status": "listed",
                    "bump_method": "manifest-rev",
                    "rev": llvm_commit,
                    "updates": ["crates/ay-jit/Cargo.toml", "Cargo.lock"],
                },
                {
                    "dependency": "external_codegen_ir",
                    "url": external_codegen_ir_url.clone(),
                    "status": "exempt",
                    "kind": "lockfile-only",
                    "bump_method": "lockfile-only",
                    "rev": null,
                    "updates": ["Cargo.lock"],
                },
            ],
        })
    }

    #[test]
    fn public_release_pins_evidence_accepts_current_no_fetch_summary() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");
        let evidence = public_release_pins_fixture(&head);

        let reasons = public_release_pins_evidence_reasons(&evidence, &repo_root);

        assert!(
            reasons.is_empty(),
            "valid no-fetch dependency pins evidence should pass: {reasons:?}"
        );
    }

    #[test]
    fn public_release_pins_evidence_rejects_stale_and_incomplete_pins() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");
        let mut evidence = public_release_pins_fixture(&head);
        evidence["source"]["ay_commit"] =
            Value::String("0000000000000000000000000000000000000000".to_string());
        evidence["pins"][0]["rev"] =
            Value::String("3333333333333333333333333333333333333333".to_string());
        evidence["pins"][1]["commit"] = Value::String("ABC".to_string());
        evidence["auto_bump"][0]["updates"] = json!(["crates/ay-jit/Cargo.toml"]);
        evidence["auto_bump"][1]["status"] = Value::String("listed".to_string());

        let reasons = public_release_pins_evidence_reasons(&evidence, &repo_root);

        for expected in [
            "source.ay_commit",
            "pins.EXTERNAL_CODEGEN.rev does not match commit",
            "pins.ExternalCodegenIr.commit is not a lowercase full commit",
            "auto_bump.external_codegen-codegen.updates does not include Cargo.lock",
            "auto_bump.external_codegen_ir.status",
        ] {
            assert!(
                reasons.iter().any(|reason| reason.contains(expected)),
                "expected {expected:?} in reasons: {reasons:?}"
            );
        }
    }

    #[test]
    fn missing_evidence_summary_prints_shell_none_sentinel() {
        let state = GateState::new();

        assert_eq!(
            missing_evidence_summary_lines(&state),
            vec![
                "=== Missing Evidence For Z3 Skeptics ===".to_string(),
                "none".to_string()
            ]
        );
    }

    fn write_native_benchmark_packet(
        dir: &Path,
        head: &str,
        build_commit: &str,
        clean: bool,
    ) -> PathBuf {
        fs::create_dir_all(dir.join("raw")).expect("create raw dir");
        let eval_ids = [
            "smt-local-suite",
            "smt-smtcomp-qf-lia",
            "smt-smtcomp-qf-lra",
            "smt-smtcomp-qf-bv",
            "smt-smtcomp-qf-abv",
            "chccomp-2025-extra-small-lia",
            "z3-perf-cliffs",
        ];
        let mut rows = Vec::new();
        let mut raw_hashes = serde_json::Map::new();
        for eval_id in eval_ids {
            let raw_path = dir.join("raw").join(format!("{eval_id}.json"));
            fs::write(
                &raw_path,
                br#"{"items":[{"name":"case.smt2","result":"sat","expected":"sat"}],"comparison":{"agree":1,"disagree":0,"ref_only":0,"ay_only":0}}"#,
            )
            .expect("write raw result");
            raw_hashes.insert(
                eval_id.to_string(),
                Value::String(sha256_file_hex(&raw_path).expect("hash raw")),
            );
            rows.push(json!({
                "eval_id": eval_id,
                "benchmarks": 1,
                "counts": {
                    "sat": 1,
                    "unsat": 0,
                    "unknown": 0,
                    "timeout": 0,
                    "error": 0,
                    "other": 0,
                },
                "agree": 1,
                "disagree": 0,
                "expected_mismatches": 0,
                "ref_only": 0,
                "ay_only": 0,
                "results_json": raw_path,
            }));
        }

        let git_status_short = if clean {
            Vec::<String>::new()
        } else {
            vec![" M src/lib.rs".to_string()]
        };
        let provenance = json!({
            "schema": "ay-launch-benchmark-provenance/v1",
            "mode": "run",
            "repo": {
                "commit": head,
                "clean": clean,
                "git_status_short": git_status_short,
            },
            "tools": {
                "ay": {
                    "sha256": "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
                    "version": {
                        "output": [
                            "ay fake",
                            format!("build.commit={build_commit}"),
                        ],
                    },
                },
            },
            "selection": {
                "launch_scope": "subset",
                "requested_evals": [],
                "excluded_evals": [
                    {"eval_id": "sat-par2-dev"},
                ],
            },
        });
        fs::write(
            dir.join("provenance.json"),
            serde_json::to_vec(&provenance).expect("serialize provenance"),
        )
        .expect("write provenance");
        fs::write(
            dir.join("provenance.txt"),
            format!(
                "git_commit={head}\ngit_status_short:\n{}\nlaunch_scope=subset\nexcluded_evals=sat-par2-dev\n",
                if clean { "" } else { " M src/lib.rs\n" }
            ),
        )
        .expect("write provenance txt");
        fs::write(dir.join("commands.log"), "$ ay bench run\n").expect("write commands");
        fs::write(
            dir.join("planned_evals.tsv"),
            eval_ids.iter().fold(String::new(), |mut out, eval_id| {
                use std::fmt::Write as _;
                writeln!(&mut out, "{eval_id}\ttrue").expect("write to String");
                out
            }),
        )
        .expect("write planned evals");
        fs::write(
            dir.join("input_inventory.jsonl"),
            eval_ids.iter().fold(String::new(), |mut out, eval_id| {
                use std::fmt::Write as _;
                writeln!(&mut out, "{{\"eval_id\":\"{eval_id}\"}}").expect("write to String");
                out
            }),
        )
        .expect("write inventory");
        fs::write(dir.join("summary.md"), "# fake\n").expect("write summary md");

        let artifact_paths = [
            ("provenance_txt", dir.join("provenance.txt")),
            ("provenance_json", dir.join("provenance.json")),
            ("commands_log", dir.join("commands.log")),
            ("planned_evals_tsv", dir.join("planned_evals.tsv")),
            ("input_inventory_jsonl", dir.join("input_inventory.jsonl")),
            ("summary_md", dir.join("summary.md")),
        ];
        let mut artifacts = artifact_paths
            .iter()
            .map(|(role, path)| {
                json!({
                    "path": path,
                    "role": role,
                    "exists": true,
                    "sha256": sha256_file_hex(path).expect("hash sidecar"),
                    "size_bytes": fs::metadata(path).expect("metadata").len(),
                })
            })
            .collect::<Vec<_>>();
        for row in &rows {
            let eval_id = row["eval_id"].as_str().expect("eval id");
            let path = dir.join("raw").join(format!("{eval_id}.json"));
            artifacts.push(json!({
                "path": path,
                "role": "raw_results_json",
                "eval_id": eval_id,
                "exists": true,
                "sha256": sha256_file_hex(&path).expect("hash raw artifact"),
                "size_bytes": fs::metadata(&path).expect("metadata").len(),
            }));
        }

        let summary = json!({
            "schema": "ay-launch-benchmark-packet/v1",
            "mode": "run",
            "benchmarks_executed": true,
            "packet_complete": true,
            "launch_scope": "subset",
            "failure_count": 0,
            "git_commit": head,
            "git_clean": clean,
            "provenance_json": dir.join("provenance.json"),
            "totals": {
                "evals": rows.len(),
                "benchmarks": rows.len(),
                "sat": rows.len(),
                "unsat": 0,
                "unknown": 0,
                "timeout": 0,
                "error": 0,
                "other": 0,
                "disagreements": 0,
                "expected_mismatches": 0,
            },
            "evals": rows,
            "raw_artifact_count": raw_hashes.len(),
            "raw_artifact_sha256s": raw_hashes.clone(),
            "artifact_index": {
                "schema": "ay-launch-benchmark-artifact-index/v1",
                "hash_algorithm": "sha256",
                "summary_json_self_hash": "excluded: summary.json carries this index",
                "artifact_count": artifacts.len(),
                "missing_count": 0,
                "raw_result_count": eval_ids.len(),
                "raw_result_sha256s": raw_hashes,
                "artifacts": artifacts,
            },
            "self_validation": {
                "schema": "ay-launch-benchmark-self-validation/v1",
                "status": "pass",
                "checks": {"ok": true},
                "errors": [],
            },
        });
        let summary_path = dir.join("summary.json");
        fs::write(
            &summary_path,
            serde_json::to_vec(&summary).expect("serialize summary"),
        )
        .expect("write summary");
        summary_path
    }

    #[test]
    fn compatibility_parser_reports_partial_rows() {
        let rows = non_ready_compatibility_rows(
            "| Surface | Status | Notes |\n\
             | --- | --- | --- |\n\
             | SMT-LIB input | Partial | scoped |\n\
             | DIMACS CNF input | Ready | ok |\n\
             | QF_NIA | Experimental | scoped |\n",
        );
        assert_eq!(
            rows,
            vec![
                "SMT-LIB input=Partial".to_string(),
                "QF_NIA=Experimental".to_string()
            ]
        );
    }

    #[test]
    fn native_benchmark_gate_accepts_deep_current_packet() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");
        let temp = TempDir::new().expect("temp packet");
        let summary_path = write_native_benchmark_packet(temp.path(), &head, &head[..12], true);
        let summary = read_json(&summary_path).expect("summary JSON");

        let reasons = benchmark_summary_reasons(&summary, &summary_path, &repo_root);

        assert!(
            reasons.is_empty(),
            "unexpected benchmark gate reasons: {reasons:#?}"
        );
    }

    #[test]
    fn native_benchmark_gate_rejects_dirty_or_stale_packet_provenance() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");

        let dirty = TempDir::new().expect("temp dirty packet");
        let dirty_summary_path = write_native_benchmark_packet(
            dirty.path(),
            &head,
            &format!("{}-dirty", &head[..12]),
            false,
        );
        let dirty_summary = read_json(&dirty_summary_path).expect("dirty summary JSON");
        let dirty_reasons =
            benchmark_summary_reasons(&dirty_summary, &dirty_summary_path, &repo_root);
        let dirty_joined = dirty_reasons.join("; ");
        assert!(
            dirty_joined.contains("git_clean is not true")
                && dirty_joined.contains("provenance_json.repo.clean is not true")
                && dirty_joined.contains("build.commit is dirty"),
            "expected dirty provenance findings, got: {dirty_reasons:#?}"
        );

        let stale = TempDir::new().expect("temp stale packet");
        let stale_summary_path =
            write_native_benchmark_packet(stale.path(), &head, "000000000000", true);
        let stale_summary = read_json(&stale_summary_path).expect("stale summary JSON");
        let stale_reasons =
            benchmark_summary_reasons(&stale_summary, &stale_summary_path, &repo_root);
        let stale_joined = stale_reasons.join("; ");
        assert!(
            stale_joined.contains("does not match current HEAD"),
            "expected stale build commit finding, got: {stale_reasons:#?}"
        );
    }

    #[test]
    fn native_benchmark_gate_rejects_shell_sidecar_and_provenance_text_gaps() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");
        let temp = TempDir::new().expect("temp packet");
        let summary_path = write_native_benchmark_packet(temp.path(), &head, &head[..12], true);
        let mut summary = read_json(&summary_path).expect("summary JSON");
        let artifacts = summary["artifact_index"]["artifacts"]
            .as_array_mut()
            .expect("artifact rows");
        artifacts.retain(|row| row["role"] != "commands_log");
        summary["artifact_index"]["artifact_count"] = json!(artifacts.len());
        fs::write(
            &summary_path,
            serde_json::to_vec(&summary).expect("serialize summary"),
        )
        .expect("rewrite summary");
        fs::remove_file(temp.path().join("provenance.txt")).expect("remove provenance txt");

        let reasons = benchmark_summary_reasons(&summary, &summary_path, &repo_root);
        let joined = reasons.join("; ");
        assert!(
            joined.contains("artifact_index missing required sidecar roles: commands_log"),
            "expected missing sidecar finding, got: {reasons:#?}"
        );
        assert!(
            joined.contains("provenance.txt is missing next to summary.json"),
            "expected missing provenance.txt finding, got: {reasons:#?}"
        );
    }

    #[test]
    fn native_benchmark_gate_rejects_partial_provenance_text_subset() {
        let repo_root = repo_root_for_tests();
        let head = current_head(&repo_root).expect("repo HEAD");
        let temp = TempDir::new().expect("temp packet");
        let summary_path = write_native_benchmark_packet(temp.path(), &head, &head[..12], true);
        fs::write(
            temp.path().join("provenance.txt"),
            format!(
                "git_commit={head}\n\
                 git_status_short:\n\n\
                 launch_scope=subset\n\
                 requested_evals=smt-local-suite,z3-perf-cliffs\n"
            ),
        )
        .expect("rewrite provenance txt");
        let summary = read_json(&summary_path).expect("summary JSON");

        let reasons = benchmark_summary_reasons(&summary, &summary_path, &repo_root);
        let joined = reasons.join("; ");
        assert!(
            joined.contains(
                "provenance requested_evals is present; broad gate requires full non-SAT packet"
            ),
            "expected requested_evals finding, got: {reasons:#?}"
        );
        assert!(
            joined.contains("launch_scope='subset' is accepted only for the standard non-SAT packet excluding sat-par2-dev"),
            "expected subset exclusion finding, got: {reasons:#?}"
        );
    }

    #[test]
    fn compatibility_parser_checks_only_launch_gated_rows_when_scoped() {
        let rows = non_ready_compatibility_rows(
            "# Z3 Compatibility\n\
             \n\
             ## Release-Gated Compatibility Surface\n\
             \n\
             | Surface | Status | Notes |\n\
             | --- | --- | --- |\n\
             | CLI invocation | Ready | scoped |\n\
             | SMT-LIB query output | Ready | scoped |\n\
             \n\
             ## Broader Z3 Compatibility Honesty Ledger\n\
             \n\
             | Surface | Status | Notes |\n\
             | --- | --- | --- |\n\
             | SMT-LIB input | Partial | broad |\n\
             | C API / FFI | Experimental | broad |\n\
             \n\
             ## Logic Matrix\n\
             \n\
             | Logic or family | Status | Notes |\n\
             | --- | --- | --- |\n\
             | QF_LRA | Blocked for broad replacement | broad |\n",
        );
        assert!(
            rows.is_empty(),
            "broader honesty-ledger rows are not launch blockers: {rows:?}"
        );
    }

    #[test]
    fn compatibility_parser_blocks_non_ready_launch_gated_rows() {
        let rows = non_ready_compatibility_rows(
            "# Z3 Compatibility\n\
             \n\
             ## Release-Gated Compatibility Surface\n\
             \n\
             | Surface | Status | Notes |\n\
             | --- | --- | --- |\n\
             | CLI invocation | Partial | scoped |\n\
             | SMT-LIB query output | Ready | scoped |\n\
             \n\
             ## Broader Z3 Compatibility Honesty Ledger\n\
             \n\
             | Surface | Status | Notes |\n\
             | --- | --- | --- |\n\
             | C API / FFI | Experimental | broad |\n",
        );
        assert_eq!(rows, vec!["CLI invocation=Partial".to_string()]);
    }

    #[test]
    fn compatibility_parser_requires_exact_ready_launch_gated_status() {
        let rows = non_ready_compatibility_rows(
            "# Z3 Compatibility\n\
             \n\
             ## Release-Gated Compatibility Surface\n\
             \n\
             | Surface | Status | Notes |\n\
             | --- | --- | --- |\n\
             | CLI invocation | Ready pending evidence | scoped |\n\
             | SMT-LIB query output | Needs evidence | scoped |\n\
             | Z3 CLI flags | Ready | scoped |\n",
        );
        assert_eq!(
            rows,
            vec![
                "CLI invocation=Ready pending evidence".to_string(),
                "SMT-LIB query output=Needs evidence".to_string(),
            ]
        );
    }

    #[test]
    fn repository_launch_gated_compatibility_rows_are_ready() {
        let doc = fs::read_to_string(repo_root_for_tests().join("the development design notes"))
            .expect("read Z3 compatibility doc");
        let rows = non_ready_compatibility_rows(&doc);
        assert!(
            rows.is_empty(),
            "launch-gated compatibility rows must all be Ready: {rows:?}"
        );
    }

    #[test]
    fn auflia_parser_requires_ready() {
        let rows = parse_auflia_rows(
            "| Logic or family | Status |\n\
             | --- | --- |\n\
             | QF_AUFLIA | Partial |\n",
        );
        assert_eq!(rows, vec![("QF_AUFLIA".to_string(), "Partial".to_string())]);
    }

    #[test]
    fn proof_findings_read_native_z3_audit_summary_json() {
        let summary = json!({
            "schema": "ay-z3-replacement-audit/v1",
            "scope": "full-replacement",
            "verdict": "pass",
            "failed": 0,
            "proof_failed": 0,
            "full_replacement_ready": true,
            "scoped_cli_ready": true,
            "proof_inventory": [
                {
                    "status": "pass",
                    "surface": "DIMACS DRAT external replay",
                    "current": "1/1 external DRAT replay command passes",
                    "goal": "1/1 external DRAT replay command passes",
                    "finding": "ok"
                },
                {
                    "status": "fail",
                    "surface": "SMT Alethe external replay",
                    "current": "0/1 external replay command passes",
                    "goal": "1/1 external replay command passes",
                    "finding": "carcara was not available"
                },
                {
                    "status": "warn",
                    "surface": "CHC certificate replay",
                    "current": "documented certificate policy",
                    "goal": "machine-checked certificate replay",
                    "finding": "policy-only row"
                }
            ]
        });

        let findings =
            proof_findings_from_summary_json(&summary).expect("native summary inventory rows");

        assert_eq!(
            findings,
            vec![
                (
                    "z3-audit-fail".to_string(),
                    "SMT Alethe external replay".to_string(),
                    "carcara was not available".to_string()
                ),
                (
                    "z3-audit-warn".to_string(),
                    "CHC certificate replay".to_string(),
                    "policy-only row".to_string()
                )
            ]
        );
    }

    #[test]
    fn proof_findings_blocks_false_readiness_booleans() {
        let summary = json!({
            "schema": "ay-z3-replacement-audit/v1",
            "scope": "full-replacement",
            "verdict": "pass",
            "failed": 0,
            "proof_failed": 0,
            "full_replacement_ready": false,
            "scoped_cli_ready": false,
            "proof_inventory": [
                {
                    "status": "pass",
                    "surface": "DIMACS DRAT external replay",
                    "finding": "ok"
                }
            ]
        });

        let findings =
            proof_findings_from_summary_json(&summary).expect("well-formed readiness summary");

        assert_eq!(
            findings,
            vec![
                (
                    "fail".to_string(),
                    "z3-audit full_replacement_ready".to_string(),
                    "full_replacement_ready must be true".to_string()
                ),
                (
                    "fail".to_string(),
                    "z3-audit scoped_cli_ready".to_string(),
                    "scoped_cli_ready must be true".to_string()
                )
            ]
        );
    }

    #[test]
    fn proof_findings_rejects_non_full_replacement_summary_json() {
        let summary = json!({
            "schema": "ay-z3-replacement-audit/v1",
            "scope": "cli-subset",
            "verdict": "pass",
            "failed": 0,
            "proof_failed": 0,
            "full_replacement_ready": true,
            "scoped_cli_ready": true,
            "proof_inventory": [
                {
                    "status": "pass",
                    "surface": "DIMACS DRAT external replay",
                    "finding": "ok"
                }
            ]
        });

        let error = proof_findings_from_summary_json(&summary).expect_err("wrong summary scope");

        assert!(
            error.contains("scope=\"full-replacement\""),
            "unexpected error: {error}"
        );
    }

    #[test]
    fn proof_findings_reports_failed_summary_verdict() {
        let summary = json!({
            "schema": "ay-z3-replacement-audit/v1",
            "scope": "full-replacement",
            "verdict": "fail",
            "failed": 2,
            "proof_failed": 0,
            "full_replacement_ready": true,
            "scoped_cli_ready": true,
            "proof_inventory": [
                {
                    "status": "pass",
                    "surface": "DIMACS DRAT external replay",
                    "finding": "ok"
                }
            ]
        });

        let findings =
            proof_findings_from_summary_json(&summary).expect("well-formed failed summary");

        assert_eq!(
            findings,
            vec![
                (
                    "fail".to_string(),
                    "z3-audit summary verdict".to_string(),
                    "verdict must be pass, got Some(String(\"fail\"))".to_string()
                ),
                (
                    "fail".to_string(),
                    "z3-audit summary failed count".to_string(),
                    "failed must be 0, got 2".to_string()
                )
            ]
        );
    }

    #[test]
    fn build_commit_parser_reads_structured_version_output() {
        assert_eq!(
            parse_build_commit(
                "ay 0.10.0+build.1.abcdef@now\n\
                 build.version=0.10.0\n\
                 build.commit=abcdef123456\n\
                 build.datetime_utc=now\n"
            ),
            Some("abcdef123456".to_string())
        );
        assert_eq!(parse_build_commit("ay without structured commit\n"), None);
    }
}
