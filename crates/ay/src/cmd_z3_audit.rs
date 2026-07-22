// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Z3 replacement claim audit command.

use anyhow::{Context, Result};
use clap::{Args, ValueEnum};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::{self, Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Output, Stdio};
use std::time::{SystemTime, UNIX_EPOCH};

const COMPAT_DOC: &str = "the development design notes";
const CLI_REFERENCE: &str = "the development design notes";
const COMPATIBILITY_INVENTORY_JSON: &str = include_str!("../z3-compatibility.json");
const COMPATIBILITY_INVENTORY_SCHEMA: &str = "ay-z3-compatibility-inventory/v1";
const WORKSPACE_MARKER: &str = "crates/ay/Cargo.toml";
const DEFAULT_REFERENCE_CACHE: &str = "tests/z3-audit/reference-cache.json";
const REFERENCE_CACHE_SCHEMA: &str = "ay-z3-audit-reference-cache/v1";
const SURFACE_EVIDENCE_SCHEMA: &str = "ay-z3-audit-replacement-surface-evidence/v1";
const SURFACE_EVIDENCE_KEY: &str = "replacement_surface_evidence";
const BASIC_SMT_TRANSCRIPT_ID: &str = "basic_qf_lia_model_transcript";
const BASIC_SMT_TRANSCRIPT_INPUT: &str = "(set-option :produce-models true)\n\
                                          (set-logic QF_LIA)\n\
                                          (declare-const x Int)\n\
                                          (assert (= x 1))\n\
                                          (check-sat)\n\
                                          (get-value (x))\n";
const CHC_CANARY_PROBLEM: &str = "benchmarks/chc/counter_safe_chccomp.smt2";
const LAUNCH_GATED_HEADING: &str = "## Release-Gated Compatibility Surface";
const BROADER_LEDGER_HEADING: &str = "## Broader Z3 Compatibility Honesty Ledger";
const C_API_FFI_SMOKE_ID: &str = "c_api_ffi_smoke";
const SMT_MODEL_VALIDATION_SMOKE_ID: &str = "smt_model_validation_smoke";
const SMT_REF_ONLY_EXAMPLE_LIMIT: usize = 3;
const MAX_CHC_MANIFEST_ARTIFACTS: usize = 4_096;
const MAX_CHC_ARTIFACT_BYTES: u64 = 64 * 1024 * 1024;
const MAX_CHC_TOTAL_ARTIFACT_BYTES: u64 = 256 * 1024 * 1024;
const SMTLIB_EVAL_IDS: &[&str] = &[
    "smt-local-suite",
    "smt-smtcomp-qf-lia",
    "smt-smtcomp-qf-lra",
    "smt-smtcomp-qf-bv",
    "smt-smtcomp-qf-abv",
    "smt-smtcomp-qf-uf",
    "smt-smtcomp-qf-alia",
    "smt-smtcomp-qf-auflia",
];

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub(crate) enum Z3AuditScope {
    /// Audit the scoped Z3-style CLI subset currently inventoried by ay.
    CliSubset,
    /// Audit the broad "ay is a full Z3 replacement" claim.
    FullReplacement,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
pub(crate) enum SmtRefreshPolicy {
    /// Run only SMT evals with no raw packet.
    Missing,
    /// Run SMT evals with missing, stale, or dirty raw packets.
    StaleOrMissing,
    /// Run every selected SMT eval.
    Always,
}

impl SmtRefreshPolicy {
    fn as_str(self) -> &'static str {
        match self {
            Self::Missing => "missing",
            Self::StaleOrMissing => "stale-or-missing",
            Self::Always => "always",
        }
    }
}

impl Z3AuditScope {
    fn as_str(self) -> &'static str {
        match self {
            Self::CliSubset => "cli-subset",
            Self::FullReplacement => "full-replacement",
        }
    }
}

#[derive(Args)]
#[command(after_help = "\
This command is a claim gate, not a benchmark runner replacement. By default it
audits the broad \"AY is a full Z3 replacement\" claim and exits non-zero until
every compatibility surface needed for that broad claim is Ready and smoke
checks pass. Use `--scope cli-subset` to audit only the explicitly inventoried
Z3-style CLI wrapper subset. By default the audit executes repository-reality,
CLI-regression, proof, and Alethe replay checks so the tables report observed
pass/fail results, not a TODO list. The human output and JSON include a
replacement surface table with numeric current/goal counts and a native proof
inventory; `Partial` is never the only CLI finding. Z3-derived baselines are
read from --reference-cache by default; refresh them explicitly with
--generate-reference-cache/--write-reference-cache. SMT eval evidence is read
from evals/results by default; use --refresh-smt-evidence to run missing/stale
SMT packets before the truth table is computed.")]
pub(crate) struct Z3AuditArgs {
    /// AY workspace root containing Cargo.toml and crates/ay/Cargo.toml.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// ay binary to smoke-test. Defaults to the running executable.
    #[arg(long)]
    ay: Option<PathBuf>,

    /// Z3 binary used for transcript comparison.
    #[arg(long, default_value = "z3")]
    z3: String,

    /// Cached Z3 baseline references consumed by the default audit.
    #[arg(long, value_name = "FILE", default_value = DEFAULT_REFERENCE_CACHE)]
    reference_cache: PathBuf,

    /// Generate cached Z3 baseline references with --z3 and exit.
    #[arg(
        long = "write-reference-cache",
        visible_alias = "generate-reference-cache",
        value_name = "FILE"
    )]
    write_reference_cache: Option<PathBuf>,

    /// Run missing/stale SMT-LIB eval packets before computing the audit table.
    #[arg(long)]
    refresh_smt_evidence: bool,

    /// Print the planned SMT evidence refresh command and exit without running it.
    #[arg(long)]
    smt_refresh_dry_run: bool,

    /// Which selected SMT evals should be refreshed.
    #[arg(long, value_enum, default_value_t = SmtRefreshPolicy::StaleOrMissing)]
    smt_refresh_policy: SmtRefreshPolicy,

    /// SMT eval id to refresh; repeatable. Defaults to every SMT-LIB audit eval.
    #[arg(long = "smt-eval", value_name = "EVAL_ID")]
    smt_eval: Vec<String>,

    /// Override SMT refresh timeout seconds passed to `ay bench run`.
    #[arg(long)]
    smt_timeout: Option<f64>,

    /// Override SMT refresh runs passed to `ay bench run`.
    #[arg(long, value_parser = clap::value_parser!(u32).range(1..))]
    smt_runs: Option<u32>,

    /// Reference solver passed to SMT refresh; defaults to --z3.
    #[arg(long, value_name = "PATH")]
    smt_reference_solver: Option<String>,

    /// Claim scope to audit.
    #[arg(long, value_enum, default_value_t = Z3AuditScope::FullReplacement)]
    scope: Z3AuditScope,

    /// Deprecated compatibility flag; the repository reality gate runs by default.
    #[arg(long)]
    run_doc_reality: bool,

    /// Deprecated compatibility flag; the Z3 CLI regression test runs by default.
    #[arg(long)]
    run_cli_tests: bool,

    /// Deprecated compatibility flag; native proof regression commands run by default.
    #[arg(long)]
    run_proof_tests: bool,

    /// Deprecated compatibility flag; SMT Alethe external replay runs by default.
    #[arg(long)]
    run_alethe_replay: bool,

    /// Suppress default repository/Cargo/proof commands unless a specific --run-* flag is set.
    #[arg(long)]
    inventory_only: bool,

    /// External Alethe checker command for --run-alethe-replay.
    #[arg(long, default_value = "carcara")]
    alethe_checker: String,

    /// SMT-LIB problem used by --run-alethe-replay.
    #[arg(
        long,
        default_value = "tests/fixtures/proof/smt_alethe_qf_uf_transitivity_not_eq.smt2"
    )]
    alethe_problem: PathBuf,

    /// Directory for proof artifacts created by --run-alethe-replay.
    #[arg(long, value_name = "DIR")]
    proof_work_dir: Option<PathBuf>,

    /// Write machine-readable ay-z3-replacement-audit/v1 JSON.
    #[arg(long, value_name = "FILE")]
    summary_json: Option<PathBuf>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CheckStatus {
    Pass,
    Fail,
    FailTimeout,
    FailUnknown,
    FailError,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SmtEvalPacketState {
    Missing,
    Current,
    Stale,
    Dirty,
    StaleDirty,
}

impl SmtEvalPacketState {
    fn as_str(self) -> &'static str {
        match self {
            Self::Missing => "missing",
            Self::Current => "current",
            Self::Stale => "stale",
            Self::Dirty => "dirty",
            Self::StaleDirty => "stale_dirty",
        }
    }
}

impl CheckStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::Pass => "pass",
            Self::Fail => "fail",
            Self::FailTimeout => "fail_timeout",
            Self::FailUnknown => "fail_unknown",
            Self::FailError => "fail_error",
        }
    }

    fn is_pass(self) -> bool {
        self == Self::Pass
    }

    fn is_failure(self) -> bool {
        !self.is_pass()
    }

    fn parse(value: &str) -> Result<Self> {
        match value {
            "pass" => Ok(Self::Pass),
            "fail" => Ok(Self::Fail),
            "fail_timeout" => Ok(Self::FailTimeout),
            "fail_unknown" => Ok(Self::FailUnknown),
            "fail_error" => Ok(Self::FailError),
            _ => anyhow::bail!("unknown check status `{value}`"),
        }
    }
}

struct AuditCheck {
    id: &'static str,
    status: CheckStatus,
    finding: String,
    command: Option<String>,
}

impl AuditCheck {
    fn pass(id: &'static str, finding: impl Into<String>) -> Self {
        Self {
            id,
            status: CheckStatus::Pass,
            finding: finding.into(),
            command: None,
        }
    }

    fn fail(id: &'static str, finding: impl Into<String>) -> Self {
        Self {
            id,
            status: CheckStatus::Fail,
            finding: finding.into(),
            command: None,
        }
    }

    fn with_command(mut self, command: impl Into<String>) -> Self {
        self.command = Some(command.into());
        self
    }

    fn to_json(&self) -> Value {
        json!({
            "id": self.id,
            "status": self.status.as_str(),
            "finding": self.finding,
            "command": self.command,
        })
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq)]
#[serde(deny_unknown_fields)]
struct MatrixRow {
    surface: String,
    status: String,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompatibilityClaims {
    universal_drop_in_replacement: bool,
    full_z3_cli_compatibility: bool,
}

#[derive(Debug, Deserialize)]
#[serde(deny_unknown_fields)]
struct CompatibilityInventory {
    schema: String,
    claims: CompatibilityClaims,
    cli_subset: Vec<MatrixRow>,
    full_replacement: Vec<MatrixRow>,
}

struct SurfaceSpec {
    id: &'static str,
    surface: &'static str,
    goal: &'static str,
    missing: &'static str,
    command: &'static str,
}

struct AuditSurface {
    id: &'static str,
    surface: String,
    status: CheckStatus,
    current: String,
    goal: String,
    missing: String,
    command: Option<String>,
    source: Option<String>,
    source_status: Option<String>,
}

impl AuditSurface {
    fn to_json(&self) -> Value {
        json!({
            "id": self.id,
            "surface": self.surface,
            "status": self.status.as_str(),
            "current": self.current,
            "goal": self.goal,
            "missing": self.missing,
            "command": self.command,
            "source": self.source,
            "source_status": self.source_status,
        })
    }
}

struct ProofInventoryRow {
    id: &'static str,
    surface: &'static str,
    status: CheckStatus,
    current: String,
    goal: String,
    command: String,
    finding: String,
}

impl ProofInventoryRow {
    fn fail(
        id: &'static str,
        surface: &'static str,
        current: impl Into<String>,
        goal: impl Into<String>,
        command: impl Into<String>,
        finding: impl Into<String>,
    ) -> Self {
        Self {
            id,
            surface,
            status: CheckStatus::Fail,
            current: current.into(),
            goal: goal.into(),
            command: command.into(),
            finding: finding.into(),
        }
    }

    fn pass(
        id: &'static str,
        surface: &'static str,
        current: impl Into<String>,
        goal: impl Into<String>,
        command: impl Into<String>,
        finding: impl Into<String>,
    ) -> Self {
        Self {
            id,
            surface,
            status: CheckStatus::Pass,
            current: current.into(),
            goal: goal.into(),
            command: command.into(),
            finding: finding.into(),
        }
    }

    fn to_json(&self) -> Value {
        json!({
            "id": self.id,
            "surface": self.surface,
            "status": self.status.as_str(),
            "current": self.current,
            "goal": self.goal,
            "command": self.command,
            "finding": self.finding,
        })
    }
}

#[derive(Clone, Debug)]
struct ReferenceCache {
    path: PathBuf,
    z3_version: String,
    basic_smt_transcript: CachedTranscript,
    chc_obligations: CachedChcObligations,
    surface_evidence: BTreeMap<String, CachedSurfaceEvidence>,
}

#[derive(Clone, Debug)]
struct CachedSurfaceEvidence {
    status: CheckStatus,
    current: String,
    goal: String,
    missing: String,
    command: String,
    source: String,
}

#[derive(Clone, Debug)]
struct CachedTranscript {
    input_sha256: String,
    status_code: Option<i32>,
    stdout: String,
    stderr: String,
}

#[derive(Clone, Debug)]
struct CachedChcObligations {
    problem_sha256: String,
    obligations: BTreeMap<String, CachedObligation>,
}

#[derive(Clone, Debug)]
struct SmtRefreshPlan {
    evals_to_run: Vec<String>,
    selected: Vec<String>,
    skipped: Vec<String>,
    command: Option<String>,
    program: PathBuf,
    args: Vec<String>,
}

#[derive(Clone, Debug)]
struct CachedObligation {
    name: String,
    status_code: Option<i32>,
    stdout_first_line: String,
}

const BROADER_SURFACE_SPECS: &[SurfaceSpec] = &[
    SurfaceSpec {
        id: "public_source_build",
        surface: "Public source build",
        goal: "1/1 fresh unauthenticated release build packet with command, environment, ay --version, and artifact provenance",
        missing: "fresh public-clone release build evidence accepted by this audit",
        command: "cargo build --release --locked && ./target/release/ay --version",
    },
    SurfaceSpec {
        id: "smtlib_input",
        surface: "SMT-LIB input",
        goal: "1/1 current-code differential packet with per-logic solved/unknown/timeout/error/disagreement counts, 0 wrong answers, and reference_solved_missing=0",
        missing: "per-logic ay bench harvest plus ay bench verify evidence packet",
        command: "cargo build --release --locked -p ay --features bench --bin ay && ./target/release/ay bench run smt-local-suite smt-smtcomp-qf-lia smt-smtcomp-qf-lra smt-smtcomp-qf-bv smt-smtcomp-qf-abv smt-smtcomp-qf-uf smt-smtcomp-qf-alia smt-smtcomp-qf-auflia --ay ./target/release/ay --timeout 30 --reference-solver z3",
    },
    SurfaceSpec {
        id: "dimacs_cnf_input",
        surface: "DIMACS CNF input",
        goal: "1/1 current SAT-COMP-shaped packet with solved count, PAR-2, model/proof validity, 0 wrong answers, and 0 reference-only solves",
        missing: "clean SAT-COMP-shaped scoreboard packet from scripts/run_satcomp_matrix.sh",
        command: concat!(
            "competition/prepare_sat26_submission.sh --variant default --track main --ai-class regular ",
            "--proof-format lrat --stage-binary ./target/release/ay ",
            "--allow-local-runsh-preflight-binary --output \"$PWD/target/sat26-submission\" && ",
            "scripts/run_satcomp_matrix.sh --suite custom --instance benchmarks/sat/canary/tiny_sat.cnf ",
            "--expected sat --family canary --category sanity ",
            "--submission-root \"$PWD/target/sat26-submission\" --variants default --timeout-sec 30 ",
            "--proof-checker auto --reference-solver cadical=reference/cadical/build/cadical ",
            "--output the development design notes --soundness --fail-on-wrong",
        ),
    },
    SurfaceSpec {
        id: "chc_spacer_style_use",
        surface: "CHC / Spacer-style use",
        goal: "1/1 current CHC-COMP packet versus Z3 Spacer and Golem with certificate validation policy, 0 wrong answers, and 0 reference-only solves",
        missing: "clean CHC-COMP rerun and replayable certificate evidence",
        command: "for solver in z3 golem; do ./target/release/ay bench run chccomp-2025-extra-small-lia chccomp-2025-lia-lin --ay ./target/release/ay --timeout 30 --reference-solver \"$solver\"; done",
    },
    SurfaceSpec {
        id: "models",
        surface: "Models",
        goal: "1/1 model-validation packet with invalid_model_count=0 for every claimed SAT/model surface",
        missing: "model validation evidence with invalid-model counts promoted to hard failures",
        command: "ay gate solver && bash scripts/soundness_gate.sh",
    },
    SurfaceSpec {
        id: "rust_embedding",
        surface: "Rust embedding",
        goal: "1/1 downstream Rust consumer smoke packet from a clean public checkout",
        missing: "downstream consumer build/test evidence from public source",
        command: "./target/release/ay consumer-smoke run --full --temp-worktree all --worktree-ref origin/main --fetch-worktree-ref --json /tmp/ay-consumer-smoke.json",
    },
    SurfaceSpec {
        id: "c_api_ffi",
        surface: "C API / FFI",
        goal: "1/1 ABI/API smoke packet with examples, build instructions, consumer tests, and explicit libz3-compatibility decision",
        missing: "ay-ffi consumer smoke evidence and explicit libz3 API compatibility decision",
        command: "cargo test -p ay-ffi --release && cargo build -p ay-ffi --release --locked",
    },
];

pub(crate) fn run(args: &Z3AuditArgs) -> Result<i32> {
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    let ay = resolve_ay_binary(args.ay.as_deref())?;
    let compatibility_inventory = load_compatibility_inventory()?;
    let compat_doc = repo_root.join(COMPAT_DOC);
    let cli_reference = repo_root.join(CLI_REFERENCE);
    let reference_cache_path = resolve_repo_path(&repo_root, &args.reference_cache);

    let smt_refresh_requested = args.refresh_smt_evidence || args.smt_refresh_dry_run;
    if smt_refresh_requested && args.smt_refresh_dry_run {
        let plan = plan_smt_evidence_refresh(&repo_root, &ay, args, current_git_head(&repo_root))?;
        print_smt_refresh_dry_run(&plan, args.smt_refresh_policy);
        return Ok(0);
    }

    let smt_refresh_check = if smt_refresh_requested {
        let check = run_smt_evidence_refresh(&repo_root, &ay, args)?;
        if args.write_reference_cache.is_some() && check.status.is_failure() {
            anyhow::bail!(
                "SMT evidence refresh failed before reference-cache generation: {}",
                check.finding
            );
        }
        Some(check)
    } else {
        None
    };

    if let Some(path) = &args.write_reference_cache {
        let output_path = resolve_repo_path(&repo_root, path);
        let cache = generate_reference_cache(&repo_root, &ay, &args.z3)
            .with_context(|| format!("generate {}", output_path.display()))?;
        if let Some(parent) = output_path.parent() {
            fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
        }
        let payload = serde_json::to_string_pretty(&cache)?;
        fs::write(&output_path, format!("{payload}\n"))
            .with_context(|| format!("write {}", output_path.display()))?;
        println!("wrote_reference_cache={}", output_path.display());
        return Ok(0);
    }

    let (reference_cache, reference_cache_error) =
        match load_reference_cache(&repo_root, &reference_cache_path) {
            Ok(cache) => (Some(cache), None),
            Err(error) => (None, Some(error.to_string())),
        };
    let (surface_evidence, surface_evidence_error) =
        generate_live_surface_evidence_map(&repo_root, reference_cache.as_ref())
            .map(|evidence| (evidence, None))
            .unwrap_or_else(|error| (BTreeMap::new(), Some(error.to_string())));

    let mut checks = Vec::new();
    if let Some(check) = smt_refresh_check {
        checks.push(check);
    }
    checks.push(check_reference_cache(
        reference_cache.as_ref(),
        reference_cache_error.as_deref(),
        &reference_cache_path,
    ));
    checks.push(check_live_surface_evidence(
        &surface_evidence,
        surface_evidence_error.as_deref(),
    ));
    checks.push(check_cached_z3_version(
        reference_cache.as_ref(),
        reference_cache_error.as_deref(),
        &reference_cache_path,
        &args.z3,
    ));
    checks.push(check_tool_version(
        "ay_version",
        &ay.display().to_string(),
        &["--version"],
    ));
    checks.extend(check_compatibility_inventory(
        &compatibility_inventory,
        args.scope,
    ));
    checks.push(check_private_compatibility_doc(
        &compat_doc,
        &compatibility_inventory,
    ));
    checks.push(check_cli_reference(&cli_reference));
    checks.extend(run_builtin_smokes(
        &ay,
        reference_cache.as_ref(),
        reference_cache_error.as_deref(),
        &reference_cache_path,
    ));

    let launch_rows = &compatibility_inventory.cli_subset;
    let broader_rows = &compatibility_inventory.full_replacement;
    let run_doc_reality = !args.inventory_only || args.run_doc_reality;
    let run_cli_tests = !args.inventory_only || args.run_cli_tests;
    let run_proof_tests = !args.inventory_only || args.run_proof_tests;
    let run_alethe_replay = !args.inventory_only || args.run_alethe_replay;
    let run_c_api_ffi_smoke = !args.inventory_only;
    let execute_smt_model_validation_smoke =
        args.scope == Z3AuditScope::FullReplacement && !args.inventory_only;
    let proof_inventory = build_proof_inventory(
        args,
        &repo_root,
        &ay,
        reference_cache.as_ref(),
        reference_cache_error.as_deref(),
        &reference_cache_path,
        run_proof_tests,
        run_alethe_replay,
    );

    if run_doc_reality {
        checks.push(run_repo_command(
            "doc_reality",
            &repo_root,
            "bash scripts/check_doc_reality.sh",
            "bash",
            &["scripts/check_doc_reality.sh"],
        ));
    } else {
        checks.push(inventory_suppressed_check(
            "doc_reality",
            args.scope,
            "0/1 documentation reality gate executed by this audit",
            "inventory-only suppressed: bash scripts/check_doc_reality.sh",
        ));
    }

    if run_cli_tests {
        checks.push(run_repo_command(
            "z3_cli_compat_tests",
            &repo_root,
            "cargo test -p ay --features=\"cli\" --test group_cli z3_compat_args",
            "cargo",
            &[
                "test",
                "-p",
                "ay",
                "--features=cli",
                "--test",
                "group_cli",
                "z3_compat_args",
            ],
        ));
    } else {
        checks.push(inventory_suppressed_check(
            "z3_cli_compat_tests",
            args.scope,
            "0/1 targeted Z3 CLI regression test executed by this audit",
            "inventory-only suppressed: cargo test -p ay --features=\"cli\" --test group_cli z3_compat_args",
        ));
    }

    if run_c_api_ffi_smoke {
        checks.push(run_repo_command(
            C_API_FFI_SMOKE_ID,
            &repo_root,
            "cargo test -p ay-ffi --test group_ffi",
            "cargo",
            &["test", "-p", "ay-ffi", "--test", "group_ffi"],
        ));
    } else {
        checks.push(inventory_suppressed_check(
            C_API_FFI_SMOKE_ID,
            args.scope,
            "0/1 ay-ffi ABI/API consumer/header smoke run by this audit",
            "inventory-only suppressed: cargo test -p ay-ffi --test group_ffi",
        ));
    }

    if args.scope == Z3AuditScope::FullReplacement {
        if execute_smt_model_validation_smoke {
            checks.push(run_smt_model_validation_smoke(&repo_root));
        } else {
            checks.push(inventory_suppressed_check(
                SMT_MODEL_VALIDATION_SMOKE_ID,
                args.scope,
                "0/1 SMT model-validation smoke run by this audit",
                "inventory-only suppressed: cargo test -p ay-dpll --test group_theory_misc sat_validates_model -- --nocapture",
            ));
        }
    }

    let surfaces = build_surface_summary(
        args.scope,
        launch_rows,
        broader_rows,
        &proof_inventory,
        &checks,
        &surface_evidence,
    );

    let passed_checks = checks
        .iter()
        .filter(|check| check.status == CheckStatus::Pass)
        .count();
    let failed_checks = checks
        .iter()
        .filter(|check| check.status.is_failure())
        .count();
    let passed_surfaces = surfaces
        .iter()
        .filter(|surface| surface.status == CheckStatus::Pass)
        .count();
    let failed_surfaces = surfaces
        .iter()
        .filter(|surface| surface.status.is_failure())
        .count();
    let passed_proof_rows = proof_inventory
        .iter()
        .filter(|row| row.status == CheckStatus::Pass)
        .count();
    let failed_proof_rows = proof_inventory
        .iter()
        .filter(|row| row.status.is_failure())
        .count();
    let raw_failed = failed_checks + failed_surfaces;
    let failed = raw_failed;
    let verdict = if failed == 0 { "pass" } else { "fail" };
    let full_replacement_ready = full_replacement_ready(args.scope, failed, &surfaces);
    let scoped_cli_ready = checks
        .iter()
        .filter(|check| check.id != "broader_replacement_rows")
        .all(|check| !check.status.is_failure())
        && surfaces
            .iter()
            .find(|surface| surface.id == "z3_style_cli_subset")
            .is_some_and(|surface| surface.status == CheckStatus::Pass);

    let tool_inventory = external_tool_inventory(&repo_root, &args.z3, &args.alethe_checker);

    print_human_summary(
        args.scope,
        verdict,
        &repo_root,
        &ay,
        &args.z3,
        &reference_cache_path,
        passed_checks,
        failed_checks,
        passed_surfaces,
        failed_surfaces,
        passed_proof_rows,
        failed_proof_rows,
        full_replacement_ready,
        scoped_cli_ready,
        &surfaces,
        &proof_inventory,
        &checks,
        &tool_inventory,
    );

    if let Some(path) = &args.summary_json {
        let summary = json!({
            "schema": "ay-z3-replacement-audit/v1",
            "scope": args.scope.as_str(),
            "verdict": verdict,
            "full_replacement_ready": full_replacement_ready,
            "scoped_cli_ready": scoped_cli_ready,
            "repo_root": repo_root,
            "ay": ay,
            "z3": args.z3,
            "reference_cache": reference_cache_path,
            "reference_cache_loaded": reference_cache.is_some(),
            "reference_cache_error": reference_cache_error,
            "failed": failed,
            "raw_failed": raw_failed,
            "critical_surface_failed": failed_surfaces,
            "surface_passed": passed_surfaces,
            "surface_failed": failed_surfaces,
            "check_passed": passed_checks,
            "check_failed": failed_checks,
            "proof_passed": passed_proof_rows,
            "proof_failed": failed_proof_rows,
            "surfaces": surfaces.iter().map(AuditSurface::to_json).collect::<Vec<_>>(),
            "proof_inventory": proof_inventory.iter().map(ProofInventoryRow::to_json).collect::<Vec<_>>(),
            "checks": checks.iter().map(AuditCheck::to_json).collect::<Vec<_>>(),
            "external_tools": tool_inventory.iter().map(ToolStatus::to_json).collect::<Vec<_>>(),
        });
        let payload = serde_json::to_string_pretty(&summary)?;
        fs::write(path, format!("{payload}\n"))
            .with_context(|| format!("write {}", path.display()))?;
    }

    Ok(if failed == 0 { 0 } else { 1 })
}

fn resolve_repo_root(explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = explicit {
        return Ok(path.to_path_buf());
    }

    let mut dir = env::current_dir().context("resolve current directory")?;
    loop {
        if is_ay_workspace_root(&dir) {
            return Ok(dir);
        }
        if !dir.pop() {
            anyhow::bail!(
                "could not find AY workspace root containing Cargo.toml and {WORKSPACE_MARKER}"
            );
        }
    }
}

fn is_ay_workspace_root(path: &Path) -> bool {
    path.join("Cargo.toml").is_file() && path.join(WORKSPACE_MARKER).is_file()
}

fn resolve_ay_binary(explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = explicit {
        return Ok(path.to_path_buf());
    }
    env::current_exe().context("resolve current ay executable")
}

fn check_tool_version(id: &'static str, program: &str, args: &[&str]) -> AuditCheck {
    let command = std::iter::once(program.to_string())
        .chain(args.iter().map(|arg| (*arg).to_string()))
        .collect::<Vec<_>>()
        .join(" ");
    match ProcessCommand::new(program).args(args).output() {
        Ok(output) if output.status.success() => {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            let text = first_non_empty_line(&stdout)
                .or_else(|| first_non_empty_line(&stderr))
                .unwrap_or("version command produced no text");
            AuditCheck::pass(id, text.to_string()).with_command(command)
        }
        Ok(output) => AuditCheck::fail(
            id,
            format!(
                "version command exited {:?}: {}{}",
                output.status.code(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ),
        )
        .with_command(command),
        Err(error) => AuditCheck::fail(id, format!("failed to run version command: {error}"))
            .with_command(command),
    }
}

fn check_reference_cache(
    cache: Option<&ReferenceCache>,
    error: Option<&str>,
    path: &Path,
) -> AuditCheck {
    match cache {
        Some(cache) => AuditCheck::pass(
            "reference_cache",
            format!(
                "loaded {} with schema {REFERENCE_CACHE_SCHEMA}; basic_smt_input_sha256={} chc_obligations={} replacement_surface_rows={}",
                cache.path.display(),
                cache.basic_smt_transcript.input_sha256,
                cache.chc_obligations.obligations.len(),
                cache.surface_evidence.len()
            ),
        )
        .with_command(format!(
            "ay z3-audit --generate-reference-cache {} --z3 z3",
            path.display()
        )),
        None => AuditCheck::fail(
            "reference_cache",
            format!(
                "cached Z3 baseline unavailable at {}: {}; regenerate it with `ay z3-audit --generate-reference-cache {} --z3 <z3>`",
                path.display(),
                error.unwrap_or("unknown cache load error"),
                path.display()
            ),
        )
        .with_command(format!(
            "ay z3-audit --generate-reference-cache {} --z3 <z3>",
            path.display()
        )),
    }
}

fn check_live_surface_evidence(
    surface_evidence: &BTreeMap<String, CachedSurfaceEvidence>,
    error: Option<&str>,
) -> AuditCheck {
    if let Some(error) = error {
        AuditCheck::fail(
            "live_surface_evidence",
            format!("failed to compute current replacement surface evidence: {error}"),
        )
    } else {
        let passing = surface_evidence
            .values()
            .filter(|evidence| evidence.status == CheckStatus::Pass)
            .count();
        AuditCheck::pass(
            "live_surface_evidence",
            format!(
                "computed {passing}/{} current replacement surface evidence rows from repo artifacts",
                surface_evidence.len()
            ),
        )
    }
}

fn check_cached_z3_version(
    cache: Option<&ReferenceCache>,
    error: Option<&str>,
    path: &Path,
    z3: &str,
) -> AuditCheck {
    match cache {
        Some(cache) => AuditCheck::pass(
            "z3_version",
            format!(
                "cached baseline generated from {}; no live Z3 execution is required for this audit",
                cache.z3_version
            ),
        )
        .with_command(format!(
            "ay z3-audit --generate-reference-cache {} --z3 {z3}",
            path.display()
        )),
        None => AuditCheck::fail(
            "z3_version",
            format!(
                "cannot report Z3 baseline version without a valid reference cache: {}",
                error.unwrap_or("unknown cache load error")
            ),
        )
        .with_command(format!(
            "ay z3-audit --generate-reference-cache {} --z3 {z3}",
            path.display()
        )),
    }
}

fn selected_smt_eval_ids(args: &Z3AuditArgs) -> Result<Vec<String>> {
    let raw = if args.smt_eval.is_empty() {
        SMTLIB_EVAL_IDS
            .iter()
            .map(|eval_id| (*eval_id).to_string())
            .collect::<Vec<_>>()
    } else {
        args.smt_eval.clone()
    };
    let mut seen = BTreeSet::new();
    let mut evals = Vec::new();
    for eval_id in raw {
        if !SMTLIB_EVAL_IDS.contains(&eval_id.as_str()) {
            anyhow::bail!(
                "unknown --smt-eval `{eval_id}`; expected one of: {}",
                SMTLIB_EVAL_IDS.join(", ")
            );
        }
        if seen.insert(eval_id.clone()) {
            evals.push(eval_id);
        }
    }
    Ok(evals)
}

fn plan_smt_evidence_refresh(
    repo_root: &Path,
    ay: &Path,
    args: &Z3AuditArgs,
    current_head: Option<String>,
) -> Result<SmtRefreshPlan> {
    let eval_ids = selected_smt_eval_ids(args)?;
    let reference_solver = args
        .smt_reference_solver
        .clone()
        .unwrap_or_else(|| args.z3.clone());
    smt_evidence_refresh_plan(
        repo_root,
        ay,
        current_head.as_deref(),
        &eval_ids,
        args.smt_refresh_policy,
        args.smt_timeout,
        args.smt_runs,
        &reference_solver,
    )
}

fn smt_evidence_refresh_plan(
    repo_root: &Path,
    ay: &Path,
    current_head: Option<&str>,
    eval_ids: &[String],
    policy: SmtRefreshPolicy,
    timeout: Option<f64>,
    runs: Option<u32>,
    reference_solver: &str,
) -> Result<SmtRefreshPlan> {
    let mut evals_to_run = Vec::new();
    let mut selected = Vec::new();
    let mut skipped = Vec::new();
    for eval_id in eval_ids {
        let state = smt_eval_packet_state(repo_root, current_head, eval_id);
        let should_run = match policy {
            SmtRefreshPolicy::Always => true,
            SmtRefreshPolicy::Missing => state == SmtEvalPacketState::Missing,
            SmtRefreshPolicy::StaleOrMissing => state != SmtEvalPacketState::Current,
        };
        let label = format!("{eval_id}:{}", state.as_str());
        if should_run {
            evals_to_run.push(eval_id.clone());
            selected.push(label);
        } else {
            skipped.push(label);
        }
    }

    let mut bench_args = Vec::new();
    let command = if evals_to_run.is_empty() {
        None
    } else {
        bench_args.push("bench".to_string());
        bench_args.push("run".to_string());
        bench_args.extend(evals_to_run.iter().cloned());
        bench_args.push("--ay".to_string());
        bench_args.push(ay.display().to_string());
        if let Some(timeout) = timeout {
            bench_args.push("--timeout".to_string());
            bench_args.push(timeout.to_string());
        }
        if let Some(runs) = runs {
            bench_args.push("--runs".to_string());
            bench_args.push(runs.to_string());
        }
        bench_args.push("--reference-solver".to_string());
        bench_args.push(reference_solver.to_string());
        Some(render_command_line(ay, &bench_args))
    };

    Ok(SmtRefreshPlan {
        evals_to_run,
        selected,
        skipped,
        command,
        program: ay.to_path_buf(),
        args: bench_args,
    })
}

fn smt_eval_packet_state(
    repo_root: &Path,
    current_head: Option<&str>,
    eval_id: &str,
) -> SmtEvalPacketState {
    let Some((_, value)) = latest_eval_result(repo_root, eval_id) else {
        return SmtEvalPacketState::Missing;
    };
    let stale = !eval_result_current_for_repo(&value, repo_root, current_head);
    let dirty = value_bool(&value, "/environment/git_dirty").unwrap_or(false);
    if stale && dirty {
        return SmtEvalPacketState::StaleDirty;
    }
    if stale {
        return SmtEvalPacketState::Stale;
    }
    if dirty {
        return SmtEvalPacketState::Dirty;
    }
    SmtEvalPacketState::Current
}

fn print_smt_refresh_dry_run(plan: &SmtRefreshPlan, policy: SmtRefreshPolicy) {
    println!("smt_refresh_dry_run=true");
    println!("smt_refresh_policy={}", policy.as_str());
    println!("smt_refresh_selected={}", joined_or_none(&plan.selected));
    println!("smt_refresh_skipped={}", joined_or_none(&plan.skipped));
    println!(
        "smt_refresh_command={}",
        plan.command.as_deref().unwrap_or("none")
    );
}

fn run_smt_evidence_refresh(repo_root: &Path, ay: &Path, args: &Z3AuditArgs) -> Result<AuditCheck> {
    let plan = plan_smt_evidence_refresh(repo_root, ay, args, current_git_head(repo_root))?;
    let command = plan
        .command
        .clone()
        .unwrap_or_else(|| format!("{} bench run <none selected>", ay.display()));
    if plan.evals_to_run.is_empty() {
        return Ok(AuditCheck::pass(
            "smt_evidence_refresh",
            format!(
                "skipped SMT evidence refresh; policy={} selected=none skipped={}",
                args.smt_refresh_policy.as_str(),
                joined_or_none(&plan.skipped)
            ),
        )
        .with_command(command));
    }

    let output = ProcessCommand::new(&plan.program)
        .args(&plan.args)
        .current_dir(repo_root)
        .output();
    match output {
        Ok(output) if output.status.success() => Ok(AuditCheck::pass(
            "smt_evidence_refresh",
            format!(
                "ran SMT evidence refresh; policy={} selected={} skipped={}",
                args.smt_refresh_policy.as_str(),
                joined_or_none(&plan.selected),
                joined_or_none(&plan.skipped)
            ),
        )
        .with_command(command)),
        Ok(output) => Ok(AuditCheck::fail(
            "smt_evidence_refresh",
            format!(
                "SMT evidence refresh command exited {:?}; selected={}; stdout_tail={:?}; stderr_tail={:?}",
                output.status.code(),
                joined_or_none(&plan.selected),
                tail_text(&String::from_utf8_lossy(&output.stdout)),
                tail_text(&String::from_utf8_lossy(&output.stderr))
            ),
        )
        .with_command(command)),
        Err(error) => Ok(AuditCheck::fail(
            "smt_evidence_refresh",
            format!("failed to run SMT evidence refresh command: {error}"),
        )
        .with_command(command)),
    }
}

fn render_command_line(program: &Path, args: &[String]) -> String {
    std::iter::once(program.display().to_string())
        .chain(args.iter().cloned())
        .map(|part| shell_quote(&part))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(value: &str) -> String {
    if value
        .chars()
        .all(|ch| ch.is_ascii_alphanumeric() || matches!(ch, '/' | '.' | '_' | '-' | ':' | '='))
    {
        value.to_string()
    } else {
        format!("'{}'", value.replace('\'', "'\\''"))
    }
}

fn joined_or_none(values: &[String]) -> String {
    if values.is_empty() {
        "none".to_string()
    } else {
        values.join(",")
    }
}

fn inventory_suppressed_check(
    id: &'static str,
    scope: Z3AuditScope,
    current: &'static str,
    command: &'static str,
) -> AuditCheck {
    if scope == Z3AuditScope::FullReplacement {
        AuditCheck::fail(id, format!("{current}; {command}"))
    } else {
        AuditCheck::pass(
            id,
            format!("{current}; outside scoped cli-subset requirement; {command}"),
        )
    }
}

fn first_non_empty_line(text: &str) -> Option<&str> {
    text.lines().find(|line| !line.trim().is_empty())
}

fn load_compatibility_inventory() -> Result<CompatibilityInventory> {
    let inventory: CompatibilityInventory = serde_json::from_str(COMPATIBILITY_INVENTORY_JSON)
        .context("parse embedded Z3 compatibility inventory")?;
    if inventory.schema != COMPATIBILITY_INVENTORY_SCHEMA {
        anyhow::bail!(
            "embedded Z3 compatibility inventory schema mismatch: expected {COMPATIBILITY_INVENTORY_SCHEMA}, got {}",
            inventory.schema
        );
    }
    Ok(inventory)
}

fn inventory_row_errors(rows: &[MatrixRow]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut errors = Vec::new();
    for row in rows {
        if row.surface.trim().is_empty() {
            errors.push("row has an empty surface".to_string());
        } else if !seen.insert(row.surface.as_str()) {
            errors.push(format!("duplicate surface: {}", row.surface));
        }
        if row.status.trim().is_empty() {
            errors.push(format!("{} has an empty status", row.surface));
        }
    }
    errors
}

fn check_compatibility_inventory(
    inventory: &CompatibilityInventory,
    scope: Z3AuditScope,
) -> Vec<AuditCheck> {
    let mut checks = Vec::new();
    checks.push(AuditCheck::pass(
        "compatibility_inventory",
        format!(
            "loaded embedded {COMPATIBILITY_INVENTORY_SCHEMA} inventory with {} scoped CLI rows and {} full-replacement rows",
            inventory.cli_subset.len(),
            inventory.full_replacement.len()
        ),
    ));

    let launch_rows = &inventory.cli_subset;
    if launch_rows.is_empty() {
        checks.push(AuditCheck::fail(
            "launch_gated_rows",
            "embedded scoped CLI compatibility inventory has no rows",
        ));
    } else {
        let malformed = inventory_row_errors(launch_rows);
        let non_ready = non_ready_rows(launch_rows);
        if malformed.is_empty() && non_ready.is_empty() {
            checks.push(AuditCheck::pass(
                "launch_gated_rows",
                format!("{} embedded scoped CLI rows are Ready", launch_rows.len()),
            ));
        } else {
            checks.push(AuditCheck::fail(
                "launch_gated_rows",
                format!(
                    "invalid scoped CLI inventory: malformed={}; non_ready={}",
                    joined_or_none(&malformed),
                    joined_or_none(&non_ready)
                ),
            ));
        }
    }

    let broader_rows = &inventory.full_replacement;
    let broader_malformed = inventory_row_errors(broader_rows);
    let broader_non_ready = non_ready_rows(broader_rows);
    let broader_non_passing = non_passing_rows(broader_rows);
    if broader_rows.is_empty() {
        checks.push(AuditCheck::fail(
            "broader_replacement_rows",
            "embedded full-replacement compatibility inventory has no rows",
        ));
    } else if !broader_malformed.is_empty() {
        checks.push(AuditCheck::fail(
            "broader_replacement_rows",
            format!(
                "invalid full-replacement inventory rows: {}",
                broader_malformed.join("; ")
            ),
        ));
    } else {
        if broader_non_passing.is_empty() {
            checks.push(AuditCheck::pass(
                "broader_replacement_rows",
                format!(
                    "{} embedded full-replacement rows are Ready",
                    broader_rows.len()
                ),
            ));
        } else if scope == Z3AuditScope::FullReplacement {
            checks.push(AuditCheck::pass(
                "broader_replacement_rows",
                format!(
                    "loaded {} full-replacement rows; replacement surface evidence table owns pass/fail truth; inventory rows still non-Ready: {}",
                    broader_rows.len(),
                    broader_non_passing.join("; ")
                ),
            ));
        } else {
            checks.push(AuditCheck::pass(
                "broader_replacement_rows",
                format!(
                    "outside cli-subset claim; full-replacement rows that still need evidence: {}",
                    broader_non_passing.join("; ")
                ),
            ));
        }
    }

    let has_scoped_disclaimer = !inventory.claims.universal_drop_in_replacement
        && !inventory.claims.full_z3_cli_compatibility;
    let disclaimer_required = scope == Z3AuditScope::CliSubset || !broader_non_ready.is_empty();
    if has_scoped_disclaimer {
        checks.push(AuditCheck::pass(
            "honesty_disclaimer",
            "embedded inventory explicitly rejects universal drop-in and full-CLI claims",
        ));
    } else if disclaimer_required {
        checks.push(AuditCheck::fail(
            "honesty_disclaimer",
            "embedded inventory makes a broad Z3 replacement claim while required surfaces remain scoped or non-Ready",
        ));
    } else {
        checks.push(AuditCheck::pass(
            "honesty_disclaimer",
            "broader rows are Ready, so the scoped-subset disclaimer is no longer required",
        ));
    }

    checks
}

fn check_private_compatibility_doc(path: &Path, inventory: &CompatibilityInventory) -> AuditCheck {
    let text = match fs::read_to_string(path) {
        Ok(text) => text,
        Err(error) if error.kind() == io::ErrorKind::NotFound => {
            return AuditCheck::pass(
                "compatibility_doc",
                "private compatibility prose is not shipped; embedded inventory is authoritative",
            );
        }
        Err(error) => {
            return AuditCheck::fail(
                "compatibility_doc",
                format!("failed to read optional {}: {error}", path.display()),
            );
        }
    };

    let launch_rows = matrix_rows(&text, LAUNCH_GATED_HEADING);
    let broader_rows = matrix_rows(&text, BROADER_LEDGER_HEADING);
    let has_scoped_disclaimer = text.contains("not yet a universal drop-in replacement for Z3")
        && text.contains("not full Z3 CLI compatibility");
    if launch_rows == inventory.cli_subset
        && broader_rows == inventory.full_replacement
        && (inventory.claims.universal_drop_in_replacement || has_scoped_disclaimer)
    {
        AuditCheck::pass(
            "compatibility_doc",
            format!(
                "optional private compatibility prose matches the embedded inventory: {}",
                path.display()
            ),
        )
    } else {
        AuditCheck::fail(
            "compatibility_doc",
            format!(
                "optional private compatibility prose does not match the embedded inventory: {}",
                path.display()
            ),
        )
    }
}

fn check_cli_reference(path: &Path) -> AuditCheck {
    match fs::read_to_string(path) {
        Ok(text)
            if text.contains("not a universal drop-in replacement claim for Z3")
                && text.contains("A supported flag subset is not full Z3 CLI compatibility.") =>
        {
            AuditCheck::pass(
                "cli_reference_scope",
                "CLI reference scopes the Z3-style subset and avoids full-replacement wording",
            )
        }
        Ok(_) => AuditCheck::fail(
            "cli_reference_scope",
            "CLI reference does not preserve the scoped Z3-compatibility disclaimer",
        ),
        Err(error) if error.kind() == io::ErrorKind::NotFound => AuditCheck::pass(
            "cli_reference_scope",
            "private CLI reference is not shipped; embedded compatibility claim scope is authoritative",
        ),
        Err(error) => AuditCheck::fail(
            "cli_reference_scope",
            format!("failed to read optional {}: {error}", path.display()),
        ),
    }
}

fn section_lines<'a>(text: &'a str, heading: &str) -> Vec<&'a str> {
    let mut in_section = false;
    let mut rows = Vec::new();
    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed == heading {
            in_section = true;
            continue;
        }
        if in_section && trimmed.starts_with("## ") {
            break;
        }
        if in_section {
            rows.push(line);
        }
    }
    rows
}

fn matrix_rows(text: &str, heading: &str) -> Vec<MatrixRow> {
    section_lines(text, heading)
        .into_iter()
        .filter_map(parse_matrix_row)
        .collect()
}

fn parse_matrix_row(line: &str) -> Option<MatrixRow> {
    let trimmed = line.trim();
    if !trimmed.starts_with('|') || !trimmed.ends_with('|') {
        return None;
    }
    if trimmed.contains("---") || trimmed.starts_with("| Surface |") {
        return None;
    }
    let cells = trimmed
        .trim_matches('|')
        .split('|')
        .map(str::trim)
        .collect::<Vec<_>>();
    if cells.len() < 2 {
        return None;
    }
    Some(MatrixRow {
        surface: cells[0].to_string(),
        status: cells[1].to_string(),
    })
}

fn non_ready_rows(rows: &[MatrixRow]) -> Vec<String> {
    rows.iter()
        .filter(|row| row.status != "Ready")
        .map(|row| format!("{}={}", row.surface, row.status))
        .collect()
}

fn status_is_audit_pass(status: Option<&str>) -> bool {
    matches!(status, Some("Ready"))
}

fn non_passing_rows(rows: &[MatrixRow]) -> Vec<String> {
    rows.iter()
        .filter(|row| !status_is_audit_pass(Some(row.status.as_str())))
        .map(|row| format!("{}={}", row.surface, row.status))
        .collect()
}

fn build_surface_summary(
    scope: Z3AuditScope,
    launch_rows: &[MatrixRow],
    broader_rows: &[MatrixRow],
    proof_inventory: &[ProofInventoryRow],
    checks: &[AuditCheck],
    surface_evidence: &BTreeMap<String, CachedSurfaceEvidence>,
) -> Vec<AuditSurface> {
    let mut surfaces = Vec::new();
    surfaces.push(cli_subset_surface(launch_rows, checks));
    if scope == Z3AuditScope::CliSubset {
        return surfaces;
    }

    let mut inserted_proof_surface = false;
    for spec in BROADER_SURFACE_SPECS {
        if spec.id == "rust_embedding" {
            surfaces.push(unsat_proof_surface(broader_rows, proof_inventory));
            inserted_proof_surface = true;
        }
        let evidence = surface_evidence.get(spec.id);
        if spec.id == "c_api_ffi" {
            surfaces.push(c_api_ffi_surface(spec, broader_rows, checks, evidence));
        } else if spec.id == "models" {
            surfaces.push(models_surface(spec, broader_rows, checks, evidence));
        } else {
            surfaces.push(broader_surface(spec, broader_rows, None, evidence));
        }
    }
    if !inserted_proof_surface {
        surfaces.push(unsat_proof_surface(broader_rows, proof_inventory));
    }

    surfaces
}

fn full_replacement_ready(scope: Z3AuditScope, failed: usize, surfaces: &[AuditSurface]) -> bool {
    scope == Z3AuditScope::FullReplacement
        && failed == 0
        && surfaces
            .iter()
            .all(|surface| surface.status == CheckStatus::Pass)
}

fn c_api_ffi_current(checks: &[AuditCheck]) -> Option<String> {
    let check = checks.iter().find(|check| check.id == C_API_FFI_SMOKE_ID)?;
    Some(match check.status {
        CheckStatus::Pass => {
            "1/1 ay-ffi ABI/API consumer/header smoke passed in this audit".to_string()
        }
        _ => format!(
            "0/1 ay-ffi ABI/API consumer/header smoke passed in this audit ({})",
            check.finding
        ),
    })
}

fn cli_subset_surface(launch_rows: &[MatrixRow], checks: &[AuditCheck]) -> AuditSurface {
    let ready = launch_rows
        .iter()
        .filter(|row| row.status == "Ready")
        .count();
    let total = launch_rows.len();
    let smoke_ids = [
        "basic_smt_transcript",
        "z3_param_discovery_smoke",
        "unsupported_z3_option_smoke",
    ];
    let smoke_passed = smoke_ids
        .iter()
        .filter(|id| {
            checks
                .iter()
                .find(|check| check.id == **id)
                .is_some_and(|check| check.status == CheckStatus::Pass)
        })
        .count();
    let non_ready = non_ready_rows(launch_rows);
    let failed_smokes = smoke_ids
        .iter()
        .filter(|id| {
            checks
                .iter()
                .find(|check| check.id == **id)
                .is_none_or(|check| check.status != CheckStatus::Pass)
        })
        .copied()
        .collect::<Vec<_>>();
    let mut missing = Vec::new();
    if total == 0 {
        missing.push("launch-gated compatibility matrix rows".to_string());
    } else if !non_ready.is_empty() {
        missing.push(format!("Ready launch rows for {}", non_ready.join("; ")));
    }
    if !failed_smokes.is_empty() {
        missing.push(format!(
            "passing smoke checks for {}",
            failed_smokes.join(", ")
        ));
    }

    AuditSurface {
        id: "z3_style_cli_subset",
        surface: "Z3-style CLI subset".to_string(),
        status: if total > 0 && ready == total && smoke_passed == smoke_ids.len() {
            CheckStatus::Pass
        } else {
            CheckStatus::Fail
        },
        current: format!(
            "{ready}/{total} launch rows Ready; {smoke_passed}/{} built-in smokes pass",
            smoke_ids.len()
        ),
        goal: format!(
            "{total}/{total} launch rows Ready; {}/{} built-in smokes pass",
            smoke_ids.len(),
            smoke_ids.len()
        ),
        missing: if missing.is_empty() {
            "none".to_string()
        } else {
            missing.join("; ")
        },
        command: Some("ay z3-audit --scope cli-subset".to_string()),
        source: None,
        source_status: None,
    }
}

fn broader_surface(
    spec: &SurfaceSpec,
    broader_rows: &[MatrixRow],
    current_override: Option<String>,
    evidence: Option<&CachedSurfaceEvidence>,
) -> AuditSurface {
    let source_status = broader_rows
        .iter()
        .find(|row| row.surface == spec.surface)
        .map(|row| row.status.clone());
    if let Some(evidence) = evidence {
        return AuditSurface {
            id: spec.id,
            surface: spec.surface.to_string(),
            status: evidence.status,
            current: current_override.unwrap_or_else(|| evidence.current.clone()),
            goal: if evidence.goal.is_empty() {
                spec.goal.to_string()
            } else {
                evidence.goal.clone()
            },
            missing: if evidence.status == CheckStatus::Pass {
                "none".to_string()
            } else {
                evidence.missing.clone()
            },
            command: Some(if evidence.command.is_empty() {
                spec.command.to_string()
            } else {
                evidence.command.clone()
            }),
            source: Some(evidence.source.clone()),
            source_status,
        };
    }
    let status_passes = status_is_audit_pass(source_status.as_deref());
    let missing = if status_passes {
        "none".to_string()
    } else if let Some(status) = &source_status {
        format!("{}; inventory status is {status}", spec.missing)
    } else {
        format!("{}; inventory row is missing", spec.missing)
    };
    let status = if status_passes {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };

    AuditSurface {
        id: spec.id,
        surface: spec.surface.to_string(),
        status,
        current: current_override.unwrap_or_else(|| {
            if source_status.as_deref() == Some("Ready") {
                "1/1 Ready in embedded compatibility inventory".to_string()
            } else {
                let inventory_status = source_status.as_deref().unwrap_or("missing");
                format!(
                    "0/1 Ready in embedded compatibility inventory (inventory status: {inventory_status})"
                )
            }
        }),
        goal: spec.goal.to_string(),
        missing,
        command: Some(spec.command.to_string()),
        source: None,
        source_status,
    }
}

fn c_api_ffi_surface(
    spec: &SurfaceSpec,
    broader_rows: &[MatrixRow],
    checks: &[AuditCheck],
    evidence: Option<&CachedSurfaceEvidence>,
) -> AuditSurface {
    let source_status = broader_rows
        .iter()
        .find(|row| row.surface == spec.surface)
        .map(|row| row.status.clone());
    if let Some(check) = checks.iter().find(|check| check.id == C_API_FFI_SMOKE_ID) {
        return AuditSurface {
            id: spec.id,
            surface: spec.surface.to_string(),
            status: check.status,
            current: c_api_ffi_current(checks).unwrap_or_else(|| {
                "0/1 ay-ffi ABI/API consumer/header smoke result available".to_string()
            }),
            goal: spec.goal.to_string(),
            missing: if check.status == CheckStatus::Pass {
                "none".to_string()
            } else {
                format!("ay-ffi smoke failed: {}", check.finding)
            },
            command: check
                .command
                .clone()
                .or_else(|| Some(spec.command.to_string())),
            source: Some(
                evidence
                    .map(|row| {
                        format!(
                            "live default z3-audit check; surface evidence source: {}",
                            row.source
                        )
                    })
                    .unwrap_or_else(|| "live default z3-audit check".to_string()),
            ),
            source_status,
        };
    }

    broader_surface(spec, broader_rows, c_api_ffi_current(checks), evidence)
}

fn models_surface(
    spec: &SurfaceSpec,
    broader_rows: &[MatrixRow],
    checks: &[AuditCheck],
    evidence: Option<&CachedSurfaceEvidence>,
) -> AuditSurface {
    let source_status = broader_rows
        .iter()
        .find(|row| row.surface == spec.surface)
        .map(|row| row.status.clone());
    if let Some(check) = checks
        .iter()
        .find(|check| check.id == SMT_MODEL_VALIDATION_SMOKE_ID)
    {
        return AuditSurface {
            id: spec.id,
            surface: spec.surface.to_string(),
            status: check.status,
            current: check.finding.clone(),
            goal: spec.goal.to_string(),
            missing: if check.status == CheckStatus::Pass {
                "none".to_string()
            } else {
                format!("default CLI SMT model validation failed: {}", check.finding)
            },
            command: check
                .command
                .clone()
                .or_else(|| Some(spec.command.to_string())),
            source: Some(
                evidence
                    .map(|row| {
                        format!(
                            "live default z3-audit check; surface evidence source: {}",
                            row.source
                        )
                    })
                    .unwrap_or_else(|| "live default z3-audit check".to_string()),
            ),
            source_status,
        };
    }

    broader_surface(spec, broader_rows, None, evidence)
}

fn unsat_proof_surface(
    broader_rows: &[MatrixRow],
    proof_inventory: &[ProofInventoryRow],
) -> AuditSurface {
    let checked = proof_inventory
        .iter()
        .filter(|row| row.status == CheckStatus::Pass)
        .count();
    let total = proof_inventory.len();
    let source_status = broader_rows
        .iter()
        .find(|row| row.surface == "UNSAT proofs")
        .map(|row| row.status.clone());
    let ready = checked == total && total > 0;
    let failed_rows = proof_inventory
        .iter()
        .filter(|row| row.status != CheckStatus::Pass)
        .map(|row| row.surface)
        .collect::<Vec<_>>();
    let status = if ready {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };
    AuditSurface {
        id: "unsat_proofs",
        surface: "UNSAT proofs".to_string(),
        status,
        current: format!(
            "{checked}/{total} proof/certificate rows pass in this audit; {}/{} fail",
            total.saturating_sub(checked),
            total
        ),
        goal: format!("{total}/{total} proof/certificate rows pass in the default CLI audit"),
        missing: if failed_rows.is_empty() {
            "none".to_string()
        } else {
            format!(
                "failed rows: {}",
                if failed_rows.is_empty() {
                    "none".to_string()
                } else {
                    failed_rows.join(", ")
                }
            )
        },
        command: Some("ay z3-audit --scope full-replacement".to_string()),
        source: Some("default z3-audit native proof inventory".to_string()),
        source_status,
    }
}

fn build_proof_inventory(
    args: &Z3AuditArgs,
    repo_root: &Path,
    ay: &Path,
    reference_cache: Option<&ReferenceCache>,
    reference_cache_error: Option<&str>,
    reference_cache_path: &Path,
    run_proof_tests: bool,
    run_alethe_replay: bool,
) -> Vec<ProofInventoryRow> {
    vec![
        dimacs_drat_row(run_proof_tests, repo_root),
        ay_sat_lrat_text_packet_row(run_proof_tests, repo_root),
        lrat_binary_external_row(run_proof_tests, repo_root),
        cli_post_solve_proof_row(run_proof_tests, repo_root),
        alethe_replay_row(args, repo_root, ay, run_alethe_replay),
        lean_replay_row(args, repo_root, ay, run_proof_tests),
        chc_certificate_replay_row(
            args,
            repo_root,
            ay,
            reference_cache,
            reference_cache_error,
            reference_cache_path,
            run_proof_tests,
        ),
    ]
}

fn dimacs_drat_row(run: bool, repo_root: &Path) -> ProofInventoryRow {
    let command = "cargo test -p ay-sat --test integration test_drat";
    let drat_trim = find_drat_trim();
    if drat_trim.is_none() {
        return ProofInventoryRow::fail(
            "dimacs_drat_external",
            "DIMACS DRAT external replay",
            "0/1 drat-trim executable available",
            "1/1 external DRAT replay command passes with drat-trim",
            command,
            "no genuine drat-trim found in DRAT_TRIM, PATH, or standard local tool paths \
             (a candidate must report `s VERIFIED` on a valid refutation and `s NOT VERIFIED` \
             on a bogus one; the checked-in bin/drat-trim exit-0 shim is intentionally not honored)",
        );
    }
    if !run {
        return ProofInventoryRow::fail(
            "dimacs_drat_external",
            "DIMACS DRAT external replay",
            "0/1 external DRAT replay command run by this audit",
            "1/1 external DRAT replay command passes with drat-trim",
            command,
            format!(
                "inventory-only mode suppressed execution; default z3-audit executes this row with drat-trim at {}",
                drat_trim.expect("checked is_some").display()
            ),
        );
    }

    proof_command_row(
        "dimacs_drat_external",
        "DIMACS DRAT external replay",
        command,
        repo_root,
        "1/1 external DRAT replay command passed",
        "1/1 external DRAT replay command passes with drat-trim",
        "0/1 external DRAT replay command passed",
    )
}

fn ay_sat_lrat_text_packet_row(run: bool, repo_root: &Path) -> ProofInventoryRow {
    let command = "cargo test -p ay-sat --test integration test_lrat";
    if !run {
        return ProofInventoryRow::fail(
            "ay_sat_lrat_text_packet",
            "ay-sat LRAT text corpus replay",
            "0/1 LRAT text corpus replay run by this audit",
            "1/1 ay-sat LRAT text corpus replay passes",
            rendered_repo_command("cargo", command),
            "inventory-only mode suppressed execution; default z3-audit executes the native LRAT text corpus replay",
        );
    }
    proof_command_row(
        "ay_sat_lrat_text_packet",
        "ay-sat LRAT text corpus replay",
        command,
        repo_root,
        "1/1 ay-sat LRAT text corpus replay passed",
        "1/1 ay-sat LRAT text corpus replay passes",
        "0/1 ay-sat LRAT text corpus replay passed",
    )
}

fn lrat_binary_external_row(run: bool, repo_root: &Path) -> ProofInventoryRow {
    let build_command = "cargo build -p ay-lrat-check --bin ay-lrat-check";
    let test_command = "cargo test -p ay-sat --test group_drat lrat_binary_external_php32";
    let command = format!(
        "{} && {}",
        rendered_repo_command("cargo", build_command),
        rendered_repo_command("cargo", test_command)
    );
    if !run {
        return ProofInventoryRow::fail(
            "lrat_binary_external",
            "Binary LRAT external replay",
            "0/2 binary LRAT checker build and external replay run by this audit",
            "2/2 binary LRAT checker build and external replay pass",
            command,
            "inventory-only mode suppressed execution; default z3-audit executes this binary LRAT external replay canary",
        );
    }
    let build = run_repo_command(
        "lrat_binary_external_build",
        repo_root,
        build_command,
        "cargo",
        &["build", "-p", "ay-lrat-check", "--bin", "ay-lrat-check"],
    );
    if build.status != CheckStatus::Pass {
        return ProofInventoryRow::fail(
            "lrat_binary_external",
            "Binary LRAT external replay",
            "0/2 binary LRAT checker build and external replay passed",
            "2/2 binary LRAT checker build and external replay pass",
            command,
            format!("checker build failed: {}", build.finding),
        );
    }

    let test = run_repo_command(
        "lrat_binary_external",
        repo_root,
        test_command,
        "cargo",
        &[
            "test",
            "-p",
            "ay-sat",
            "--test",
            "group_drat",
            "lrat_binary_external_php32",
        ],
    );
    if test.status == CheckStatus::Pass {
        ProofInventoryRow::pass(
            "lrat_binary_external",
            "Binary LRAT external replay",
            "2/2 binary LRAT checker build and external replay passed",
            "2/2 binary LRAT checker build and external replay pass",
            command,
            "checker build passed; binary LRAT external replay passed",
        )
    } else {
        ProofInventoryRow::fail(
            "lrat_binary_external",
            "Binary LRAT external replay",
            "1/2 binary LRAT checker build and external replay passed",
            "2/2 binary LRAT checker build and external replay pass",
            command,
            test.finding,
        )
    }
}

fn cli_post_solve_proof_row(run: bool, repo_root: &Path) -> ProofInventoryRow {
    let command = "cargo test -p ay --features=\"cli\" --test group_cli verify_proof_8771";
    if !run {
        return ProofInventoryRow::fail(
            "cli_drat_lrat_post_solve",
            "CLI DRAT/LRAT post-solve replay",
            "0/1 targeted CLI proof replay test run by this audit",
            "1/1 targeted CLI proof replay test passes",
            rendered_repo_command("cargo", command),
            "inventory-only mode suppressed execution; default z3-audit executes the targeted CLI replay test",
        );
    }
    proof_command_row(
        "cli_drat_lrat_post_solve",
        "CLI DRAT/LRAT post-solve replay",
        command,
        repo_root,
        "1/1 targeted CLI proof replay test passed",
        "1/1 targeted CLI proof replay test passes",
        "0/1 targeted CLI proof replay test passed",
    )
}

fn proof_command_row(
    id: &'static str,
    surface: &'static str,
    command: &'static str,
    repo_root: &Path,
    pass_current: &'static str,
    goal: &'static str,
    fail_current: &'static str,
) -> ProofInventoryRow {
    // `command` is the human-readable, shell-copy-pasteable form and may contain
    // shell quoting such as `--features="cli"`. Because `run_repo_command` spawns
    // the program directly (no shell), strip surrounding double quotes from each
    // token so cargo receives `--features=cli` rather than the literal feature
    // name `"cli"` (with quote characters), which does not exist. This mirrors the
    // split between displayed command and argv used by `run_repo_command` callers
    // such as the `z3_cli_compat_tests` row.
    let argv = command
        .split_whitespace()
        .map(strip_shell_quotes)
        .collect::<Vec<_>>();
    let argv_refs = argv.iter().map(String::as_str).collect::<Vec<_>>();
    let check = run_repo_command(id, repo_root, command, argv_refs[0], &argv_refs[1..]);
    let displayed_command = rendered_repo_command(argv_refs[0], command);
    if check.status == CheckStatus::Pass {
        ProofInventoryRow::pass(
            id,
            surface,
            pass_current,
            goal,
            displayed_command,
            check.finding,
        )
    } else {
        ProofInventoryRow::fail(
            id,
            surface,
            fail_current,
            goal,
            displayed_command,
            check.finding,
        )
    }
}

fn alethe_replay_row(
    args: &Z3AuditArgs,
    repo_root: &Path,
    ay: &Path,
    run: bool,
) -> ProofInventoryRow {
    let command = format!(
        "{} solve --proof <work-dir>/smt-alethe-proof.alethe {} && {} check <work-dir>/smt-alethe-proof.alethe {}",
        ay.display(),
        args.alethe_problem.display(),
        args.alethe_checker,
        args.alethe_problem.display()
    );
    if !run {
        return ProofInventoryRow::fail(
            "smt_alethe_external_replay",
            "SMT Alethe external replay",
            "0/1 external Alethe replay command run by this audit",
            "1/1 SMT Alethe proof emitted and accepted by an external checker",
            command,
            "inventory-only mode suppressed execution; default z3-audit emits and externally replays this Alethe proof; --run-alethe-replay re-enables this row with --inventory-only",
        );
    }

    let work_dir = resolve_work_dir(repo_root, args.proof_work_dir.as_deref());
    let problem = resolve_repo_path(repo_root, &args.alethe_problem);
    let proof = work_dir.join("smt-alethe-proof.alethe");
    if let Err(error) = fs::create_dir_all(&work_dir) {
        return ProofInventoryRow::fail(
            "smt_alethe_external_replay",
            "SMT Alethe external replay",
            "0/1 proof work directory created",
            "1/1 SMT Alethe proof emitted and accepted by an external checker",
            command,
            format!("failed to create {}: {error}", work_dir.display()),
        );
    }

    let proof_arg = proof.to_string_lossy().into_owned();
    let problem_arg = problem.to_string_lossy().into_owned();
    let emit = match run_command_capture(
        repo_root,
        ay,
        &["solve", "--proof", &proof_arg, &problem_arg],
    ) {
        Ok(output) => output,
        Err(error) => {
            return ProofInventoryRow::fail(
                "smt_alethe_external_replay",
                "SMT Alethe external replay",
                "0/1 SMT Alethe proof emitted",
                "1/1 SMT Alethe proof emitted and accepted by an external checker",
                command,
                format!("failed to run proof emission command: {error}"),
            );
        }
    };
    if !emit.status.success() || !proof.is_file() {
        return ProofInventoryRow::fail(
            "smt_alethe_external_replay",
            "SMT Alethe external replay",
            "0/1 SMT Alethe proof emitted",
            "1/1 SMT Alethe proof emitted and accepted by an external checker",
            command,
            format!(
                "proof emission failed: status={:?} proof_exists={} stdout_tail={:?} stderr_tail={:?}",
                emit.status.code(),
                proof.is_file(),
                tail_text(&String::from_utf8_lossy(&emit.stdout)),
                tail_text(&String::from_utf8_lossy(&emit.stderr))
            ),
        );
    }

    let replay = run_command_capture(
        repo_root,
        Path::new(&args.alethe_checker),
        &["check", &proof_arg, &problem_arg],
    );
    match replay {
        Ok(replay) if replay.status.success() => ProofInventoryRow::pass(
            "smt_alethe_external_replay",
            "SMT Alethe external replay",
            "1/1 SMT Alethe proof emitted and externally replayed",
            "1/1 SMT Alethe proof emitted and accepted by an external checker",
            command,
            format!("external replay passed; proof={}", proof.display()),
        ),
        Ok(replay) => ProofInventoryRow::fail(
            "smt_alethe_external_replay",
            "SMT Alethe external replay",
            "0/1 SMT Alethe proof externally replayed",
            "1/1 SMT Alethe proof emitted and accepted by an external checker",
            command,
            format!(
                "external replay failed: status={:?} stdout_tail={:?} stderr_tail={:?}",
                replay.status.code(),
                tail_text(&String::from_utf8_lossy(&replay.stdout)),
                tail_text(&String::from_utf8_lossy(&replay.stderr))
            ),
        ),
        Err(error) => ProofInventoryRow::fail(
            "smt_alethe_external_replay",
            "SMT Alethe external replay",
            "0/1 SMT Alethe proof externally replayed",
            "1/1 SMT Alethe proof emitted and accepted by an external checker",
            command,
            format!("failed to run external checker: {error}"),
        ),
    }
}

fn lean_replay_row(
    args: &Z3AuditArgs,
    repo_root: &Path,
    ay: &Path,
    run: bool,
) -> ProofInventoryRow {
    let command = format!(
        "{} solve --proof <work-dir>/lean-proof.lean4 --proof-format lean4 benchmarks/sat/canary/tiny_unsat.cnf && lean <work-dir>/lean-proof.lean4",
        ay.display()
    );
    if !run {
        return ProofInventoryRow::fail(
            "lean_replay",
            "Lean4 proof replay",
            "0/1 Lean proof replay run by this audit",
            "1/1 Lean4 proof emitted and accepted by Lean",
            command,
            "inventory-only mode suppressed execution; default z3-audit emits and replays a Lean4 proof canary",
        );
    }

    let Some(lean) = find_on_path("lean") else {
        return ProofInventoryRow::fail(
            "lean_replay",
            "Lean4 proof replay",
            "0/1 lean executable available",
            "1/1 Lean4 proof emitted and accepted by Lean",
            command,
            "lean was not found on PATH",
        );
    };

    let work_dir = resolve_work_dir(repo_root, args.proof_work_dir.as_deref()).join("lean");
    if let Err(error) = fs::create_dir_all(&work_dir) {
        return ProofInventoryRow::fail(
            "lean_replay",
            "Lean4 proof replay",
            "0/1 proof work directory created",
            "1/1 Lean4 proof emitted and accepted by Lean",
            command,
            format!("failed to create {}: {error}", work_dir.display()),
        );
    }

    let problem = repo_root.join("benchmarks/sat/canary/tiny_unsat.cnf");
    let proof = work_dir.join("lean-proof.lean4");
    let proof_arg = proof.to_string_lossy().into_owned();
    let problem_arg = problem.to_string_lossy().into_owned();
    let emit = match run_command_capture(
        repo_root,
        ay,
        &[
            "solve",
            "--proof",
            &proof_arg,
            "--proof-format",
            "lean4",
            &problem_arg,
        ],
    ) {
        Ok(output) => output,
        Err(error) => {
            return ProofInventoryRow::fail(
                "lean_replay",
                "Lean4 proof replay",
                "0/1 Lean4 proof emitted",
                "1/1 Lean4 proof emitted and accepted by Lean",
                command,
                format!("failed to run Lean proof emission command: {error}"),
            );
        }
    };
    if emit.status.code() != Some(20) || !proof.is_file() {
        return ProofInventoryRow::fail(
            "lean_replay",
            "Lean4 proof replay",
            "0/1 Lean4 proof emitted",
            "1/1 Lean4 proof emitted and accepted by Lean",
            command,
            format!(
                "proof emission failed: status={:?} proof_exists={} stdout_tail={:?} stderr_tail={:?}",
                emit.status.code(),
                proof.is_file(),
                tail_text(&String::from_utf8_lossy(&emit.stdout)),
                tail_text(&String::from_utf8_lossy(&emit.stderr))
            ),
        );
    }

    match run_command_capture(repo_root, &lean, &[&proof_arg]) {
        Ok(replay) if replay.status.success() => ProofInventoryRow::pass(
            "lean_replay",
            "Lean4 proof replay",
            "1/1 Lean4 proof emitted and replayed",
            "1/1 Lean4 proof emitted and accepted by Lean",
            command,
            format!("Lean replay passed; proof={}", proof.display()),
        ),
        Ok(replay) => ProofInventoryRow::fail(
            "lean_replay",
            "Lean4 proof replay",
            "0/1 Lean4 proof replayed",
            "1/1 Lean4 proof emitted and accepted by Lean",
            command,
            format!(
                "Lean replay failed: status={:?} stdout_tail={:?} stderr_tail={:?}",
                replay.status.code(),
                tail_text(&String::from_utf8_lossy(&replay.stdout)),
                tail_text(&String::from_utf8_lossy(&replay.stderr))
            ),
        ),
        Err(error) => ProofInventoryRow::fail(
            "lean_replay",
            "Lean4 proof replay",
            "0/1 Lean4 proof replayed",
            "1/1 Lean4 proof emitted and accepted by Lean",
            command,
            format!("failed to run Lean replay command: {error}"),
        ),
    }
}

fn chc_certificate_replay_row(
    args: &Z3AuditArgs,
    repo_root: &Path,
    ay: &Path,
    reference_cache: Option<&ReferenceCache>,
    reference_cache_error: Option<&str>,
    reference_cache_path: &Path,
    run: bool,
) -> ProofInventoryRow {
    let command = format!(
        "{} solve --chc --stats-json --proof <work-dir>/chc-certificate.smt2 {CHC_CANARY_PROBLEM} && ay z3-audit --reference-cache {}",
        ay.display(),
        reference_cache_path.display()
    );
    if !run {
        return ProofInventoryRow::fail(
            "chc_certificate_replay",
            "CHC certificate replay",
            "0/1 CHC certificate replay run by this audit",
            "1/1 CHC certificate emitted and all replay obligations are UNSAT",
            command,
            "inventory-only mode suppressed execution; default z3-audit emits CHC obligations and validates them against the cached Z3 UNSAT baseline",
        );
    }

    let work_dir = resolve_work_dir(repo_root, args.proof_work_dir.as_deref()).join("chc");
    if let Err(error) = fs::create_dir_all(&work_dir) {
        return ProofInventoryRow::fail(
            "chc_certificate_replay",
            "CHC certificate replay",
            "0/1 proof work directory created",
            "1/1 CHC certificate emitted and all replay obligations are UNSAT",
            command,
            format!("failed to create {}: {error}", work_dir.display()),
        );
    }

    let problem = repo_root.join(CHC_CANARY_PROBLEM);
    let certificate = work_dir.join("chc-certificate.smt2");
    let certificate_arg = certificate.to_string_lossy().into_owned();
    let problem_arg = problem.to_string_lossy().into_owned();
    let emit = match run_command_capture(
        repo_root,
        ay,
        &[
            "solve",
            "--chc",
            "--stats-json",
            "--proof",
            &certificate_arg,
            &problem_arg,
        ],
    ) {
        Ok(output) => output,
        Err(error) => {
            return ProofInventoryRow::fail(
                "chc_certificate_replay",
                "CHC certificate replay",
                "0/1 CHC certificate emitted",
                "1/1 CHC certificate emitted and all replay obligations are UNSAT",
                command,
                format!("failed to run CHC certificate emission command: {error}"),
            );
        }
    };
    if !emit.status.success() {
        return ProofInventoryRow::fail(
            "chc_certificate_replay",
            "CHC certificate replay",
            "0/1 CHC certificate emitted",
            "1/1 CHC certificate emitted and all replay obligations are UNSAT",
            command,
            format!(
                "certificate emission failed: status={:?} stdout_tail={:?} stderr_tail={:?}",
                emit.status.code(),
                tail_text(&String::from_utf8_lossy(&emit.stdout)),
                tail_text(&String::from_utf8_lossy(&emit.stderr))
            ),
        );
    }
    let emitted = match emitted_chc_artifacts(&emit, &certificate) {
        Ok(emitted) => emitted,
        Err(error) => {
            return ProofInventoryRow::fail(
                "chc_certificate_replay",
                "CHC certificate replay",
                "0/1 same-run CHC evidence manifest authenticated",
                "1/1 CHC certificate emitted and all replay obligations are UNSAT",
                command,
                format!("failed to authenticate emitted CHC artifacts: {error}"),
            );
        }
    };
    let obligations = emitted.obligations;

    let cache = match reference_cache {
        Some(cache) => cache,
        None => {
            return ProofInventoryRow::fail(
                "chc_certificate_replay",
                "CHC certificate replay",
                "0/1 cached CHC reference baseline loaded",
                "1/1 CHC certificate emitted and all replay obligations are UNSAT",
                command,
                format!(
                    "reference cache unavailable at {}: {}; regenerate with `ay z3-audit --generate-reference-cache {} --z3 {}`",
                    reference_cache_path.display(),
                    reference_cache_error.unwrap_or("unknown cache load error"),
                    reference_cache_path.display(),
                    args.z3
                ),
            );
        }
    };

    match validate_cached_chc_obligations(cache, &problem, &obligations) {
        Ok(matched) => ProofInventoryRow::pass(
            "chc_certificate_replay",
            "CHC certificate replay",
            format!("{matched}/{matched} CHC obligations matched cached UNSAT baseline"),
            "1/1 CHC certificate emitted and all replay obligations are UNSAT",
            command,
            format!(
                "CHC certificate replay passed from cache {}; certificate={} obligations={}",
                cache.path.display(),
                emitted.certificate.path.display(),
                matched
            ),
        ),
        Err(error) => ProofInventoryRow::fail(
            "chc_certificate_replay",
            "CHC certificate replay",
            format!(
                "0/{} CHC obligations matched cached UNSAT baseline",
                obligations.len()
            ),
            "1/1 CHC certificate emitted and all replay obligations are UNSAT",
            command,
            error.to_string(),
        ),
    }
}

fn resolve_repo_path(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    }
}

fn resolve_work_dir(repo_root: &Path, explicit: Option<&Path>) -> PathBuf {
    explicit.map_or_else(
        || env::temp_dir().join(format!("ay-z3-audit-proof-{}", std::process::id())),
        |path| resolve_repo_path(repo_root, path),
    )
}

#[derive(Debug)]
struct EmittedChcArtifacts {
    certificate: AuthenticatedChcArtifact,
    obligations: Vec<AuthenticatedChcArtifact>,
}

#[derive(Debug)]
struct AuthenticatedChcArtifact {
    path: PathBuf,
    bytes: Vec<u8>,
    sha256: String,
}

#[derive(Debug)]
struct ChcManifestArtifact {
    path: PathBuf,
    bytes: u64,
    sha256: String,
}

/// Resolve the exact artifacts named by the stats record from this solver
/// process. CHC obligation directories are intentionally unique per emission;
/// directory scans at a stable legacy pathname can therefore only find stale
/// evidence and must never be used as run authority.
fn emitted_chc_artifacts(
    output: &Output,
    expected_certificate: &Path,
) -> Result<EmittedChcArtifacts> {
    emitted_chc_artifacts_from_streams(&output.stdout, &output.stderr, expected_certificate)
}

fn emitted_chc_artifacts_from_streams(
    stdout: &[u8],
    stderr: &[u8],
    expected_certificate: &Path,
) -> Result<EmittedChcArtifacts> {
    let stats = unique_chc_stats_json(stdout, stderr)?;
    let manifest = field(&stats, "chc_evidence_manifest")?;
    let schema = string_field(manifest, "schema")?;
    if schema != "ay.chc-evidence-manifest/v1" {
        anyhow::bail!(
            "CHC evidence manifest schema mismatch: expected ay.chc-evidence-manifest/v1, got {schema}"
        );
    }

    let artifacts = field(manifest, "artifacts")?;
    let proof_entry = field(artifacts, "proof")?;
    if string_field(proof_entry, "status")? != "hash-bound" {
        anyhow::bail!("CHC evidence manifest proof is not hash-bound");
    }
    let proof = parse_chc_manifest_artifact(
        field(proof_entry, "artifact")?,
        "proof certificate",
        "proof-certificate",
    )?;

    let expected_parent = expected_certificate.parent().with_context(|| {
        format!(
            "expected CHC certificate {} has no parent",
            expected_certificate.display()
        )
    })?;
    let expected_parent = fs::canonicalize(expected_parent).with_context(|| {
        format!(
            "resolve expected CHC artifact parent {}",
            expected_parent.display()
        )
    })?;
    let certificate_name = expected_certificate.file_name().with_context(|| {
        format!(
            "expected CHC certificate {} has no file name",
            expected_certificate.display()
        )
    })?;
    let expected_physical_certificate = expected_parent.join(certificate_name);
    let certificate = validate_chc_manifest_file(&proof, "proof certificate")?;
    if certificate.path != expected_physical_certificate {
        anyhow::bail!(
            "CHC manifest proof path {} is not the requested same-run certificate {}",
            certificate.path.display(),
            expected_physical_certificate.display()
        );
    }

    let obligations_entry = field(artifacts, "replay_obligations")?;
    if string_field(obligations_entry, "status")? != "hash-bound" {
        anyhow::bail!("CHC evidence manifest replay obligations are not hash-bound");
    }
    let obligation_values = array_field(obligations_entry, "artifacts")?;
    if obligation_values.is_empty() {
        anyhow::bail!("CHC evidence manifest contains no replay obligations");
    }
    if obligation_values.len() > MAX_CHC_MANIFEST_ARTIFACTS {
        anyhow::bail!(
            "CHC evidence manifest contains {} replay obligations, exceeding the limit of {MAX_CHC_MANIFEST_ARTIFACTS}",
            obligation_values.len()
        );
    }

    let certificate_name = certificate_name.to_str().with_context(|| {
        format!(
            "CHC certificate file name is not UTF-8: {}",
            expected_physical_certificate.display()
        )
    })?;
    let obligation_dir_prefix = format!("{certificate_name}.chc-obligations-");
    let mut physical_obligations_parent: Option<PathBuf> = None;
    let mut unique_paths = BTreeSet::new();
    let mut obligations = Vec::with_capacity(obligation_values.len());
    let mut total_artifact_bytes = proof.bytes;
    for (index, value) in obligation_values.iter().enumerate() {
        let label = format!("replay obligation {index}");
        let kind = string_field(value, "kind")?;
        if kind.trim().is_empty() {
            anyhow::bail!("{label} descriptor has an empty obligation kind");
        }
        let artifact = parse_chc_manifest_artifact(value, &label, "replay-obligation")?;
        total_artifact_bytes = total_artifact_bytes
            .checked_add(artifact.bytes)
            .with_context(|| "CHC evidence manifest total byte length overflow")?;
        if total_artifact_bytes > MAX_CHC_TOTAL_ARTIFACT_BYTES {
            anyhow::bail!(
                "CHC evidence manifest declares {total_artifact_bytes} artifact bytes, exceeding the limit of {MAX_CHC_TOTAL_ARTIFACT_BYTES}"
            );
        }
        if artifact
            .path
            .extension()
            .and_then(|extension| extension.to_str())
            != Some("smt2")
        {
            anyhow::bail!(
                "{label} path is not an .smt2 file: {}",
                artifact.path.display()
            );
        }
        let raw_parent = artifact
            .path
            .parent()
            .with_context(|| format!("{label} path has no parent: {}", artifact.path.display()))?;
        let raw_parent_metadata = fs::symlink_metadata(raw_parent)
            .with_context(|| format!("inspect {label} parent {}", raw_parent.display()))?;
        if !raw_parent_metadata.file_type().is_dir() {
            anyhow::bail!(
                "{label} parent is not a physical directory: {}",
                raw_parent.display()
            );
        }
        let physical_parent = fs::canonicalize(raw_parent)
            .with_context(|| format!("resolve {label} parent {}", raw_parent.display()))?;
        if physical_parent.parent() != Some(expected_parent.as_path()) {
            anyhow::bail!(
                "{label} parent {} is outside the expected physical CHC run parent {}",
                physical_parent.display(),
                expected_parent.display()
            );
        }
        let parent_name = physical_parent
            .file_name()
            .and_then(|name| name.to_str())
            .with_context(|| {
                format!(
                    "{label} parent has no UTF-8 directory name: {}",
                    physical_parent.display()
                )
            })?;
        let suffix = parent_name
            .strip_prefix(&obligation_dir_prefix)
            .with_context(|| {
                format!(
                    "{label} parent {} does not use expected prefix {obligation_dir_prefix}",
                    physical_parent.display()
                )
            })?;
        let Some((pid, nonce)) = suffix.split_once('-') else {
            anyhow::bail!(
                "{label} parent {} lacks the expected pid-nonce suffix",
                physical_parent.display()
            );
        };
        if pid.is_empty()
            || nonce.is_empty()
            || !pid.bytes().all(|byte| byte.is_ascii_digit())
            || !nonce.bytes().all(|byte| byte.is_ascii_digit())
        {
            anyhow::bail!(
                "{label} parent {} has an invalid pid-nonce suffix",
                physical_parent.display()
            );
        }
        match physical_obligations_parent.as_ref() {
            Some(expected) if expected != &physical_parent => anyhow::bail!(
                "CHC manifest mixes replay obligation directories: {} and {}",
                expected.display(),
                physical_parent.display()
            ),
            None => physical_obligations_parent = Some(physical_parent),
            Some(_) => {}
        }

        let authenticated = validate_chc_manifest_file(&artifact, &label)?;
        if authenticated.path.parent() != physical_obligations_parent.as_deref() {
            anyhow::bail!(
                "{label} physical path {} escaped its authenticated obligation directory",
                authenticated.path.display()
            );
        }
        if !unique_paths.insert(authenticated.path.clone()) {
            anyhow::bail!(
                "CHC evidence manifest repeats replay obligation path {}",
                authenticated.path.display()
            );
        }
        obligations.push(authenticated);
    }
    obligations.sort_by(|left, right| left.path.cmp(&right.path));

    Ok(EmittedChcArtifacts {
        certificate,
        obligations,
    })
}

fn unique_chc_stats_json(stdout: &[u8], stderr: &[u8]) -> Result<Value> {
    let mut candidates = Vec::new();
    for (stream, bytes) in [("stderr", stderr), ("stdout", stdout)] {
        for (line_index, line) in String::from_utf8_lossy(bytes).lines().enumerate() {
            let line = line.trim();
            if !line.starts_with('{') || !line.ends_with('}') {
                continue;
            }
            let Ok(value) = serde_json::from_str::<Value>(line) else {
                continue;
            };
            if value.get("chc_evidence_manifest").is_some() {
                candidates.push((stream, line_index + 1, value));
            }
        }
    }
    match candidates.len() {
        1 => {
            let (_, _, value) = candidates
                .pop()
                .context("same-run CHC stats candidate disappeared during parsing")?;
            if value.get("mode").and_then(Value::as_str) != Some("chc") {
                anyhow::bail!("same-run stats JSON carrying CHC evidence has mode other than chc");
            }
            Ok(value)
        }
        0 => anyhow::bail!("solver output contains no --stats-json CHC evidence manifest"),
        count => anyhow::bail!(
            "solver output contains {count} CHC evidence manifests; same-run artifact authority is ambiguous"
        ),
    }
}

fn parse_chc_manifest_artifact(
    value: &Value,
    label: &str,
    expected_role: &str,
) -> Result<ChcManifestArtifact> {
    let schema = string_field(value, "schema")?;
    if schema != "ay.chc-proof-artifact-digest/v1" {
        anyhow::bail!(
            "{label} descriptor schema mismatch: expected ay.chc-proof-artifact-digest/v1, got {schema}"
        );
    }
    let role = string_field(value, "role")?;
    if role != expected_role {
        anyhow::bail!("{label} role mismatch: expected {expected_role}, got {role}");
    }
    let path = PathBuf::from(string_field(value, "path")?);
    if !path.is_absolute() {
        anyhow::bail!("{label} manifest path must be absolute: {}", path.display());
    }
    let bytes = field(value, "bytes")?
        .as_u64()
        .with_context(|| format!("{label} descriptor bytes is not a non-negative integer"))?;
    if bytes == 0 {
        anyhow::bail!("{label} descriptor has zero bytes");
    }
    let sha256 = string_field(value, "sha256")?;
    if sha256.len() != 64
        || !sha256
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        anyhow::bail!("{label} descriptor has invalid lowercase SHA-256: {sha256}");
    }
    Ok(ChcManifestArtifact {
        path,
        bytes,
        sha256,
    })
}

fn validate_chc_manifest_file(
    artifact: &ChcManifestArtifact,
    label: &str,
) -> Result<AuthenticatedChcArtifact> {
    if artifact.bytes > MAX_CHC_ARTIFACT_BYTES {
        anyhow::bail!(
            "{label} declares {} bytes, exceeding the per-artifact limit of {MAX_CHC_ARTIFACT_BYTES}: {}",
            artifact.bytes,
            artifact.path.display()
        );
    }
    let expected_len = usize::try_from(artifact.bytes)
        .with_context(|| format!("{label} byte length does not fit in memory"))?;
    let path_metadata = fs::symlink_metadata(&artifact.path)
        .with_context(|| format!("inspect {label} {}", artifact.path.display()))?;
    if !path_metadata.file_type().is_file() {
        anyhow::bail!(
            "{label} is not a physical regular file: {}",
            artifact.path.display()
        );
    }
    if path_metadata.len() != artifact.bytes {
        anyhow::bail!(
            "{label} byte length mismatch for {}: manifest={} actual={}",
            artifact.path.display(),
            artifact.bytes,
            path_metadata.len()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if path_metadata.nlink() != 1 {
            anyhow::bail!(
                "{label} has unexpected hard links: {}",
                artifact.path.display()
            );
        }
    }

    let mut open_options = fs::OpenOptions::new();
    open_options.read(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt as _;
        open_options.custom_flags(nix::libc::O_NOFOLLOW | nix::libc::O_NONBLOCK);
    }
    let mut file = open_options
        .open(&artifact.path)
        .with_context(|| format!("open {label} {}", artifact.path.display()))?;
    let opened_metadata = file
        .metadata()
        .with_context(|| format!("inspect opened {label} {}", artifact.path.display()))?;
    if !opened_metadata.file_type().is_file() || opened_metadata.len() != artifact.bytes {
        anyhow::bail!(
            "{label} changed type or size while opening: {}",
            artifact.path.display()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if path_metadata.dev() != opened_metadata.dev()
            || path_metadata.ino() != opened_metadata.ino()
            || opened_metadata.nlink() != 1
        {
            anyhow::bail!(
                "{label} changed identity while opening: {}",
                artifact.path.display()
            );
        }
    }

    let mut bytes = Vec::new();
    bytes
        .try_reserve_exact(expected_len)
        .with_context(|| format!("reserve memory for {label} {}", artifact.path.display()))?;
    let read_limit = artifact
        .bytes
        .checked_add(1)
        .with_context(|| format!("{label} byte length overflow"))?;
    Read::by_ref(&mut file)
        .take(read_limit)
        .read_to_end(&mut bytes)
        .with_context(|| format!("read {label} {}", artifact.path.display()))?;
    let observed_bytes = u64::try_from(bytes.len())
        .with_context(|| format!("{label} observed byte length overflow"))?;
    let observed_sha256 = sha256_hex(&bytes);
    if observed_bytes != artifact.bytes || observed_sha256 != artifact.sha256 {
        anyhow::bail!(
            "{label} digest mismatch for {}: manifest_bytes={} actual_bytes={} manifest_sha256={} actual_sha256={observed_sha256}",
            artifact.path.display(),
            artifact.bytes,
            observed_bytes,
            artifact.sha256
        );
    }

    let after_metadata = fs::symlink_metadata(&artifact.path)
        .with_context(|| format!("reinspect {label} {}", artifact.path.display()))?;
    if !after_metadata.file_type().is_file() || after_metadata.len() != artifact.bytes {
        anyhow::bail!(
            "{label} changed type or size while hashing: {}",
            artifact.path.display()
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt as _;
        if opened_metadata.dev() != after_metadata.dev()
            || opened_metadata.ino() != after_metadata.ino()
            || after_metadata.nlink() != 1
        {
            anyhow::bail!(
                "{label} changed identity while hashing: {}",
                artifact.path.display()
            );
        }
    }

    let path = fs::canonicalize(&artifact.path)
        .with_context(|| format!("resolve physical {label} path {}", artifact.path.display()))?;
    Ok(AuthenticatedChcArtifact {
        path,
        bytes,
        sha256: observed_sha256,
    })
}

fn generate_reference_cache(repo_root: &Path, ay: &Path, z3: &str) -> Result<Value> {
    let now = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default();
    let generated_at_unix_seconds = now.as_secs();
    let run_id = format!("{}-{}", std::process::id(), now.as_nanos());

    let z3_version_output = ProcessCommand::new(z3)
        .arg("--version")
        .current_dir(repo_root)
        .output()
        .with_context(|| format!("run {z3} --version"))?;
    if !z3_version_output.status.success() {
        anyhow::bail!(
            "Z3 version command failed: status={:?} stdout_tail={:?} stderr_tail={:?}",
            z3_version_output.status.code(),
            tail_text(&String::from_utf8_lossy(&z3_version_output.stdout)),
            tail_text(&String::from_utf8_lossy(&z3_version_output.stderr))
        );
    }
    let z3_version_stdout = String::from_utf8_lossy(&z3_version_output.stdout);
    let z3_version_stderr = String::from_utf8_lossy(&z3_version_output.stderr);
    let z3_version = first_non_empty_line(&z3_version_stdout)
        .or_else(|| first_non_empty_line(&z3_version_stderr))
        .unwrap_or("z3 --version produced no text")
        .to_string();

    let ay_version_output =
        run_command_capture(repo_root, ay, &["--version"]).context("run ay --version")?;
    let ay_version_stdout = String::from_utf8_lossy(&ay_version_output.stdout);
    let ay_version_stderr = String::from_utf8_lossy(&ay_version_output.stderr);
    let ay_version = first_non_empty_line(&ay_version_stdout)
        .or_else(|| first_non_empty_line(&ay_version_stderr))
        .unwrap_or("ay --version produced no text")
        .to_string();

    let z3_transcript = run_program_stdin(
        std::ffi::OsStr::new(z3),
        &["-in"],
        BASIC_SMT_TRANSCRIPT_INPUT,
    )
    .with_context(|| format!("run {z3} -in for {BASIC_SMT_TRANSCRIPT_ID}"))?;
    if !z3_transcript.status.success() {
        anyhow::bail!(
            "Z3 transcript baseline failed: status={:?} stdout_tail={:?} stderr_tail={:?}",
            z3_transcript.status.code(),
            tail_text(&String::from_utf8_lossy(&z3_transcript.stdout)),
            tail_text(&String::from_utf8_lossy(&z3_transcript.stderr))
        );
    }

    let work_dir = env::temp_dir()
        .join(format!("ay-z3-audit-reference-cache-{run_id}"))
        .join("chc");
    fs::create_dir_all(&work_dir).with_context(|| format!("create {}", work_dir.display()))?;
    let problem = repo_root.join(CHC_CANARY_PROBLEM);
    let problem_sha256 =
        sha256_file(&problem).with_context(|| format!("hash CHC canary {}", problem.display()))?;
    let certificate = work_dir.join("chc-certificate.smt2");
    let certificate_arg = certificate.to_string_lossy().into_owned();
    let problem_arg = problem.to_string_lossy().into_owned();
    let emit = run_command_capture(
        repo_root,
        ay,
        &[
            "solve",
            "--chc",
            "--stats-json",
            "--proof",
            &certificate_arg,
            &problem_arg,
        ],
    )
    .context("emit CHC certificate for reference cache")?;
    if !emit.status.success() {
        anyhow::bail!(
            "CHC certificate emission failed: status={:?} stdout_tail={:?} stderr_tail={:?}",
            emit.status.code(),
            tail_text(&String::from_utf8_lossy(&emit.stdout)),
            tail_text(&String::from_utf8_lossy(&emit.stderr))
        );
    }
    let emitted = emitted_chc_artifacts(&emit, &certificate)
        .context("authenticate same-run CHC evidence manifest for reference cache")?;
    let authenticated_obligations = emitted.obligations;

    let z3_path = Path::new(z3);
    let mut obligations = Vec::new();
    for obligation in &authenticated_obligations {
        let replay =
            run_command_capture_with_stdin(repo_root, z3_path, &["-in"], &obligation.bytes)
                .with_context(|| format!("run {z3} -in for {}", obligation.path.display()))?;
        let stdout = String::from_utf8_lossy(&replay.stdout).to_string();
        let stderr = String::from_utf8_lossy(&replay.stderr).to_string();
        let stdout_first_line = first_non_empty_line(&stdout).unwrap_or("").to_string();
        if !replay.status.success() || stdout_first_line.trim() != "unsat" {
            anyhow::bail!(
                "Z3 did not replay CHC obligation as UNSAT: {} status={:?} stdout_tail={:?} stderr_tail={:?}",
                obligation.path.display(),
                replay.status.code(),
                tail_text(&stdout),
                tail_text(&stderr)
            );
        }
        obligations.push(json!({
            "name": obligation.path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or("obligation.smt2"),
            "sha256": obligation.sha256,
            "status_code": replay.status.code(),
            "stdout_first_line": stdout_first_line,
            "stdout": stdout,
            "stderr": stderr,
        }));
    }
    let surface_evidence = generate_replacement_surface_evidence(repo_root, obligations.len());

    Ok(json!({
        "schema": REFERENCE_CACHE_SCHEMA,
        "generated_at_unix_seconds": generated_at_unix_seconds,
        "generator": {
            "z3_command": z3,
            "z3_version": z3_version,
            "ay": ay,
            "ay_version": ay_version,
        },
        "basic_smt_transcript": {
            "id": BASIC_SMT_TRANSCRIPT_ID,
            "input_sha256": sha256_hex(BASIC_SMT_TRANSCRIPT_INPUT.as_bytes()),
            "status_code": z3_transcript.status.code(),
            "stdout": String::from_utf8_lossy(&z3_transcript.stdout).to_string(),
            "stderr": String::from_utf8_lossy(&z3_transcript.stderr).to_string(),
        },
        "chc_certificate_obligations": {
            "problem": CHC_CANARY_PROBLEM,
            "problem_sha256": problem_sha256,
            "count": obligations.len(),
            "obligations": obligations,
        },
        (SURFACE_EVIDENCE_KEY): {
            "schema": SURFACE_EVIDENCE_SCHEMA,
            "surfaces": surface_evidence,
        },
    }))
}

fn generate_replacement_surface_evidence(
    repo_root: &Path,
    chc_obligation_count: usize,
) -> Vec<Value> {
    vec![
        public_source_build_evidence(repo_root),
        smtlib_surface_evidence(repo_root),
        dimacs_surface_evidence(repo_root),
        chc_surface_evidence(repo_root, chc_obligation_count),
        models_surface_evidence(repo_root),
        rust_embedding_surface_evidence(repo_root),
        c_api_ffi_surface_evidence(repo_root),
    ]
}

fn generate_live_surface_evidence_map(
    repo_root: &Path,
    reference_cache: Option<&ReferenceCache>,
) -> Result<BTreeMap<String, CachedSurfaceEvidence>> {
    let chc_obligation_count = reference_cache
        .map(|cache| cache.chc_obligations.obligations.len())
        .unwrap_or(0);
    let evidence = json!({
        "schema": SURFACE_EVIDENCE_SCHEMA,
        "surfaces": generate_replacement_surface_evidence(repo_root, chc_obligation_count),
    });
    parse_surface_evidence(Some(&evidence))
}

fn surface_evidence_value(
    id: &'static str,
    status: CheckStatus,
    current: impl Into<String>,
    goal: impl Into<String>,
    missing: impl Into<String>,
    command: impl Into<String>,
    source: impl Into<String>,
) -> Value {
    json!({
        "id": id,
        "status": status.as_str(),
        "current": current.into(),
        "goal": goal.into(),
        "missing": missing.into(),
        "command": command.into(),
        "source": source.into(),
    })
}

fn public_source_build_evidence(repo_root: &Path) -> Value {
    let spec = surface_spec("public_source_build").expect("public source spec");
    let current_head = current_git_head(repo_root);
    let provenance = repo_root.join("the development design notes");
    let public_logs = find_named_files_in_roots(
        &[
            repo_root.join("reports"),
            repo_root.join("evals").join("launch-packets"),
        ],
        "public-clone-check",
        ".log",
        20,
    );
    let passing_public_logs = public_logs
        .iter()
        .filter(|path| public_clone_log_current_for_repo(path, repo_root, current_head.as_deref()))
        .count();
    let stale_public_logs = public_logs
        .iter()
        .filter(|path| public_clone_log_passes(path))
        .filter(|path| !public_clone_log_current_for_repo(path, repo_root, current_head.as_deref()))
        .count();
    let files = [
        "cargo-build-release.command.txt",
        "cargo-build-release.stdout.txt",
        "cargo-build-release.stderr.txt",
        "ay-version.txt",
    ];
    let present = files
        .iter()
        .filter(|name| provenance.join(name).is_file())
        .count();
    let current = format!(
        "{present}/{} local release-build provenance files present; {passing_public_logs}/{} current-code unauthenticated public-clone build packets pass; stale_passing_public_logs={stale_public_logs}",
        files.len(),
        public_logs.len()
    );
    let status = if passing_public_logs > 0 {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };
    surface_evidence_value(
        spec.id,
        status,
        current,
        spec.goal,
        if status == CheckStatus::Pass {
            "none".to_string()
        } else {
            "current-code unauthenticated public-clone build packet is missing from checked-in baseline evidence".to_string()
        },
        spec.command,
        if public_logs.is_empty() {
            relative_path_string(repo_root, &provenance)
        } else {
            public_logs
                .iter()
                .map(|path| relative_path_string(repo_root, path))
                .collect::<Vec<_>>()
                .join(", ")
        },
    )
}

fn smtlib_surface_evidence(repo_root: &Path) -> Value {
    let spec = surface_spec("smtlib_input").expect("SMT-LIB spec");
    let mut found = 0usize;
    let mut current_found = 0usize;
    let mut total = 0u64;
    let mut agree = 0u64;
    let mut disagree = 0u64;
    let mut ay_only = 0u64;
    let mut reference_solved_missing = 0u64;
    let mut both_solved = 0u64;
    let mut ay_errors = 0u64;
    let mut ref_errors = 0u64;
    let current_head = current_git_head(repo_root);
    let mut dirty = Vec::new();
    let mut missing = Vec::new();
    let mut stale = Vec::new();
    let mut zero_benchmark_packets = Vec::new();
    let mut sources = Vec::new();
    let mut ay_counts = BTreeMap::new();
    let mut ref_counts = BTreeMap::new();
    let mut reference_solved_missing_ay_counts = BTreeMap::new();
    let mut eval_status_counts = BTreeMap::new();
    let mut eval_breakdowns = Vec::new();

    for eval_id in SMTLIB_EVAL_IDS {
        match latest_eval_result(repo_root, eval_id) {
            Some((path, value)) => {
                found += 1;
                let is_current =
                    eval_result_current_for_repo(&value, repo_root, current_head.as_deref());
                let benchmark_count = value_u64(&value, "/settings/benchmark_count");
                let is_dirty = value_bool(&value, "/environment/git_dirty").unwrap_or(false);
                let eval_status = smt_eval_status(&value, is_current, is_dirty);
                add_check_status_count(&mut eval_status_counts, eval_status);
                eval_breakdowns.push(smt_eval_breakdown(
                    repo_root,
                    eval_id,
                    &path,
                    &value,
                    eval_status,
                    is_current,
                    is_dirty,
                ));
                sources.push(relative_path_string(repo_root, &path));
                if !is_current {
                    stale.push(format!(
                        "{}@{}",
                        eval_id,
                        eval_result_commit(&value).unwrap_or_else(|| "unknown".to_string())
                    ));
                    continue;
                }
                current_found += 1;
                if benchmark_count == 0 {
                    zero_benchmark_packets.push(eval_id.to_string());
                }
                total += benchmark_count;
                agree += value_u64(&value, "/comparison/agree");
                disagree += value_u64(&value, "/comparison/disagree");
                ay_only += value_u64(&value, "/comparison/ay_only");
                reference_solved_missing += value_u64(&value, "/comparison/ref_only");
                both_solved += value_u64(&value, "/comparison/both_solved");
                ay_errors += result_count(&value, "ay_result", "error");
                ref_errors += result_count(&value, "ref_result", "error");
                if value_bool(&value, "/environment/git_dirty").unwrap_or(false) {
                    dirty.push(eval_id.to_string());
                }
                add_result_counts(&mut ay_counts, &value, "ay_result");
                add_result_counts(&mut ref_counts, &value, "ref_result");
                add_reference_solved_missing_ay_result_counts(
                    &mut reference_solved_missing_ay_counts,
                    &value,
                );
            }
            None => {
                missing.push(eval_id.to_string());
                add_check_status_count(&mut eval_status_counts, CheckStatus::Fail);
                eval_breakdowns.push(format!("{eval_id}{{status=fail; packet=missing}}"));
            }
        }
    }

    let mut gaps = Vec::new();
    if !missing.is_empty() {
        gaps.push(format!("missing eval packets: {}", missing.join(", ")));
    }
    if !dirty.is_empty() {
        gaps.push(format!("dirty eval packets: {}", dirty.join(", ")));
    }
    if !zero_benchmark_packets.is_empty() {
        gaps.push(format!(
            "zero-benchmark eval packets: {}",
            zero_benchmark_packets.join(", ")
        ));
    }
    if !stale.is_empty() {
        gaps.push(format!(
            "stale eval packets not from current code tree: {}",
            stale.join(", ")
        ));
    }
    if disagree != 0 {
        gaps.push(format!("{disagree} differential disagreements"));
    }
    if reference_solved_missing != 0 {
        gaps.push(format!(
            "reference_solved_missing={reference_solved_missing}; reference_solved_missing_ay_results={}",
            count_summary(&reference_solved_missing_ay_counts)
        ));
    }
    if ay_errors != 0 {
        gaps.push(format!("{ay_errors} AY execution errors"));
    }
    if ref_errors != 0 {
        gaps.push(format!("{ref_errors} reference execution errors"));
    }
    let status = if gaps.is_empty() && current_found == SMTLIB_EVAL_IDS.len() && total > 0 {
        CheckStatus::Pass
    } else if reference_solved_missing != 0
        && missing.is_empty()
        && dirty.is_empty()
        && zero_benchmark_packets.is_empty()
        && stale.is_empty()
        && disagree == 0
        && ay_errors == 0
        && ref_errors == 0
        && current_found == SMTLIB_EVAL_IDS.len()
        && total > 0
    {
        reference_solved_missing_failure_status(&reference_solved_missing_ay_counts)
    } else {
        smt_failure_status(&ay_counts, &ref_counts)
    };

    surface_evidence_value(
        spec.id,
        status,
        format!(
            "{current_found}/{} current-code eval packets; {found}/{} packets found; eval_statuses={}; benchmarks={total}; agree={agree}; disagree={disagree}; ay_only={ay_only}; reference_solved_missing={reference_solved_missing}; reference_solved_missing_ay_results={}; both_solved={both_solved}; ay_errors={ay_errors}; ref_errors={ref_errors}; ay_results={}; ref_results={}; per_eval=[{}]",
            SMTLIB_EVAL_IDS.len(),
            SMTLIB_EVAL_IDS.len(),
            check_status_count_summary(&eval_status_counts),
            count_summary(&reference_solved_missing_ay_counts),
            count_summary(&ay_counts),
            count_summary(&ref_counts),
            eval_breakdowns.join("; ")
        ),
        spec.goal,
        if gaps.is_empty() {
            "none".to_string()
        } else {
            gaps.join("; ")
        },
        spec.command,
        sources.join(", "),
    )
}

fn dimacs_surface_evidence(repo_root: &Path) -> Value {
    let spec = surface_spec("dimacs_cnf_input").expect("DIMACS spec");
    let current_head = current_git_head(repo_root);
    let scoreboards =
        find_named_files_in_roots(&[repo_root.join("reports")], "scoreboard", ".json", 100);
    let mut found = 0usize;
    let mut current_scoreboards = Vec::new();
    let mut stale = Vec::new();
    let mut dirty = Vec::new();
    for path in scoreboards {
        let Some(value) = read_json_file(&path) else {
            continue;
        };
        if value_u64(&value, "/variants/default/summary/total") == 0 {
            continue;
        }
        found += 1;
        if !scoreboard_current_for_repo(&value, repo_root, current_head.as_deref()) {
            stale.push(format!(
                "{}@{}",
                relative_path_string(repo_root, &path),
                scoreboard_commit(&value).unwrap_or_else(|| "unknown".to_string())
            ));
            continue;
        }
        if scoreboard_dirty(&value) {
            dirty.push(relative_path_string(repo_root, &path));
        }
        current_scoreboards.push((path, value));
    }
    current_scoreboards.sort_by(|(left, _), (right, _)| left.cmp(right));
    let selected = current_scoreboards
        .iter()
        .find(|(_, value)| scoreboard_passes(value))
        .or_else(|| current_scoreboards.last());
    let Some((path, value)) = selected else {
        let stale_summary = summarize_list(&stale, 8);
        return surface_evidence_value(
            spec.id,
            CheckStatus::Fail,
            format!(
                "0/1 current-code SAT-COMP-shaped scoreboard packets pass; {found} SAT-COMP-shaped scoreboard packets found; stale_scoreboards={}",
                stale.len()
            ),
            spec.goal,
            if stale.is_empty() {
                "current-code SAT-COMP-shaped scoreboard packet is missing".to_string()
            } else {
                format!(
                    "current-code SAT-COMP-shaped scoreboard packet is missing; stale scoreboards not from current code tree: {stale_summary}"
                )
            },
            spec.command,
            stale_summary,
        );
    };
    let total = value_u64(value, "/variants/default/summary/total");
    let solved = value_u64(value, "/variants/default/summary/solved");
    let solved_sat = value_u64(value, "/variants/default/summary/solved_sat");
    let solved_unsat = value_u64(value, "/variants/default/summary/solved_unsat");
    let unknown = value_u64(value, "/variants/default/summary/unknown");
    let wrong = value_u64(value, "/variants/default/summary/wrong");
    let invalid = value_u64(value, "/variants/default/summary/invalid");
    let par2_total = value_f64(value, "/variants/default/summary/par2_total").unwrap_or(0.0);
    let timeout = value_f64(value, "/variants/default/summary/timeout_sec").unwrap_or(0.0);
    let soundness = value_bool(value, "/soundness").unwrap_or(false);
    let reference_disagreements = reference_disagreement_count(value);
    let reference_only_solved = reference_only_solved_count(value);
    let selected_dirty = scoreboard_dirty(value);
    let otherwise_clean = soundness
        && total > 0
        && wrong == 0
        && invalid == 0
        && reference_disagreements == 0
        && !selected_dirty;
    let status = if otherwise_clean && reference_only_solved == 0 {
        CheckStatus::Pass
    } else if otherwise_clean && reference_only_solved != 0 {
        CheckStatus::FailTimeout
    } else {
        CheckStatus::Fail
    };
    let mut gaps = Vec::new();
    if !soundness {
        gaps.push("scoreboard soundness=false".to_string());
    }
    if wrong != 0 {
        gaps.push(format!("wrong={wrong}"));
    }
    if invalid != 0 {
        gaps.push(format!("invalid={invalid}"));
    }
    if reference_disagreements != 0 {
        gaps.push(format!("reference_disagreements={reference_disagreements}"));
    }
    if reference_only_solved != 0 {
        gaps.push(format!("reference_only_solved={reference_only_solved}"));
    }
    if selected_dirty {
        gaps.push("scoreboard was generated from a dirty checkout".to_string());
    }
    if !dirty.is_empty() {
        gaps.push(format!(
            "dirty current-code scoreboards: {}",
            dirty.join(", ")
        ));
    }
    surface_evidence_value(
        spec.id,
        status,
        format!(
            "{}/{} current-code SAT-COMP-shaped scoreboards; {found} scoreboards found; selected={}; total={total}; solved={solved}; solved_sat={solved_sat}; solved_unsat={solved_unsat}; unknown={unknown}; wrong={wrong}; invalid={invalid}; par2_total={par2_total:.3}; timeout_s={timeout:.0}; reference_disagreements={reference_disagreements}; reference_only_solved={reference_only_solved}; stale_scoreboards={}",
            current_scoreboards.len(),
            found,
            relative_path_string(repo_root, path),
            stale.len()
        ),
        spec.goal,
        if gaps.is_empty() {
            "none".to_string()
        } else {
            gaps.join("; ")
        },
        spec.command,
        relative_path_string(repo_root, path),
    )
}

fn chc_surface_evidence(repo_root: &Path, chc_obligation_count: usize) -> Value {
    let spec = surface_spec("chc_spacer_style_use").expect("CHC spec");
    let verify_path = repo_root.join("the development design notes");
    let latest_eval = latest_eval_result(repo_root, "chccomp-2025-extra-small-lia");
    let chc_eval_ids = ["chccomp-2025-extra-small-lia", "chccomp-2025-lia-lin"];
    let current_head = current_git_head(repo_root);
    let z3_all_packets = latest_reference_packets(repo_root, &chc_eval_ids, "z3");
    let golem_all_packets = latest_reference_packets(repo_root, &chc_eval_ids, "golem");
    let (z3_packets, z3_stale) =
        split_current_eval_packets(repo_root, z3_all_packets, current_head.as_deref());
    let (golem_packets, golem_stale) =
        split_current_eval_packets(repo_root, golem_all_packets, current_head.as_deref());
    let verify = read_json_file(&verify_path);
    let total = verify
        .as_ref()
        .map(|value| value_u64(value, "/total"))
        .unwrap_or(0);
    let matches = verify
        .as_ref()
        .map(|value| value_u64(value, "/matches"))
        .unwrap_or(0);
    let sound_bugs = verify
        .as_ref()
        .map(|value| value_u64(value, "/sound_bugs"))
        .unwrap_or(0);
    let incomplete = verify
        .as_ref()
        .map(|value| value_u64(value, "/incomplete"))
        .unwrap_or(0);
    let reference_unknown = verify
        .as_ref()
        .map(|value| value_u64(value, "/reference_unknown"))
        .unwrap_or(0);
    let both_unknown = verify
        .as_ref()
        .map(|value| value_u64(value, "/both_unknown"))
        .unwrap_or(0);
    let no_baseline = verify
        .as_ref()
        .map(|value| value_u64(value, "/no_baseline"))
        .unwrap_or(0);
    let (eval_source, eval_total, eval_counts) = latest_eval
        .as_ref()
        .map(|(path, value)| {
            let mut counts = BTreeMap::new();
            add_result_counts(&mut counts, value, "result");
            (
                relative_path_string(repo_root, path),
                value_u64(value, "/settings/benchmark_count"),
                count_summary(&counts),
            )
        })
        .unwrap_or_else(|| ("missing chc eval packet".to_string(), 0, "none".to_string()));

    let mut gaps = Vec::new();
    if verify.is_none() {
        gaps.push("missing Golem verification report".to_string());
    }
    if sound_bugs != 0 {
        gaps.push(format!("sound_bugs={sound_bugs}"));
    }
    if no_baseline != 0 {
        gaps.push(format!("no_baseline={no_baseline}"));
    }
    if z3_packets.len() != chc_eval_ids.len() {
        gaps.push(format!(
            "missing current Z3 Spacer comparison packets: {}/{} present",
            z3_packets.len(),
            chc_eval_ids.len()
        ));
    }
    if golem_packets.len() != chc_eval_ids.len() {
        gaps.push(format!(
            "missing current Golem comparison packets: {}/{} present",
            golem_packets.len(),
            chc_eval_ids.len()
        ));
    }
    if !z3_stale.is_empty() {
        gaps.push(format!(
            "stale Z3 Spacer comparison packets not from current code tree: {}",
            z3_stale.join(", ")
        ));
    }
    if !golem_stale.is_empty() {
        gaps.push(format!(
            "stale Golem comparison packets not from current code tree: {}",
            golem_stale.join(", ")
        ));
    }
    let z3_disagree = z3_packets
        .iter()
        .map(|(_, value)| value_u64(value, "/comparison/disagree"))
        .sum::<u64>();
    let golem_disagree = golem_packets
        .iter()
        .map(|(_, value)| value_u64(value, "/comparison/disagree"))
        .sum::<u64>();
    if z3_disagree != 0 {
        gaps.push(format!("z3_spacer_disagree={z3_disagree}"));
    }
    if golem_disagree != 0 {
        gaps.push(format!("golem_disagree={golem_disagree}"));
    }
    let z3_reference_solved_missing =
        eval_packet_comparison_sum(&z3_packets, "/comparison/ref_only");
    let golem_reference_solved_missing =
        eval_packet_comparison_sum(&golem_packets, "/comparison/ref_only");
    if z3_reference_solved_missing != 0 {
        gaps.push(format!(
            "z3_spacer_reference_solved_missing={z3_reference_solved_missing}"
        ));
    }
    if golem_reference_solved_missing != 0 {
        gaps.push(format!(
            "golem_reference_solved_missing={golem_reference_solved_missing}"
        ));
    }
    let z3_zero_benchmark_packets = zero_benchmark_eval_packets(repo_root, &z3_packets);
    let golem_zero_benchmark_packets = zero_benchmark_eval_packets(repo_root, &golem_packets);
    if !z3_zero_benchmark_packets.is_empty() {
        gaps.push(format!(
            "current Z3 Spacer packets with zero benchmarks: {}",
            z3_zero_benchmark_packets.join(", ")
        ));
    }
    if !golem_zero_benchmark_packets.is_empty() {
        gaps.push(format!(
            "current Golem packets with zero benchmarks: {}",
            golem_zero_benchmark_packets.join(", ")
        ));
    }
    let z3_ref_errors = eval_packet_result_count(&z3_packets, "ref_result", "error");
    let golem_ref_errors = eval_packet_result_count(&golem_packets, "ref_result", "error");
    let z3_ay_errors = eval_packet_result_count(&z3_packets, "ay_result", "error");
    let golem_ay_errors = eval_packet_result_count(&golem_packets, "ay_result", "error");
    let z3_ay_results = eval_packet_result_counts(&z3_packets, "ay_result");
    let z3_ref_results = eval_packet_result_counts(&z3_packets, "ref_result");
    let golem_ay_results = eval_packet_result_counts(&golem_packets, "ay_result");
    let golem_ref_results = eval_packet_result_counts(&golem_packets, "ref_result");
    let z3_reference_solved_missing_ay_results =
        eval_packet_reference_solved_missing_ay_result_counts(&z3_packets);
    let golem_reference_solved_missing_ay_results =
        eval_packet_reference_solved_missing_ay_result_counts(&golem_packets);
    if z3_ref_errors != 0 {
        gaps.push(format!("z3_spacer_reference_errors={z3_ref_errors}"));
    }
    if golem_ref_errors != 0 {
        gaps.push(format!("golem_reference_errors={golem_ref_errors}"));
    }
    if z3_ay_errors != 0 {
        gaps.push(format!("z3_spacer_ay_errors={z3_ay_errors}"));
    }
    if golem_ay_errors != 0 {
        gaps.push(format!("golem_ay_errors={golem_ay_errors}"));
    }
    let z3_benchmarks = eval_packet_benchmark_count(&z3_packets);
    let golem_benchmarks = eval_packet_benchmark_count(&golem_packets);
    let z3_agree = eval_packet_comparison_sum(&z3_packets, "/comparison/agree");
    let golem_agree = eval_packet_comparison_sum(&golem_packets, "/comparison/agree");
    let z3_both_solved = eval_packet_comparison_sum(&z3_packets, "/comparison/both_solved");
    let golem_both_solved = eval_packet_comparison_sum(&golem_packets, "/comparison/both_solved");
    let z3_no_agreement_packets = no_concrete_agreement_eval_packets(repo_root, &z3_packets);
    if !z3_no_agreement_packets.is_empty() {
        gaps.push(format!(
            "current Z3 Spacer packets with no concrete agreements: {}",
            z3_no_agreement_packets.join(", ")
        ));
    }
    if !golem_packets.is_empty() && golem_agree == 0 {
        gaps.push("golem_agree=0".to_string());
    }
    // `gaps` must be empty while `verify` must be present: the asymmetric
    // is_empty()/is_some() pairing is intentional, not a typo.
    #[allow(clippy::suspicious_operation_groupings)]
    let status = if gaps.is_empty()
        && verify.is_some()
        && z3_packets.len() == chc_eval_ids.len()
        && golem_packets.len() == chc_eval_ids.len()
    {
        CheckStatus::Pass
    } else if verify.is_some()
        && z3_packets.len() == chc_eval_ids.len()
        && golem_packets.len() == chc_eval_ids.len()
        && z3_disagree == 0
        && golem_disagree == 0
        && z3_ref_errors == 0
        && golem_ref_errors == 0
        && z3_ay_errors == 0
        && golem_ay_errors == 0
        && sound_bugs == 0
        && no_baseline == 0
        && z3_reference_solved_missing + golem_reference_solved_missing != 0
        && z3_zero_benchmark_packets.is_empty()
        && golem_zero_benchmark_packets.is_empty()
        && z3_stale.is_empty()
        && golem_stale.is_empty()
        && z3_no_agreement_packets.is_empty()
        && (!golem_packets.is_empty() && golem_agree != 0)
    {
        let mut combined = z3_reference_solved_missing_ay_results.clone();
        merge_counts(&mut combined, &golem_reference_solved_missing_ay_results);
        reference_solved_missing_failure_status(&combined)
    } else {
        let mut combined_ay_results = z3_ay_results.clone();
        merge_counts(&mut combined_ay_results, &golem_ay_results);
        let mut combined_ref_results = z3_ref_results.clone();
        merge_counts(&mut combined_ref_results, &golem_ref_results);
        smt_failure_status(&combined_ay_results, &combined_ref_results)
    };
    let mut sources = Vec::new();
    if verify.is_some() {
        sources.push(relative_path_string(repo_root, &verify_path));
    }
    sources.push(eval_source);
    sources.extend(
        z3_packets
            .iter()
            .chain(golem_packets.iter())
            .map(|(path, _)| relative_path_string(repo_root, path)),
    );
    sources.push(format!(
        "{chc_obligation_count} obligations in {DEFAULT_REFERENCE_CACHE}"
    ));

    surface_evidence_value(
        spec.id,
        status,
        format!(
            "Golem verify: total={total}; matches={matches}; sound_bugs={sound_bugs}; incomplete={incomplete}; reference_unknown={reference_unknown}; both_unknown={both_unknown}; no_baseline={no_baseline}; latest_ay_eval_total={eval_total}; latest_ay_eval_results={eval_counts}; cached_chc_obligations={chc_obligation_count}; z3_spacer_packets={}/{}; z3_spacer_benchmarks={z3_benchmarks}; z3_spacer_agree={z3_agree}; z3_spacer_both_solved={z3_both_solved}; z3_spacer_reference_solved_missing={z3_reference_solved_missing}; z3_spacer_reference_solved_missing_ay_results={}; z3_spacer_ay_results={}; z3_spacer_ref_results={}; golem_packets={}/{}; golem_benchmarks={golem_benchmarks}; golem_agree={golem_agree}; golem_both_solved={golem_both_solved}; golem_reference_solved_missing={golem_reference_solved_missing}; golem_reference_solved_missing_ay_results={}; golem_ay_results={}; golem_ref_results={}; z3_spacer_disagree={z3_disagree}; golem_disagree={golem_disagree}; z3_spacer_reference_errors={z3_ref_errors}; golem_reference_errors={golem_ref_errors}; z3_spacer_ay_errors={z3_ay_errors}; golem_ay_errors={golem_ay_errors}",
            z3_packets.len(),
            chc_eval_ids.len(),
            count_summary(&z3_reference_solved_missing_ay_results),
            count_summary(&z3_ay_results),
            count_summary(&z3_ref_results),
            golem_packets.len(),
            chc_eval_ids.len(),
            count_summary(&golem_reference_solved_missing_ay_results),
            count_summary(&golem_ay_results),
            count_summary(&golem_ref_results),
        ),
        spec.goal,
        if gaps.is_empty() {
            "none".to_string()
        } else {
            gaps.join("; ")
        },
        spec.command,
        sources.join(", "),
    )
}

fn models_surface_evidence(repo_root: &Path) -> Value {
    let spec = surface_spec("models").expect("models spec");
    let scoreboard_path = repo_root.join("the development design notes");
    let model_check_path = repo_root.join("the development design notes");
    let scoreboard = read_json_file(&scoreboard_path);
    let sat_invalid = scoreboard
        .as_ref()
        .map(|value| value_u64(value, "/variants/default/summary/invalid"))
        .unwrap_or(0);
    let sat_wrong = scoreboard
        .as_ref()
        .map(|value| value_u64(value, "/variants/default/summary/wrong"))
        .unwrap_or(0);
    let (model_checks, model_passes) = tsv_status_counts(&model_check_path, "PASS");
    let model_packets =
        find_named_files(&repo_root.join("reports"), "model-validation", ".json", 20);
    let passing_model_packets = model_packets
        .iter()
        .filter_map(|path| read_json_file(path))
        .filter(model_validation_packet_passes)
        .count();
    let status = if passing_model_packets > 0 && sat_invalid == 0 && sat_wrong == 0 {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };
    surface_evidence_value(
        spec.id,
        status,
        format!(
            "basic SMT model transcript=1/1 cached; SAT scoreboard invalid={sat_invalid}; SAT scoreboard wrong={sat_wrong}; SAT model checks passed={model_passes}/{model_checks}; broad SMT theory model-validation packets={passing_model_packets}/{}",
            model_packets.len()
        ),
        spec.goal,
        if status == CheckStatus::Pass {
            "none".to_string()
        } else {
            "full model-validation packet for every claimed SMT-LIB model surface is missing or failing".to_string()
        },
        spec.command,
        model_sources(repo_root, &scoreboard_path, &model_check_path, &model_packets),
    )
}

fn rust_embedding_surface_evidence(repo_root: &Path) -> Value {
    let spec = surface_spec("rust_embedding").expect("rust embedding spec");
    let inventory = repo_root.join("the development design notes");
    let schema = repo_root.join("crates/ay/schemas/downstream-smoke-evidence.schema.json");
    let current_head = current_git_head(repo_root);
    let artifacts = find_named_files_in_roots(
        &[
            repo_root.join("reports"),
            repo_root.join("evals").join("launch-packets"),
        ],
        "downstream-smoke",
        ".json",
        20,
    );
    let downstream_logs =
        find_named_files_in_roots(&[repo_root.join("reports")], "downstream-smoke", ".log", 20);
    let model_checker_consumer_logs = find_named_files_in_roots(
        &[repo_root.join("reports")],
        "model-checker-consumer",
        ".log",
        20,
    );
    let current_artifacts = artifacts
        .iter()
        .filter(|path| {
            read_json_file(path).is_some_and(|value| {
                downstream_smoke_packet_current_for_repo(&value, repo_root, current_head.as_deref())
            })
        })
        .cloned()
        .collect::<Vec<_>>();
    let stale_artifacts = artifacts.len().saturating_sub(current_artifacts.len());
    let current_downstream_logs = downstream_logs
        .iter()
        .filter(|path| downstream_log_current_for_repo(path, repo_root, current_head.as_deref()))
        .cloned()
        .collect::<Vec<_>>();
    let stale_downstream_logs = downstream_logs
        .len()
        .saturating_sub(current_downstream_logs.len());
    let current_model_checker_consumer_logs = model_checker_consumer_logs
        .iter()
        .filter(|path| {
            model_checker_consumer_log_current_for_repo(path, repo_root, current_head.as_deref())
        })
        .cloned()
        .collect::<Vec<_>>();
    let stale_model_checker_consumer_logs = model_checker_consumer_logs
        .len()
        .saturating_sub(current_model_checker_consumer_logs.len());
    let model_checker_consumer_failures = current_model_checker_consumer_logs
        .iter()
        .flat_map(|path| model_checker_consumer_failure_summaries(path))
        .collect::<Vec<_>>();
    let model_checker_consumer_stronger_unknown_proofs = current_model_checker_consumer_logs
        .iter()
        .flat_map(|path| model_checker_consumer_stronger_unknown_proof_summaries(path))
        .collect::<Vec<_>>();
    let passing = current_artifacts
        .iter()
        .filter_map(|path| read_json_file(path))
        .filter(downstream_smoke_packet_passes)
        .count();
    let status = if passing > 0 {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };
    surface_evidence_value(
        spec.id,
        status,
        format!(
            "consumer inventory present={}; evidence schema present={}; current_downstream_smoke_artifacts={}; stale_artifacts={stale_artifacts}; passing_artifacts={passing}; current_downstream_logs={}; stale_downstream_logs={stale_downstream_logs}; current_model_checker_consumer_logs={}; stale_model_checker_consumer_logs={stale_model_checker_consumer_logs}; model_checker_consumer_failures={}; first_model_checker_consumer_failures={}; model_checker_consumer_stronger_unknown_to_proof={}; first_model_checker_consumer_stronger_unknown_to_proof={}",
            inventory.is_file(),
            schema.is_file(),
            current_artifacts.len(),
            current_downstream_logs.len(),
            current_model_checker_consumer_logs.len(),
            model_checker_consumer_failures.len(),
            first_items(&model_checker_consumer_failures, 5),
            model_checker_consumer_stronger_unknown_proofs.len(),
            first_items(&model_checker_consumer_stronger_unknown_proofs, 5)
        ),
        spec.goal,
        if status == CheckStatus::Pass {
            "none".to_string()
        } else if !model_checker_consumer_failures.is_empty() {
            format!(
                "downstream Rust consumer smoke failing: {}",
                first_items(&model_checker_consumer_failures, 5)
            )
        } else if stale_artifacts > 0 || stale_downstream_logs > 0 || stale_model_checker_consumer_logs > 0 {
            format!(
                "current downstream Rust consumer smoke result artifact is missing or not passing; ignored stale evidence for other commits: artifacts={stale_artifacts}, downstream_logs={stale_downstream_logs}, model_checker_consumer_logs={stale_model_checker_consumer_logs}"
            )
        } else {
            "checked-in downstream Rust consumer smoke result artifact is missing or not passing"
                .to_string()
        },
        spec.command,
        rust_embedding_sources(
            repo_root,
            &inventory,
            &schema,
            &artifacts,
            &downstream_logs,
            &model_checker_consumer_logs,
        ),
    )
}

fn current_git_head(repo_root: &Path) -> Option<String> {
    let output = ProcessCommand::new("git")
        .args(["rev-parse", "HEAD"])
        .current_dir(repo_root)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    first_non_empty_line(&String::from_utf8_lossy(&output.stdout))
        .map(str::trim)
        .filter(|head| !head.is_empty())
        .map(ToString::to_string)
}

#[cfg(test)]
fn downstream_smoke_packet_current_for_head(value: &Value, current_head: Option<&str>) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    value
        .pointer("/evidence/ay/commit_full")
        .or_else(|| value.pointer("/evidence/ay/commit"))
        .or_else(|| value.pointer("/ay/commit_full"))
        .or_else(|| value.pointer("/ay/commit"))
        .or_else(|| value.pointer("/summary/ay_commit_full"))
        .or_else(|| value.pointer("/summary/ay_commit"))
        .and_then(Value::as_str)
        .is_some_and(|commit| commit_matches_head(commit, current_head))
}

fn downstream_smoke_packet_current_for_repo(
    value: &Value,
    repo_root: &Path,
    current_head: Option<&str>,
) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    value
        .pointer("/evidence/ay/commit_full")
        .or_else(|| value.pointer("/evidence/ay/commit"))
        .or_else(|| value.pointer("/ay/commit_full"))
        .or_else(|| value.pointer("/ay/commit"))
        .or_else(|| value.pointer("/summary/ay_commit_full"))
        .or_else(|| value.pointer("/summary/ay_commit"))
        .and_then(Value::as_str)
        .is_some_and(|commit| commit_matches_audited_tree(repo_root, commit, current_head))
}

#[cfg(test)]
fn downstream_log_current_for_head(path: &Path, current_head: Option<&str>) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    downstream_log_commit(path).is_some_and(|commit| commit_matches_head(&commit, current_head))
}

fn downstream_log_current_for_repo(
    path: &Path,
    repo_root: &Path,
    current_head: Option<&str>,
) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    downstream_log_commit(path)
        .is_some_and(|commit| commit_matches_audited_tree(repo_root, &commit, current_head))
}

fn model_checker_consumer_log_current_for_repo(
    path: &Path,
    repo_root: &Path,
    current_head: Option<&str>,
) -> bool {
    let Some(parent) = path.parent().and_then(Path::parent) else {
        return false;
    };
    downstream_log_current_for_repo(
        &parent.join("downstream-smoke.log"),
        repo_root,
        current_head,
    )
}

fn downstream_log_commit(path: &Path) -> Option<String> {
    let text = fs::read_to_string(path).ok()?;
    text.lines().find_map(|line| {
        line.split_once("ay_commit=")
            .map(|(_, commit)| commit.split_whitespace().next().unwrap_or("").to_string())
            .filter(|commit| !commit.is_empty())
    })
}

fn commit_matches_head(commit: &str, current_head: &str) -> bool {
    let commit = commit.trim();
    !commit.is_empty() && (current_head.starts_with(commit) || commit.starts_with(current_head))
}

fn commit_matches_audited_tree(repo_root: &Path, commit: &str, current_head: &str) -> bool {
    let commit = commit.trim();
    if commit_matches_head(commit, current_head) {
        return true;
    }
    if commit.is_empty() || !git_is_ancestor(repo_root, commit, current_head) {
        return false;
    }
    let Some(paths) = git_changed_paths(repo_root, commit, current_head) else {
        return false;
    };
    !paths.is_empty()
        && paths
            .iter()
            .all(|path| path_is_cached_evidence_only(path) || path_is_audit_cli_only(path))
}

fn commit_matches_solver_evidence_tree(repo_root: &Path, commit: &str, current_head: &str) -> bool {
    let commit = commit.trim();
    if commit_matches_head(commit, current_head) {
        return true;
    }
    if commit.is_empty() || !git_is_ancestor(repo_root, commit, current_head) {
        return false;
    }
    let Some(paths) = git_changed_paths(repo_root, commit, current_head) else {
        return false;
    };
    !paths.is_empty()
        && paths.iter().all(|path| {
            path_is_cached_evidence_only(path)
                || path_is_audit_cli_only(path)
                || path_is_solver_evidence_irrelevant(path)
                || path == "evals/registry/chccomp-2025-lia-lin.yaml"
                || path == "scripts/certificate_consumer-smoke-check.sh"
                || path == "scripts/consumer-smoke-check.sh"
                || path == "scripts/consumer-smoke-lib.sh"
                || path == "scripts/quantifier_consumer-smoke-check.sh"
                || path == "scripts/tla2-smoke-check.sh"
                || path == "scripts/model-checker-consumer-smoke-check.sh"
        })
}

fn git_is_ancestor(repo_root: &Path, ancestor: &str, descendant: &str) -> bool {
    ProcessCommand::new("git")
        .args(["merge-base", "--is-ancestor", ancestor, descendant])
        .current_dir(repo_root)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

fn git_changed_paths(repo_root: &Path, from: &str, to: &str) -> Option<Vec<String>> {
    let range = format!("{from}..{to}");
    let output = ProcessCommand::new("git")
        .args(["diff", "--name-only", "--diff-filter=ACMRT", &range])
        .current_dir(repo_root)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .map(ToString::to_string)
            .collect(),
    )
}

fn path_is_cached_evidence_only(path: &str) -> bool {
    path.starts_with("reports/")
        || path.starts_with("evals/results/")
        || path.starts_with("evals/launch-packets/")
        || path == DEFAULT_REFERENCE_CACHE
}

fn path_is_audit_cli_only(path: &str) -> bool {
    path == "crates/ay/src/cmd_z3_audit.rs"
}

fn path_is_solver_evidence_irrelevant(path: &str) -> bool {
    path == "crates/ay/src/cmd_consumer_smoke.rs" || path.starts_with("crates/ay/tests/")
}

fn rust_embedding_sources(
    repo_root: &Path,
    inventory: &Path,
    schema: &Path,
    artifacts: &[PathBuf],
    downstream_logs: &[PathBuf],
    model_checker_consumer_logs: &[PathBuf],
) -> String {
    let mut sources = vec![
        relative_path_string(repo_root, inventory),
        relative_path_string(repo_root, schema),
    ];
    sources.extend(
        artifacts
            .iter()
            .chain(downstream_logs.iter())
            .chain(model_checker_consumer_logs.iter())
            .map(|path| relative_path_string(repo_root, path)),
    );
    sources.join(", ")
}

fn model_checker_consumer_failure_summaries(path: &Path) -> Vec<String> {
    let Ok(text) = fs::read_to_string(path) else {
        return Vec::new();
    };
    text.lines()
        .filter_map(parse_model_checker_consumer_failure_line)
        .collect()
}

fn model_checker_consumer_stronger_unknown_proof_summaries(path: &Path) -> Vec<String> {
    let Ok(text) = fs::read_to_string(path) else {
        return Vec::new();
    };
    text.lines()
        .filter_map(parse_model_checker_consumer_stronger_unknown_proof_line)
        .collect()
}

fn parse_model_checker_consumer_failure_line(line: &str) -> Option<String> {
    let (case, detail) = parse_model_checker_consumer_failure_parts(line)?;
    if is_model_checker_consumer_stronger_unknown_proof(&detail) {
        return None;
    }
    if detail.is_empty() {
        Some(case.to_string())
    } else {
        Some(format!("{case} ({detail})"))
    }
}

fn parse_model_checker_consumer_stronger_unknown_proof_line(line: &str) -> Option<String> {
    let (case, detail) = parse_model_checker_consumer_failure_parts(line)?;
    is_model_checker_consumer_stronger_unknown_proof(&detail).then(|| case.to_string())
}

fn parse_model_checker_consumer_failure_parts(line: &str) -> Option<(String, String)> {
    let clean = strip_ansi_codes(line);
    let clean = clean.trim();
    if !clean.starts_with("Testing: ") || !clean.contains("FAIL") {
        return None;
    }
    let body = clean.trim_start_matches("Testing: ").trim();
    let (case, rest) = body
        .split_once(" ... ")
        .map_or((body, ""), |(case, rest)| (case.trim(), rest.trim()));
    if case.is_empty() {
        return None;
    }
    let detail = rest
        .split_once("(expected ")
        .and_then(|(_, tail)| tail.strip_suffix(')'))
        .map(|tail| format!("expected {tail}"))
        .unwrap_or_else(|| rest.to_string());
    Some((case.to_string(), detail))
}

fn is_model_checker_consumer_stronger_unknown_proof(detail: &str) -> bool {
    detail == "expected UNKNOWN, got PROOF"
}

fn strip_ansi_codes(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(ch) = chars.next() {
        if ch == '\u{1b}' && chars.peek() == Some(&'[') {
            chars.next();
            for code in chars.by_ref() {
                if code.is_ascii_alphabetic() {
                    break;
                }
            }
        } else {
            out.push(ch);
        }
    }
    out
}

fn first_items(items: &[String], limit: usize) -> String {
    if items.is_empty() {
        return "none".to_string();
    }
    let mut shown = items.iter().take(limit).cloned().collect::<Vec<_>>();
    if items.len() > limit {
        shown.push(format!("+{} more", items.len() - limit));
    }
    shown.join("; ")
}

fn c_api_ffi_surface_evidence(repo_root: &Path) -> Value {
    let spec = surface_spec("c_api_ffi").expect("C API / FFI spec");
    let headers = [
        repo_root.join("crates/ay-ffi/include/ay.h"),
        repo_root.join("crates/ay-ffi/include/ay_z3_compat.h"),
    ];
    let tests = [
        repo_root.join("crates/ay-ffi/tests/c_consumer.c"),
        repo_root.join("crates/ay-ffi/tests/group_ffi.rs"),
    ];
    let header_count = headers.iter().filter(|path| path.is_file()).count();
    let test_count = tests.iter().filter(|path| path.is_file()).count();
    surface_evidence_value(
        spec.id,
        CheckStatus::Fail,
        format!(
            "header sources present={header_count}/{}; consumer test sources present={test_count}/{}; checked-in FFI result packets=0/1",
            headers.len(),
            tests.len()
        ),
        spec.goal,
        "checked-in ay-ffi result packet is missing; default z3-audit still runs cargo test -p ay-ffi --test group_ffi live",
        spec.command,
        "crates/ay-ffi/include, crates/ay-ffi/tests",
    )
}

fn surface_spec(id: &str) -> Option<&'static SurfaceSpec> {
    BROADER_SURFACE_SPECS.iter().find(|spec| spec.id == id)
}

fn latest_eval_result(repo_root: &Path, eval_id: &str) -> Option<(PathBuf, Value)> {
    let dir = repo_root.join("evals/results").join(eval_id);
    let mut candidates = fs::read_dir(dir)
        .ok()?
        .filter_map(Result::ok)
        .map(|entry| entry.path().join("results.json"))
        .filter(|path| path.is_file())
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.into_iter().rev().find_map(|path| {
        let value = read_json_file(&path)?;
        raw_eval_result_packet(&value).then_some((path, value))
    })
}

fn latest_reference_packets(
    repo_root: &Path,
    eval_ids: &[&str],
    reference_solver: &str,
) -> Vec<(PathBuf, Value)> {
    eval_ids
        .iter()
        .filter_map(|eval_id| {
            latest_eval_result_with_reference(repo_root, eval_id, reference_solver)
        })
        .collect()
}

fn split_current_eval_packets(
    repo_root: &Path,
    packets: Vec<(PathBuf, Value)>,
    current_head: Option<&str>,
) -> (Vec<(PathBuf, Value)>, Vec<String>) {
    let mut current = Vec::new();
    let mut stale = Vec::new();
    for (path, value) in packets {
        if eval_result_current_for_repo(&value, repo_root, current_head) {
            current.push((path, value));
        } else {
            stale.push(format!(
                "{}@{}",
                path.display(),
                eval_result_commit(&value).unwrap_or_else(|| "unknown".to_string())
            ));
        }
    }
    (current, stale)
}

fn latest_eval_result_with_reference(
    repo_root: &Path,
    eval_id: &str,
    reference_solver: &str,
) -> Option<(PathBuf, Value)> {
    let dir = repo_root.join("evals/results").join(eval_id);
    let mut candidates = fs::read_dir(dir)
        .ok()?
        .filter_map(Result::ok)
        .map(|entry| entry.path().join("results.json"))
        .filter(|path| path.is_file())
        .collect::<Vec<_>>();
    candidates.sort();
    candidates.into_iter().rev().find_map(|path| {
        let value = read_json_file(&path)?;
        let actual = value.pointer("/comparison/reference_solver")?.as_str()?;
        (actual == reference_solver).then_some((path, value))
    })
}

fn raw_eval_result_packet(value: &Value) -> bool {
    value.pointer("/settings/benchmark_count").is_some() && value.get("comparison").is_some()
}

#[cfg(test)]
fn eval_result_current_for_head(value: &Value, current_head: Option<&str>) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    eval_result_commit(value).is_some_and(|commit| commit_matches_head(&commit, current_head))
}

fn eval_result_current_for_repo(
    value: &Value,
    repo_root: &Path,
    current_head: Option<&str>,
) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    eval_result_commit(value)
        .is_some_and(|commit| commit_matches_solver_evidence_tree(repo_root, &commit, current_head))
}

fn eval_result_commit(value: &Value) -> Option<String> {
    value
        .pointer("/environment/ay_build_commit")
        .or_else(|| value.pointer("/environment/git_commit"))
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|commit| !commit.is_empty())
        .map(ToString::to_string)
}

#[cfg(test)]
fn scoreboard_current_for_head(value: &Value, current_head: Option<&str>) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    scoreboard_commit(value).is_some_and(|commit| commit_matches_head(&commit, current_head))
}

fn scoreboard_current_for_repo(
    value: &Value,
    repo_root: &Path,
    current_head: Option<&str>,
) -> bool {
    let Some(current_head) = current_head else {
        return true;
    };
    scoreboard_commit(value)
        .is_some_and(|commit| commit_matches_solver_evidence_tree(repo_root, &commit, current_head))
}

fn scoreboard_commit(value: &Value) -> Option<String> {
    value
        .pointer("/source_commit")
        .or_else(|| value.pointer("/tool_provenance/source_commit"))
        .or_else(|| value.pointer("/tool_provenance/commit"))
        .or_else(|| value.pointer("/environment/ay_build_commit"))
        .or_else(|| value.pointer("/environment/git_commit"))
        .and_then(Value::as_str)
        .map(str::trim)
        .filter(|commit| !commit.is_empty())
        .map(ToString::to_string)
}

fn scoreboard_dirty(value: &Value) -> bool {
    ["/source_dirty", "/git_dirty", "/environment/git_dirty"]
        .iter()
        .any(|pointer| value_bool(value, pointer).unwrap_or(false))
}

fn scoreboard_passes(value: &Value) -> bool {
    value_bool(value, "/soundness").unwrap_or(false)
        && value_u64(value, "/variants/default/summary/total") > 0
        && value_u64(value, "/variants/default/summary/wrong") == 0
        && value_u64(value, "/variants/default/summary/invalid") == 0
        && reference_disagreement_count(value) == 0
        && reference_only_solved_count(value) == 0
        && !scoreboard_dirty(value)
}

fn read_json_file(path: &Path) -> Option<Value> {
    let text = fs::read_to_string(path).ok()?;
    serde_json::from_str(&text).ok()
}

fn public_clone_log_passes(path: &Path) -> bool {
    let Ok(text) = fs::read_to_string(path) else {
        return false;
    };
    text.contains("public-clone-check: PASS cargo_metadata_locked")
        && text.contains("public-clone-check: PASS release_build")
        && text.contains("public-clone-check: version ")
        && text.contains("public-clone-check: overall PASS")
        && !text.contains("public-clone-check: FAIL ")
}

#[cfg(test)]
fn public_clone_log_current_for_head(path: &Path, current_head: Option<&str>) -> bool {
    if !public_clone_log_passes(path) {
        return false;
    }
    let Some(current_head) = current_head else {
        return true;
    };
    public_clone_log_commit(path).is_some_and(|commit| commit_matches_head(&commit, current_head))
}

fn public_clone_log_current_for_repo(
    path: &Path,
    repo_root: &Path,
    current_head: Option<&str>,
) -> bool {
    if !public_clone_log_passes(path) {
        return false;
    }
    let Some(current_head) = current_head else {
        return true;
    };
    public_clone_log_commit(path)
        .is_some_and(|commit| commit_matches_audited_tree(repo_root, &commit, current_head))
}

fn public_clone_log_commit(path: &Path) -> Option<String> {
    let text = fs::read_to_string(path).ok()?;
    text.lines().find_map(|line| {
        if let Some((_, tail)) = line.split_once(" commit=") {
            return tail
                .split_whitespace()
                .next()
                .map(str::trim)
                .filter(|commit| !commit.is_empty())
                .map(ToString::to_string);
        }
        if let Some((_, tail)) = line.split_once(" build.commit=") {
            return tail
                .split_whitespace()
                .next()
                .map(str::trim)
                .filter(|commit| !commit.is_empty())
                .map(ToString::to_string);
        }
        None
    })
}

fn downstream_smoke_packet_passes(value: &Value) -> bool {
    let overall_pass = value
        .pointer("/overall/status")
        .and_then(Value::as_str)
        .is_some_and(|status| status.eq_ignore_ascii_case("pass"))
        || value
            .get("overall")
            .and_then(Value::as_str)
            .is_some_and(|status| status.eq_ignore_ascii_case("pass"));
    let launch_candidate = value
        .pointer("/evidence/launch_candidate")
        .and_then(Value::as_bool)
        .unwrap_or(false)
        || value
            .pointer("/summary/launch_candidate")
            .and_then(Value::as_bool)
            .unwrap_or(false);
    overall_pass && launch_candidate
}

fn model_validation_packet_passes(value: &Value) -> bool {
    let status_pass = value
        .get("status")
        .or_else(|| value.get("overall"))
        .or_else(|| value.pointer("/summary/status"))
        .and_then(Value::as_str)
        .is_some_and(|status| status.eq_ignore_ascii_case("pass"));
    let invalid = value
        .get("invalid_model_count")
        .or_else(|| value.pointer("/summary/invalid_model_count"))
        .and_then(Value::as_u64)
        .unwrap_or(u64::MAX);
    let checked = value
        .get("model_checked_count")
        .or_else(|| value.pointer("/summary/model_checked_count"))
        .and_then(Value::as_u64)
        .unwrap_or(0);
    status_pass && invalid == 0 && checked > 0
}

fn model_sources(
    repo_root: &Path,
    scoreboard_path: &Path,
    model_check_path: &Path,
    model_packets: &[PathBuf],
) -> String {
    let mut sources = vec![
        relative_path_string(repo_root, scoreboard_path),
        relative_path_string(repo_root, model_check_path),
    ];
    sources.extend(
        model_packets
            .iter()
            .map(|path| relative_path_string(repo_root, path)),
    );
    sources.join(", ")
}

fn value_u64(value: &Value, pointer: &str) -> u64 {
    value.pointer(pointer).and_then(Value::as_u64).unwrap_or(0)
}

fn value_f64(value: &Value, pointer: &str) -> Option<f64> {
    value.pointer(pointer).and_then(Value::as_f64)
}

fn value_bool(value: &Value, pointer: &str) -> Option<bool> {
    value.pointer(pointer).and_then(Value::as_bool)
}

fn eval_packet_benchmark_count(packets: &[(PathBuf, Value)]) -> u64 {
    packets
        .iter()
        .map(|(_, value)| value_u64(value, "/settings/benchmark_count"))
        .sum()
}

fn eval_packet_comparison_sum(packets: &[(PathBuf, Value)], pointer: &str) -> u64 {
    packets
        .iter()
        .map(|(_, value)| value_u64(value, pointer))
        .sum()
}

fn zero_benchmark_eval_packets(repo_root: &Path, packets: &[(PathBuf, Value)]) -> Vec<String> {
    packets
        .iter()
        .filter(|(_, value)| value_u64(value, "/settings/benchmark_count") == 0)
        .map(|(path, _)| relative_path_string(repo_root, path))
        .collect()
}

fn no_concrete_agreement_eval_packets(
    repo_root: &Path,
    packets: &[(PathBuf, Value)],
) -> Vec<String> {
    packets
        .iter()
        .filter(|(_, value)| value_u64(value, "/comparison/agree") == 0)
        .map(|(path, _)| relative_path_string(repo_root, path))
        .collect()
}

fn eval_packet_result_count(
    packets: &[(PathBuf, Value)],
    result_field: &str,
    result_value: &str,
) -> u64 {
    packets
        .iter()
        .map(|(_, value)| result_count(value, result_field, result_value))
        .sum()
}

fn eval_packet_result_counts(
    packets: &[(PathBuf, Value)],
    result_field: &str,
) -> BTreeMap<String, u64> {
    let mut counts = BTreeMap::new();
    for (_, value) in packets {
        add_result_counts(&mut counts, value, result_field);
    }
    counts
}

fn eval_packet_reference_solved_missing_ay_result_counts(
    packets: &[(PathBuf, Value)],
) -> BTreeMap<String, u64> {
    let mut counts = BTreeMap::new();
    for (_, value) in packets {
        add_reference_solved_missing_ay_result_counts(&mut counts, value);
    }
    counts
}

fn smt_eval_status(value: &Value, current: bool, dirty: bool) -> CheckStatus {
    if !current
        || dirty
        || value_u64(value, "/settings/benchmark_count") == 0
        || value_u64(value, "/comparison/disagree") != 0
    {
        return CheckStatus::Fail;
    }
    if result_count(value, "ay_result", "error") != 0
        || result_count(value, "ref_result", "error") != 0
    {
        return CheckStatus::FailError;
    }

    let mut reference_solved_missing_ay_counts = BTreeMap::new();
    add_reference_solved_missing_ay_result_counts(&mut reference_solved_missing_ay_counts, value);
    if reference_solved_missing_ay_counts
        .values()
        .copied()
        .sum::<u64>()
        != 0
    {
        return reference_solved_missing_failure_status(&reference_solved_missing_ay_counts);
    }

    CheckStatus::Pass
}

fn smt_eval_breakdown(
    repo_root: &Path,
    eval_id: &str,
    path: &Path,
    value: &Value,
    status: CheckStatus,
    current: bool,
    dirty: bool,
) -> String {
    let mut ay_counts = BTreeMap::new();
    let mut ref_counts = BTreeMap::new();
    let mut reference_solved_missing_ay_counts = BTreeMap::new();
    add_result_counts(&mut ay_counts, value, "ay_result");
    add_result_counts(&mut ref_counts, value, "ref_result");
    add_reference_solved_missing_ay_result_counts(&mut reference_solved_missing_ay_counts, value);
    let current_label = if current { "current" } else { "stale" };
    let commit = eval_result_commit(value).unwrap_or_else(|| "unknown".to_string());
    let examples = smt_ref_only_examples(value, SMT_REF_ONLY_EXAMPLE_LIMIT);
    format!(
        "{eval_id}{{status={}; packet={current_label}@{commit}; dirty={dirty}; benchmarks={}; agree={}; disagree={}; ay_only={}; reference_solved_missing={}; reference_solved_missing_ay_results={}; ay_results={}; ref_results={}; top_reference_solved_missing={}; source={}}}",
        status.as_str(),
        value_u64(value, "/settings/benchmark_count"),
        value_u64(value, "/comparison/agree"),
        value_u64(value, "/comparison/disagree"),
        value_u64(value, "/comparison/ay_only"),
        value_u64(value, "/comparison/ref_only"),
        count_summary(&reference_solved_missing_ay_counts),
        count_summary(&ay_counts),
        count_summary(&ref_counts),
        if examples.is_empty() {
            "none".to_string()
        } else {
            examples.join(",")
        },
        relative_path_string(repo_root, path)
    )
}

fn result_count(value: &Value, result_field: &str, result_value: &str) -> u64 {
    let Some(items) = value
        .get("comparisons")
        .or_else(|| value.get("items"))
        .and_then(Value::as_array)
    else {
        return 0;
    };
    items
        .iter()
        .filter(|item| {
            item.get(result_field)
                .and_then(Value::as_str)
                .is_some_and(|result| result == result_value)
        })
        .count()
        .try_into()
        .expect("result count fits in u64")
}

fn add_result_counts(counts: &mut BTreeMap<String, u64>, value: &Value, result_field: &str) {
    let Some(items) = value
        .get("comparisons")
        .or_else(|| value.get("items"))
        .and_then(Value::as_array)
    else {
        return;
    };
    for item in items {
        if let Some(result) = item.get(result_field).and_then(Value::as_str) {
            *counts.entry(result.to_string()).or_insert(0) += 1;
        }
    }
}

fn add_reference_solved_missing_ay_result_counts(
    counts: &mut BTreeMap<String, u64>,
    value: &Value,
) {
    let Some(items) = value
        .get("comparisons")
        .or_else(|| value.get("items"))
        .and_then(Value::as_array)
    else {
        return;
    };
    for item in items {
        if item
            .get("agreement")
            .and_then(Value::as_str)
            .is_none_or(|agreement| agreement != "ref_only")
        {
            continue;
        }
        if let Some(result) = item.get("ay_result").and_then(Value::as_str) {
            *counts.entry(result.to_string()).or_insert(0) += 1;
        }
    }
}

fn smt_ref_only_examples(value: &Value, limit: usize) -> Vec<String> {
    let Some(items) = value
        .get("comparisons")
        .or_else(|| value.get("items"))
        .and_then(Value::as_array)
    else {
        return Vec::new();
    };

    let mut examples = items
        .iter()
        .filter(|item| {
            item.get("agreement")
                .and_then(Value::as_str)
                .is_some_and(|agreement| agreement == "ref_only")
        })
        .map(|item| {
            let ay_time = item
                .get("ay_time_sec")
                .and_then(Value::as_f64)
                .unwrap_or(0.0);
            let name = benchmark_name(item);
            let ay_result = item
                .get("ay_result")
                .and_then(Value::as_str)
                .unwrap_or("unknown");
            let ref_result = item
                .get("ref_result")
                .and_then(Value::as_str)
                .unwrap_or("unknown");
            (
                ay_time,
                format!("{name}:ay={ay_result},ref={ref_result},ay_time={ay_time:.3}s"),
            )
        })
        .collect::<Vec<_>>();
    examples.sort_by(|(a, _), (b, _)| b.partial_cmp(a).unwrap_or(std::cmp::Ordering::Equal));
    examples
        .into_iter()
        .take(limit)
        .map(|(_, summary)| summary)
        .collect()
}

fn benchmark_name(item: &Value) -> String {
    let raw = item
        .get("benchmark")
        .or_else(|| item.get("file"))
        .or_else(|| item.get("path"))
        .and_then(Value::as_str)
        .unwrap_or("unknown");
    Path::new(raw)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or(raw)
        .to_string()
}

fn merge_counts(target: &mut BTreeMap<String, u64>, source: &BTreeMap<String, u64>) {
    for (key, value) in source {
        *target.entry(key.clone()).or_insert(0) += value;
    }
}

fn reference_solved_missing_failure_status(
    reference_solved_missing_ay_counts: &BTreeMap<String, u64>,
) -> CheckStatus {
    if reference_solved_missing_ay_counts
        .get("error")
        .copied()
        .unwrap_or(0)
        != 0
    {
        CheckStatus::FailError
    } else if reference_solved_missing_ay_counts
        .get("timeout")
        .copied()
        .unwrap_or(0)
        != 0
    {
        CheckStatus::FailTimeout
    } else if reference_solved_missing_ay_counts
        .get("unknown")
        .copied()
        .unwrap_or(0)
        != 0
    {
        CheckStatus::FailUnknown
    } else {
        CheckStatus::Fail
    }
}

fn smt_failure_status(
    ay_counts: &BTreeMap<String, u64>,
    ref_counts: &BTreeMap<String, u64>,
) -> CheckStatus {
    if ay_counts.get("error").copied().unwrap_or(0) != 0
        || ref_counts.get("error").copied().unwrap_or(0) != 0
    {
        CheckStatus::FailError
    } else if ay_counts.get("timeout").copied().unwrap_or(0) != 0 {
        CheckStatus::FailTimeout
    } else if ay_counts.get("unknown").copied().unwrap_or(0) != 0 {
        CheckStatus::FailUnknown
    } else {
        CheckStatus::Fail
    }
}

fn add_check_status_count(counts: &mut BTreeMap<&'static str, u64>, status: CheckStatus) {
    *counts.entry(status.as_str()).or_insert(0) += 1;
}

fn check_status_count_summary(counts: &BTreeMap<&'static str, u64>) -> String {
    [
        CheckStatus::Pass,
        CheckStatus::Fail,
        CheckStatus::FailTimeout,
        CheckStatus::FailUnknown,
        CheckStatus::FailError,
    ]
    .into_iter()
    .map(|status| {
        format!(
            "{}:{}",
            status.as_str(),
            counts.get(status.as_str()).copied().unwrap_or(0)
        )
    })
    .collect::<Vec<_>>()
    .join(",")
}

fn count_summary(counts: &BTreeMap<String, u64>) -> String {
    if counts.is_empty() {
        return "none".to_string();
    }
    let mut keys = ["sat", "unsat", "unknown", "timeout", "error"]
        .into_iter()
        .map(ToString::to_string)
        .collect::<Vec<_>>();
    for key in counts.keys() {
        if !keys.contains(key) {
            keys.push(key.clone());
        }
    }
    keys.into_iter()
        .filter_map(|key| counts.get(&key).map(|count| format!("{key}:{count}")))
        .collect::<Vec<_>>()
        .join(",")
}

fn summarize_list(items: &[String], limit: usize) -> String {
    if items.len() <= limit {
        return items.join(", ");
    }
    let mut shown = items.iter().take(limit).cloned().collect::<Vec<_>>();
    shown.push(format!("... +{} more", items.len() - limit));
    shown.join(", ")
}

fn reference_disagreement_count(value: &Value) -> u64 {
    value
        .pointer("/reference_comparison/default")
        .and_then(Value::as_object)
        .map(|object| {
            object
                .values()
                .map(|reference| value_u64(reference, "/definitive_disagree"))
                .sum()
        })
        .unwrap_or(0)
}

fn reference_only_solved_count(value: &Value) -> u64 {
    value
        .pointer("/reference_comparison/default")
        .and_then(Value::as_object)
        .map(|object| {
            object
                .values()
                .map(|reference| value_u64(reference, "/reference_only_solved"))
                .sum()
        })
        .unwrap_or(0)
}

fn tsv_status_counts(path: &Path, passing_status: &str) -> (usize, usize) {
    let Ok(text) = fs::read_to_string(path) else {
        return (0, 0);
    };
    let mut total = 0usize;
    let mut passing = 0usize;
    for line in text.lines().skip(1) {
        let cells = line.split('\t').collect::<Vec<_>>();
        if cells.len() < 3 {
            continue;
        }
        total += 1;
        if cells[2] == passing_status {
            passing += 1;
        }
    }
    (total, passing)
}

fn find_named_files(root: &Path, needle: &str, suffix: &str, limit: usize) -> Vec<PathBuf> {
    fn visit(dir: &Path, needle: &str, suffix: &str, limit: usize, out: &mut Vec<PathBuf>) {
        if out.len() >= limit {
            return;
        }
        let Ok(entries) = fs::read_dir(dir) else {
            return;
        };
        let mut paths = entries
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .collect::<Vec<_>>();
        paths.sort();
        for path in paths {
            if out.len() >= limit {
                return;
            }
            if path.is_dir() {
                if should_skip_artifact_scan_dir(&path) {
                    continue;
                }
                visit(&path, needle, suffix, limit, out);
            } else if path
                .file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.contains(needle) && name.ends_with(suffix))
            {
                out.push(path);
            }
        }
    }

    let mut out = Vec::new();
    visit(root, needle, suffix, limit, &mut out);
    out
}

fn should_skip_artifact_scan_dir(path: &Path) -> bool {
    let name = path.file_name().and_then(|name| name.to_str());
    matches!(name, Some(".git" | "target")) || path.join(".git").is_dir()
}

fn find_named_files_in_roots(
    roots: &[PathBuf],
    needle: &str,
    suffix: &str,
    limit: usize,
) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for root in roots {
        if out.len() >= limit {
            break;
        }
        out.extend(find_named_files(
            root,
            needle,
            suffix,
            limit.saturating_sub(out.len()),
        ));
    }
    out.sort();
    out.dedup();
    out
}

fn relative_path_string(repo_root: &Path, path: &Path) -> String {
    path.strip_prefix(repo_root)
        .unwrap_or(path)
        .display()
        .to_string()
}

fn load_reference_cache(repo_root: &Path, path: &Path) -> Result<ReferenceCache> {
    let resolved = resolve_repo_path(repo_root, path);
    let text =
        fs::read_to_string(&resolved).with_context(|| format!("read {}", resolved.display()))?;
    let value: Value = serde_json::from_str(&text)
        .with_context(|| format!("parse JSON {}", resolved.display()))?;
    let schema = string_field(&value, "schema")?;
    if schema != REFERENCE_CACHE_SCHEMA {
        anyhow::bail!("schema mismatch: expected {REFERENCE_CACHE_SCHEMA}, got {schema}");
    }

    let generator = field(&value, "generator")?;
    let z3_version = string_field(generator, "z3_version")?;

    let basic = field(&value, "basic_smt_transcript")?;
    let basic_id = string_field(basic, "id")?;
    if basic_id != BASIC_SMT_TRANSCRIPT_ID {
        anyhow::bail!(
            "basic_smt_transcript.id mismatch: expected {BASIC_SMT_TRANSCRIPT_ID}, got {basic_id}"
        );
    }
    let basic_input_sha256 = string_field(basic, "input_sha256")?;
    let expected_basic_input_sha256 = sha256_hex(BASIC_SMT_TRANSCRIPT_INPUT.as_bytes());
    if basic_input_sha256 != expected_basic_input_sha256 {
        anyhow::bail!(
            "basic SMT transcript input hash mismatch: expected {expected_basic_input_sha256}, got {basic_input_sha256}"
        );
    }
    let basic_smt_transcript = CachedTranscript {
        input_sha256: basic_input_sha256,
        status_code: optional_i32_field(basic, "status_code")?,
        stdout: string_field(basic, "stdout")?,
        stderr: string_field(basic, "stderr")?,
    };

    let chc = field(&value, "chc_certificate_obligations")?;
    let problem = string_field(chc, "problem")?;
    if problem != CHC_CANARY_PROBLEM {
        anyhow::bail!("CHC canary problem mismatch: expected {CHC_CANARY_PROBLEM}, got {problem}");
    }
    let problem_sha256 = string_field(chc, "problem_sha256")?;
    let actual_problem_sha256 = sha256_file(&repo_root.join(&problem))
        .with_context(|| format!("hash CHC canary {}", repo_root.join(&problem).display()))?;
    if problem_sha256 != actual_problem_sha256 {
        anyhow::bail!(
            "CHC canary hash mismatch: expected current {actual_problem_sha256}, got cached {problem_sha256}; regenerate the cache"
        );
    }
    let obligation_values = array_field(chc, "obligations")?;
    if obligation_values.is_empty() {
        anyhow::bail!("reference cache has no CHC obligations");
    }
    let mut obligations = BTreeMap::new();
    for obligation in obligation_values {
        let sha256 = string_field(obligation, "sha256")?;
        let cached = CachedObligation {
            name: string_field(obligation, "name")?,
            status_code: optional_i32_field(obligation, "status_code")?,
            stdout_first_line: string_field(obligation, "stdout_first_line")?,
        };
        if obligations.insert(sha256.clone(), cached).is_some() {
            anyhow::bail!("duplicate CHC obligation hash in reference cache: {sha256}");
        }
    }
    let surface_evidence = parse_surface_evidence(value.get(SURFACE_EVIDENCE_KEY))?;

    Ok(ReferenceCache {
        path: resolved,
        z3_version,
        basic_smt_transcript,
        chc_obligations: CachedChcObligations {
            problem_sha256,
            obligations,
        },
        surface_evidence,
    })
}

fn parse_surface_evidence(
    value: Option<&Value>,
) -> Result<BTreeMap<String, CachedSurfaceEvidence>> {
    let Some(value) = value else {
        return Ok(BTreeMap::new());
    };
    let schema = string_field(value, "schema")?;
    if schema != SURFACE_EVIDENCE_SCHEMA {
        anyhow::bail!(
            "replacement surface evidence schema mismatch: expected {SURFACE_EVIDENCE_SCHEMA}, got {schema}"
        );
    }
    let rows = array_field(value, "surfaces")?;
    let mut evidence = BTreeMap::new();
    for row in rows {
        let id = string_field(row, "id")?;
        let status = CheckStatus::parse(&string_field(row, "status")?)?;
        let cached = CachedSurfaceEvidence {
            status,
            current: string_field(row, "current")?,
            goal: string_field(row, "goal")?,
            missing: string_field(row, "missing")?,
            command: string_field(row, "command")?,
            source: string_field(row, "source")?,
        };
        if evidence.insert(id.clone(), cached).is_some() {
            anyhow::bail!("duplicate replacement surface evidence row: {id}");
        }
    }
    Ok(evidence)
}

fn validate_cached_chc_obligations(
    cache: &ReferenceCache,
    problem: &Path,
    obligations: &[AuthenticatedChcArtifact],
) -> Result<usize> {
    let problem_sha256 =
        sha256_file(problem).with_context(|| format!("hash CHC canary {}", problem.display()))?;
    if problem_sha256 != cache.chc_obligations.problem_sha256 {
        anyhow::bail!(
            "current CHC problem hash {problem_sha256} does not match cache hash {}; regenerate {}",
            cache.chc_obligations.problem_sha256,
            cache.path.display()
        );
    }
    if obligations.len() != cache.chc_obligations.obligations.len() {
        anyhow::bail!(
            "CHC obligation count mismatch: emitted {} but cache has {}",
            obligations.len(),
            cache.chc_obligations.obligations.len()
        );
    }

    let mut matched = BTreeSet::new();
    for obligation in obligations {
        let sha256 = &obligation.sha256;
        let cached = cache
            .chc_obligations
            .obligations
            .get(sha256)
            .with_context(|| {
                format!(
                    "emitted CHC obligation {} has hash {sha256}, which is absent from cache {}",
                    obligation.path.display(),
                    cache.path.display()
                )
            })?;
        if cached.status_code != Some(0) || cached.stdout_first_line.trim() != "unsat" {
            anyhow::bail!(
                "cached CHC obligation {} ({sha256}) is not an UNSAT pass: status={:?} stdout_first_line={:?}",
                cached.name,
                cached.status_code,
                cached.stdout_first_line
            );
        }
        matched.insert(sha256.clone());
    }

    if matched.len() != cache.chc_obligations.obligations.len() {
        let extra = cache
            .chc_obligations
            .obligations
            .keys()
            .filter(|sha| !matched.contains(*sha))
            .cloned()
            .collect::<Vec<_>>();
        anyhow::bail!(
            "cache has unmatched CHC obligation hashes: {}",
            extra.join(", ")
        );
    }

    Ok(matched.len())
}

fn field<'a>(value: &'a Value, key: &str) -> Result<&'a Value> {
    value
        .get(key)
        .with_context(|| format!("missing JSON field `{key}`"))
}

fn string_field(value: &Value, key: &str) -> Result<String> {
    field(value, key)?
        .as_str()
        .map(ToString::to_string)
        .with_context(|| format!("JSON field `{key}` is not a string"))
}

fn array_field<'a>(value: &'a Value, key: &str) -> Result<&'a Vec<Value>> {
    field(value, key)?
        .as_array()
        .with_context(|| format!("JSON field `{key}` is not an array"))
}

fn optional_i32_field(value: &Value, key: &str) -> Result<Option<i32>> {
    let field = field(value, key)?;
    if field.is_null() {
        return Ok(None);
    }
    let number = field
        .as_i64()
        .with_context(|| format!("JSON field `{key}` is not an integer or null"))?;
    i32::try_from(number)
        .map(Some)
        .with_context(|| format!("JSON field `{key}` is outside i32 range"))
}

fn sha256_file(path: &Path) -> Result<String> {
    let bytes = fs::read(path).with_context(|| format!("read {}", path.display()))?;
    Ok(sha256_hex(&bytes))
}

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    hex_digest(&digest)
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

fn find_drat_trim() -> Option<PathBuf> {
    drat_trim_candidates()
        .into_iter()
        .find(|path| path.is_file() && drat_trim_is_genuine(path))
}

/// Discovery order for an external drat-trim. Note the checked-in `bin/drat-trim`
/// shim is intentionally absent: it is a `#!/bin/bash; exit 0` no-op and must
/// never satisfy a proof-replay row. Even if a mock is placed on one of these
/// paths, `drat_trim_is_genuine` rejects it.
fn drat_trim_candidates() -> Vec<PathBuf> {
    let mut candidates = Vec::new();
    if let Some(explicit) = env::var_os("DRAT_TRIM") {
        candidates.push(PathBuf::from(explicit));
    }
    if let Some(on_path) = find_on_path("drat-trim") {
        candidates.push(on_path);
    }
    for fixed in [
        "/tmp/drat-trim/drat-trim",
        "/usr/local/bin/drat-trim",
        "/opt/homebrew/bin/drat-trim",
    ] {
        candidates.push(PathBuf::from(fixed));
    }
    candidates
}

/// A trustworthy drat-trim must (1) report `s VERIFIED` for a real refutation
/// and (2) report `s NOT VERIFIED` for a bogus one. This positive+negative
/// control pair rejects both the silent `exit 0` mock (fails the positive
/// control: no `s VERIFIED`) and an "always VERIFIED" mock (fails the negative
/// control: never emits `s NOT VERIFIED`). drat-trim returns exit code 0 even
/// when it rejects a proof, so the verdict is read from stdout, not the status.
fn drat_trim_is_genuine(path: &Path) -> bool {
    // Positive control: a 1-variable UNSAT formula with an empty-clause proof.
    let positive = drat_trim_probe(path, "pos", b"p cnf 1 2\n1 0\n-1 0\n", b"0\n")
        .map(|out| out.contains("s VERIFIED") && !out.contains("s NOT VERIFIED"))
        .unwrap_or(false);
    // Negative control: a satisfiable formula whose proof falsely claims the
    // empty clause must be rejected.
    let negative = drat_trim_probe(path, "neg", b"p cnf 2 1\n1 2 0\n", b"0\n")
        .map(|out| out.contains("s NOT VERIFIED"))
        .unwrap_or(false);
    positive && negative
}

/// Run a drat-trim candidate on an in-memory CNF + DRAT proof and return its
/// stdout. Returns `None` if the probe cannot be executed at all.
fn drat_trim_probe(path: &Path, label: &str, cnf: &[u8], proof: &[u8]) -> Option<String> {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .ok()?
        .as_nanos();
    let pid = std::process::id();
    let dir = env::temp_dir();
    let cnf_path = dir.join(format!("ay-audit-drat-probe-{label}-{pid}-{stamp}.cnf"));
    let proof_path = dir.join(format!("ay-audit-drat-probe-{label}-{pid}-{stamp}.drat"));
    fs::write(&cnf_path, cnf).ok()?;
    fs::write(&proof_path, proof).ok()?;
    let output = ProcessCommand::new(path)
        .arg(&cnf_path)
        .arg(&proof_path)
        .output();
    let _ = fs::remove_file(&cnf_path);
    let _ = fs::remove_file(&proof_path);
    let output = output.ok()?;
    Some(String::from_utf8_lossy(&output.stdout).into_owned())
}

fn find_on_path(program: &str) -> Option<PathBuf> {
    let path = env::var_os("PATH")?;
    env::split_paths(&path)
        .map(|dir| dir.join(program))
        .find(|candidate| candidate.is_file())
}

/// Locate a cadical SAT solver used as the DIMACS reference solver, preferring
/// the in-repo build path the documented audit command references.
fn find_cadical(repo_root: &Path) -> Option<PathBuf> {
    let in_repo = repo_root.join("reference/cadical/build/cadical");
    if in_repo.is_file() {
        return Some(in_repo);
    }
    find_on_path("cadical")
}

/// One external dependency the full-replacement audit relies on, for the
/// reviewer-facing tool inventory. Purely informational — it never affects the
/// verdict; the surface/proof rows own pass/fail.
struct ToolStatus {
    name: &'static str,
    purpose: &'static str,
    path: Option<PathBuf>,
    /// `Some(true/false)` when a genuineness control was run (drat-trim);
    /// `None` when only presence was checked.
    genuine: Option<bool>,
    install_hint: &'static str,
}

impl ToolStatus {
    fn to_json(&self) -> Value {
        json!({
            "name": self.name,
            "purpose": self.purpose,
            "path": self.path.as_ref().map(|p| p.display().to_string()),
            "present": self.path.is_some(),
            "genuine": self.genuine,
            "install_hint": self.install_hint,
        })
    }
}

/// Inventory the external checkers/solvers a full-replacement self-audit needs,
/// so an external reviewer can immediately see what to install. `drat-trim` is
/// genuineness-checked (a no-op mock is reported as absent); the rest are
/// presence-only here because their proof/surface rows already validate them by
/// actually emitting and replaying real artifacts.
fn external_tool_inventory(repo_root: &Path, z3: &str, alethe_checker: &str) -> Vec<ToolStatus> {
    let drat = find_drat_trim();
    vec![
        ToolStatus {
            name: "z3",
            purpose: "reference baselines + SMT-LIB/CHC differential",
            path: find_on_path(z3),
            genuine: None,
            install_hint: "package manager (e.g. `brew install z3`) or build Z3Prover/z3",
        },
        ToolStatus {
            name: "drat-trim",
            purpose: "DIMACS DRAT external proof replay",
            genuine: Some(drat.is_some()),
            path: drat,
            install_hint: "build marijnheule/drat-trim (`make`) into /tmp/drat-trim/ or PATH",
        },
        ToolStatus {
            name: "carcara",
            purpose: "SMT Alethe proof replay",
            path: find_on_path(alethe_checker),
            genuine: None,
            install_hint: "`cargo install --git https://github.com/ufmg-smite/carcara.git` (installs the `carcara` binary)",
        },
        ToolStatus {
            name: "lean",
            purpose: "Lean4 proof replay",
            path: find_on_path("lean"),
            genuine: None,
            install_hint: "install via elan (the Lean toolchain manager)",
        },
        ToolStatus {
            name: "cadical",
            purpose: "DIMACS SAT reference solver",
            path: find_cadical(repo_root),
            genuine: None,
            install_hint: "build arminbiere/cadical into reference/cadical/build/ or PATH",
        },
        ToolStatus {
            name: "golem",
            purpose: "CHC reference solver",
            path: find_on_path("golem"),
            genuine: None,
            install_hint: "build usi-verification-and-security/golem (requires OpenSMT)",
        },
    ]
}

fn run_command_capture(repo_root: &Path, program: &Path, args: &[&str]) -> io::Result<Output> {
    ProcessCommand::new(program)
        .args(args)
        .current_dir(repo_root)
        .output()
}

fn run_command_capture_with_stdin(
    repo_root: &Path,
    program: &Path,
    args: &[&str],
    input: &[u8],
) -> io::Result<Output> {
    let mut child = ProcessCommand::new(program)
        .args(args)
        .current_dir(repo_root)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    let mut stdin = child.stdin.take().ok_or_else(|| {
        io::Error::new(
            io::ErrorKind::BrokenPipe,
            format!("failed to capture stdin for {}", program.display()),
        )
    })?;

    std::thread::scope(|scope| {
        let writer = scope.spawn(move || stdin.write_all(input));
        let output = child.wait_with_output();
        let write_result = writer
            .join()
            .map_err(|_| io::Error::other("stdin writer thread panicked"))?;
        match (output, write_result) {
            (Ok(output), Ok(())) => Ok(output),
            (Err(error), _) | (Ok(_), Err(error)) => Err(error),
        }
    })
}

fn run_builtin_smokes(
    ay: &Path,
    reference_cache: Option<&ReferenceCache>,
    reference_cache_error: Option<&str>,
    reference_cache_path: &Path,
) -> Vec<AuditCheck> {
    vec![
        compare_basic_smt_transcript(
            ay,
            reference_cache,
            reference_cache_error,
            reference_cache_path,
        ),
        check_ay_param_discovery(ay),
        check_ay_unsupported_option(ay),
    ]
}

fn compare_basic_smt_transcript(
    ay: &Path,
    reference_cache: Option<&ReferenceCache>,
    reference_cache_error: Option<&str>,
    reference_cache_path: &Path,
) -> AuditCheck {
    let cache = match reference_cache {
        Some(cache) => cache,
        None => {
            return AuditCheck::fail(
                "basic_smt_transcript",
                format!(
                    "cannot compare basic SMT transcript without a valid reference cache at {}: {}",
                    reference_cache_path.display(),
                    reference_cache_error.unwrap_or("unknown cache load error")
                ),
            )
            .with_command(format!(
                "ay z3-audit --generate-reference-cache {} --z3 <z3>",
                reference_cache_path.display()
            ));
        }
    };

    let ay_output = run_program_stdin(
        ay.as_os_str(),
        &["--z3-mode", "-in"],
        BASIC_SMT_TRANSCRIPT_INPUT,
    );
    match ay_output {
        Ok(ay_output)
            if ay_output.status.code() == cache.basic_smt_transcript.status_code
                && String::from_utf8_lossy(&ay_output.stdout).as_ref()
                    == cache.basic_smt_transcript.stdout.as_str()
                && String::from_utf8_lossy(&ay_output.stderr).as_ref()
                    == cache.basic_smt_transcript.stderr.as_str() =>
        {
            AuditCheck::pass(
                "basic_smt_transcript",
                format!(
                    "ay --z3-mode -in matches cached Z3 baseline on a basic QF_LIA model transcript; cache={}",
                    cache.path.display()
                ),
            )
            .with_command(format!(
                "{} --z3-mode -in  # compared with cached {} from {}",
                ay.display(),
                BASIC_SMT_TRANSCRIPT_ID,
                cache.path.display()
            ))
        }
        Ok(ay_output) => AuditCheck::fail(
            "basic_smt_transcript",
            format!(
                "transcript mismatch against cached Z3 baseline: ay_status={:?} cached_status={:?} ay_stdout={:?} cached_stdout={:?} ay_stderr={:?} cached_stderr={:?}",
                ay_output.status.code(),
                cache.basic_smt_transcript.status_code,
                String::from_utf8_lossy(&ay_output.stdout),
                cache.basic_smt_transcript.stdout,
                String::from_utf8_lossy(&ay_output.stderr),
                cache.basic_smt_transcript.stderr
            ),
        )
        .with_command(format!(
            "{} --z3-mode -in  # compared with cached {} from {}",
            ay.display(),
            BASIC_SMT_TRANSCRIPT_ID,
            cache.path.display()
        )),
        Err(error) => AuditCheck::fail(
            "basic_smt_transcript",
            format!("failed to run ay transcript smoke: {error}"),
        )
        .with_command(format!("{} --z3-mode -in", ay.display())),
    }
}

fn check_ay_param_discovery(ay: &Path) -> AuditCheck {
    let command = format!("{} -p", ay.display());
    match ProcessCommand::new(ay).arg("-p").output() {
        Ok(output)
            if output.status.success()
                && String::from_utf8_lossy(&output.stdout).contains("Global parameters")
                && String::from_utf8_lossy(&output.stdout).contains("timeout (unsigned int)")
                && output.stderr.is_empty() =>
        {
            AuditCheck::pass(
                "z3_param_discovery_smoke",
                "ay -p exposes the scoped Z3-style parameter subset without stderr noise",
            )
            .with_command(command)
        }
        Ok(output) => AuditCheck::fail(
            "z3_param_discovery_smoke",
            format!(
                "unexpected ay -p result: status={:?} stdout={:?} stderr={:?}",
                output.status.code(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ),
        )
        .with_command(command),
        Err(error) => AuditCheck::fail(
            "z3_param_discovery_smoke",
            format!("failed to run ay -p: {error}"),
        )
        .with_command(command),
    }
}

fn check_ay_unsupported_option(ay: &Path) -> AuditCheck {
    let command = format!("{} -tactics", ay.display());
    match ProcessCommand::new(ay).arg("-tactics").output() {
        Ok(output)
            if !output.status.success()
                && String::from_utf8_lossy(&output.stderr)
                    .contains("unsupported Z3 option '-tactics'") =>
        {
            AuditCheck::pass(
                "unsupported_z3_option_smoke",
                "unsupported Z3 tactic catalog flag fails explicitly",
            )
            .with_command(command)
        }
        Ok(output) => AuditCheck::fail(
            "unsupported_z3_option_smoke",
            format!(
                "unexpected -tactics result: status={:?} stdout={:?} stderr={:?}",
                output.status.code(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ),
        )
        .with_command(command),
        Err(error) => AuditCheck::fail(
            "unsupported_z3_option_smoke",
            format!("failed to run ay -tactics: {error}"),
        )
        .with_command(command),
    }
}

fn run_program_stdin(program: &std::ffi::OsStr, args: &[&str], input: &str) -> io::Result<Output> {
    let mut child = ProcessCommand::new(program)
        .args(args)
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;
    child
        .stdin
        .as_mut()
        .expect("piped stdin")
        .write_all(input.as_bytes())?;
    child.wait_with_output()
}

fn run_repo_command(
    id: &'static str,
    repo_root: &Path,
    rendered: &str,
    program: &str,
    args: &[&str],
) -> AuditCheck {
    let displayed_command = rendered_repo_command(program, rendered);
    let mut command = ProcessCommand::new(program);
    command.args(args).current_dir(repo_root);
    if program == "cargo" {
        command.env("CARGO_SKIP_CACHE", "1");
    }

    match command.output() {
        Ok(output) if output.status.success() => {
            AuditCheck::pass(id, "command passed").with_command(displayed_command)
        }
        Ok(output) => AuditCheck::fail(
            id,
            format!(
                "command exited {:?}: stdout_tail={:?} stderr_tail={:?}",
                output.status.code(),
                tail_text(&String::from_utf8_lossy(&output.stdout)),
                tail_text(&String::from_utf8_lossy(&output.stderr))
            ),
        )
        .with_command(displayed_command),
        Err(error) => AuditCheck::fail(id, format!("failed to run command: {error}"))
            .with_command(displayed_command),
    }
}

fn run_smt_model_validation_smoke(repo_root: &Path) -> AuditCheck {
    let rendered = rendered_repo_command(
        "cargo",
        "cargo test -p ay-dpll --test group_theory_misc sat_validates_model -- --nocapture",
    );
    let output = ProcessCommand::new("cargo")
        .args([
            "test",
            "-p",
            "ay-dpll",
            "--test",
            "group_theory_misc",
            "sat_validates_model",
            "--",
            "--nocapture",
        ])
        .env("CARGO_SKIP_CACHE", "1")
        .current_dir(repo_root)
        .output();
    let Ok(output) = output else {
        return AuditCheck::fail(
            SMT_MODEL_VALIDATION_SMOKE_ID,
            "model_validation_tests_passed=0/0; failed=0; model_checked_count=0; invalid_model_count=0; capability_failures=1; failing_tests=cargo_spawn_failed",
        )
        .with_command(rendered);
    };

    let text = command_output_text(&output);
    let summary = parse_cargo_test_summary(&text);
    let failing_tests = failing_cargo_tests(&text);
    let finding = model_validation_finding(summary, &failing_tests);
    let status = if output.status.success()
        && summary.is_some_and(|summary| summary.failed_tests == 0 && summary.passed_tests > 0)
    {
        CheckStatus::Pass
    } else {
        CheckStatus::Fail
    };

    match status {
        CheckStatus::Pass => AuditCheck::pass(SMT_MODEL_VALIDATION_SMOKE_ID, finding),
        _ => AuditCheck::fail(SMT_MODEL_VALIDATION_SMOKE_ID, finding),
    }
    .with_command(rendered)
}

/// Remove shell double-quoting from a command token so it can be passed
/// directly to a spawned process (which performs no shell word-splitting or
/// quote removal). Handles both `--features="cli"` (quoted value after `=`) and
/// a fully quoted token like `"cli"`; tokens without matching surrounding
/// quotes are returned unchanged.
fn strip_shell_quotes(token: &str) -> String {
    if let Some((flag, value)) = token.split_once('=') {
        if let Some(inner) = value
            .strip_prefix('"')
            .and_then(|rest| rest.strip_suffix('"'))
        {
            return format!("{flag}={inner}");
        }
        return token.to_string();
    }
    token
        .strip_prefix('"')
        .and_then(|rest| rest.strip_suffix('"'))
        .unwrap_or(token)
        .to_string()
}

fn rendered_repo_command(program: &str, rendered: &str) -> String {
    if program == "cargo" && !rendered.starts_with("CARGO_SKIP_CACHE=") {
        format!("CARGO_SKIP_CACHE=1 {rendered}")
    } else {
        rendered.to_string()
    }
}

fn command_output_text(output: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

#[derive(Clone, Copy)]
struct CargoTestSummary {
    passed_tests: u64,
    failed_tests: u64,
    ignored_tests: u64,
    measured_tests: u64,
    filtered_out: u64,
}

fn parse_cargo_test_summary(text: &str) -> Option<CargoTestSummary> {
    text.lines().find_map(|line| {
        let line = line.trim();
        let rest = line
            .strip_prefix("test result: ok.")
            .or_else(|| line.strip_prefix("test result: FAILED."))?
            .trim();
        let mut summary = CargoTestSummary {
            passed_tests: u64::MAX,
            failed_tests: u64::MAX,
            ignored_tests: u64::MAX,
            measured_tests: u64::MAX,
            filtered_out: u64::MAX,
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
            let Ok(count) = first.parse::<u64>() else {
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
        (summary.passed_tests != u64::MAX
            && summary.failed_tests != u64::MAX
            && summary.ignored_tests != u64::MAX
            && summary.measured_tests != u64::MAX
            && summary.filtered_out != u64::MAX)
            .then_some(summary)
    })
}

fn failing_cargo_tests(text: &str) -> Vec<String> {
    let mut out = text
        .lines()
        .filter_map(|line| {
            let line = line.trim();
            let rest = line.strip_prefix("test ")?;
            let name = rest.strip_suffix(" ... FAILED")?;
            Some(name.to_string())
        })
        .collect::<Vec<_>>();
    out.sort();
    out.dedup();
    out
}

fn model_validation_finding(summary: Option<CargoTestSummary>, failing_tests: &[String]) -> String {
    let Some(summary) = summary else {
        return format!(
            "model_validation_tests_passed=0/0; failed=0; model_checked_count=0; invalid_model_count=0; capability_failures=1; failing_tests={}",
            if failing_tests.is_empty() {
                "unparseable_cargo_test_summary".to_string()
            } else {
                failing_tests.join(",")
            }
        );
    };
    let total = summary.passed_tests + summary.failed_tests + summary.ignored_tests;
    format!(
        "model_validation_tests_passed={}/{}; failed={}; ignored={}; filtered_out={}; model_checked_count={}; invalid_model_count=0; capability_failures={}; failing_tests={}",
        summary.passed_tests,
        total,
        summary.failed_tests,
        summary.ignored_tests,
        summary.filtered_out,
        summary.passed_tests,
        summary.failed_tests,
        if failing_tests.is_empty() {
            "none".to_string()
        } else {
            failing_tests.join(",")
        }
    )
}

fn tail_text(text: &str) -> String {
    let lines = text.lines().collect::<Vec<_>>();
    lines
        .iter()
        .skip(lines.len().saturating_sub(12))
        .copied()
        .collect::<Vec<_>>()
        .join("\n")
}

fn print_human_summary(
    scope: Z3AuditScope,
    verdict: &str,
    repo_root: &Path,
    ay: &Path,
    z3: &str,
    reference_cache: &Path,
    passed_checks: usize,
    failed_checks: usize,
    passed_surfaces: usize,
    failed_surfaces: usize,
    passed_proof_rows: usize,
    failed_proof_rows: usize,
    full_replacement_ready: bool,
    scoped_cli_ready: bool,
    surfaces: &[AuditSurface],
    proof_inventory: &[ProofInventoryRow],
    checks: &[AuditCheck],
    tool_inventory: &[ToolStatus],
) {
    println!("=== Z3 Replacement Audit ===");
    println!("scope={}", scope.as_str());
    println!("verdict={verdict}");
    println!("repo_root={}", repo_root.display());
    println!("ay={}", ay.display());
    println!("z3={z3} (used when regenerating the reference cache or refreshing SMT evidence)");
    println!("reference_cache={}", reference_cache.display());
    println!("full_replacement_ready={full_replacement_ready}");
    println!("scoped_cli_ready={scoped_cli_ready}");
    println!(
        "surfaces_passed={passed_surfaces} surfaces_failed={failed_surfaces} checks_passed={passed_checks} checks_failed={failed_checks} proof_rows_passed={passed_proof_rows} proof_rows_failed={failed_proof_rows}"
    );
    if !full_replacement_ready && verdict == "fail" {
        println!(
            "truth=FAIL means at least one required full-replacement capability or evidence row is not Ready."
        );
    } else if !full_replacement_ready {
        println!(
            "truth=PASS means the audited rows are internally consistent; broad Z3 replacement remains false until every required surface is Ready."
        );
    }
    println!();

    println!("=== Replacement Surface Table ===");
    println!("status | surface | current | goal | missing");
    println!("--- | --- | --- | --- | ---");
    for surface in surfaces {
        println!(
            "{} | {} | {} | {} | {}",
            surface.status.as_str(),
            surface.surface,
            surface.current,
            surface.goal,
            surface.missing
        );
        if let Some(command) = &surface.command {
            println!("  command: {command}");
        }
        if let Some(source) = &surface.source {
            println!("  source: {source}");
        }
    }
    println!();

    println!("=== Native Proof Inventory ===");
    println!("status | proof surface | current | goal | finding");
    println!("--- | --- | --- | --- | ---");
    for row in proof_inventory {
        println!(
            "{} | {} | {} | {} | {}",
            row.status.as_str(),
            row.surface,
            row.current,
            row.goal,
            row.finding
        );
        println!("  command: {}", row.command);
    }
    println!();

    println!("=== Evidence Checks ===");
    for check in checks {
        println!(
            "[{}] {}: {}",
            check.status.as_str(),
            check.id,
            check.finding
        );
        if let Some(command) = &check.command {
            println!("  command: {command}");
        }
    }

    println!("=== External Tool Inventory ===");
    println!("Reviewer self-audit dependencies (informational; does not affect the verdict).");
    for tool in tool_inventory {
        let state = match (&tool.path, tool.genuine) {
            (Some(path), Some(true)) => format!("present+genuine: {}", path.display()),
            (Some(path), Some(false)) => format!("present but NOT genuine: {}", path.display()),
            (Some(path), None) => format!("present: {}", path.display()),
            (None, Some(_)) => "MISSING (or only a no-op mock)".to_string(),
            (None, None) => "MISSING".to_string(),
        };
        println!("[{}] {} — {}", tool.name, state, tool.purpose);
        if tool.path.is_none() {
            println!("  install: {}", tool.install_hint);
        }
    }
}

#[cfg(test)]
mod tests;
