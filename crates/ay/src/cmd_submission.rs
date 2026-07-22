// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Competition submission artifact generators.
//!
//! These commands generate small, auditable submission skeletons for the
//! 2026 solver competitions. They intentionally do not submit anything.

mod chc_worker;
mod satcomp_matrix;
mod satcomp_repair;

use std::collections::HashSet;
use std::env;
use std::fs;
#[cfg(feature = "submission-live")]
use std::io::Read;
use std::io::{self, BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use anyhow::{bail, Context, Result};
use clap::{Args, Subcommand, ValueEnum};
use serde_json::{json, Value as JsonValue};
use sha2::{Digest, Sha256};

use crate::build_info::BUILD_INFO;

use self::chc_worker::{run_chc_comp_worker, ChcCompBenchmarkCase};

const SAT_DEFAULT_DIR: &str = "sat-comp-2026";
const CHC_DEFAULT_DIR: &str = "chc-comp-2026";
const PB_DEFAULT_DIR: &str = "pb-comp-2026";
const SMT_DEFAULT_DIR: &str = "smt-comp-2026";

const CHC_DEFAULT_ARCHIVE_URL: &str =
    "https://zenodo.org/records/PLACEHOLDER/files/ay-chccomp-2026-linux-x86_64.tar.gz";
const CHC_ZENODO_ARTIFACT_NAME: &str = "ay-chccomp-2026-linux-x86_64.tar.gz";
const CHC_ZENODO_BRANCH_PREFIX: &str = "ay-chccomp-2026-submit";
const CHC_ZENODO_DEFAULT_REPO: &str = "https://github.com/chc-comp/chc-comp-2026.git";
const CHC_ZENODO_GITHUB_REPO: &str = "chc-comp/chc-comp-2026";
const CHC_ZENODO_DEFAULT_REPORT_DIR: &str = "target/chccomp-zenodo-submit";
const CHC_ZENODO_DEFAULT_CHECKOUT: &str = "target/chc-comp-2026-submit";
// CHC-COMP external submission credentials are operator-owned machinery.
// Only the machine/account with operator auth can publish this PR. If this
// auth is unavailable, this is not the publishing machine: leave this policy
// block alone and ask the user before editing it.
const CHC_ZENODO_REQUIRED_GITHUB_OWNER: &str = "operator";
const CHC_ZENODO_REQUIRED_GITHUB_LOGIN: &str = "operator";
const CHC_ZENODO_FORBIDDEN_GITHUB_LOGINS: &[&str] = &["example-login"];
const CHC_ZENODO_GIT_AUTHOR_NAME: &str = "Andrew Yates";
const CHC_ZENODO_GIT_AUTHOR_EMAIL: &str = "operator@users.noreply.github.com";
const CHC_ZENODO_DEFAULT_FORK_SSH_KEY: &str = "~/.ssh/id_ed25519_operator_chc_comp_2026";
const CHC_DEFAULT_TRACKS: &str =
    "BOOL,BV,BV-Lin,LRA-Lin,LIA-Lin,LIA,LIA-Arrays,LIA-Lin-Arrays,ADT-LIA,ADT-LIA-Arrays,mixed_LIA_LRA";
const CHC_WORKER_FIXED_LANES: &[&str] = &[
    "triangle-location",
    "o0-arrays",
    "recursive-adt",
    "erc777-safe",
    "package-preflight",
    "reference-verdict-audit",
];
const CHC_LATE_PREFLIGHT_SCHEMA: &str = "ay.chccomp-late-entry-preflight/v1";
const CHC_WORKER_REPORT_SCHEMA: &str = "ay.chccomp-worker-report/v1";
const CHC_WORKER_AUDIT_SCHEMA: &str = "ay.chccomp-worker-audit/v1";
const CHC_WORKER_DEFAULT_REPORT_DIR: &str = "the development design notes";
const CHC_BASELINE_COMPARE_DEFAULT_BASELINE: &str = "benchmarks/chc-extra-small-lia-baseline.json";
const CHC_BASELINE_COMPARE_DEFAULT_AY: &str = "target/release/ay";
const CHC_BASELINE_COMPARE_DEFAULT_OUTPUT_DIR: &str = "target/chc-baseline-compare";
const CHC_OFFICIAL_SOURCE_URL: &str = "https://chc-comp.github.io/";
const CHC_NORMAL_SOLVER_BENCHMARK_DEADLINE: &str = "2026-04-25";
const CHC_TECHNICAL_SOLVER_RESUBMISSION_DEADLINE: &str = "2026-05-02";
// Current chc-comp26-benchmarks set-file categories. Keep this in sync with
// the competition repository, not only the public website's abbreviated list.
const CHC_ALLOWED_TRACKS: &[&str] = &[
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
const CHC_OFFICIAL_2026_TRACKS: &[&str] = &[
    "LIA-Lin",
    "LIA-Nonlin",
    "LIA-Lin-Arrays",
    "LIA-Nonlin-Arrays",
    "ADT-LIA",
    "ADT-LIA-Arrays",
    "LRA-Lin",
    "BV-Lin",
    "BV-Nonlin",
];
const CHC_TRACK_MODEL_ROWS: &[(&str, Option<&str>, &str, &str)] = &[
    (
        "BOOL",
        None,
        "internal-smoke-category",
        "Bool appears in benchmark logic but is not a public CHC-COMP 2026 track.",
    ),
    (
        "BV",
        Some("BV-Nonlin"),
        "official-track-alias",
        "Local set-file/category name for the official BV-Nonlin track.",
    ),
    (
        "BV-Lin",
        Some("BV-Lin"),
        "official-track",
        "Official CHC-COMP 2026 track.",
    ),
    (
        "LRA-Lin",
        Some("LRA-Lin"),
        "official-track",
        "Official CHC-COMP 2026 track.",
    ),
    (
        "LIA-Lin",
        Some("LIA-Lin"),
        "official-track",
        "Official CHC-COMP 2026 track.",
    ),
    (
        "LIA",
        Some("LIA-Nonlin"),
        "official-track-alias",
        "Local set-file/category name for the official LIA-Nonlin track.",
    ),
    (
        "LIA-Arrays",
        Some("LIA-Nonlin-Arrays"),
        "official-track-alias",
        "Local set-file/category name for the official LIA-Nonlin-Arrays track.",
    ),
    (
        "LIA-Lin-Arrays",
        Some("LIA-Lin-Arrays"),
        "official-track",
        "Official CHC-COMP 2026 track.",
    ),
    (
        "ADT-LIA",
        Some("ADT-LIA"),
        "official-track",
        "Official CHC-COMP 2026 track.",
    ),
    (
        "ADT-LIA-Arrays",
        Some("ADT-LIA-Arrays"),
        "official-track",
        "Official CHC-COMP 2026 track.",
    ),
    (
        "mixed_LIA_LRA",
        None,
        "internal-smoke-category",
        "Local mixed Int/Real routing guard; not a public CHC-COMP 2026 track.",
    ),
];
const CHC_TRACK_MODEL_CLAIM_POLICY: &str =
    "A CHC-COMP verify/preflight pass over samples is local category-smoke evidence, not full-suite CHC-COMP solved-count, PAR-2, package, or submission-readiness evidence.";
const CHC_TRACK_MODEL_LEGACY_FIELD_NOTE: &str =
    "Legacy JSON field `tracks` is retained for compatibility and means local set-file categories; new consumers should read `local_set_file_categories` or `track_model`.";
const CHC_LATE_REQUIRED_ARCHIVE_MEMBERS: &[(&str, u32)] = &[
    ("ay/ay", 0o755),
    ("ay/run_solver.sh", 0o755),
    ("ay/LICENSE", 0o644),
    ("ay/README.md", 0o644),
];
const CHC_LATE_VALID_STATUSES: &[&str] = &["sat", "unsat", "unknown"];

const PB_OFFICIAL_SOURCE_URL: &str = "https://www.cril.univ-artois.fr/PB26/";
const PB_PREFLIGHT_SCHEMA: &str = "ay.pbcomp-verify/v1";
const PB26_GENERIC_PACKAGE_GUARD: &str = "PB-COMP generic submission packaging is disabled for PB26; stage real PB26 submissions with competition/pb26/prepare_submission.sh --archive and validate them with scripts/check_pb26_submission.sh or ay submission preflight pb-comp-verify";

const SMT_DEFAULT_ARCHIVE_URL: &str =
    "https://zenodo.org/records/PLACEHOLDER/files/ay-smt-comp-2026.tar.gz";
const SMT_DEFAULT_SYSTEM_DESCRIPTION_URL: &str =
    "https://zenodo.org/records/PLACEHOLDER/files/ay-system-description.pdf";
const SUBMISSION_EXECUTABLE_NAMES: &[&str] = &[
    "ay",
    "build.sh",
    "run.sh",
    "run_solver.sh",
    "run_solver_mv.sh",
    "run_solver_incr.sh",
];

/// Generate competition submission artifacts.
#[derive(Subcommand)]
pub(crate) enum SubmissionCommand {
    /// Generate submission skeletons for one or more competitions.
    #[command(subcommand)]
    Generate(GenerateTarget),
    /// Build complete local submission package directories and archives.
    #[command(subcommand)]
    Package(PackageTarget),
    /// Build and verify a competition package with one operator-facing command.
    #[command(subcommand)]
    Prepare(PrepareTarget),
    /// Run native readiness gates against generated submission packages.
    #[command(subcommand)]
    Gate(GateTarget),
    /// Run local-only competition preflights.
    #[command(subcommand)]
    Preflight(PreflightTarget),
    /// Run distributed worker jobs and evidence audits.
    #[command(subcommand)]
    Worker(WorkerTarget),
    /// Run external submission flows.
    #[command(subcommand)]
    Submit(SubmitTarget),
}

/// Submission generator targets.
#[derive(Subcommand)]
pub(crate) enum GenerateTarget {
    /// Generate all supported competition skeletons under OUTPUT.
    All(AllOptions),
    /// Generate SAT-COMP 2026 private-repository files.
    Sat(SatOptions),
    /// Generate CHC-COMP 2026 pull-request files.
    Chc(ChcOptions),
    /// Generate PB-COMP 2026 portal-upload files.
    Pb(PbOptions),
    /// Generate SMT-COMP 2026 pull-request files.
    Smt(SmtOptions),
}

/// Submission package builder targets.
#[derive(Subcommand)]
pub(crate) enum PackageTarget {
    /// Package all supported competitions under OUTPUT.
    All(PackageAllOptions),
    /// Package SAT-COMP 2026 private-repository files.
    Sat(PackageOneOptions),
    /// Package CHC-COMP 2026 PR files and tool archive.
    Chc(ChcPackageOptions),
    /// Package PB-COMP 2026 portal-upload archive.
    Pb(PackageOneOptions),
    /// Package SMT-COMP 2026 PR JSON and solver archive.
    Smt(SmtPackageOptions),
}

/// Submission prepare targets.
#[derive(Subcommand)]
pub(crate) enum PrepareTarget {
    /// Package, gate, and verify a CHC-COMP 2026 submission.
    Chc(ChcPrepareOptions),
}

/// Submission gate targets.
#[derive(Subcommand)]
pub(crate) enum GateTarget {
    /// Gate all supported competition packages under PACKAGE.
    All(GateAllOptions),
    /// Gate a SAT-COMP 2026 package.
    Sat(GateOneOptions),
    /// Gate a CHC-COMP 2026 package.
    Chc(GateOneOptions),
    /// Gate a PB-COMP 2026 package.
    Pb(GateOneOptions),
    /// Gate an SMT-COMP 2026 package.
    Smt(GateOneOptions),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
#[clap(rename_all = "kebab-case")]
pub(crate) enum SubmissionPrepareProfile {
    /// Local host package and smoke checks; useful before cross-compiling.
    Local,
    /// Submission artifact checks: Linux/static/public URL required, local smoke skipped.
    Submission,
    /// Prove-ready checks: submission requirements plus benchmark smoke.
    Prove,
}

impl SubmissionPrepareProfile {
    fn gate_config(self) -> GateConfig {
        match self {
            Self::Local => GateConfig {
                require_linux: false,
                require_static: false,
                require_public_urls: false,
                skip_smoke: false,
            },
            Self::Submission => GateConfig {
                require_linux: true,
                require_static: true,
                require_public_urls: true,
                skip_smoke: true,
            },
            Self::Prove => GateConfig {
                require_linux: true,
                require_static: true,
                require_public_urls: true,
                skip_smoke: false,
            },
        }
    }

    fn require_current_build(self) -> bool {
        matches!(self, Self::Submission | Self::Prove)
    }

    fn skip_benchmark_smoke(self, benchmarks_root: Option<&Path>) -> bool {
        match self {
            Self::Local | Self::Submission => benchmarks_root.is_none(),
            Self::Prove => false,
        }
    }

    fn as_str(self) -> &'static str {
        match self {
            Self::Local => "local",
            Self::Submission => "submission",
            Self::Prove => "prove",
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, ValueEnum)]
#[clap(rename_all = "kebab-case")]
pub(crate) enum ChcBaselineCompareProfile {
    /// Use the timeout recorded in the baseline; direct regression gate.
    SameTimeout,
    /// Run an explicit short timeout; warning-only proxy evidence.
    FastProxy,
}

impl ChcBaselineCompareProfile {
    fn as_str(self) -> &'static str {
        match self {
            Self::SameTimeout => "same-timeout",
            Self::FastProxy => "fast-proxy",
        }
    }
}

/// Submission preflight targets.
#[derive(Subcommand)]
pub(crate) enum PreflightTarget {
    /// Run the CHC-COMP 2026 late-entry local preflight.
    ChcLateEntry(ChcLateEntryPreflightOptions),
    /// Compare CHC baseline evidence with timeout-safe run classification.
    #[command(name = "chc-baseline-compare")]
    ChcBaselineCompare(ChcBaselineCompareOptions),
    /// Run Rust-owned SAT-COMP repair diagnostics.
    #[command(name = "sat-comp-repair", subcommand)]
    SatCompRepair(satcomp_repair::SatCompRepairCommand),
    /// Run a Rust-owned SAT-COMP matrix preflight.
    #[command(name = "sat-matrix", subcommand)]
    SatMatrix(satcomp_matrix::SatCompMatrixCommand),
    /// Run a prove-ready CHC-COMP package and benchmark audit.
    #[command(name = "chc-comp-verify")]
    ChcCompVerify(ChcCompVerifyOptions),
    /// Run a prove-ready PB-COMP 2026 package and wrapper audit.
    #[command(name = "pb-comp-verify")]
    PbCompVerify(PbCompVerifyOptions),
    /// Build and smoke every competition entry AY currently claims.
    #[command(name = "competition-audit")]
    CompetitionAudit(CompetitionAuditOptions),
    /// Estimate current competition scores from local official/proxy corpora.
    #[command(name = "competition-score-estimate")]
    CompetitionScoreEstimate(CompetitionScoreEstimateOptions),
}

/// Distributed worker targets.
#[derive(Subcommand)]
pub(crate) enum WorkerTarget {
    /// Run CHC-COMP worker jobs and report audits.
    #[command(name = "chc-comp", subcommand)]
    ChcComp(ChcCompWorkerCommand),
}

/// CHC-COMP worker commands.
#[derive(Subcommand)]
pub(crate) enum ChcCompWorkerCommand {
    /// Verify that this machine can participate in the CHC-COMP worker pool.
    Bootstrap(ChcWorkerBootstrapOptions),
    /// Print deterministic CHC-COMP worker lanes.
    #[command(name = "shard-plan")]
    ShardPlan(ChcWorkerShardPlanOptions),
    /// Run one CHC-COMP worker lane and write evidence reports.
    Run(ChcWorkerRunOptions),
    /// Audit CHC-COMP worker reports for promotion readiness.
    Audit(ChcWorkerAuditOptions),
}

/// External submission targets.
#[derive(Subcommand)]
pub(crate) enum SubmitTarget {
    /// Build, publish to Zenodo, and open the CHC-COMP 2026 PR.
    #[command(name = "chc-comp-zenodo")]
    ChcCompZenodo(ChcCompZenodoSubmitOptions),
}

#[derive(Args)]
pub(crate) struct AllOptions {
    /// Base output directory.
    #[arg(short, long, value_name = "DIR", default_value = "target/submissions")]
    output: PathBuf,

    /// Public CHC archive URL for the Makefile snippet.
    #[arg(long, value_name = "URL", default_value = CHC_DEFAULT_ARCHIVE_URL)]
    chc_archive_url: String,

    /// Comma-separated CHC local set-file categories or public track aliases to enter.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    chc_tracks: String,

    /// Public SMT archive URL for the submission JSON.
    #[arg(long, value_name = "URL", default_value = SMT_DEFAULT_ARCHIVE_URL)]
    smt_archive_url: String,

    /// SHA-256 of the SMT archive, when known.
    #[arg(long, value_name = "SHA256")]
    smt_archive_sha256: Option<String>,

    /// Public SMT system-description URL.
    #[arg(
        long,
        value_name = "URL",
        default_value = SMT_DEFAULT_SYSTEM_DESCRIPTION_URL
    )]
    smt_system_description_url: String,

    /// Mark the SMT JSON as a final submission.
    #[arg(long = "smt-final")]
    smt_final: bool,
}

#[derive(Args)]
pub(crate) struct SatOptions {
    /// Output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submissions/sat-comp-2026"
    )]
    output: PathBuf,
}

#[derive(Args)]
pub(crate) struct ChcOptions {
    /// Output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submissions/chc-comp-2026"
    )]
    output: PathBuf,

    /// Public archive URL to download from the CHC-COMP Makefile.
    #[arg(long, value_name = "URL", default_value = CHC_DEFAULT_ARCHIVE_URL)]
    archive_url: String,

    /// Comma-separated CHC local set-file categories or public track aliases to enter.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    tracks: String,
}

#[derive(Args)]
pub(crate) struct PbOptions {
    /// Output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submissions/pb-comp-2026"
    )]
    output: PathBuf,
}

#[derive(Args)]
pub(crate) struct SmtOptions {
    /// Output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submissions/smt-comp-2026"
    )]
    output: PathBuf,

    /// Public archive URL for the SMT-COMP submission JSON.
    #[arg(long, value_name = "URL", default_value = SMT_DEFAULT_ARCHIVE_URL)]
    archive_url: String,

    /// SHA-256 of the archive, when known.
    #[arg(long, value_name = "SHA256")]
    archive_sha256: Option<String>,

    /// Public system-description URL.
    #[arg(
        long,
        value_name = "URL",
        default_value = SMT_DEFAULT_SYSTEM_DESCRIPTION_URL
    )]
    system_description_url: String,

    /// Mark the generated SMT JSON as final.
    #[arg(long = "final")]
    final_submission: bool,
}

#[derive(Args)]
pub(crate) struct PackageAllOptions {
    /// Base output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submission-packages"
    )]
    output: PathBuf,

    /// ay executable to copy into package archives.
    #[arg(long, value_name = "FILE")]
    ay_bin: Option<PathBuf>,

    /// Public CHC archive URL for the generated PR fragment.
    #[arg(long, value_name = "URL", default_value = CHC_DEFAULT_ARCHIVE_URL)]
    chc_archive_url: String,

    /// Comma-separated CHC local set-file categories or public track aliases to enter.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    chc_tracks: String,

    /// Public SMT archive URL for the generated submission JSON.
    #[arg(long, value_name = "URL", default_value = SMT_DEFAULT_ARCHIVE_URL)]
    smt_archive_url: String,

    /// Public SMT system-description URL.
    #[arg(
        long,
        value_name = "URL",
        default_value = SMT_DEFAULT_SYSTEM_DESCRIPTION_URL
    )]
    smt_system_description_url: String,

    /// Mark the generated SMT JSON as final.
    #[arg(long = "smt-final")]
    smt_final: bool,
}

#[derive(Args)]
pub(crate) struct PackageOneOptions {
    /// Output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submission-packages"
    )]
    output: PathBuf,

    /// ay executable to copy into package archives.
    #[arg(long, value_name = "FILE")]
    ay_bin: Option<PathBuf>,
}

#[derive(Args)]
pub(crate) struct ChcPackageOptions {
    /// Output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submission-packages/chc-comp-2026"
    )]
    output: PathBuf,

    /// ay executable to copy into the CHC tool archive.
    #[arg(long, value_name = "FILE")]
    ay_bin: Option<PathBuf>,

    /// Public archive URL to download from the CHC-COMP Makefile.
    #[arg(long, value_name = "URL", default_value = CHC_DEFAULT_ARCHIVE_URL)]
    archive_url: String,

    /// Comma-separated CHC local set-file categories or public track aliases to enter.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    tracks: String,
}

#[derive(Args)]
pub(crate) struct ChcPrepareOptions {
    /// Prepared CHC-COMP package directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submission-packages/chc-comp-2026"
    )]
    output: PathBuf,

    /// ay executable to copy into the CHC tool archive.
    #[arg(long, value_name = "FILE")]
    ay_bin: Option<PathBuf>,

    /// Public archive URL to write into the generated CHC-COMP PR files.
    #[arg(long, value_name = "URL", default_value = CHC_DEFAULT_ARCHIVE_URL)]
    archive_url: String,

    /// Comma-separated CHC local set-file categories or public track aliases to enter.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    tracks: String,

    /// Preparation profile.
    #[arg(long, value_enum, default_value_t = SubmissionPrepareProfile::Local)]
    profile: SubmissionPrepareProfile,

    /// Root of a chc-comp26-benchmarks checkout containing *.set files.
    #[arg(long, value_name = "DIR")]
    benchmarks_root: Option<PathBuf>,

    /// Number of non-comment set entries to smoke per track when benchmarks are supplied.
    #[arg(long, value_name = "N", default_value_t = 1)]
    samples_per_track: usize,

    /// Wall-clock timeout for each package-wrapper benchmark smoke.
    #[arg(long, value_name = "MS", default_value_t = 30000)]
    benchmark_timeout_ms: u64,

    /// Scratch directory for archive extraction and smoke checks.
    #[arg(long, value_name = "DIR", default_value = "target/chccomp-prepare")]
    work_dir: PathBuf,

    /// JSON verification report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    json: PathBuf,

    /// Markdown verification report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    report: PathBuf,

    /// Keep existing work-dir contents before running.
    #[arg(long)]
    keep_work_dir: bool,
}

#[derive(Args)]
pub(crate) struct SmtPackageOptions {
    /// Output directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submission-packages/smt-comp-2026"
    )]
    output: PathBuf,

    /// ay executable to copy into the SMT solver archive.
    #[arg(long, value_name = "FILE")]
    ay_bin: Option<PathBuf>,

    /// Public archive URL for the SMT-COMP submission JSON.
    #[arg(long, value_name = "URL", default_value = SMT_DEFAULT_ARCHIVE_URL)]
    archive_url: String,

    /// Public system-description URL.
    #[arg(
        long,
        value_name = "URL",
        default_value = SMT_DEFAULT_SYSTEM_DESCRIPTION_URL
    )]
    system_description_url: String,

    /// Mark the generated SMT JSON as final.
    #[arg(long = "final")]
    final_submission: bool,
}

#[derive(Args)]
pub(crate) struct GateAllOptions {
    /// Base package directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submission-packages"
    )]
    package: PathBuf,

    /// Require packaged ay binaries to be Linux ELF executables.
    #[arg(long)]
    require_linux: bool,

    /// Require packaged Linux ELF binaries to be static.
    #[arg(long)]
    require_static: bool,

    /// Require generated PR files to use non-placeholder public URLs.
    #[arg(long)]
    require_public_urls: bool,

    /// Skip wrapper smoke tests that execute the packaged binary.
    #[arg(long)]
    skip_smoke: bool,
}

#[derive(Args)]
pub(crate) struct GateOneOptions {
    /// Package directory.
    #[arg(
        short,
        long,
        value_name = "DIR",
        default_value = "target/submission-packages"
    )]
    package: PathBuf,

    /// Require packaged ay binaries to be Linux ELF executables.
    #[arg(long)]
    require_linux: bool,

    /// Require packaged Linux ELF binaries to be static.
    #[arg(long)]
    require_static: bool,

    /// Require generated PR files to use non-placeholder public URLs.
    #[arg(long)]
    require_public_urls: bool,

    /// Skip wrapper smoke tests that execute the packaged binary.
    #[arg(long)]
    skip_smoke: bool,
}

#[derive(Args)]
pub(crate) struct ChcLateEntryPreflightOptions {
    /// Existing ay-chccomp-2026-linux-x86_64.tar.gz to validate.
    #[arg(long, value_name = "FILE")]
    archive: Option<PathBuf>,

    /// Fail if --archive is not supplied instead of using a local stub archive.
    #[arg(long)]
    require_real_artifact: bool,

    /// Scratch directory for stub archives and extraction checks.
    #[arg(
        long,
        value_name = "DIR",
        default_value = "target/chccomp-late-entry-preflight"
    )]
    work_dir: PathBuf,

    /// JSON report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    json: PathBuf,

    /// Markdown report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    report: PathBuf,

    /// Keep existing work-dir contents before running.
    #[arg(long)]
    keep_work_dir: bool,
}

#[derive(Args)]
pub(crate) struct ChcBaselineCompareOptions {
    /// Baseline JSON snapshot to compare against.
    #[arg(
        long,
        value_name = "FILE",
        default_value = CHC_BASELINE_COMPARE_DEFAULT_BASELINE
    )]
    baseline: PathBuf,

    /// Benchmark directory override. Defaults to benchmarks_dir from the baseline.
    #[arg(long, value_name = "DIR")]
    bench_dir: Option<PathBuf>,

    /// ay executable to run against the CHC baseline.
    #[arg(long, value_name = "FILE", default_value = CHC_BASELINE_COMPARE_DEFAULT_AY)]
    ay: PathBuf,

    /// Evidence profile. same-timeout is a direct gate; fast-proxy is warning-only.
    #[arg(long, value_enum, default_value_t = ChcBaselineCompareProfile::SameTimeout)]
    profile: ChcBaselineCompareProfile,

    /// Required for --profile fast-proxy; forbidden for same-timeout evidence.
    #[arg(long, value_name = "SECONDS")]
    timeout_sec: Option<u64>,

    /// Directory for JSON and CSV evidence reports.
    #[arg(
        long,
        value_name = "DIR",
        default_value = CHC_BASELINE_COMPARE_DEFAULT_OUTPUT_DIR
    )]
    output_dir: PathBuf,
}

#[derive(Args)]
pub(crate) struct ChcCompVerifyOptions {
    /// CHC-COMP package directory to verify.
    #[arg(
        long,
        value_name = "DIR",
        default_value = "target/submission-packages/chc-comp-2026"
    )]
    package: PathBuf,

    /// Root of a chc-comp26-benchmarks checkout containing *.set files.
    #[arg(long, value_name = "DIR")]
    benchmarks_root: Option<PathBuf>,

    /// Comma-separated CHC local set-file categories or public track aliases to audit.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    tracks: String,

    /// Number of non-comment set entries to smoke per track.
    #[arg(long, value_name = "N", default_value_t = 1)]
    samples_per_track: usize,

    /// Wall-clock timeout for each package-wrapper benchmark smoke.
    #[arg(long, value_name = "MS", default_value_t = 30000)]
    benchmark_timeout_ms: u64,

    /// Require packaged and archived ay binaries to be Linux x86_64 ELF.
    #[arg(long)]
    require_linux: bool,

    /// Require packaged and archived Linux ELF binaries to be static.
    #[arg(long)]
    require_static: bool,

    /// Require generated PR files to use non-placeholder public URLs.
    #[arg(long)]
    require_public_urls: bool,

    /// Require MANIFEST.json generated_by.commit to match this ay build.
    #[arg(long)]
    require_current_build: bool,

    /// Skip benchmark-root smoke checks.
    #[arg(long)]
    skip_benchmark_smoke: bool,

    /// Scratch directory for archive extraction and smoke checks.
    #[arg(long, value_name = "DIR", default_value = "target/chccomp-verify")]
    work_dir: PathBuf,

    /// JSON report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    json: PathBuf,

    /// Markdown report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    report: PathBuf,

    /// Keep existing work-dir contents before running.
    #[arg(long)]
    keep_work_dir: bool,
}

#[derive(Args)]
pub(crate) struct PbCompVerifyOptions {
    /// PB-COMP package directory staged by competition/pb26/prepare_submission.sh.
    #[arg(
        long,
        value_name = "DIR",
        default_value = "competition/pb26/dist/ay-pb26"
    )]
    package: PathBuf,

    /// PB-COMP package archive to validate. Defaults to PACKAGE.tar.gz when present.
    #[arg(long, value_name = "FILE")]
    archive: Option<PathBuf>,

    /// Runnable ay binary for wrapper smoke tests when the staged Linux binary cannot run locally.
    #[arg(long, value_name = "FILE")]
    runner_bin: Option<PathBuf>,

    /// VeriPB binary for optional certified-track proof validation.
    #[arg(long, value_name = "FILE")]
    veripb_bin: Option<PathBuf>,

    /// Require running the staged Linux binary locally, not only inspecting it.
    #[arg(long)]
    require_linux_runtime: bool,

    /// Require external VeriPB proof validation instead of skipping it.
    #[arg(long)]
    require_veripb: bool,

    /// Allow non-static staged binaries. This is not submission-ready for PB26.
    #[arg(long)]
    allow_nonstatic: bool,

    /// Allow packages generated from a different commit than current HEAD.
    #[arg(long)]
    allow_stale_package: bool,

    /// Allow unavailable git provenance in package metadata.
    #[arg(long)]
    allow_unavailable_git_provenance: bool,

    /// Skip archive-vs-directory validation.
    #[arg(long)]
    skip_archive_check: bool,

    /// Wall-clock timeout for the local PB package checker.
    #[arg(long, value_name = "MS", default_value_t = 120000)]
    timeout_ms: u64,

    /// JSON report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    json: PathBuf,

    /// Markdown report path.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "the development design notes"
    )]
    report: PathBuf,
}

#[derive(Args)]
pub(crate) struct CompetitionAuditOptions {
    /// Directory for scratch outputs and the generated audit summary.
    #[arg(long, value_name = "DIR", default_value = "target/competition-audit")]
    output: PathBuf,

    /// VeriPB binary to use for the PB-COMP certified-track proof smoke.
    #[arg(long, value_name = "FILE")]
    veripb_bin: Option<PathBuf>,
}

#[derive(Args)]
pub(crate) struct CompetitionScoreEstimateOptions {
    /// Directory for scratch outputs and the generated score estimate summary.
    #[arg(
        long,
        value_name = "DIR",
        default_value = "target/competition-score-estimate"
    )]
    output: PathBuf,
}

#[derive(Args)]
pub(crate) struct ChcWorkerBootstrapOptions {
    /// CHC-COMP package directory this worker will use.
    #[arg(
        long,
        value_name = "DIR",
        default_value = "target/submission-packages/chc-comp-2026"
    )]
    package: PathBuf,

    /// Root of a chc-comp26-benchmarks checkout containing *.set files.
    #[arg(long, value_name = "DIR")]
    benchmarks_root: Option<PathBuf>,

    /// Worker-local Cargo target directory convention.
    #[arg(long, value_name = "DIR", default_value = "target/chc-worker")]
    target_dir: PathBuf,

    /// Do not probe GitHub CLI auth.
    #[arg(long)]
    no_gh: bool,

    /// Do not mark a dirty worktree as a blocker in the report.
    #[arg(long)]
    allow_dirty: bool,

    /// JSON report path.
    #[arg(long, value_name = "FILE")]
    json: Option<PathBuf>,

    /// Markdown report path.
    #[arg(long, value_name = "FILE")]
    report: Option<PathBuf>,
}

#[derive(Args)]
pub(crate) struct ChcWorkerShardPlanOptions {
    /// Comma-separated CHC local set-file categories or public track aliases for the deterministic plan.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    tracks: String,

    /// Number of machines to spread generic track shards across.
    #[arg(long, value_name = "N", default_value_t = 1)]
    machines: usize,

    /// Emit JSON to stdout instead of the compact text plan.
    #[arg(long)]
    json: bool,
}

#[derive(Args)]
pub(crate) struct ChcWorkerRunOptions {
    /// GitHub issue number that owns this worker lane.
    #[arg(long, value_name = "N")]
    issue: u64,

    /// Lane name, for example triangle-location, o0-arrays, recursive-adt, erc777-safe, or track-BV.
    #[arg(long, value_name = "NAME")]
    lane: String,

    /// CHC-COMP package directory to run through the archived wrapper.
    #[arg(
        long,
        value_name = "DIR",
        default_value = "target/submission-packages/chc-comp-2026"
    )]
    package: PathBuf,

    /// Root of a chc-comp26-benchmarks checkout containing *.set files.
    #[arg(long, value_name = "DIR")]
    benchmarks_root: Option<PathBuf>,

    /// Comma-separated CHC local set-file categories or public track aliases to run.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS)]
    tracks: String,

    /// Number of non-comment set entries to run per track.
    #[arg(long, value_name = "N", default_value_t = 1)]
    samples_per_track: usize,

    /// Wall-clock timeout for each archived-wrapper benchmark run.
    #[arg(long, value_name = "MS", default_value_t = 30000)]
    benchmark_timeout_ms: u64,

    /// Worker-local Cargo target directory convention.
    #[arg(long, value_name = "DIR")]
    target_dir: Option<PathBuf>,

    /// Directory for derived worker reports.
    #[arg(
        long,
        value_name = "DIR",
        default_value = CHC_WORKER_DEFAULT_REPORT_DIR
    )]
    report_dir: PathBuf,

    /// JSON report path. Defaults under --report-dir.
    #[arg(long, value_name = "FILE")]
    json: Option<PathBuf>,

    /// Markdown report path. Defaults under --report-dir.
    #[arg(long, value_name = "FILE")]
    report: Option<PathBuf>,

    /// Skip benchmark-root smoke checks.
    #[arg(long)]
    skip_benchmark_smoke: bool,

    /// Do not fail this worker report solely because the local worktree is dirty.
    #[arg(long)]
    allow_dirty: bool,

    /// Add in-progress and owner labels before running.
    #[arg(long, value_name = "OWNER")]
    claim: Option<String>,

    /// Comment the Markdown report on the issue after running.
    #[arg(long)]
    comment_issue: bool,

    /// Move the issue to do-audit after a successful local worker run.
    #[arg(long)]
    move_do_audit: bool,

    /// Skip GitHub CLI actions and print replay commands instead.
    #[arg(long)]
    no_gh: bool,
}

#[derive(Args)]
pub(crate) struct ChcWorkerAuditOptions {
    /// Worker JSON report(s) to audit.
    #[arg(value_name = "REPORT_JSON", num_args = 1..)]
    reports: Vec<PathBuf>,

    /// Permit reports captured from a dirty local worktree.
    #[arg(long)]
    allow_dirty: bool,

    /// Permit reports whose package commit differs from the report repo commit.
    #[arg(long)]
    allow_stale_package: bool,

    /// JSON audit report path.
    #[arg(long, value_name = "FILE")]
    json: Option<PathBuf>,

    /// Markdown audit report path.
    #[arg(long, value_name = "FILE")]
    report: Option<PathBuf>,
}

#[derive(Args)]
pub(crate) struct ChcCompZenodoSubmitOptions {
    /// Preview the package/PR flow without publishing to Zenodo or pushing to GitHub.
    #[arg(long)]
    dry_run: bool,

    /// Allow tracked local source changes while building the artifact.
    #[arg(long, hide = true)]
    allow_dirty: bool,

    /// Use --ay-bin instead of running scripts/build_linux_static.sh first.
    #[arg(long)]
    skip_build: bool,

    /// Static build backend passed to scripts/build_linux_static.sh.
    #[arg(
        long,
        value_name = "TOOL",
        default_value = "zigbuild",
        value_parser = ["auto", "native", "cross", "docker", "zigbuild"],
        hide = true
    )]
    build_tool: String,

    /// Existing or expected static Linux x86_64 ay binary.
    #[arg(
        long,
        value_name = "FILE",
        default_value = "target/x86_64-unknown-linux-musl/release/ay"
    )]
    ay_bin: PathBuf,

    /// Host ay executable used to run package/gate commands.
    #[arg(long, value_name = "FILE", hide = true)]
    host_ay: Option<PathBuf>,

    /// Generated CHC package directory.
    #[arg(
        long,
        value_name = "DIR",
        default_value = "target/submission-packages/chc-comp-2026",
        hide = true
    )]
    package_dir: PathBuf,

    /// Report output directory.
    #[arg(long, value_name = "DIR", default_value = CHC_ZENODO_DEFAULT_REPORT_DIR)]
    report_dir: PathBuf,

    /// CHC-COMP tracks to include.
    #[arg(long, value_name = "TRACKS", default_value = CHC_DEFAULT_TRACKS, hide = true)]
    tracks: String,

    /// Build/package/publish only; do not push or open a PR.
    #[arg(long)]
    skip_pr: bool,

    /// Create a Zenodo draft but do not publish it. This cannot complete PR submission.
    #[arg(long, hide = true)]
    no_publish: bool,

    /// Env file containing ZENODO_API_KEY.
    #[arg(long, value_name = "FILE", default_value = "~/.env")]
    env_file: PathBuf,

    /// Environment variable name for the Zenodo token.
    #[arg(
        long,
        value_name = "NAME",
        default_value = "ZENODO_API_KEY",
        hide = true
    )]
    zenodo_token_env: String,

    /// Zenodo API base URL.
    #[arg(
        long,
        value_name = "URL",
        default_value = "https://zenodo.org",
        hide = true
    )]
    zenodo_base_url: String,

    /// Zenodo HTTP timeout in seconds.
    #[arg(long, value_name = "SECONDS", default_value_t = 180)]
    zenodo_timeout_seconds: u64,

    /// Optional Zenodo record title.
    #[arg(long, value_name = "TITLE")]
    zenodo_title: Option<String>,

    /// Zenodo creator name.
    #[arg(
        long,
        value_name = "NAME",
        default_value = "Yates, Andrew",
        hide = true
    )]
    creator_name: String,

    /// Source URL recorded in Zenodo metadata and PR text.
    #[arg(
        long,
        value_name = "URL",
        default_value = "https://github.com/alabsystems/ay",
        hide = true
    )]
    source_url: String,

    /// CHC-COMP repository to clone/fetch.
    #[arg(long, value_name = "URL", default_value = CHC_ZENODO_DEFAULT_REPO, hide = true)]
    chc_repo_url: String,

    /// Local CHC-COMP checkout path.
    #[arg(long, value_name = "DIR", default_value = CHC_ZENODO_DEFAULT_CHECKOUT, hide = true)]
    chc_checkout: PathBuf,

    /// Explicit fork remote URL. Defaults to git@github.com:<owner>/chc-comp-2026.git and still requires the checked GitHub account.
    #[arg(long, value_name = "URL", hide = true)]
    fork_repo_url: Option<String>,

    /// SSH private key used for CHC-COMP fork pushes and account proof.
    #[arg(long, value_name = "FILE", default_value = CHC_ZENODO_DEFAULT_FORK_SSH_KEY, hide = true)]
    fork_ssh_key: PathBuf,

    /// PR title.
    #[arg(
        long,
        value_name = "TITLE",
        default_value = "Add ay CHC-COMP 2026 verifier",
        hide = true
    )]
    pr_title: String,
}

pub(crate) fn run(cmd: SubmissionCommand) -> Result<()> {
    match cmd {
        SubmissionCommand::Generate(target) => match target {
            GenerateTarget::All(opts) => generate_all(&opts),
            GenerateTarget::Sat(opts) => generate_sat(&opts.output),
            GenerateTarget::Chc(opts) => {
                generate_chc(&opts.output, &opts.archive_url, &opts.tracks)
            }
            GenerateTarget::Pb(opts) => generate_pb(&opts.output),
            GenerateTarget::Smt(opts) => generate_smt(
                &opts.output,
                &opts.archive_url,
                opts.archive_sha256.as_deref(),
                &opts.system_description_url,
                opts.final_submission,
            ),
        },
        SubmissionCommand::Package(target) => match target {
            PackageTarget::All(opts) => package_all(&opts),
            PackageTarget::Sat(opts) => {
                package_sat(&opts.output.join(SAT_DEFAULT_DIR), opts.ay_bin.as_deref())
            }
            PackageTarget::Chc(opts) => package_chc(
                &opts.output,
                opts.ay_bin.as_deref(),
                &opts.archive_url,
                &opts.tracks,
            ),
            PackageTarget::Pb(opts) => {
                package_pb(&opts.output.join(PB_DEFAULT_DIR), opts.ay_bin.as_deref())
            }
            PackageTarget::Smt(opts) => package_smt(
                &opts.output,
                opts.ay_bin.as_deref(),
                &opts.archive_url,
                &opts.system_description_url,
                opts.final_submission,
            ),
        },
        SubmissionCommand::Prepare(target) => match target {
            PrepareTarget::Chc(opts) => prepare_chc_comp(&opts),
        },
        SubmissionCommand::Gate(target) => match target {
            GateTarget::All(opts) => gate_all(&opts),
            GateTarget::Sat(opts) => gate_sat(&opts.package, opts.gate_config()),
            GateTarget::Chc(opts) => gate_chc(&opts.package, opts.gate_config()),
            GateTarget::Pb(opts) => gate_pb(&opts.package, opts.gate_config()),
            GateTarget::Smt(opts) => gate_smt(&opts.package, opts.gate_config()),
        },
        SubmissionCommand::Preflight(target) => match target {
            PreflightTarget::ChcLateEntry(opts) => preflight_chc_late_entry(&opts),
            PreflightTarget::ChcBaselineCompare(opts) => compare_chc_baseline(&opts),
            PreflightTarget::SatCompRepair(cmd) => satcomp_repair::run(cmd),
            PreflightTarget::SatMatrix(cmd) => satcomp_matrix::run(cmd),
            PreflightTarget::ChcCompVerify(opts) => verify_chc_comp(&opts),
            PreflightTarget::PbCompVerify(opts) => verify_pb_comp(&opts),
            PreflightTarget::CompetitionAudit(opts) => run_competition_audit(&opts),
            PreflightTarget::CompetitionScoreEstimate(opts) => {
                run_competition_score_estimate(&opts)
            }
        },
        SubmissionCommand::Worker(target) => match target {
            WorkerTarget::ChcComp(cmd) => run_chc_comp_worker(cmd),
        },
        SubmissionCommand::Submit(target) => match target {
            SubmitTarget::ChcCompZenodo(opts) => submit_chc_comp_zenodo(&opts),
        },
    }
}

fn generate_all(opts: &AllOptions) -> Result<()> {
    generate_sat(&opts.output.join(SAT_DEFAULT_DIR))?;
    generate_chc(
        &opts.output.join(CHC_DEFAULT_DIR),
        &opts.chc_archive_url,
        &opts.chc_tracks,
    )?;
    generate_pb(&opts.output.join(PB_DEFAULT_DIR))?;
    generate_smt(
        &opts.output.join(SMT_DEFAULT_DIR),
        &opts.smt_archive_url,
        opts.smt_archive_sha256.as_deref(),
        &opts.smt_system_description_url,
        opts.smt_final,
    )?;
    Ok(())
}

fn package_all(opts: &PackageAllOptions) -> Result<()> {
    package_sat(&opts.output.join(SAT_DEFAULT_DIR), opts.ay_bin.as_deref())?;
    package_chc(
        &opts.output.join(CHC_DEFAULT_DIR),
        opts.ay_bin.as_deref(),
        &opts.chc_archive_url,
        &opts.chc_tracks,
    )?;
    eprintln!("skipping PB-COMP generic package path: {PB26_GENERIC_PACKAGE_GUARD}");
    package_smt(
        &opts.output.join(SMT_DEFAULT_DIR),
        opts.ay_bin.as_deref(),
        &opts.smt_archive_url,
        &opts.smt_system_description_url,
        opts.smt_final,
    )?;
    Ok(())
}

fn package_sat(output: &Path, ay_bin: Option<&Path>) -> Result<()> {
    reset_dir(output)?;
    let repo = output.join("repo");
    generate_sat(&repo)?;
    let resolved_bin = install_runtime_files(&repo, ay_bin)?;
    let archive = output.join("ay-sat-comp-2026.tar.gz");
    create_tar_gz(&repo, &archive)?;
    write_package_manifest(output, "sat-comp-2026", &repo, &archive, &resolved_bin)?;
    println!("packaged SAT-COMP at {}", output.display());
    Ok(())
}

fn package_chc(
    output: &Path,
    ay_bin: Option<&Path>,
    archive_url: &str,
    tracks: &str,
) -> Result<()> {
    split_required_chc_tracks(tracks)?;
    reset_dir(output)?;
    let tool_archive = output.join("tool-archive").join("ay");
    fs::create_dir_all(&tool_archive)
        .with_context(|| format!("failed to create '{}'", tool_archive.display()))?;
    let resolved_bin = install_runtime_files(&tool_archive, ay_bin)?;
    write_chc_run_solver(&tool_archive)?;
    write_text(
        &tool_archive.join("README.md"),
        "# ay CHC-COMP 2026 Tool Archive\n\nRun interface:\n\n./run_solver.sh benchmark.smt2\n\nThe wrapper prints exactly one of sat, unsat, or unknown to stdout. Unsupported or failed runs degrade to unknown.\n",
        false,
    )?;

    let archive = output.join("ay-chccomp-2026-linux-x86_64.tar.gz");
    create_tar_gz(&output.join("tool-archive"), &archive)?;
    generate_chc(&output.join("pr"), archive_url, tracks)?;
    write_package_manifest(
        output,
        "chc-comp-2026",
        &tool_archive,
        &archive,
        &resolved_bin,
    )?;
    println!("packaged CHC-COMP at {}", output.display());
    Ok(())
}

fn prepare_chc_comp(opts: &ChcPrepareOptions) -> Result<()> {
    if opts.profile == SubmissionPrepareProfile::Prove && opts.benchmarks_root.is_none() {
        bail!("--profile prove requires --benchmarks-root");
    }

    let gate_config = opts.profile.gate_config();
    println!(
        "[submission-prepare] competition=chc-comp profile={} output={}",
        opts.profile.as_str(),
        opts.output.display()
    );
    package_chc(
        &opts.output,
        opts.ay_bin.as_deref(),
        &opts.archive_url,
        &opts.tracks,
    )?;
    gate_chc(&opts.output, gate_config)?;

    let verify_opts = ChcCompVerifyOptions {
        package: opts.output.clone(),
        benchmarks_root: opts.benchmarks_root.clone(),
        tracks: opts.tracks.clone(),
        samples_per_track: opts.samples_per_track,
        benchmark_timeout_ms: opts.benchmark_timeout_ms,
        require_linux: gate_config.require_linux,
        require_static: gate_config.require_static,
        require_public_urls: gate_config.require_public_urls,
        require_current_build: opts.profile.require_current_build(),
        skip_benchmark_smoke: opts
            .profile
            .skip_benchmark_smoke(opts.benchmarks_root.as_deref()),
        work_dir: opts.work_dir.clone(),
        json: opts.json.clone(),
        report: opts.report.clone(),
        keep_work_dir: opts.keep_work_dir,
    };
    verify_chc_comp(&verify_opts)?;
    println!(
        "status=pass prepared=true competition=chc-comp profile={} package={}",
        opts.profile.as_str(),
        opts.output.display()
    );
    Ok(())
}

fn package_pb(_output: &Path, _ay_bin: Option<&Path>) -> Result<()> {
    bail!("{PB26_GENERIC_PACKAGE_GUARD}");
}

fn package_smt(
    output: &Path,
    ay_bin: Option<&Path>,
    archive_url: &str,
    system_description_url: &str,
    final_submission: bool,
) -> Result<()> {
    reset_dir(output)?;
    let package = output.join("package");
    generate_smt(
        &package,
        archive_url,
        None,
        system_description_url,
        final_submission,
    )?;
    let _ = fs::remove_file(package.join("ay-smt-comp-2026.json"));
    let resolved_bin = install_runtime_files(&package, ay_bin)?;
    let archive = output.join("ay-smt-comp-2026.tar.gz");
    create_tar_gz(&package, &archive)?;
    let archive_sha256 = sha256_file(&archive)?;
    generate_smt(
        &output.join("pr"),
        archive_url,
        Some(&archive_sha256),
        system_description_url,
        final_submission,
    )?;
    write_package_manifest(output, "smt-comp-2026", &package, &archive, &resolved_bin)?;
    println!("packaged SMT-COMP at {}", output.display());
    Ok(())
}

#[derive(Clone, Copy)]
struct GateConfig {
    require_linux: bool,
    require_static: bool,
    require_public_urls: bool,
    skip_smoke: bool,
}

impl GateOneOptions {
    fn gate_config(&self) -> GateConfig {
        GateConfig {
            require_linux: self.require_linux,
            require_static: self.require_static,
            require_public_urls: self.require_public_urls,
            skip_smoke: self.skip_smoke,
        }
    }
}

impl GateAllOptions {
    fn gate_config(&self) -> GateConfig {
        GateConfig {
            require_linux: self.require_linux,
            require_static: self.require_static,
            require_public_urls: self.require_public_urls,
            skip_smoke: self.skip_smoke,
        }
    }
}

fn gate_all(opts: &GateAllOptions) -> Result<()> {
    let cfg = opts.gate_config();
    gate_sat(&opts.package.join(SAT_DEFAULT_DIR), cfg)?;
    gate_chc(&opts.package.join(CHC_DEFAULT_DIR), cfg)?;
    eprintln!("skipping PB-COMP generic gate path: {PB26_GENERIC_PACKAGE_GUARD}");
    gate_smt(&opts.package.join(SMT_DEFAULT_DIR), cfg)?;
    Ok(())
}

fn gate_sat(package: &Path, cfg: GateConfig) -> Result<()> {
    let package = resolve_gate_dir(package, SAT_DEFAULT_DIR);
    let repo = child_or_self(&package, "repo");
    let mut gate = GateReport::new("SAT-COMP");
    gate.file(&repo.join("build.sh"), "SAT build.sh exists");
    gate.file(&repo.join("run.sh"), "SAT run.sh exists");
    gate.executable(&repo.join("build.sh"), "SAT build.sh executable");
    gate.executable(&repo.join("run.sh"), "SAT run.sh executable");
    gate.binary(
        &repo.join("ay"),
        cfg.require_linux,
        cfg.require_static,
        "SAT ay binary",
    );
    gate.command(
        Command::new("bash")
            .arg("-n")
            .arg(repo.join("build.sh"))
            .arg(repo.join("run.sh")),
        "SAT shell wrappers parse",
    );
    gate.archive(
        &package.join("ay-sat-comp-2026.tar.gz"),
        "SAT archive exists",
    );
    if cfg.skip_smoke {
        gate.skip("SAT wrapper smoke skipped");
    } else {
        match sat_smoke(&repo) {
            Ok(()) => gate.pass("SAT wrapper emits UNSAT and proof.out"),
            Err(err) => gate.fail(format!("SAT wrapper smoke failed: {err:#}")),
        }
    }
    gate.finish()
}

fn gate_chc(package: &Path, cfg: GateConfig) -> Result<()> {
    let package = resolve_gate_dir(package, CHC_DEFAULT_DIR);
    let pr = child_or_self(&package, "pr");
    let tool_archive_parent = child_or_self(&package, "tool-archive");
    let tool_archive = child_or_self(&tool_archive_parent, "ay");
    let mut gate = GateReport::new("CHC-COMP");
    gate.file(
        &pr.join("Makefile.ay.fragment"),
        "CHC Makefile fragment exists",
    );
    gate.file(
        &pr.join("benchmark-defs").join("ay.xml.template"),
        "CHC BenchExec XML exists",
    );
    gate.file(&pr.join("tooldefs").join("ay.py"), "CHC tooldef exists");
    gate.file(
        &tool_archive.join("run_solver.sh"),
        "CHC run_solver.sh exists",
    );
    gate.executable(
        &tool_archive.join("run_solver.sh"),
        "CHC run_solver.sh executable",
    );
    gate.binary(
        &tool_archive.join("ay"),
        cfg.require_linux,
        cfg.require_static,
        "CHC ay binary",
    );
    let chc_archive = package.join("ay-chccomp-2026-linux-x86_64.tar.gz");
    gate.archive(&chc_archive, "CHC archive exists");
    match validate_chc_archive_layout(&chc_archive) {
        Ok(()) => gate.pass("CHC archive has ay/ root layout"),
        Err(err) => gate.fail(format!("CHC archive layout invalid: {err:#}")),
    }
    match extract_archive(&chc_archive, "ay-chc-submission-archive-binary-gate") {
        Ok(extracted) => gate.binary(
            &extracted.join("ay").join("ay"),
            cfg.require_linux,
            cfg.require_static,
            "CHC archived ay binary",
        ),
        Err(err) => gate.fail(format!(
            "CHC archived ay binary: cannot extract archive: {err:#}"
        )),
    }
    gate.command(
        Command::new("bash")
            .arg("-n")
            .arg(tool_archive.join("run_solver.sh")),
        "CHC wrapper parses",
    );
    gate.command(
        Command::new("python3")
            .arg("-c")
            .arg("import pathlib, sys; path = pathlib.Path(sys.argv[1]); compile(path.read_text(encoding='utf-8'), str(path), 'exec')")
            .arg(pr.join("tooldefs").join("ay.py")),
        "CHC Python tooldef compiles",
    );
    gate.command(
        Command::new("xmllint")
            .arg("--noout")
            .arg(pr.join("benchmark-defs").join("ay.xml.template")),
        "CHC BenchExec XML parses",
    );
    gate.text_contains(
        &pr.join("benchmark-defs").join("ay.xml.template"),
        "<rundefinition name=\"CHC-COMP2026_check-sat\">",
        "CHC XML has 2026 rundefinition",
    );
    match read_chc_xml_track_includes(&pr.join("benchmark-defs").join("ay.xml.template"))
        .and_then(|tracks| require_all_chc_comp_tracks(&tracks).map(|()| tracks))
    {
        Ok(tracks) => gate.pass(format!(
            "CHC XML includes all 2026 set-file categories: {}",
            sorted_unique_tracks(tracks).join(", ")
        )),
        Err(err) => gate.fail(format!("CHC XML track coverage invalid: {err:#}")),
    }
    if cfg.require_public_urls {
        gate.text_not_contains(
            &pr.join("Makefile.ay.fragment"),
            "PLACEHOLDER",
            "CHC archive URL is not a placeholder",
        );
    }
    if cfg.skip_smoke {
        gate.skip("CHC binary smoke skipped");
    } else {
        gate.command(
            Command::new(tool_archive.join("ay")).arg("--version"),
            "CHC ay --version runs",
        );
        match chc_smoke(&tool_archive) {
            Ok(()) => gate.pass("CHC wrapper emits one clean status on HORN smoke"),
            Err(err) => gate.fail(format!("CHC wrapper smoke failed: {err:#}")),
        }
    }
    gate.finish()
}

fn gate_pb(_package: &Path, _cfg: GateConfig) -> Result<()> {
    bail!("{PB26_GENERIC_PACKAGE_GUARD}");
}

fn gate_smt(package: &Path, cfg: GateConfig) -> Result<()> {
    let package = resolve_gate_dir(package, SMT_DEFAULT_DIR);
    let root = child_or_self(&package, "package");
    let pr = child_or_self(&package, "pr");
    let json_path = pr.join("ay-smt-comp-2026.json");
    let mut gate = GateReport::new("SMT-COMP");
    gate.file(&json_path, "SMT submission JSON exists");
    gate.file(
        &root.join("run_solver.sh"),
        "SMT single-query wrapper exists",
    );
    gate.file(
        &root.join("run_solver_mv.sh"),
        "SMT model-validation wrapper exists",
    );
    gate.file(
        &root.join("run_solver_incr.sh"),
        "SMT incremental wrapper exists",
    );
    gate.binary(
        &root.join("ay"),
        cfg.require_linux,
        cfg.require_static,
        "SMT ay binary",
    );
    gate.command(
        Command::new("bash")
            .arg("-n")
            .arg(root.join("run_solver.sh"))
            .arg(root.join("run_solver_mv.sh"))
            .arg(root.join("run_solver_incr.sh")),
        "SMT wrappers parse",
    );
    gate.archive(
        &package.join("ay-smt-comp-2026.tar.gz"),
        "SMT archive exists",
    );
    let archive_path = package.join("ay-smt-comp-2026.tar.gz");
    let archive_hash = sha256_file(&archive_path).ok();
    match validate_smt_json(&json_path, cfg.require_public_urls, archive_hash.as_deref()) {
        Ok(()) => gate.pass("SMT submission JSON shape is schema-clean"),
        Err(err) => gate.fail(format!("SMT JSON gate failed: {err:#}")),
    }
    if cfg.skip_smoke {
        gate.skip("SMT wrapper smoke skipped");
    } else {
        match extract_archive(&archive_path, "ay-smt-submission-archive-gate") {
            Ok(extracted) => match smt_archive_smoke(&extracted, &json_path) {
                Ok(()) => gate.pass("SMT extracted archive commands pass smoke tests"),
                Err(err) => gate.fail(format!("SMT extracted archive smoke failed: {err:#}")),
            },
            Err(err) => gate.fail(format!("SMT wrapper smoke failed: {err:#}")),
        }
    }
    gate.finish()
}

fn preflight_chc_late_entry(opts: &ChcLateEntryPreflightOptions) -> Result<()> {
    if opts.work_dir.exists() && !opts.keep_work_dir {
        fs::remove_dir_all(&opts.work_dir)
            .with_context(|| format!("failed to remove '{}'", opts.work_dir.display()))?;
    }
    fs::create_dir_all(&opts.work_dir)
        .with_context(|| format!("failed to create '{}'", opts.work_dir.display()))?;

    let workspace = workspace_root();
    let root = workspace.as_path();
    let mut checks = Vec::new();
    let (archive, validation_mode) = if let Some(archive) = &opts.archive {
        let archive = archive.to_path_buf();
        if !archive.is_file() {
            push_check(
                &mut checks,
                "archive_exists",
                "fail",
                format!("missing archive: {}", archive.display()),
            );
        }
        (archive, "real-archive-local-wrapper-stub")
    } else if opts.require_real_artifact {
        push_check(
            &mut checks,
            "archive_exists",
            "fail",
            "no --archive supplied and --require-real-artifact was set",
        );
        (
            opts.work_dir.join("missing-real-archive.tar.gz"),
            "real-archive-required",
        )
    } else {
        let stub_parent = opts.work_dir.join("stub-source");
        create_chc_late_entry_stub_package(&stub_parent)?;
        let archive = opts
            .work_dir
            .join("ay-chccomp-2026-linux-x86_64.stub.tar.gz");
        create_tar_gz(&stub_parent, &archive)?;
        push_check(
            &mut checks,
            "stub_archive_created",
            "pass",
            format!(
                "created local-only stub archive at {}",
                display_path_for_report(&archive, root)
            ),
        );
        (archive, "local-stub-archive")
    };

    let archive_sha256 = if archive.is_file() {
        sha256_file(&archive)?
    } else {
        "unavailable".to_string()
    };
    let mut members = Vec::new();
    if archive.is_file() {
        push_check(
            &mut checks,
            "archive_exists",
            "pass",
            format!(
                "archive is present: {}",
                display_path_for_report(&archive, root)
            ),
        );
        members = validate_chc_late_entry_archive_layout(&archive, &mut checks)?;
        validate_chc_late_entry_strip_layout(&archive, &opts.work_dir, &mut checks)?;
    }

    let stripped_root = opts
        .work_dir
        .join("strip-components-1")
        .join("tools")
        .join("ay");
    let binary = stripped_root.join("ay");
    let file_text = if binary.exists() {
        preflight_file_output(&binary)
    } else {
        "binary unavailable".to_string()
    };
    let platform = if binary.exists() {
        preflight_binary_platform(&binary)
    } else {
        "unknown".to_string()
    };
    let real_linux = opts.archive.is_some() && platform == "linux-elf-x86_64";
    if opts.archive.is_none() {
        push_check(
            &mut checks,
            "real_linux_artifact_available",
            "warn",
            "no real archive supplied; validation used a local stub archive",
        );
    } else if real_linux {
        push_check(
            &mut checks,
            "real_linux_artifact_available",
            "pass",
            "archive binary is Linux x86_64 ELF",
        );
    } else {
        push_check(
            &mut checks,
            "real_linux_artifact_available",
            "fail",
            format!("archive binary is not Linux x86_64 ELF: {platform}"),
        );
    }

    let mut wrapper_cases = Vec::new();
    if stripped_root.join("run_solver.sh").is_file() {
        let harness_root = prepare_chc_late_entry_wrapper_harness(
            &stripped_root,
            &opts.work_dir.join("wrapper-harness").join("ay"),
        )?;
        wrapper_cases =
            run_chc_late_entry_wrapper_cases(&harness_root, &opts.work_dir, &mut checks)?;
    } else {
        push_check(
            &mut checks,
            "wrapper_harness",
            "fail",
            "run_solver.sh unavailable after archive extraction",
        );
    }

    let fail_count = checks
        .iter()
        .filter(|check| check["status"].as_str() == Some("fail"))
        .count();
    let mut blockers = Vec::new();
    if opts.archive.is_none() {
        blockers.push(
            "No real Linux x86_64 ay archive was supplied; this is local stub validation only."
                .to_string(),
        );
    } else if !real_linux {
        blockers.push("Supplied archive did not contain a Linux x86_64 ELF ay binary.".to_string());
    }
    if fail_count > 0 {
        blockers.push(format!("{fail_count} preflight check(s) failed."));
    }

    let actual_submission_ready = opts.archive.is_some() && real_linux && fail_count == 0;
    let payload = json!({
        "schema_version": CHC_LATE_PREFLIGHT_SCHEMA,
        "generated_at_utc": BUILD_INFO.datetime_utc,
        "official_source_url": CHC_OFFICIAL_SOURCE_URL,
        "validation_mode": validation_mode,
        "local_only": true,
        "submission_actions_performed": [],
        "normal_solver_benchmark_deadline": CHC_NORMAL_SOLVER_BENCHMARK_DEADLINE,
        "technical_solver_resubmission_deadline": CHC_TECHNICAL_SOLVER_RESUBMISSION_DEADLINE,
        "tracks": CHC_ALLOWED_TRACKS,
        "local_set_file_categories": CHC_ALLOWED_TRACKS,
        "track_model": chc_track_model_json(),
        "archive": {
            "path": display_path_for_report(&archive, root),
            "absolute_path": absolute_path_for_report(&archive),
            "sha256": archive_sha256,
            "members": members,
        },
        "binary": {
            "path": display_path_for_report(&binary, root),
            "absolute_path": absolute_path_for_report(&binary),
            "file_output": file_text.replace(&format!("{}/", root.display()), ""),
            "raw_file_output": file_text,
            "platform": platform,
        },
        "real_linux_artifact_available": real_linux,
        "actual_submission_ready": actual_submission_ready,
        "checks": checks,
        "wrapper_cases": wrapper_cases,
        "blockers": blockers,
    });

    write_json_report(&opts.json, &payload)?;
    write_chc_late_entry_markdown(&opts.report, &payload, root)?;
    println!("wrote {}", display_path_for_report(&opts.json, root));
    println!("wrote {}", display_path_for_report(&opts.report, root));
    print_chc_track_model_summary();
    if actual_submission_ready {
        println!("status=pass actual_submission_ready=true local_only=true");
    } else if fail_count == 0 {
        println!("status=pass actual_submission_ready=false local_only=true");
    } else {
        bail!("status=fail actual_submission_ready=false local_only=true");
    }
    Ok(())
}

fn compare_chc_baseline(opts: &ChcBaselineCompareOptions) -> Result<()> {
    let root = workspace_root();
    if opts.profile == ChcBaselineCompareProfile::SameTimeout && opts.timeout_sec.is_some() {
        bail!("--timeout-sec is only valid with --profile fast-proxy");
    }
    if opts.profile == ChcBaselineCompareProfile::FastProxy && opts.timeout_sec.is_none() {
        bail!("--profile fast-proxy requires --timeout-sec");
    }

    let baseline = repo_relative_path(&root, &opts.baseline);
    let ay = repo_relative_path(&root, &opts.ay);
    let output_dir = repo_relative_path(&root, &opts.output_dir);
    let json_path = output_dir.join("chc-baseline-compare.json");
    let csv_path = output_dir.join("chc-baseline-compare.csv");
    let script = root.join("scripts/chc_baseline_compare.py");

    if !script.is_file() {
        bail!(
            "CHC baseline compare implementation missing: {}",
            script.display()
        );
    }
    if !baseline.is_file() {
        bail!("baseline JSON not found: {}", baseline.display());
    }
    if !ay.is_file() {
        bail!("ay binary not found: {}", ay.display());
    }
    fs::create_dir_all(&output_dir)
        .with_context(|| format!("failed to create '{}'", output_dir.display()))?;

    println!(
        "status=running evidence=chc-baseline-compare profile={} baseline={} ay={} output_dir={}",
        opts.profile.as_str(),
        display_path_for_report(&baseline, &root),
        display_path_for_report(&ay, &root),
        display_path_for_report(&output_dir, &root),
    );

    let mut command = Command::new("python3");
    command
        .current_dir(&root)
        .env("PYTHONUNBUFFERED", "1")
        .arg(&script)
        .arg("compare")
        .arg("--baseline")
        .arg(&baseline)
        .arg("--ay")
        .arg(&ay)
        .arg("--run-all")
        .arg("--json-out")
        .arg(&json_path)
        .arg("--csv-out")
        .arg(&csv_path);
    if let Some(bench_dir) = &opts.bench_dir {
        command
            .arg("--bench-dir")
            .arg(repo_relative_path(&root, bench_dir));
    }
    if let Some(timeout_sec) = opts.timeout_sec {
        command.arg("--timeout").arg(timeout_sec.to_string());
    }

    let status = command
        .status()
        .context("failed to run CHC baseline compare")?;
    let payload = if json_path.is_file() {
        let text = fs::read_to_string(&json_path)
            .with_context(|| format!("failed to read '{}'", json_path.display()))?;
        serde_json::from_str::<JsonValue>(&text)
            .with_context(|| format!("failed to parse '{}'", json_path.display()))?
    } else {
        json!({})
    };
    print_chc_baseline_compare_summary(
        opts.profile,
        status.success(),
        &payload,
        &json_path,
        &csv_path,
        &root,
    );

    if status.success() {
        Ok(())
    } else {
        bail!(
            "status=fail evidence=chc-baseline-compare profile={} exit_code={}",
            opts.profile.as_str(),
            status.code().unwrap_or(-1)
        )
    }
}

fn print_chc_baseline_compare_summary(
    profile: ChcBaselineCompareProfile,
    success: bool,
    payload: &JsonValue,
    json_path: &Path,
    csv_path: &Path,
    root: &Path,
) {
    let summary = &payload["summary"];
    let run_type = payload["run_classification"]["run_type"]
        .as_str()
        .unwrap_or("unavailable");
    let timeout_relation = payload["run_classification"]["timeout_relation"]
        .as_str()
        .unwrap_or("unavailable");
    let checked = summary["checked"].as_u64().unwrap_or(0);
    let solved = summary["current_solved_checked"].as_u64().unwrap_or(0);
    let direct_regressions = summary["direct_regressions"].as_u64().unwrap_or(0);
    let proxy_regressions = summary["proxy_regressions"].as_u64().unwrap_or(0);
    let wrong_answers = summary["wrong_answers"].as_u64().unwrap_or(0);
    let invalid_answers = summary["invalid_answers"].as_u64().unwrap_or(0);
    println!("wrote {}", display_path_for_report(json_path, root));
    println!("wrote {}", display_path_for_report(csv_path, root));
    println!(
        "status={} evidence=chc-baseline-compare profile={} run_type={} timeout_relation={} current_solved={}/{} direct_regressions={} proxy_regressions={} wrong_answers={} invalid_answers={}",
        if success { "pass" } else { "fail" },
        profile.as_str(),
        run_type,
        timeout_relation,
        solved,
        checked,
        direct_regressions,
        proxy_regressions,
        wrong_answers,
        invalid_answers,
    );
}

fn verify_chc_comp(opts: &ChcCompVerifyOptions) -> Result<()> {
    if opts.work_dir.exists() && !opts.keep_work_dir {
        fs::remove_dir_all(&opts.work_dir)
            .with_context(|| format!("failed to remove '{}'", opts.work_dir.display()))?;
    }
    fs::create_dir_all(&opts.work_dir)
        .with_context(|| format!("failed to create '{}'", opts.work_dir.display()))?;

    let workspace = workspace_root();
    let root = workspace.as_path();
    let package = resolve_gate_dir(&opts.package, CHC_DEFAULT_DIR);
    let pr = child_or_self(&package, "pr");
    let tool_archive_parent = child_or_self(&package, "tool-archive");
    let tool_archive = child_or_self(&tool_archive_parent, "ay");
    let tracks = split_required_chc_tracks(&opts.tracks)?;

    let mut checks = Vec::new();
    let mut blockers = Vec::new();

    chc_verify_file(
        &mut checks,
        "package:makefile_fragment",
        &pr.join("Makefile.ay.fragment"),
        "CHC Makefile fragment exists",
        root,
    );
    chc_verify_file(
        &mut checks,
        "package:benchexec_xml",
        &pr.join("benchmark-defs").join("ay.xml.template"),
        "CHC BenchExec XML exists",
        root,
    );
    chc_verify_file(
        &mut checks,
        "package:tooldef",
        &pr.join("tooldefs").join("ay.py"),
        "CHC tooldef exists",
        root,
    );
    chc_verify_file(
        &mut checks,
        "package:run_solver",
        &tool_archive.join("run_solver.sh"),
        "CHC run_solver.sh exists",
        root,
    );
    chc_verify_executable(
        &mut checks,
        "package:run_solver_executable",
        &tool_archive.join("run_solver.sh"),
        "CHC run_solver.sh executable",
        root,
    );
    let packaged_platform = chc_verify_binary(
        &mut checks,
        "package:ay_binary",
        &tool_archive.join("ay"),
        opts.require_linux,
        opts.require_static,
        "CHC packaged ay binary",
        root,
    );

    let archive = package.join("ay-chccomp-2026-linux-x86_64.tar.gz");
    chc_verify_file(
        &mut checks,
        "package:archive",
        &archive,
        "CHC archive exists",
        root,
    );
    let archive_sha256 = if archive.is_file() {
        Some(sha256_file(&archive)?)
    } else {
        None
    };
    match validate_chc_archive_layout(&archive) {
        Ok(()) => push_check(
            &mut checks,
            "archive:layout",
            "pass",
            "archive has required ay/ root layout",
        ),
        Err(err) => push_check(
            &mut checks,
            "archive:layout",
            "fail",
            format!("archive layout invalid: {err:#}"),
        ),
    }
    let mut archived_platform = None;
    let mut archive_wrapper = None;
    match extract_archive(&archive, "ay-chc-comp-verify-archive") {
        Ok(extracted) => {
            let archived_root = extracted.join("ay");
            archived_platform = chc_verify_binary(
                &mut checks,
                "archive:ay_binary",
                &archived_root.join("ay"),
                opts.require_linux,
                opts.require_static,
                "CHC archived ay binary",
                root,
            );
            let wrapper = archived_root.join("run_solver.sh");
            chc_verify_file(
                &mut checks,
                "archive:run_solver",
                &wrapper,
                "CHC archived run_solver.sh exists",
                root,
            );
            chc_verify_executable(
                &mut checks,
                "archive:run_solver_executable",
                &wrapper,
                "CHC archived run_solver.sh executable",
                root,
            );
            if wrapper.is_file() && is_executable(&wrapper) {
                archive_wrapper = Some(wrapper);
            }
        }
        Err(err) => push_check(
            &mut checks,
            "archive:extract",
            "fail",
            format!("cannot extract archive: {err:#}"),
        ),
    }

    chc_verify_command(
        &mut checks,
        "wrapper:bash_parse",
        Command::new("bash")
            .arg("-n")
            .arg(tool_archive.join("run_solver.sh")),
        "bash -n accepts CHC run_solver.sh",
    );
    chc_verify_command(
        &mut checks,
        "tooldef:python_compile",
        Command::new("python3")
            .arg("-c")
            .arg("import pathlib, sys; path = pathlib.Path(sys.argv[1]); compile(path.read_text(encoding='utf-8'), str(path), 'exec')")
            .arg(pr.join("tooldefs").join("ay.py")),
        "Python compiles CHC tooldef",
    );
    chc_verify_command(
        &mut checks,
        "xml:xmllint",
        Command::new("xmllint")
            .arg("--noout")
            .arg(pr.join("benchmark-defs").join("ay.xml.template")),
        "xmllint parses CHC BenchExec XML",
    );
    verify_chc_xml_tracks(
        &mut checks,
        &pr.join("benchmark-defs").join("ay.xml.template"),
        &tracks,
    );
    if opts.require_public_urls {
        verify_chc_public_url(
            &mut checks,
            &pr.join("Makefile.ay.fragment"),
            "makefile:public_archive_url",
        );
    }

    let manifest_path = package.join("MANIFEST.json");
    let manifest = read_json_file(&manifest_path, &mut checks, "manifest:read", root);
    verify_chc_manifest_archive_sha(&mut checks, manifest.as_ref(), archive_sha256.as_deref());
    if opts.require_current_build {
        verify_chc_manifest_current_build(&mut checks, manifest.as_ref());
    }

    if let Some(wrapper) = &archive_wrapper {
        chc_verify_command(
            &mut checks,
            "archive_wrapper:bash_parse",
            Command::new("bash").arg("-n").arg(wrapper),
            "bash -n accepts archived CHC run_solver.sh",
        );
    } else {
        push_check(
            &mut checks,
            "archive_wrapper:bash_parse",
            "fail",
            "archived run_solver.sh unavailable for bash parse",
        );
    }

    let benchmark_smokes = if opts.skip_benchmark_smoke {
        push_check(
            &mut checks,
            "benchmarks:smoke",
            "skip",
            "benchmark smoke skipped by --skip-benchmark-smoke",
        );
        blockers
            .push("Benchmark smoke was skipped; report is not prove-ready evidence.".to_string());
        Vec::new()
    } else if opts.samples_per_track == 0 {
        push_check(
            &mut checks,
            "benchmarks:samples_per_track",
            "fail",
            "--samples-per-track must be positive unless --skip-benchmark-smoke is set",
        );
        Vec::new()
    } else if let Some(benchmarks_root) = &opts.benchmarks_root {
        if let Some(wrapper) = &archive_wrapper {
            run_chc_comp_benchmark_smokes(
                &mut checks,
                wrapper,
                benchmarks_root,
                &tracks,
                opts.samples_per_track,
                Duration::from_millis(opts.benchmark_timeout_ms),
                root,
            )?
        } else {
            push_check(
                &mut checks,
                "benchmarks:smoke",
                "fail",
                "archived run_solver.sh unavailable; benchmark smoke not run",
            );
            Vec::new()
        }
    } else {
        push_check(
            &mut checks,
            "benchmarks:root",
            "fail",
            "missing --benchmarks-root; pass a chc-comp26-benchmarks checkout or use --skip-benchmark-smoke",
        );
        Vec::new()
    };

    let fail_count = count_checks(&checks, "fail");
    let warn_count = count_checks(&checks, "warn");
    let skip_count = count_checks(&checks, "skip");
    for check in checks
        .iter()
        .filter(|check| check["status"].as_str() == Some("fail"))
    {
        blockers.push(format!(
            "{}: {}",
            check["name"].as_str().unwrap_or("unnamed-check"),
            check["detail"].as_str().unwrap_or("failed")
        ));
    }

    let benchmark_smoke_ready = !opts.skip_benchmark_smoke
        && opts.benchmarks_root.is_some()
        && opts.samples_per_track > 0
        && !benchmark_smokes.is_empty();
    let actual_prove_ready = fail_count == 0 && benchmark_smoke_ready;
    let payload = json!({
        "schema_version": "ay.chccomp-verify/v1",
        "generated_at_utc": BUILD_INFO.datetime_utc,
        "official_source_url": CHC_OFFICIAL_SOURCE_URL,
        "local_only": true,
        "submission_actions_performed": [],
        "package": {
            "path": display_path_for_report(&package, root),
            "absolute_path": absolute_path_for_report(&package),
            "archive": {
                "path": display_path_for_report(&archive, root),
                "absolute_path": absolute_path_for_report(&archive),
                "sha256": archive_sha256,
            },
            "packaged_binary_platform": packaged_platform,
            "archived_binary_platform": archived_platform,
            "manifest": manifest,
        },
        "requirements": {
            "tracks": tracks.clone(),
            "local_set_file_categories": tracks,
            "track_model": chc_track_model_json(),
            "require_linux": opts.require_linux,
            "require_static": opts.require_static,
            "require_public_urls": opts.require_public_urls,
            "require_current_build": opts.require_current_build,
        },
        "benchmarks": {
            "root": opts.benchmarks_root.as_ref().map(|path| display_path_for_report(path, root)),
            "samples_per_track": opts.samples_per_track,
            "benchmark_timeout_ms": opts.benchmark_timeout_ms,
            "smokes": benchmark_smokes,
        },
        "summary": {
            "actual_prove_ready": actual_prove_ready,
            "fail_count": fail_count,
            "warn_count": warn_count,
            "skip_count": skip_count,
        },
        "checks": checks,
        "blockers": blockers,
    });

    write_json_report(&opts.json, &payload)?;
    write_chc_comp_verify_markdown(&opts.report, &payload, root)?;
    println!("wrote {}", display_path_for_report(&opts.json, root));
    println!("wrote {}", display_path_for_report(&opts.report, root));
    print_chc_track_model_summary();
    if fail_count == 0 {
        println!("status=pass actual_prove_ready={actual_prove_ready} local_only=true");
        Ok(())
    } else {
        bail!("status=fail actual_prove_ready=false local_only=true")
    }
}

fn verify_pb_comp(opts: &PbCompVerifyOptions) -> Result<()> {
    let workspace = workspace_root();
    let root = workspace.as_path();
    let package = opts.package.clone();
    let auto_archive = package.with_extension("tar.gz");
    let archive = opts
        .archive
        .clone()
        .or_else(|| auto_archive.is_file().then_some(auto_archive));
    let checker = root.join("scripts").join("check_pb26_submission.sh");

    let mut checks = Vec::new();
    let mut blockers = Vec::new();
    if package.is_dir() {
        push_check(
            &mut checks,
            "package:directory",
            "pass",
            format!("package directory exists: {}", package.display()),
        );
    } else {
        push_check(
            &mut checks,
            "package:directory",
            "fail",
            format!("missing package directory: {}", package.display()),
        );
    }
    if checker.is_file() {
        push_check(
            &mut checks,
            "checker:script",
            "pass",
            format!("using {}", display_path_for_report(&checker, root)),
        );
    } else {
        push_check(
            &mut checks,
            "checker:script",
            "fail",
            format!("missing {}", checker.display()),
        );
    }
    match (&archive, opts.skip_archive_check) {
        (Some(path), false) if path.is_file() => push_check(
            &mut checks,
            "archive:file",
            "pass",
            format!("archive exists: {}", path.display()),
        ),
        (Some(path), false) => push_check(
            &mut checks,
            "archive:file",
            "fail",
            format!("missing archive: {}", path.display()),
        ),
        (_, true) => {
            push_check(
                &mut checks,
                "archive:file",
                "skip",
                "archive validation skipped by --skip-archive-check",
            );
            blockers.push(
                "Archive validation was skipped; this is not upload-ready evidence.".to_string(),
            );
        }
        (None, false) => {
            push_check(
                &mut checks,
                "archive:file",
                "warn",
                "no --archive supplied and PACKAGE.tar.gz was not present",
            );
            blockers.push("No PB-COMP archive was validated.".to_string());
        }
    }
    if opts.allow_nonstatic {
        push_check(
            &mut checks,
            "policy:static",
            "warn",
            "--allow-nonstatic permits a binary shape PB26 only lists as non-preferred",
        );
        blockers.push("Non-static binaries were allowed during this preflight.".to_string());
    }
    if opts.allow_stale_package {
        push_check(
            &mut checks,
            "policy:freshness",
            "warn",
            "--allow-stale-package permits stale package provenance",
        );
        blockers.push("Stale package provenance was allowed during this preflight.".to_string());
    }
    if opts.allow_unavailable_git_provenance {
        push_check(
            &mut checks,
            "policy:provenance",
            "warn",
            "--allow-unavailable-git-provenance permits incomplete git provenance",
        );
        blockers.push("Unavailable git provenance was allowed during this preflight.".to_string());
    }
    if opts.require_veripb {
        push_check(
            &mut checks,
            "policy:veripb",
            "pass",
            "external VeriPB validation is required",
        );
    }

    let mut command = Command::new("bash");
    command
        .current_dir(root)
        .arg(&checker)
        .arg("--dir")
        .arg(&package);
    let mut command_line = vec![
        "bash".to_string(),
        display_path_for_report(&checker, root),
        "--dir".to_string(),
        display_path_for_report(&package, root),
    ];

    if opts.skip_archive_check {
        command.arg("--skip-archive-check");
        command_line.push("--skip-archive-check".to_string());
    } else if let Some(archive) = &archive {
        command.arg("--archive").arg(archive);
        command_line.push("--archive".to_string());
        command_line.push(display_path_for_report(archive, root));
    }
    if let Some(runner_bin) = &opts.runner_bin {
        command.arg("--runner-bin").arg(runner_bin);
        command_line.push("--runner-bin".to_string());
        command_line.push(display_path_for_report(runner_bin, root));
    }
    if let Some(veripb_bin) = &opts.veripb_bin {
        command.arg("--veripb-bin").arg(veripb_bin);
        command_line.push("--veripb-bin".to_string());
        command_line.push(display_path_for_report(veripb_bin, root));
    }
    if opts.require_linux_runtime {
        command.arg("--require-linux-runtime");
        command_line.push("--require-linux-runtime".to_string());
    }
    if opts.require_veripb {
        command.arg("--require-veripb");
        command_line.push("--require-veripb".to_string());
    }
    if opts.allow_nonstatic {
        command.arg("--allow-nonstatic");
        command_line.push("--allow-nonstatic".to_string());
    }
    if opts.allow_stale_package {
        command.arg("--allow-stale-package");
        command_line.push("--allow-stale-package".to_string());
    }
    if opts.allow_unavailable_git_provenance {
        command.arg("--allow-unavailable-git-provenance");
        command_line.push("--allow-unavailable-git-provenance".to_string());
    }

    let run = run_command_with_timeout(
        &mut command,
        Duration::from_millis(opts.timeout_ms),
        "PB-COMP package checker",
    )?;
    let stdout = String::from_utf8_lossy(&run.stdout).to_string();
    let stderr = String::from_utf8_lossy(&run.stderr).to_string();
    if run.timed_out {
        push_check(
            &mut checks,
            "checker:timeout",
            "fail",
            format!("checker exceeded {}ms", opts.timeout_ms),
        );
    } else {
        push_check(
            &mut checks,
            "checker:timeout",
            "pass",
            format!("checker completed in {}ms", run.elapsed_ms),
        );
    }
    if run.exit_code == Some(0) && !run.timed_out {
        push_check(
            &mut checks,
            "checker:exit",
            "pass",
            "PB26 checker exited successfully",
        );
    } else {
        push_check(
            &mut checks,
            "checker:exit",
            "fail",
            format!(
                "PB26 checker exit={:?} timed_out={}",
                run.exit_code, run.timed_out
            ),
        );
    }

    let fail_count = count_checks(&checks, "fail");
    let warn_count = count_checks(&checks, "warn");
    let skip_count = count_checks(&checks, "skip");
    for check in checks
        .iter()
        .filter(|check| check["status"].as_str() == Some("fail"))
    {
        blockers.push(format!(
            "{}: {}",
            check["name"].as_str().unwrap_or("unnamed-check"),
            check["detail"].as_str().unwrap_or("failed")
        ));
    }
    let archive_validated = archive.is_some() && !opts.skip_archive_check;
    let actual_submission_ready = fail_count == 0
        && archive_validated
        && !opts.allow_nonstatic
        && !opts.allow_stale_package
        && !opts.allow_unavailable_git_provenance;
    let payload = json!({
        "schema_version": PB_PREFLIGHT_SCHEMA,
        "generated_at_utc": BUILD_INFO.datetime_utc,
        "official_source_url": PB_OFFICIAL_SOURCE_URL,
        "local_only": true,
        "submission_actions_performed": [],
        "package": {
            "path": display_path_for_report(&package, root),
            "absolute_path": absolute_path_for_report(&package),
            "archive": archive.as_ref().map(|path| json!({
                "path": display_path_for_report(path, root),
                "absolute_path": absolute_path_for_report(path),
            })),
        },
        "requirements": {
            "require_linux_runtime": opts.require_linux_runtime,
            "require_veripb": opts.require_veripb,
            "allow_nonstatic": opts.allow_nonstatic,
            "allow_stale_package": opts.allow_stale_package,
            "allow_unavailable_git_provenance": opts.allow_unavailable_git_provenance,
            "skip_archive_check": opts.skip_archive_check,
        },
        "checker": {
            "command": command_line,
            "exit_code": run.exit_code,
            "timed_out": run.timed_out,
            "elapsed_ms": run.elapsed_ms,
            "stdout": stdout,
            "stderr": stderr,
        },
        "summary": {
            "actual_submission_ready": actual_submission_ready,
            "archive_validated": archive_validated,
            "fail_count": fail_count,
            "warn_count": warn_count,
            "skip_count": skip_count,
        },
        "checks": checks,
        "blockers": blockers,
    });

    write_json_report(&opts.json, &payload)?;
    write_pb_comp_verify_markdown(&opts.report, &payload, root)?;
    println!("wrote {}", display_path_for_report(&opts.json, root));
    println!("wrote {}", display_path_for_report(&opts.report, root));
    if fail_count == 0 {
        println!("status=pass actual_submission_ready={actual_submission_ready} local_only=true");
        Ok(())
    } else {
        bail!("status=fail actual_submission_ready=false local_only=true")
    }
}

fn run_competition_audit(opts: &CompetitionAuditOptions) -> Result<()> {
    if cfg!(windows) {
        bail!(
            "competition-audit must run inside native Linux or WSL Ubuntu; \
             Windows can invoke it through the Ubuntu ay binary"
        );
    }

    let root = workspace_root();
    let script = root.join("scripts").join("audit_competition_entries.sh");
    if !script.is_file() {
        bail!("missing competition audit script: {}", script.display());
    }

    let output = workspace_relative_path(&root, &opts.output);
    let mut command = Command::new("bash");
    command
        .current_dir(&root)
        .arg(&script)
        .arg("--output")
        .arg(&output);
    if let Some(veripb_bin) = &opts.veripb_bin {
        command
            .arg("--veripb-bin")
            .arg(workspace_relative_path(&root, veripb_bin));
    }

    println!(
        "running competition audit script: {}",
        display_path_for_report(&script, &root)
    );
    let status = command
        .status()
        .with_context(|| format!("failed to run '{}'", script.display()))?;
    if status.success() {
        Ok(())
    } else {
        bail!("competition audit failed with status {status}")
    }
}

fn run_competition_score_estimate(opts: &CompetitionScoreEstimateOptions) -> Result<()> {
    if cfg!(windows) {
        bail!(
            "competition-score-estimate must run inside native Linux or WSL Ubuntu; \
             Windows can invoke it through the Ubuntu ay binary"
        );
    }

    let root = workspace_root();
    let script = root.join("scripts").join("competition_score_estimate.sh");
    if !script.is_file() {
        bail!(
            "missing competition score estimate script: {}",
            script.display()
        );
    }

    let output = workspace_relative_path(&root, &opts.output);
    let status = Command::new("bash")
        .current_dir(&root)
        .arg(&script)
        .arg("--output")
        .arg(&output)
        .status()
        .with_context(|| format!("failed to run '{}'", script.display()))?;
    if status.success() {
        Ok(())
    } else {
        bail!("competition score estimate failed with status {status}")
    }
}

fn workspace_relative_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    }
}

fn probe_chc_worker_command(
    checks: &mut Vec<JsonValue>,
    name: &'static str,
    program: &str,
    args: &[&str],
) {
    match Command::new(program).args(args).output() {
        Ok(output) if output.status.success() => push_check(
            checks,
            name,
            "pass",
            first_nonempty_output_line(&output).unwrap_or_else(|| "available".to_string()),
        ),
        Ok(output) => push_check(
            checks,
            name,
            "warn",
            format!(
                "exit={:?} stdout={} stderr={}",
                output.status.code(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ),
        ),
        Err(err) => push_check(checks, name, "warn", format!("unavailable: {err}")),
    }
}

fn first_nonempty_output_line(output: &std::process::Output) -> Option<String> {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    stdout
        .lines()
        .chain(stderr.lines())
        .map(str::trim)
        .find(|line| !line.is_empty())
        .map(ToOwned::to_owned)
}

fn chc_worker_case_from_smoke(smoke: &JsonValue) -> JsonValue {
    let actual = smoke["actual_status"].as_str().unwrap_or("no-status");
    let stdout = smoke["stdout"].as_str().unwrap_or("");
    let stdout_status_clean = stdout.trim() == actual && stdout.lines().count() == 1;
    json!({
        "path": smoke["input_path"].as_str().unwrap_or("unknown"),
        "track": smoke["track"].as_str().unwrap_or("unknown"),
        "metadata": smoke["metadata"].as_str().unwrap_or("unknown"),
        "expected": smoke["expected_status"].as_str().unwrap_or("unknown"),
        "actual": actual,
        "elapsed_ms": smoke["elapsed_ms"].as_u64().unwrap_or(0),
        "exit_code": smoke["exit_code"].clone(),
        "timed_out": smoke["timed_out"].as_bool().unwrap_or(false),
        "stdout_status_clean": stdout_status_clean,
        "proof_verified": JsonValue::Null,
        "model_verified": JsonValue::Null,
        "passed": smoke["passed"].as_bool().unwrap_or(false),
        "stdout": stdout,
        "stderr": smoke["stderr"].as_str().unwrap_or(""),
    })
}

fn summarize_chc_worker_cases(cases: &[JsonValue], checks: &[JsonValue]) -> JsonValue {
    let mut sat = 0_u64;
    let mut unsat = 0_u64;
    let mut unknown = 0_u64;
    let mut timeout = 0_u64;
    let mut invalid = 0_u64;
    let mut wrong = 0_u64;
    let mut failed_cases = 0_u64;
    let mut stdout_clean_failures = 0_u64;
    for case in cases {
        let actual = case["actual"].as_str().unwrap_or("no-status");
        match actual {
            "sat" => sat += 1,
            "unsat" => unsat += 1,
            "unknown" => unknown += 1,
            _ => invalid += 1,
        }
        if case["timed_out"].as_bool().unwrap_or(false) {
            timeout += 1;
        }
        if case["passed"].as_bool() != Some(true) {
            failed_cases += 1;
        }
        if case["stdout_status_clean"].as_bool() != Some(true) {
            stdout_clean_failures += 1;
        }
        let expected = case["expected"].as_str().unwrap_or("unknown");
        if matches!(expected, "sat" | "unsat")
            && matches!(actual, "sat" | "unsat")
            && expected != actual
        {
            wrong += 1;
        }
    }
    json!({
        "total_cases": cases.len(),
        "sat": sat,
        "unsat": unsat,
        "unknown": unknown,
        "timeout": timeout,
        "wrong": wrong,
        "invalid": invalid,
        "solved": sat + unsat,
        "failed_cases": failed_cases,
        "stdout_clean_failures": stdout_clean_failures,
        "fail_count": count_checks(checks, "fail"),
        "warn_count": count_checks(checks, "warn"),
        "skip_count": count_checks(checks, "skip"),
    })
}

fn with_worker_blockers(mut payload: JsonValue) -> Result<JsonValue> {
    let checks = payload["checks"].as_array().cloned().unwrap_or_default();
    payload["blockers"] = json!(worker_blockers_from_checks(&checks));
    Ok(payload)
}

fn worker_blockers_from_checks(checks: &[JsonValue]) -> Vec<String> {
    checks
        .iter()
        .filter(|check| check["status"].as_str() == Some("fail"))
        .map(|check| {
            format!(
                "{}: {}",
                check["name"].as_str().unwrap_or("unnamed-check"),
                check["detail"].as_str().unwrap_or("failed")
            )
        })
        .collect()
}

fn chc_worker_report_paths(
    kind: &str,
    issue: Option<u64>,
    lane: &str,
    report_dir: &Path,
    explicit_json: Option<&Path>,
    explicit_report: Option<&Path>,
) -> (PathBuf, PathBuf) {
    let issue_dir = issue
        .map(|issue| issue.to_string())
        .unwrap_or_else(|| kind.to_string());
    let stem = format!(
        "{}-{}-{}-{}",
        machine_hostname(),
        kind,
        sanitize_report_component(lane),
        unix_now()
    );
    let base = report_dir.join(issue_dir);
    let json_path = explicit_json
        .map(Path::to_path_buf)
        .unwrap_or_else(|| base.join(format!("{stem}.json")));
    let report_path = explicit_report
        .map(Path::to_path_buf)
        .unwrap_or_else(|| base.join(format!("{stem}.md")));
    (json_path, report_path)
}

fn sanitize_report_component(value: &str) -> String {
    let sanitized: String = value
        .chars()
        .map(|ch| {
            if ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_') {
                ch
            } else {
                '-'
            }
        })
        .collect();
    if sanitized.is_empty() {
        "lane".to_string()
    } else {
        sanitized
    }
}

fn machine_hostname() -> String {
    for key in ["HOSTNAME", "COMPUTERNAME"] {
        if let Ok(value) = env::var(key) {
            let value = value.trim();
            if !value.is_empty() {
                return sanitize_report_component(value);
            }
        }
    }
    Command::new("hostname")
        .output()
        .ok()
        .and_then(|output| {
            output
                .status
                .success()
                .then(|| String::from_utf8_lossy(&output.stdout).trim().to_string())
        })
        .filter(|value| !value.is_empty())
        .map(|value| sanitize_report_component(&value))
        .unwrap_or_else(|| "unknown-host".to_string())
}

fn chc_worker_gh(no_gh: bool, args: Vec<String>) -> JsonValue {
    let replay = format!("gh {}", args.join(" "));
    if no_gh {
        println!("github_action=skipped replay_command={replay}");
        return json!({
            "command": replay,
            "status": "skipped",
            "detail": "--no-gh was set",
        });
    }
    match Command::new("gh").args(&args).output() {
        Ok(output) if output.status.success() => json!({
            "command": replay,
            "status": "pass",
            "stdout": String::from_utf8_lossy(&output.stdout).to_string(),
            "stderr": String::from_utf8_lossy(&output.stderr).to_string(),
        }),
        Ok(output) => {
            println!("github_action=failed replay_command={replay}");
            json!({
                "command": replay,
                "status": "warn",
                "exit_code": output.status.code(),
                "stdout": String::from_utf8_lossy(&output.stdout).to_string(),
                "stderr": String::from_utf8_lossy(&output.stderr).to_string(),
            })
        }
        Err(err) => {
            println!("github_action=failed replay_command={replay}");
            json!({
                "command": replay,
                "status": "warn",
                "detail": format!("failed to run gh: {err}"),
            })
        }
    }
}

fn write_chc_worker_markdown(path: &Path, payload: &JsonValue) -> Result<()> {
    let summary = &payload["summary"];
    let mut lines = vec![
        "# CHC-COMP Worker Report".to_string(),
        String::new(),
        "This report is local-only worker evidence. It did not submit to CHC-COMP.".to_string(),
        String::new(),
        "## Summary".to_string(),
        format!("- Kind: {}", payload["kind"].as_str().unwrap_or("unknown")),
        format!(
            "- Issue: {}",
            payload["issue"]
                .as_u64()
                .map(|value| value.to_string())
                .unwrap_or_else(|| "none".to_string())
        ),
        format!("- Lane: {}", payload["lane"].as_str().unwrap_or("none")),
        format!("- Host: {}", payload["host"].as_str().unwrap_or("unknown")),
        format!(
            "- Total cases: {}",
            summary["total_cases"].as_u64().unwrap_or(0)
        ),
        format!("- Solved: {}", summary["solved"].as_u64().unwrap_or(0)),
        format!(
            "- Failed cases: {}",
            summary["failed_cases"].as_u64().unwrap_or(0)
        ),
        format!("- Wrong: {}", summary["wrong"].as_u64().unwrap_or(0)),
        format!("- Invalid: {}", summary["invalid"].as_u64().unwrap_or(0)),
        format!(
            "- Check failures: {}",
            summary["fail_count"].as_u64().unwrap_or(0)
        ),
        String::new(),
    ];
    push_chc_track_model_markdown(&mut lines);
    lines.extend([
        "## Provenance".to_string(),
        format!(
            "- Repo commit: {}",
            payload["repo"]["commit"].as_str().unwrap_or("unavailable")
        ),
        format!(
            "- Dirty: {}",
            payload["repo"]["dirty"].as_bool().unwrap_or(false)
        ),
        format!(
            "- Package commit: {}",
            payload["package_manifest_commit"]
                .as_str()
                .unwrap_or("unavailable")
        ),
        format!(
            "- Binary SHA256: {}",
            payload["binary_sha256"].as_str().unwrap_or("unavailable")
        ),
        String::new(),
        "## Cases".to_string(),
        "| Local category | Input | Expected | Actual | Timeout | Elapsed ms | Clean stdout | Result |"
            .to_string(),
        "| --- | --- | --- | --- | --- | ---: | --- | --- |".to_string(),
    ]);
    for case in payload["cases"].as_array().into_iter().flatten() {
        lines.push(format!(
            "| `{}` | `{}` | `{}` | `{}` | {} | {} | {} | `{}` |",
            markdown_cell(case["track"].as_str().unwrap_or("unknown")),
            markdown_cell(case["path"].as_str().unwrap_or("unknown")),
            markdown_cell(case["expected"].as_str().unwrap_or("unknown")),
            markdown_cell(case["actual"].as_str().unwrap_or("unknown")),
            case["timed_out"].as_bool().unwrap_or(false),
            case["elapsed_ms"].as_u64().unwrap_or(0),
            case["stdout_status_clean"].as_bool().unwrap_or(false),
            if case["passed"].as_bool() == Some(true) {
                "pass"
            } else {
                "fail"
            },
        ));
    }
    lines.extend([
        String::new(),
        "## Checks".to_string(),
        "| Check | Status | Detail |".to_string(),
        "| --- | --- | --- |".to_string(),
    ]);
    for check in payload["checks"].as_array().into_iter().flatten() {
        lines.push(format!(
            "| `{}` | `{}` | {} |",
            markdown_cell(check["name"].as_str().unwrap_or("unnamed")),
            markdown_cell(check["status"].as_str().unwrap_or("unknown")),
            markdown_cell(check["detail"].as_str().unwrap_or(""))
        ));
    }
    lines.extend([String::new(), "## Blockers".to_string()]);
    let blockers = payload["blockers"].as_array().cloned().unwrap_or_default();
    if blockers.is_empty() {
        lines.push("- None.".to_string());
    } else {
        for blocker in blockers {
            lines.push(format!(
                "- {}",
                blocker.as_str().unwrap_or("unknown blocker")
            ));
        }
    }
    lines.extend([String::new(), "## GitHub Actions".to_string()]);
    for action in payload["github_actions"].as_array().into_iter().flatten() {
        lines.push(format!(
            "- `{}`: {}",
            markdown_cell(action["command"].as_str().unwrap_or("gh")),
            action["status"].as_str().unwrap_or("unknown")
        ));
    }
    lines.push(String::new());
    write_text(path, &lines.join("\n"), false)
}

fn write_chc_worker_audit_markdown(path: &Path, payload: &JsonValue) -> Result<()> {
    let summary = &payload["summary"];
    let mut lines = vec![
        "# CHC-COMP Worker Audit".to_string(),
        String::new(),
        format!(
            "- Audit ready: {}",
            summary["audit_ready"].as_bool().unwrap_or(false)
        ),
        format!(
            "- Reports: {}",
            summary["report_count"].as_u64().unwrap_or(0)
        ),
        format!(
            "- Failures: {}",
            summary["fail_count"].as_u64().unwrap_or(0)
        ),
        String::new(),
        "## Checks".to_string(),
        "| Check | Status | Detail |".to_string(),
        "| --- | --- | --- |".to_string(),
    ];
    for check in payload["checks"].as_array().into_iter().flatten() {
        lines.push(format!(
            "| `{}` | `{}` | {} |",
            markdown_cell(check["name"].as_str().unwrap_or("unnamed")),
            markdown_cell(check["status"].as_str().unwrap_or("unknown")),
            markdown_cell(check["detail"].as_str().unwrap_or(""))
        ));
    }
    lines.push(String::new());
    write_text(path, &lines.join("\n"), false)
}

struct ChcZenodoSubmitReport {
    started_at_unix: u64,
    finished_at_unix: Option<u64>,
    dry_run: bool,
    steps: Vec<JsonValue>,
    commands: Vec<JsonValue>,
    outputs: serde_json::Map<String, JsonValue>,
    error: Option<String>,
}

impl ChcZenodoSubmitReport {
    fn new(dry_run: bool) -> Self {
        Self {
            started_at_unix: unix_now(),
            finished_at_unix: None,
            dry_run,
            steps: Vec::new(),
            commands: Vec::new(),
            outputs: serde_json::Map::new(),
            error: None,
        }
    }

    fn step(&mut self, name: &'static str, detail: impl Into<String>) {
        self.steps.push(json!({
            "name": name,
            "detail": detail.into(),
        }));
    }

    fn command(&mut self, command: &[String], cwd: &Path, output: &std::process::Output) {
        self.commands.push(json!({
            "command": command,
            "cwd": cwd,
            "exit_code": output.status.code(),
            "stdout": trim_report_text(&String::from_utf8_lossy(&output.stdout)),
            "stderr": trim_report_text(&String::from_utf8_lossy(&output.stderr)),
        }));
    }

    fn output(&mut self, key: &'static str, value: JsonValue) {
        self.outputs.insert(key.to_string(), value);
    }

    fn payload(&self) -> JsonValue {
        json!({
            "schema_version": "ay.chccomp-zenodo-submit/v1",
            "started_at_unix": self.started_at_unix,
            "finished_at_unix": self.finished_at_unix,
            "dry_run": self.dry_run,
            "steps": self.steps,
            "commands": self.commands,
            "outputs": self.outputs,
            "error": self.error,
        })
    }
}

#[derive(Clone, Copy)]
struct SubmissionGithubAccountPolicy {
    context: &'static str,
    required_owner: &'static str,
    required_login: &'static str,
    forbidden_logins: &'static [&'static str],
    git_author_name: &'static str,
    git_author_email: &'static str,
}

const CHC_ZENODO_GITHUB_ACCOUNT_POLICY: SubmissionGithubAccountPolicy =
    SubmissionGithubAccountPolicy {
        context: "CHC-COMP 2026 submission",
        required_owner: CHC_ZENODO_REQUIRED_GITHUB_OWNER,
        required_login: CHC_ZENODO_REQUIRED_GITHUB_LOGIN,
        forbidden_logins: CHC_ZENODO_FORBIDDEN_GITHUB_LOGINS,
        git_author_name: CHC_ZENODO_GIT_AUTHOR_NAME,
        git_author_email: CHC_ZENODO_GIT_AUTHOR_EMAIL,
    };

fn require_submission_github_account(
    policy: &SubmissionGithubAccountPolicy,
    supplied_owner: &str,
    probe_login: bool,
    ssh_key: Option<&Path>,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<()> {
    report.step(
        "github_account_policy",
        submission_github_account_policy_message(policy),
    );
    report.output(
        "github_account_policy",
        json!({
            "context": policy.context,
            "required_owner": policy.required_owner,
            "required_login": policy.required_login,
            "forbidden_logins": policy.forbidden_logins,
            "supplied_owner": supplied_owner,
        }),
    );
    require_submission_github_owner(policy, supplied_owner)?;
    if let Some(ssh_key) = ssh_key {
        require_submission_github_ssh_account(policy, ssh_key, root, report)?;
    }

    if !probe_login {
        report.step("github_account", "dry-run; active gh API login not probed");
        return Ok(());
    }

    require_submission_github_api_account(policy, root, report)
}

fn require_submission_github_api_account(
    policy: &SubmissionGithubAccountPolicy,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<()> {
    let output = run_submit_command_allow(
        report,
        root,
        vec![
            "gh".to_string(),
            "api".to_string(),
            "user".to_string(),
            "--jq".to_string(),
            ".login".to_string(),
        ],
    )?;
    if !output.status.success() {
        bail!(
            "failed to inspect active GitHub account with `gh api user --jq .login`; authenticate gh as '{}' before {}. stdout={} stderr={}",
            policy.required_login,
            policy.context,
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let login = String::from_utf8_lossy(&output.stdout).trim().to_string();
    report.output(
        "github_account",
        json!({
            "context": policy.context,
            "required_login": policy.required_login,
            "active_login": login,
        }),
    );
    if let Some(error) = submission_github_login_error(policy, &login) {
        bail!("{error}");
    }
    report.step("github_account", format!("verified gh login `{login}`"));
    Ok(())
}

fn require_submission_github_ssh_account(
    policy: &SubmissionGithubAccountPolicy,
    ssh_key: &Path,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<()> {
    let ssh_key = expand_tilde(ssh_key);
    let output = run_submit_command_allow(
        report,
        root,
        vec![
            "ssh".to_string(),
            "-F".to_string(),
            "/dev/null".to_string(),
            "-o".to_string(),
            "IdentitiesOnly=yes".to_string(),
            "-o".to_string(),
            "BatchMode=yes".to_string(),
            "-o".to_string(),
            "StrictHostKeyChecking=accept-new".to_string(),
            "-i".to_string(),
            ssh_key.to_string_lossy().into_owned(),
            "-T".to_string(),
            "git@github.com".to_string(),
        ],
    )?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{stdout}{stderr}");
    let expected = format!("Hi {}!", policy.required_login);
    if !combined.contains(&expected) {
        bail!(
            "SSH key '{}' did not authenticate to GitHub as '{}'. ssh output: {}",
            ssh_key.display(),
            policy.required_login,
            trim_report_text(combined.trim())
        );
    }
    report.step(
        "github_ssh_account",
        format!(
            "verified SSH key '{}' as `{}`",
            ssh_key.display(),
            policy.required_login
        ),
    );
    report.output(
        "github_ssh_account",
        json!({
            "required_login": policy.required_login,
            "ssh_key": ssh_key.to_string_lossy(),
        }),
    );
    Ok(())
}

fn require_submission_github_owner(
    policy: &SubmissionGithubAccountPolicy,
    supplied_owner: &str,
) -> Result<()> {
    if supplied_owner != policy.required_owner {
        bail!(
            "{} requires GitHub owner '{}', got '{}'",
            policy.context,
            policy.required_owner,
            supplied_owner
        );
    }
    Ok(())
}

fn configure_submission_git_identity(
    policy: &SubmissionGithubAccountPolicy,
    report: &mut ChcZenodoSubmitReport,
    checkout: &Path,
) -> Result<()> {
    run_submit_command(
        report,
        checkout,
        submission_git_command([
            "config".to_string(),
            "user.name".to_string(),
            policy.git_author_name.to_string(),
        ]),
    )?;
    run_submit_command(
        report,
        checkout,
        submission_git_command([
            "config".to_string(),
            "user.email".to_string(),
            policy.git_author_email.to_string(),
        ]),
    )?;
    Ok(())
}

fn submission_github_login_error(
    policy: &SubmissionGithubAccountPolicy,
    active_login: &str,
) -> Option<String> {
    if active_login == policy.required_login {
        return None;
    }
    let account = if active_login.is_empty() {
        "<empty>"
    } else {
        active_login
    };
    let forbidden = render_forbidden_logins(policy);
    Some(format!(
        "refusing {} with GitHub account '{}'; authenticate gh as '{}'{}",
        policy.context, account, policy.required_login, forbidden
    ))
}

fn submission_github_account_policy_message(policy: &SubmissionGithubAccountPolicy) -> String {
    let forbidden = render_forbidden_logins(policy);
    format!(
        "{} must use GitHub owner '{}' and account-specific GitHub auth for '{}'; PR creation requires `gh api user --jq .login` to match{}",
        policy.context, policy.required_owner, policy.required_login, forbidden
    )
}

fn render_forbidden_logins(policy: &SubmissionGithubAccountPolicy) -> String {
    if policy.forbidden_logins.is_empty() {
        String::new()
    } else {
        format!(
            "; forbidden account(s): {}",
            policy.forbidden_logins.join(", ")
        )
    }
}

fn default_submission_git_program() -> String {
    let system_git = Path::new("/usr/bin/git");
    if system_git.is_file() {
        system_git.to_string_lossy().into_owned()
    } else {
        "git".to_string()
    }
}

fn submission_git_program() -> String {
    if let Ok(program) = env::var("AY_SUBMISSION_GIT") {
        let program = program.trim();
        if !program.is_empty() {
            return program.to_string();
        }
    }
    default_submission_git_program()
}

fn submission_git_command<I, S>(args: I) -> Vec<String>
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    let mut command = vec![submission_git_program()];
    command.extend(args.into_iter().map(Into::into));
    command
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SubmissionSourcePin {
    commit: String,
}

fn source_commit_short(commit: &str) -> &str {
    commit.get(..12).unwrap_or(commit)
}

fn pin_submit_source(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<SubmissionSourcePin> {
    let commit = run_submit_stdout(report, root, submission_git_command(["rev-parse", "HEAD"]))?;
    report.output("source_commit", json!(&commit));
    report.output(
        "source_pin",
        json!({
            "commit": &commit,
            "policy": "resolved once at submit startup; later source HEAD changes are rejected",
        }),
    );
    require_clean_submit_source(opts, root, report)?;
    Ok(SubmissionSourcePin { commit })
}

fn resolve_chc_submit_branch(
    source_pin: &SubmissionSourcePin,
    report: &mut ChcZenodoSubmitReport,
) -> Result<String> {
    let branch = format!(
        "{}-{}-{}-{}",
        CHC_ZENODO_BRANCH_PREFIX,
        source_commit_short(&source_pin.commit),
        report.started_at_unix,
        std::process::id()
    );
    validate_chc_submit_branch_name(&branch)?;
    report.output(
        "submit_branch",
        json!({
            "name": &branch,
            "generated": true,
            "policy": "fresh branch per live CHC-COMP submit; existing branches and PRs are rejected",
        }),
    );
    report.step("submit_branch", format!("using fresh PR branch {branch}"));
    Ok(branch)
}

// git-check-ref-format forbids refs ending in exactly ".lock" (case-sensitive);
// this is a ref-name rule, not a file-extension comparison.
#[allow(clippy::case_sensitive_file_extension_comparisons)]
fn validate_chc_submit_branch_name(branch: &str) -> Result<()> {
    if branch.is_empty()
        || branch.starts_with('/')
        || branch.ends_with('/')
        || branch.ends_with(".lock")
        || branch.contains("..")
        || branch.contains("@{")
        || branch.chars().any(|ch| {
            ch.is_ascii_whitespace() || matches!(ch, '~' | '^' | ':' | '?' | '*' | '[' | '\\')
        })
    {
        bail!("invalid CHC-COMP submission branch name: {branch}");
    }
    Ok(())
}

fn require_submit_source_pin(
    report: &mut ChcZenodoSubmitReport,
    root: &Path,
    pin: &SubmissionSourcePin,
    stage: &'static str,
) -> Result<()> {
    let current = run_submit_stdout(report, root, submission_git_command(["rev-parse", "HEAD"]))?;
    report.output(
        "source_pin_check",
        json!({
            "stage": stage,
            "expected": &pin.commit,
            "actual": &current,
        }),
    );
    if current != pin.commit {
        bail!(
            "source commit changed during CHC-COMP submit at {stage}: pinned {}, now {}",
            pin.commit,
            current
        );
    }
    report.step("source_pin", format!("{stage}: still at {}", pin.commit));
    Ok(())
}

fn submit_chc_comp_zenodo(opts: &ChcCompZenodoSubmitOptions) -> Result<()> {
    let root = workspace_root();
    let live = !opts.dry_run;
    let mut report = ChcZenodoSubmitReport::new(opts.dry_run);
    let result = submit_chc_comp_zenodo_impl(opts, &root, &mut report);
    if let Err(err) = &result {
        report.error = Some(format!("{err:#}"));
    }
    write_chc_zenodo_submit_reports(opts, &root, &mut report)?;
    result?;
    if live {
        println!("status=pass submitted=true");
    } else {
        println!("status=pass submitted=false dry_run=true");
    }
    Ok(())
}

fn submit_chc_comp_zenodo_impl(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<()> {
    split_required_chc_tracks(&opts.tracks)?;
    let source_pin = pin_submit_source(opts, root, report)?;
    let submit_branch = resolve_chc_submit_branch(&source_pin, report)?;
    let live = !opts.dry_run;
    let github_owner = CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner;
    if opts.skip_pr {
        require_submission_github_owner(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY, github_owner)?;
        report.step("github_account", "skipped by --skip-pr");
    } else {
        require_submission_github_account(
            &CHC_ZENODO_GITHUB_ACCOUNT_POLICY,
            github_owner,
            live,
            live.then_some(opts.fork_ssh_key.as_path()),
            root,
            report,
        )?;
    }

    let linux_ay = build_or_validate_chc_linux_ay(opts, root, report)?;
    require_submit_source_pin(report, root, &source_pin, "after_build")?;
    let archive_url = CHC_DEFAULT_ARCHIVE_URL.to_string();
    let mut artifact = package_chc_for_zenodo(opts, root, report, &linux_ay, &archive_url)?;
    let final_archive_url = if live {
        let published_url =
            publish_chc_artifact_to_zenodo(opts, root, report, &source_pin, &artifact, &linux_ay)?;
        require_submit_source_pin(report, root, &source_pin, "after_zenodo_publish")?;
        artifact = package_chc_for_zenodo(opts, root, report, &linux_ay, &published_url)?;
        published_url
    } else {
        report.step("zenodo", "dry-run; no upload performed");
        archive_url
    };
    report.output(
        "artifact",
        json!({
            "path": artifact,
            "sha256": sha256_file(&artifact)?,
            "size_bytes": artifact.metadata().map(|m| m.len()).unwrap_or(0),
            "archive_url": final_archive_url,
        }),
    );

    require_submit_source_pin(report, root, &source_pin, "before_pr_checkout")?;
    let checkout =
        prepare_chc_comp_pr_checkout(opts, root, report, &submit_branch, &final_archive_url)?;
    if opts.skip_pr {
        report.step("pr", "skipped by --skip-pr");
    } else {
        commit_push_and_create_chc_pr(
            opts,
            root,
            report,
            &checkout,
            &submit_branch,
            &final_archive_url,
        )?;
    }
    Ok(())
}

fn require_clean_submit_source(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<()> {
    let status = run_submit_stdout(
        report,
        root,
        submission_git_command(["status", "--porcelain=v1", "--untracked-files=no"]),
    )?;
    report.output("source_dirty_tracked", json!(!status.trim().is_empty()));
    if !status.trim().is_empty() {
        report.output("source_dirty_tracked_status", json!(status));
        if !opts.allow_dirty {
            bail!(
                "refusing to submit from dirty tracked worktree; commit/stash changes or pass --allow-dirty"
            );
        }
    }
    Ok(())
}

fn build_or_validate_chc_linux_ay(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<PathBuf> {
    let binary = resolve_cli_path(root, &opts.ay_bin);
    if opts.skip_build {
        report.step("build", format!("skipped; using {}", binary.display()));
    } else {
        let script = root.join("scripts/build_linux_static.sh");
        let mut command = vec![script.to_string_lossy().into_owned()];
        if opts.build_tool != "auto" {
            command.push("--tool".to_string());
            command.push(opts.build_tool.clone());
        }
        run_submit_command(report, root, command)?;
        report.step("build", format!("completed with tool {}", opts.build_tool));
    }
    run_submit_command(
        report,
        root,
        vec![
            root.join("scripts/validate_linux_static_binary.sh")
                .to_string_lossy()
                .into_owned(),
            binary.to_string_lossy().into_owned(),
        ],
    )?;
    report.output(
        "linux_binary",
        json!({
            "path": binary,
            "sha256": sha256_file(&binary)?,
            "size_bytes": binary.metadata().map(|m| m.len()).unwrap_or(0),
            "build_metadata": build_metadata_sidecar_path(&binary),
        }),
    );
    Ok(binary)
}

fn package_chc_for_zenodo(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
    linux_ay: &Path,
    archive_url: &str,
) -> Result<PathBuf> {
    let host_ay = resolve_host_ay(root, opts.host_ay.as_deref())?;
    let package_dir = resolve_cli_path(root, &opts.package_dir);
    run_submit_command(
        report,
        root,
        vec![
            host_ay.to_string_lossy().into_owned(),
            "submission".to_string(),
            "package".to_string(),
            "chc".to_string(),
            "--output".to_string(),
            package_dir.to_string_lossy().into_owned(),
            "--ay-bin".to_string(),
            linux_ay.to_string_lossy().into_owned(),
            "--archive-url".to_string(),
            archive_url.to_string(),
            "--tracks".to_string(),
            opts.tracks.clone(),
        ],
    )?;
    let mut gate = vec![
        host_ay.to_string_lossy().into_owned(),
        "submission".to_string(),
        "gate".to_string(),
        "chc".to_string(),
        "--package".to_string(),
        package_dir.to_string_lossy().into_owned(),
        "--require-linux".to_string(),
        "--require-static".to_string(),
        "--skip-smoke".to_string(),
    ];
    if submit_public_url(archive_url) {
        gate.push("--require-public-urls".to_string());
    }
    run_submit_command(report, root, gate)?;
    let artifact = package_dir.join(CHC_ZENODO_ARTIFACT_NAME);
    if !artifact.is_file() {
        bail!("expected CHC artifact missing: {}", artifact.display());
    }
    report.output(
        "package",
        json!({
            "path": package_dir,
            "archive": artifact,
            "archive_sha256": sha256_file(&artifact)?,
            "host_ay": host_ay,
        }),
    );
    Ok(artifact)
}

fn publish_chc_artifact_to_zenodo(
    opts: &ChcCompZenodoSubmitOptions,
    _root: &Path,
    report: &mut ChcZenodoSubmitReport,
    source_pin: &SubmissionSourcePin,
    artifact: &Path,
    linux_ay: &Path,
) -> Result<String> {
    #[cfg(not(feature = "submission-live"))]
    {
        let _ = (opts, _root, report, source_pin, artifact, linux_ay);
        bail!(
            "this ay binary was built without live Zenodo submission support; rebuild with --features submission-live"
        );
    }

    #[cfg(feature = "submission-live")]
    {
        let token = read_submit_env_key(&expand_tilde(&opts.env_file), &opts.zenodo_token_env)?;
        let base = opts.zenodo_base_url.trim_end_matches('/');
        let agent = ureq::AgentBuilder::new()
            .timeout(Duration::from_secs(opts.zenodo_timeout_seconds))
            .build();
        let auth = format!("Bearer {token}");
        let deposition = zenodo_post_json(
            &agent,
            &auth,
            &format!("{base}/api/deposit/depositions"),
            json!({}),
        )?;
        let deposition_id = deposition["id"]
            .as_i64()
            .context("Zenodo create response missing id")?;
        let bucket = deposition["links"]["bucket"]
            .as_str()
            .context("Zenodo create response missing links.bucket")?;
        report.step("zenodo_create", format!("deposition_id={deposition_id}"));

        let metadata = chc_zenodo_metadata(opts, source_pin, artifact, linux_ay)?;
        let _ = zenodo_put_json(
            &agent,
            &auth,
            &format!("{base}/api/deposit/depositions/{deposition_id}"),
            json!({ "metadata": metadata }),
        )?;
        report.step("zenodo_metadata", "metadata accepted");

        let artifact_bytes = fs::read(artifact)
            .with_context(|| format!("failed to read artifact '{}'", artifact.display()))?;
        let upload_url = format!(
            "{}/{}",
            bucket.trim_end_matches('/'),
            CHC_ZENODO_ARTIFACT_NAME
        );
        let _ = zenodo_put_bytes(&agent, &auth, &upload_url, &artifact_bytes)?;
        report.step(
            "zenodo_upload",
            format!("uploaded {CHC_ZENODO_ARTIFACT_NAME}"),
        );

        if opts.no_publish {
            report.output(
                "zenodo",
                json!({
                    "deposition_id": deposition_id,
                    "published": false,
                    "draft_url": deposition["links"]["html"],
                }),
            );
            bail!("--no-publish created a Zenodo draft, but no public archive URL exists for PR submission");
        }

        let published = zenodo_post_no_body(
            &agent,
            &auth,
            &format!("{base}/api/deposit/depositions/{deposition_id}/actions/publish"),
        )?;
        let record_id = published["record_id"]
            .as_i64()
            .or_else(|| published["id"].as_i64())
            .context("Zenodo publish response missing record id")?;
        let record_url = published["links"]["record_html"]
            .as_str()
            .map(ToOwned::to_owned)
            .unwrap_or_else(|| format!("{base}/records/{record_id}"));
        let archive_url =
            format!("{base}/records/{record_id}/files/{CHC_ZENODO_ARTIFACT_NAME}?download=1");
        verify_zenodo_download(&agent, &archive_url, &sha256_file(artifact)?)?;
        report.output(
            "zenodo",
            json!({
                "deposition_id": deposition_id,
                "record_id": record_id,
                "record_url": record_url,
                "archive_url": archive_url,
                "published": true,
            }),
        );
        report.step("zenodo_publish", format!("record_url={record_url}"));
        Ok(archive_url)
    }
}

fn prepare_chc_comp_pr_checkout(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
    branch: &str,
    archive_url: &str,
) -> Result<PathBuf> {
    let checkout = resolve_cli_path(root, &opts.chc_checkout);
    if checkout.exists() && !checkout.join(".git").is_dir() {
        bail!(
            "CHC checkout path exists but is not a git checkout: {}",
            checkout.display()
        );
    }
    if !checkout.exists() {
        if let Some(parent) = checkout.parent() {
            fs::create_dir_all(parent)
                .with_context(|| format!("failed to create '{}'", parent.display()))?;
        }
        run_submit_command(
            report,
            root,
            submission_git_command([
                "clone".to_string(),
                opts.chc_repo_url.clone(),
                checkout.to_string_lossy().into_owned(),
            ]),
        )?;
    }
    run_submit_command(
        report,
        &checkout,
        submission_git_command(["fetch", "origin", "main"]),
    )?;
    run_submit_command(
        report,
        &checkout,
        submission_git_command([
            "checkout".to_string(),
            "-B".to_string(),
            branch.to_string(),
            "origin/main".to_string(),
        ]),
    )?;

    let pr_dir = resolve_cli_path(root, &opts.package_dir).join("pr");
    copy_submit_pr_file(
        &pr_dir.join("benchmark-defs/ay.xml.template"),
        &checkout.join("benchmark-defs/ay.xml.template"),
    )?;
    copy_submit_pr_file(
        &pr_dir.join("tooldefs/ay.py"),
        &checkout.join("tooldefs/ay.py"),
    )?;
    let fragment = fs::read_to_string(pr_dir.join("Makefile.ay.fragment"))
        .context("failed to read generated CHC Makefile fragment")?;
    let makefile = checkout.join("Makefile");
    let patched = patch_chc_submit_makefile(
        &fs::read_to_string(&makefile)
            .with_context(|| format!("failed to read '{}'", makefile.display()))?,
        &fragment,
    )?;
    fs::write(&makefile, patched)
        .with_context(|| format!("failed to write '{}'", makefile.display()))?;
    run_submit_command(
        report,
        &checkout,
        vec!["make".to_string(), "debug-discovery".to_string()],
    )?;
    let status = run_submit_stdout(
        report,
        &checkout,
        submission_git_command(["status", "--short"]),
    )?;
    report.output(
        "chc_checkout",
        json!({
            "path": checkout,
            "branch": branch,
            "status_short": status,
            "archive_url": archive_url,
        }),
    );
    Ok(checkout)
}

fn commit_push_and_create_chc_pr(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
    checkout: &Path,
    branch: &str,
    archive_url: &str,
) -> Result<()> {
    configure_submission_git_identity(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY, report, checkout)?;
    run_submit_command(
        report,
        checkout,
        submission_git_command([
            "add".to_string(),
            "Makefile".to_string(),
            "benchmark-defs/ay.xml.template".to_string(),
            "tooldefs/ay.py".to_string(),
        ]),
    )?;
    let diff = run_submit_command_allow(
        report,
        checkout,
        submission_git_command(["diff", "--cached", "--quiet"]),
    )?;
    if !diff.status.success() {
        run_submit_command(
            report,
            checkout,
            submission_git_command([
                "commit".to_string(),
                "-m".to_string(),
                "Add ay CHC-COMP 2026 verifier".to_string(),
            ]),
        )?;
    } else {
        report.step("commit", "no staged diff; reusing existing branch commit");
    }

    if opts.dry_run {
        report.step("push", "dry-run; --dry-run set");
        return Ok(());
    }
    let fork_url = opts.fork_repo_url.clone().unwrap_or_else(|| {
        format!(
            "git@github.com:{}/chc-comp-2026.git",
            CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner
        )
    });
    let remotes = run_submit_stdout(report, checkout, submission_git_command(["remote"]))?;
    if remotes.lines().any(|line| line == "fork") {
        run_submit_command(
            report,
            checkout,
            submission_git_command([
                "remote".to_string(),
                "set-url".to_string(),
                "fork".to_string(),
                fork_url.clone(),
            ]),
        )?;
    } else {
        run_submit_command(
            report,
            checkout,
            submission_git_command([
                "remote".to_string(),
                "add".to_string(),
                "fork".to_string(),
                fork_url.clone(),
            ]),
        )?;
    }
    let fork_ssh_key = expand_tilde(&opts.fork_ssh_key);
    let git_ssh_command = submission_git_ssh_command(&fork_ssh_key);
    require_fresh_chc_fork_branch(report, checkout, branch, &git_ssh_command)?;
    let push = submission_git_command([
        "push".to_string(),
        "fork".to_string(),
        format!("HEAD:refs/heads/{branch}"),
    ]);
    run_submit_command_with_env(
        report,
        checkout,
        push,
        &[("GIT_SSH_COMMAND", git_ssh_command)],
    )?;
    let pr_url = create_fresh_chc_submit_pr(opts, root, report, branch, archive_url)?;
    report.output("pull_request", json!(pr_url));
    Ok(())
}

fn require_fresh_chc_fork_branch(
    report: &mut ChcZenodoSubmitReport,
    checkout: &Path,
    branch: &str,
    git_ssh_command: &str,
) -> Result<()> {
    let output = run_submit_command_allow_with_env(
        report,
        checkout,
        submission_git_command([
            "ls-remote".to_string(),
            "--heads".to_string(),
            "fork".to_string(),
            branch.to_string(),
        ]),
        &[("GIT_SSH_COMMAND", git_ssh_command.to_string())],
    )?;
    if !output.status.success() {
        bail!(
            "failed to check fork branch freshness for {branch}: stdout={} stderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    if !stdout.trim().is_empty() {
        bail!("refusing to reuse existing fork branch {branch}; CHC-COMP submit requires a fresh branch");
    }
    report.step(
        "fork_branch",
        format!("confirmed fork branch {branch} does not exist"),
    );
    Ok(())
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ExistingChcSubmitPr {
    number: Option<u64>,
    url: String,
    state: Option<String>,
}

impl ExistingChcSubmitPr {
    fn selector(&self) -> String {
        self.number
            .map(|number| number.to_string())
            .unwrap_or_else(|| self.url.clone())
    }
}

fn create_fresh_chc_submit_pr(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
    branch: &str,
    archive_url: &str,
) -> Result<String> {
    require_submission_github_api_account(&CHC_ZENODO_GITHUB_ACCOUNT_POLICY, root, report)?;
    let head = format!(
        "{}:{}",
        CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner, branch
    );
    let body_dir = make_temp_dir("ay-chccomp-pr-body")?;
    let body_path = body_dir.join("body.md");
    fs::write(&body_path, chc_submit_pr_body(report, archive_url)?)
        .with_context(|| format!("failed to write '{}'", body_path.display()))?;

    if let Some(existing) = find_existing_chc_submit_pr(root, report, "all", branch)? {
        bail!(
            "refusing to update existing CHC-COMP PR {} for branch {head}; submit requires a fresh PR",
            existing.selector()
        );
    }

    let created = run_submit_command_allow(
        report,
        root,
        vec![
            "gh".to_string(),
            "pr".to_string(),
            "create".to_string(),
            "--repo".to_string(),
            CHC_ZENODO_GITHUB_REPO.to_string(),
            "--base".to_string(),
            "main".to_string(),
            "--head".to_string(),
            head,
            "--title".to_string(),
            opts.pr_title.clone(),
            "--body-file".to_string(),
            body_path.to_string_lossy().into_owned(),
        ],
    )?;
    if !created.status.success() {
        let stdout = String::from_utf8_lossy(&created.stdout);
        let stderr = String::from_utf8_lossy(&created.stderr);
        bail!("gh pr create failed; no existing PR was edited: stdout={stdout} stderr={stderr}");
    }
    let url = extract_github_pr_url(&String::from_utf8_lossy(&created.stdout))
        .or_else(|| last_non_empty_line(&String::from_utf8_lossy(&created.stdout)));
    let Some(url) = url else {
        bail!("gh pr create did not print a PR URL");
    };
    report.step("pr", format!("created {url}"));
    Ok(url)
}

fn find_existing_chc_submit_pr(
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
    state: &str,
    branch: &str,
) -> Result<Option<ExistingChcSubmitPr>> {
    let output = run_submit_command_allow(
        report,
        root,
        vec![
            "gh".to_string(),
            "pr".to_string(),
            "list".to_string(),
            "--repo".to_string(),
            CHC_ZENODO_GITHUB_REPO.to_string(),
            "--state".to_string(),
            state.to_string(),
            "--author".to_string(),
            CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner.to_string(),
            "--limit".to_string(),
            "100".to_string(),
            "--json".to_string(),
            "number,url,state,headRefName,headRepositoryOwner".to_string(),
        ],
    )?;
    if !output.status.success() {
        bail!(
            "failed to check existing CHC-COMP PRs for branch {branch}; refusing to submit blindly: stdout={} stderr={}",
            trim_report_text(&String::from_utf8_lossy(&output.stdout)),
            trim_report_text(&String::from_utf8_lossy(&output.stderr))
        );
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    let existing = parse_chc_submit_pr_list(
        &stdout,
        CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner,
        branch,
    )
    .with_context(|| "failed to parse gh pr list JSON for CHC-COMP submission")?;
    if let Some(pr) = &existing {
        report.step(
            "pr_lookup",
            format!(
                "found existing {} PR {} for {}:{}",
                pr.state.as_deref().unwrap_or(state),
                pr.selector(),
                CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner,
                branch
            ),
        );
    } else {
        report.step(
            "pr_lookup",
            format!(
                "no {state} PR found for {}:{}",
                CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner, branch
            ),
        );
    }
    Ok(existing)
}

fn parse_chc_submit_pr_list(
    stdout: &str,
    owner: &str,
    branch: &str,
) -> Result<Option<ExistingChcSubmitPr>> {
    let payload: JsonValue = serde_json::from_str(stdout)?;
    let prs = payload
        .as_array()
        .context("gh pr list response was not a JSON array")?;
    let mut matches = prs.iter().filter(|pr| {
        pr.get("headRefName").and_then(JsonValue::as_str) == Some(branch)
            && pr_owner_login(pr) == Some(owner)
    });
    let Some(pr) = matches.next() else {
        return Ok(None);
    };
    if matches.next().is_some() {
        bail!("multiple PRs matched CHC-COMP submission head {owner}:{branch}");
    }
    let url = pr
        .get("url")
        .and_then(JsonValue::as_str)
        .context("matching gh PR entry missing url")?
        .to_string();
    let number = pr.get("number").and_then(JsonValue::as_u64);
    let state = pr
        .get("state")
        .and_then(JsonValue::as_str)
        .map(ToOwned::to_owned);
    Ok(Some(ExistingChcSubmitPr { number, url, state }))
}

fn pr_owner_login(pr: &JsonValue) -> Option<&str> {
    pr.get("headRepositoryOwner")
        .and_then(|owner| {
            owner
                .get("login")
                .and_then(JsonValue::as_str)
                .or(owner.as_str())
        })
        .or_else(|| pr.get("headOwner").and_then(JsonValue::as_str))
}

fn extract_github_pr_url(text: &str) -> Option<String> {
    text.split_whitespace().find_map(|word| {
        let cleaned = word
            .trim_matches(|ch: char| matches!(ch, '"' | '\'' | '`' | ',' | ';' | ')' | ']' | '}'));
        if cleaned.starts_with("https://github.com/") && cleaned.contains("/pull/") {
            Some(cleaned.to_string())
        } else {
            None
        }
    })
}

#[cfg(test)]
fn github_pr_number_from_url(url: &str) -> Option<u64> {
    url.rsplit('/').next()?.parse().ok()
}

fn last_non_empty_line(text: &str) -> Option<String> {
    text.lines()
        .rev()
        .map(str::trim)
        .find(|line| !line.is_empty())
        .map(ToOwned::to_owned)
}

fn run_submit_command(
    report: &mut ChcZenodoSubmitReport,
    cwd: &Path,
    command: Vec<String>,
) -> Result<std::process::Output> {
    run_submit_command_with_env(report, cwd, command, &[])
}

fn run_submit_command_with_env(
    report: &mut ChcZenodoSubmitReport,
    cwd: &Path,
    command: Vec<String>,
    envs: &[(&str, String)],
) -> Result<std::process::Output> {
    let output = run_submit_command_allow_with_env(report, cwd, command.clone(), envs)?;
    if !output.status.success() {
        bail!(
            "command failed: {} (exit {:?})\nstdout={}\nstderr={}",
            command.join(" "),
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(output)
}

fn run_submit_command_allow(
    report: &mut ChcZenodoSubmitReport,
    cwd: &Path,
    command: Vec<String>,
) -> Result<std::process::Output> {
    run_submit_command_allow_with_env(report, cwd, command, &[])
}

fn run_submit_command_allow_with_env(
    report: &mut ChcZenodoSubmitReport,
    cwd: &Path,
    command: Vec<String>,
    envs: &[(&str, String)],
) -> Result<std::process::Output> {
    let (program, args) = command
        .split_first()
        .context("internal error: empty submit command")?;
    let mut process = Command::new(program);
    process.args(args).current_dir(cwd);
    for (key, value) in envs {
        process.env(key, value);
    }
    let output = process
        .output()
        .with_context(|| format!("failed to start submit command '{}'", command.join(" ")))?;
    report.command(&command, cwd, &output);
    Ok(output)
}

fn run_submit_stdout(
    report: &mut ChcZenodoSubmitReport,
    cwd: &Path,
    command: Vec<String>,
) -> Result<String> {
    let output = run_submit_command(report, cwd, command)?;
    Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
}

fn resolve_host_ay(root: &Path, explicit: Option<&Path>) -> Result<PathBuf> {
    let mut candidates = Vec::new();
    if let Some(path) = explicit {
        candidates.push(resolve_cli_path(root, path));
    }
    candidates.push(root.join("target/release/ay"));
    candidates.push(root.join("target/debug/ay"));
    candidates.push(env::current_exe().context("failed to resolve current executable")?);
    for candidate in candidates {
        if candidate.is_file() {
            return Ok(candidate);
        }
    }
    bail!("no host ay executable found; pass --host-ay")
}

fn resolve_cli_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    }
}

fn submission_git_ssh_command(ssh_key: &Path) -> String {
    format!(
        "ssh -F /dev/null -o IdentitiesOnly=yes -o BatchMode=yes -o StrictHostKeyChecking=accept-new -i {}",
        ssh_key.to_string_lossy()
    )
}

fn expand_tilde(path: &Path) -> PathBuf {
    let text = path.to_string_lossy();
    if text == "~" {
        env::var_os("HOME")
            .map(PathBuf::from)
            .unwrap_or_else(|| path.to_path_buf())
    } else if let Some(rest) = text.strip_prefix("~/") {
        env::var_os("HOME")
            .map(PathBuf::from)
            .map(|home| home.join(rest))
            .unwrap_or_else(|| path.to_path_buf())
    } else {
        path.to_path_buf()
    }
}

#[cfg(feature = "submission-live")]
fn read_submit_env_key(path: &Path, key: &str) -> Result<String> {
    if let Ok(value) = env::var(key) {
        if !value.trim().is_empty() {
            return Ok(value);
        }
    }
    let values = parse_dotenv_file(path)?;
    values
        .into_iter()
        .find_map(|(candidate, value)| (candidate == key && !value.is_empty()).then_some(value))
        .with_context(|| {
            format!(
                "missing {key}; set it in the environment or {}",
                path.display()
            )
        })
}

#[cfg(any(feature = "submission-live", test))]
fn parse_dotenv_file(path: &Path) -> Result<Vec<(String, String)>> {
    let text = fs::read_to_string(path).unwrap_or_default();
    Ok(text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#') && line.contains('='))
        .filter_map(|line| {
            let (key, value) = line.split_once('=')?;
            Some((
                key.trim().to_string(),
                value
                    .trim()
                    .trim_matches('"')
                    .trim_matches('\'')
                    .to_string(),
            ))
        })
        .collect())
}

fn submit_public_url(url: &str) -> bool {
    url.starts_with("https://") && !url.contains("PLACEHOLDER")
}

#[cfg(feature = "submission-live")]
fn zenodo_post_json(
    agent: &ureq::Agent,
    auth: &str,
    url: &str,
    payload: JsonValue,
) -> Result<JsonValue> {
    zenodo_response_json(
        agent
            .post(url)
            .set("Authorization", auth)
            .set("Content-Type", "application/json")
            .send_json(payload),
        "POST",
        url,
    )
}

#[cfg(feature = "submission-live")]
fn zenodo_put_json(
    agent: &ureq::Agent,
    auth: &str,
    url: &str,
    payload: JsonValue,
) -> Result<JsonValue> {
    zenodo_response_json(
        agent
            .put(url)
            .set("Authorization", auth)
            .set("Content-Type", "application/json")
            .send_json(payload),
        "PUT",
        url,
    )
}

#[cfg(feature = "submission-live")]
fn zenodo_put_bytes(agent: &ureq::Agent, auth: &str, url: &str, bytes: &[u8]) -> Result<JsonValue> {
    zenodo_response_json(
        agent
            .put(url)
            .set("Authorization", auth)
            .set("Content-Type", "application/octet-stream")
            .send_bytes(bytes),
        "PUT",
        url,
    )
}

#[cfg(feature = "submission-live")]
fn zenodo_post_no_body(agent: &ureq::Agent, auth: &str, url: &str) -> Result<JsonValue> {
    zenodo_response_json(
        agent.post(url).set("Authorization", auth).call(),
        "POST",
        url,
    )
}

#[cfg(feature = "submission-live")]
fn zenodo_response_json(
    response: std::result::Result<ureq::Response, ureq::Error>,
    method: &str,
    url: &str,
) -> Result<JsonValue> {
    match response {
        Ok(response) => response
            .into_json::<JsonValue>()
            .with_context(|| format!("failed to decode Zenodo {method} response")),
        Err(ureq::Error::Status(code, response)) => {
            let body = response.into_string().unwrap_or_default();
            bail!(
                "Zenodo {method} {} returned HTTP {code}: {}",
                redact_submit_url(url),
                trim_report_text(&body)
            )
        }
        Err(err) => bail!("Zenodo {method} {} failed: {err}", redact_submit_url(url)),
    }
}

#[cfg(feature = "submission-live")]
fn verify_zenodo_download(
    agent: &ureq::Agent,
    archive_url: &str,
    expected_sha256: &str,
) -> Result<()> {
    let response = agent
        .get(archive_url)
        .call()
        .with_context(|| format!("failed to download {}", redact_submit_url(archive_url)))?;
    let mut reader = response.into_reader();
    let mut digest = Sha256::new();
    let mut buffer = [0u8; 1024 * 1024];
    loop {
        let read = reader
            .read(&mut buffer)
            .with_context(|| format!("failed while reading {}", redact_submit_url(archive_url)))?;
        if read == 0 {
            break;
        }
        digest.update(&buffer[..read]);
    }
    let actual = format!("{:x}", digest.finalize());
    if actual != expected_sha256 {
        bail!("Zenodo download hash mismatch: expected {expected_sha256}, got {actual}");
    }
    Ok(())
}

#[cfg(feature = "submission-live")]
fn chc_zenodo_metadata(
    opts: &ChcCompZenodoSubmitOptions,
    source_pin: &SubmissionSourcePin,
    artifact: &Path,
    linux_ay: &Path,
) -> Result<JsonValue> {
    let commit = &source_pin.commit;
    let title = opts
        .zenodo_title
        .clone()
        .unwrap_or_else(|| format!("ay CHC-COMP 2026 Linux x86_64 artifact ({})", &commit[..12]));
    let description = format!(
        "CHC-COMP 2026 submission artifact for ay.\n\n\
         This record contains `{CHC_ZENODO_ARTIFACT_NAME}`, a Linux x86_64 static ay binary packaged with the CHC-COMP wrapper. \
         The wrapper prints exactly one of `sat`, `unsat`, or `unknown`, and degrades unsupported or failed runs to `unknown`.\n\n\
         Source commit: `{commit}`\n\n\
         Archive SHA256: `{}`\n\n\
         Binary SHA256: `{}`\n",
        sha256_file(artifact)?,
        sha256_file(linux_ay)?
    );
    Ok(json!({
        "title": title,
        "upload_type": "software",
        "description": description,
        "creators": [{"name": opts.creator_name}],
        "access_right": "open",
        "license": "Apache-2.0",
        "publication_date": BUILD_INFO.datetime_utc.split('T').next().unwrap_or("2026-05-03"),
        "version": &commit[..12],
        "keywords": ["CHC-COMP", "Constrained Horn Clauses", "solver", "ay"],
        "related_identifiers": [{
            "identifier": opts.source_url,
            "relation": "isSupplementTo",
            "scheme": "url",
        }],
    }))
}

fn copy_submit_pr_file(src: &Path, dst: &Path) -> Result<()> {
    if let Some(parent) = dst.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create '{}'", parent.display()))?;
    }
    fs::copy(src, dst).with_context(|| {
        format!(
            "failed to copy generated PR file '{}' to '{}'",
            src.display(),
            dst.display()
        )
    })?;
    Ok(())
}

fn patch_chc_submit_makefile(text: &str, fragment: &str) -> Result<String> {
    let mut lines: Vec<String> = text.lines().map(ToOwned::to_owned).collect();
    if !download_verifiers_block(&lines)?.contains("$(TOOLS_DIRECTORY)/ay") {
        lines = add_ay_download_dependency(lines)?;
    }
    let text = lines.join("\n");
    let text = remove_existing_ay_make_target(&text);
    Ok(format!(
        "{}\n\n{}\n",
        text.trim_end(),
        ay_make_target_from_fragment(fragment)?
    ))
}

fn download_verifiers_block(lines: &[String]) -> Result<String> {
    let start = lines
        .iter()
        .position(|line| line.starts_with("download-verifiers:"))
        .context("Makefile has no download-verifiers target")?;
    let mut block = Vec::new();
    for line in &lines[start..] {
        if block.len() > 1 && line.trim().is_empty() {
            break;
        }
        block.push(line.clone());
    }
    Ok(block.join("\n"))
}

fn add_ay_download_dependency(mut lines: Vec<String>) -> Result<Vec<String>> {
    let start = lines
        .iter()
        .position(|line| line.starts_with("download-verifiers:"))
        .context("Makefile has no download-verifiers target")?;
    let mut end = start + 1;
    while end < lines.len() && !lines[end].trim().is_empty() {
        end += 1;
    }
    let last = end
        .checked_sub(1)
        .filter(|idx| *idx > start)
        .context("download-verifiers target has no dependency lines")?;
    if !lines[last].trim_end().ends_with('\\') {
        lines[last].push_str(" \\");
    }
    lines.insert(end, "\t$(TOOLS_DIRECTORY)/ay".to_string());
    Ok(lines)
}

fn ay_make_target_from_fragment(fragment: &str) -> Result<String> {
    let lines: Vec<_> = fragment.lines().collect();
    let start = lines
        .iter()
        .position(|line| line.starts_with("$(TOOLS_DIRECTORY)/ay:"))
        .context("generated Makefile fragment has no ay target")?;
    Ok(lines[start..].join("\n"))
}

fn remove_existing_ay_make_target(text: &str) -> String {
    let lines: Vec<_> = text.lines().collect();
    let mut out = Vec::new();
    let mut idx = 0;
    while idx < lines.len() {
        if lines[idx].starts_with("$(TOOLS_DIRECTORY)/ay:") {
            idx += 1;
            while idx < lines.len() && !lines[idx].trim().is_empty() {
                idx += 1;
            }
            while idx < lines.len() && lines[idx].trim().is_empty() {
                idx += 1;
            }
            continue;
        }
        out.push(lines[idx]);
        idx += 1;
    }
    out.join("\n")
}

fn chc_submit_pr_body(report: &ChcZenodoSubmitReport, archive_url: &str) -> Result<String> {
    let artifact = report
        .outputs
        .get("artifact")
        .cloned()
        .unwrap_or_else(|| json!({}));
    let binary = report
        .outputs
        .get("linux_binary")
        .cloned()
        .unwrap_or_else(|| json!({}));
    let source_commit = report
        .outputs
        .get("source_commit")
        .and_then(JsonValue::as_str)
        .unwrap_or("unavailable");
    Ok(format!(
        "This PR adds ay as a plain CHC-COMP 2026 verifier.\n\n\
         Artifact:\n\
         - Zenodo archive: {archive_url}\n\
         - Archive SHA256: `{}`\n\
         - Linux binary SHA256: `{}`\n\
         - Source commit: `{source_commit}`\n\n\
         Submission notes:\n\
         - `run_solver.sh` prints exactly one of `sat`, `unsat`, or `unknown`.\n\
         - Unsupported inputs, parser failures, crashes, and missing files degrade to `unknown`.\n\
         - The package is generated by `ay submission package chc`.\n\
         - Local gate used `ay submission gate chc --require-linux --require-static --require-public-urls --skip-smoke`.\n\n\
         Operator:\n\
         - GitHub owner/fork: `{}`\n\
         - Generated by: `ay submission submit chc-comp-zenodo`\n",
        artifact["sha256"].as_str().unwrap_or("unavailable"),
        binary["sha256"].as_str().unwrap_or("unavailable"),
        CHC_ZENODO_GITHUB_ACCOUNT_POLICY.required_owner
    ))
}

fn write_chc_zenodo_submit_reports(
    opts: &ChcCompZenodoSubmitOptions,
    root: &Path,
    report: &mut ChcZenodoSubmitReport,
) -> Result<()> {
    report.finished_at_unix = Some(unix_now());
    let report_dir = resolve_cli_path(root, &opts.report_dir);
    fs::create_dir_all(&report_dir)
        .with_context(|| format!("failed to create '{}'", report_dir.display()))?;
    let payload = report.payload();
    write_json_report(&report_dir.join("submission-report.json"), &payload)?;
    write_text(
        &report_dir.join("submission-report.md"),
        &chc_zenodo_submit_markdown(&payload),
        false,
    )?;
    println!(
        "wrote {}",
        display_path_for_report(&report_dir.join("submission-report.json"), root)
    );
    println!(
        "wrote {}",
        display_path_for_report(&report_dir.join("submission-report.md"), root)
    );
    Ok(())
}

fn chc_zenodo_submit_markdown(payload: &JsonValue) -> String {
    let mut out = String::new();
    out.push_str("# CHC-COMP 2026 Zenodo Submission Report\n\n");
    out.push_str(&format!("- Dry run: {}\n", payload["dry_run"]));
    if !payload["error"].is_null() {
        out.push_str(&format!("- Error: {}\n", payload["error"]));
    }
    if let Some(zenodo) = payload["outputs"]["zenodo"].as_object() {
        out.push_str("\n## Zenodo\n\n");
        out.push_str(&format!(
            "- Record: {}\n",
            zenodo
                .get("record_url")
                .and_then(JsonValue::as_str)
                .unwrap_or("unavailable")
        ));
        out.push_str(&format!(
            "- Archive URL: {}\n",
            zenodo
                .get("archive_url")
                .and_then(JsonValue::as_str)
                .unwrap_or("unavailable")
        ));
    }
    if let Some(pr) = payload["outputs"]["pull_request"].as_str() {
        out.push_str("\n## Pull Request\n\n");
        out.push_str(&format!("- URL: {pr}\n"));
    }
    out.push_str("\n## Steps\n\n");
    if let Some(steps) = payload["steps"].as_array() {
        for step in steps {
            out.push_str(&format!(
                "- `{}`: {}\n",
                step["name"].as_str().unwrap_or("step"),
                step["detail"].as_str().unwrap_or("")
            ));
        }
    }
    out.push_str("\n## Commands\n\n");
    if let Some(commands) = payload["commands"].as_array() {
        for command in commands {
            let rendered = command["command"]
                .as_array()
                .map(|args| {
                    args.iter()
                        .filter_map(JsonValue::as_str)
                        .collect::<Vec<_>>()
                        .join(" ")
                })
                .unwrap_or_else(|| "unknown".to_string());
            out.push_str(&format!(
                "- exit {}: `{rendered}`\n",
                command["exit_code"]
                    .as_i64()
                    .map(|code| code.to_string())
                    .unwrap_or_else(|| "signal".to_string())
            ));
        }
    }
    out
}

fn unix_now() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_secs())
        .unwrap_or(0)
}

fn trim_report_text(text: &str) -> String {
    const LIMIT: usize = 8000;
    if text.len() <= LIMIT {
        text.to_string()
    } else {
        format!("{}\n... truncated ...", &text[..LIMIT])
    }
}

#[cfg(any(feature = "submission-live", test))]
fn redact_submit_url(url: &str) -> String {
    if let Some((base, query)) = url.split_once('?') {
        let query = query
            .split('&')
            .map(|part| {
                if part.to_ascii_lowercase().contains("token") {
                    part.split_once('=')
                        .map(|(key, _)| format!("{key}=REDACTED"))
                        .unwrap_or_else(|| "token=REDACTED".to_string())
                } else {
                    part.to_string()
                }
            })
            .collect::<Vec<_>>()
            .join("&");
        format!("{base}?{query}")
    } else {
        url.to_string()
    }
}

#[cfg(test)]
mod submit_tests;

fn chc_verify_file(
    checks: &mut Vec<serde_json::Value>,
    name: &'static str,
    path: &Path,
    detail: &'static str,
    root: &Path,
) {
    if path.is_file() {
        push_check(
            checks,
            name,
            "pass",
            format!("{detail}: {}", display_path_for_report(path, root)),
        );
    } else {
        push_check(
            checks,
            name,
            "fail",
            format!("missing {detail}: {}", display_path_for_report(path, root)),
        );
    }
}

fn chc_verify_executable(
    checks: &mut Vec<serde_json::Value>,
    name: &'static str,
    path: &Path,
    detail: &'static str,
    root: &Path,
) {
    if path.is_file() && is_executable(path) {
        push_check(
            checks,
            name,
            "pass",
            format!("{detail}: {}", display_path_for_report(path, root)),
        );
    } else {
        push_check(
            checks,
            name,
            "fail",
            format!(
                "{detail} missing or not executable: {}",
                display_path_for_report(path, root)
            ),
        );
    }
}

fn chc_verify_binary(
    checks: &mut Vec<serde_json::Value>,
    name: &'static str,
    path: &Path,
    require_linux: bool,
    require_static: bool,
    detail: &'static str,
    root: &Path,
) -> Option<String> {
    if !path.is_file() {
        push_check(
            checks,
            name,
            "fail",
            format!("missing {detail}: {}", display_path_for_report(path, root)),
        );
        return None;
    }
    let platform = binary_platform(path).unwrap_or_else(|err| format!("unknown: {err:#}"));
    if require_linux && !platform.starts_with("linux-elf-x86_64") {
        push_check(
            checks,
            name,
            "fail",
            format!("{detail}: expected linux-elf-x86_64, got {platform}"),
        );
    } else if require_static && platform.contains("dynamic") {
        push_check(
            checks,
            name,
            "fail",
            format!("{detail}: expected static Linux ELF, got {platform}"),
        );
    } else {
        push_check(checks, name, "pass", format!("{detail}: {platform}"));
    }
    Some(platform)
}

fn chc_verify_command(
    checks: &mut Vec<serde_json::Value>,
    name: &'static str,
    command: &mut Command,
    detail: &'static str,
) {
    match command.output() {
        Ok(output) if output.status.success() => {
            push_check(checks, name, "pass", detail);
        }
        Ok(output) => {
            push_check(
                checks,
                name,
                "fail",
                format!(
                    "{detail}: exit={:?} stdout={} stderr={}",
                    output.status.code(),
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                ),
            );
        }
        Err(err) => push_check(checks, name, "fail", format!("{detail}: {err:#}")),
    }
}

fn verify_chc_xml_tracks(
    checks: &mut Vec<serde_json::Value>,
    xml_path: &Path,
    expected_tracks: &[String],
) {
    let Ok(text) = fs::read_to_string(xml_path) else {
        push_check(
            checks,
            "xml:track_includes",
            "fail",
            format!("failed to read XML {}", xml_path.display()),
        );
        return;
    };
    let mut found_task_names = Vec::new();
    let mut found_set_files = Vec::new();
    for line in text.lines() {
        if let Some(after_prefix) = line.split("<tasks name=\"").nth(1) {
            if let Some(track) = after_prefix.split('"').next() {
                found_task_names.push(track.to_string());
            }
        }
        let Some(after_prefix) = line.split("../chc-comp26-benchmarks/").nth(1) else {
            continue;
        };
        if !after_prefix.contains(".set") {
            continue;
        }
        let Some(set_file) = after_prefix.split(".set").next() else {
            continue;
        };
        found_set_files.push(set_file.to_string());
    }
    found_task_names.sort();
    found_task_names.dedup();
    found_set_files.sort();
    found_set_files.dedup();
    let mut expected_task_names = expected_tracks.to_vec();
    expected_task_names.sort();
    let mut expected_set_files: Vec<String> = expected_tracks
        .iter()
        .filter_map(|track| chc_track_set_file(track).map(ToOwned::to_owned))
        .collect();
    expected_set_files.sort();
    expected_set_files.dedup();
    if found_task_names == expected_task_names && found_set_files == expected_set_files {
        push_check(
            checks,
            "xml:track_includes",
            "pass",
            format!(
                "XML includes expected CHC-COMP local set-file categories [{}] via set files [{}]",
                expected_task_names.join(", "),
                expected_set_files.join(", ")
            ),
        );
    } else {
        push_check(
            checks,
            "xml:track_includes",
            "fail",
            format!(
                "XML local category mismatch: expected task names [{}] and set files [{}], found task names [{}] and set files [{}]",
                expected_task_names.join(", "),
                expected_set_files.join(", "),
                found_task_names.join(", "),
                found_set_files.join(", ")
            ),
        );
    }
}

fn verify_chc_public_url(
    checks: &mut Vec<serde_json::Value>,
    makefile_fragment: &Path,
    name: &'static str,
) {
    match fs::read_to_string(makefile_fragment) {
        Ok(text)
            if !text.contains("PLACEHOLDER")
                && (text.contains("https://") || text.contains("http://")) =>
        {
            push_check(
                checks,
                name,
                "pass",
                "Makefile fragment uses a public archive URL",
            );
        }
        Ok(_) => push_check(
            checks,
            name,
            "fail",
            "Makefile fragment does not contain a non-placeholder public archive URL",
        ),
        Err(err) => push_check(
            checks,
            name,
            "fail",
            format!("failed to read Makefile fragment: {err:#}"),
        ),
    }
}

fn read_json_file(
    path: &Path,
    checks: &mut Vec<serde_json::Value>,
    name: &'static str,
    root: &Path,
) -> Option<serde_json::Value> {
    match fs::read_to_string(path) {
        Ok(text) => match serde_json::from_str::<serde_json::Value>(&text) {
            Ok(value) => {
                push_check(
                    checks,
                    name,
                    "pass",
                    format!("read {}", display_path_for_report(path, root)),
                );
                Some(value)
            }
            Err(err) => {
                push_check(
                    checks,
                    name,
                    "fail",
                    format!(
                        "failed to parse {}: {err:#}",
                        display_path_for_report(path, root)
                    ),
                );
                None
            }
        },
        Err(err) => {
            push_check(
                checks,
                name,
                "fail",
                format!(
                    "failed to read {}: {err:#}",
                    display_path_for_report(path, root)
                ),
            );
            None
        }
    }
}

fn verify_chc_manifest_archive_sha(
    checks: &mut Vec<serde_json::Value>,
    manifest: Option<&serde_json::Value>,
    archive_sha256: Option<&str>,
) {
    let Some(manifest) = manifest else {
        push_check(
            checks,
            "manifest:archive_sha256",
            "fail",
            "MANIFEST.json unavailable",
        );
        return;
    };
    let Some(expected) = manifest["archive"]["sha256"].as_str() else {
        push_check(
            checks,
            "manifest:archive_sha256",
            "fail",
            "MANIFEST.json archive.sha256 unavailable",
        );
        return;
    };
    let Some(actual) = archive_sha256 else {
        push_check(
            checks,
            "manifest:archive_sha256",
            "fail",
            format!("archive unavailable; MANIFEST expected {expected}"),
        );
        return;
    };
    if actual == expected {
        push_check(
            checks,
            "manifest:archive_sha256",
            "pass",
            format!("archive SHA256 matches MANIFEST: {actual}"),
        );
    } else {
        push_check(
            checks,
            "manifest:archive_sha256",
            "fail",
            format!("archive SHA256 {actual} does not match MANIFEST {expected}"),
        );
    }
}

fn verify_chc_manifest_current_build(
    checks: &mut Vec<serde_json::Value>,
    manifest: Option<&serde_json::Value>,
) {
    let Some(manifest) = manifest else {
        push_check(
            checks,
            "manifest:current_build",
            "fail",
            "MANIFEST.json unavailable",
        );
        return;
    };
    let commit = manifest["generated_by"]["commit"]
        .as_str()
        .unwrap_or("unavailable");
    if commit == BUILD_INFO.commit {
        push_check(
            checks,
            "manifest:current_build",
            "pass",
            format!("package commit matches current build: {commit}"),
        );
    } else {
        push_check(
            checks,
            "manifest:current_build",
            "fail",
            format!(
                "package commit {commit} does not match current build {}",
                BUILD_INFO.commit
            ),
        );
    }
}

fn run_chc_comp_benchmark_smokes(
    checks: &mut Vec<serde_json::Value>,
    wrapper: &Path,
    benchmarks_root: &Path,
    tracks: &[String],
    samples_per_track: usize,
    timeout: Duration,
    repo_root: &Path,
) -> Result<Vec<serde_json::Value>> {
    if !benchmarks_root.is_dir() {
        push_check(
            checks,
            "benchmarks:root",
            "fail",
            format!("benchmark root is missing: {}", benchmarks_root.display()),
        );
        return Ok(Vec::new());
    }
    push_check(
        checks,
        "benchmarks:root",
        "pass",
        format!(
            "using benchmark root {}",
            display_path_for_report(benchmarks_root, repo_root)
        ),
    );

    let mut cases = Vec::new();
    for track in tracks {
        let Some(set_file) = chc_track_set_file(track) else {
            push_check(
                checks,
                format!("benchmarks:{track}:set"),
                "fail",
                format!("no benchmark-set mapping for CHC-COMP track {track}"),
            );
            continue;
        };
        let set_path = benchmarks_root.join(format!("{set_file}.set"));
        let entries = match chc_set_entries(&set_path, samples_per_track) {
            Ok(entries) if entries.is_empty() => {
                push_check(
                    checks,
                    format!("benchmarks:{track}:set"),
                    "fail",
                    format!("no benchmark entries in {}", set_path.display()),
                );
                continue;
            }
            Ok(entries) => {
                push_check(
                    checks,
                    format!("benchmarks:{track}:set"),
                    "pass",
                    format!(
                        "loaded {} sample(s) from {}",
                        entries.len(),
                        set_path.display()
                    ),
                );
                entries
            }
            Err(err) => {
                push_check(
                    checks,
                    format!("benchmarks:{track}:set"),
                    "fail",
                    format!("failed to read {}: {err:#}", set_path.display()),
                );
                continue;
            }
        };
        for entry in entries {
            cases.push(ChcCompBenchmarkCase::new(track, entry));
        }
    }
    run_chc_comp_benchmark_smoke_cases(checks, wrapper, benchmarks_root, &cases, timeout, repo_root)
}

fn run_chc_comp_benchmark_fixed_smokes(
    checks: &mut Vec<serde_json::Value>,
    wrapper: &Path,
    benchmarks_root: &Path,
    cases: &[ChcCompBenchmarkCase],
    timeout: Duration,
    repo_root: &Path,
) -> Result<Vec<serde_json::Value>> {
    if !benchmarks_root.is_dir() {
        push_check(
            checks,
            "benchmarks:root",
            "fail",
            format!("benchmark root is missing: {}", benchmarks_root.display()),
        );
        return Ok(Vec::new());
    }
    push_check(
        checks,
        "benchmarks:root",
        "pass",
        format!(
            "using benchmark root {}",
            display_path_for_report(benchmarks_root, repo_root)
        ),
    );

    for case in cases {
        let Some(set_file) = chc_track_set_file(&case.track) else {
            push_check(
                checks,
                format!("benchmarks:{}:set", case.track),
                "fail",
                format!("no benchmark-set mapping for CHC-COMP track {}", case.track),
            );
            continue;
        };
        let set_path = benchmarks_root.join(format!("{set_file}.set"));
        match chc_set_contains_entry(&set_path, &case.set_entry) {
            Ok(true) => push_check(
                checks,
                format!("benchmarks:{}:set", case.track),
                "pass",
                format!(
                    "fixed lane entry {} is present in {}",
                    case.set_entry,
                    set_path.display()
                ),
            ),
            Ok(false) => push_check(
                checks,
                format!("benchmarks:{}:set", case.track),
                "fail",
                format!(
                    "fixed lane entry {} is missing from {}",
                    case.set_entry,
                    set_path.display()
                ),
            ),
            Err(err) => push_check(
                checks,
                format!("benchmarks:{}:set", case.track),
                "fail",
                format!("failed to read {}: {err:#}", set_path.display()),
            ),
        }
    }

    run_chc_comp_benchmark_smoke_cases(checks, wrapper, benchmarks_root, cases, timeout, repo_root)
}

fn run_chc_comp_benchmark_smoke_cases(
    checks: &mut Vec<serde_json::Value>,
    wrapper: &Path,
    benchmarks_root: &Path,
    cases: &[ChcCompBenchmarkCase],
    timeout: Duration,
    repo_root: &Path,
) -> Result<Vec<serde_json::Value>> {
    let mut smokes = Vec::new();
    for selected in cases {
        let yml_path = benchmarks_root.join(selected.set_entry.trim_start_matches("./"));
        let case = run_chc_comp_benchmark_smoke(
            wrapper,
            benchmarks_root,
            &selected.track,
            &selected.set_entry,
            &yml_path,
            timeout,
            repo_root,
        )?;
        let status = if case["passed"].as_bool() == Some(true) {
            "pass"
        } else {
            "fail"
        };
        push_check(
            checks,
            format!(
                "benchmark_smoke:{}:{}",
                selected.track,
                case["input"].as_str().unwrap_or(&selected.set_entry)
            ),
            status,
            case["detail"]
                .as_str()
                .unwrap_or("benchmark smoke completed")
                .to_string(),
        );
        smokes.push(case);
    }
    if smokes
        .iter()
        .all(|case| case["passed"].as_bool() == Some(true))
        && !smokes.is_empty()
    {
        push_check(
            checks,
            "benchmarks:smoke",
            "pass",
            format!(
                "{} benchmark smoke(s) matched expected statuses",
                smokes.len()
            ),
        );
    } else {
        let failed = smokes
            .iter()
            .filter(|case| case["passed"].as_bool() != Some(true))
            .count();
        push_check(
            checks,
            "benchmarks:smoke",
            "fail",
            format!("{failed}/{} benchmark smoke(s) failed", smokes.len()),
        );
    }
    Ok(smokes)
}

fn chc_set_contains_entry(set_path: &Path, expected: &str) -> Result<bool> {
    let expected = expected.trim_start_matches("./");
    let entries = chc_set_entries(set_path, usize::MAX)?;
    Ok(entries
        .iter()
        .any(|entry| entry.trim_start_matches("./") == expected))
}

fn chc_set_entries(set_path: &Path, limit: usize) -> Result<Vec<String>> {
    let text = fs::read_to_string(set_path)
        .with_context(|| format!("failed to read set file '{}'", set_path.display()))?;
    Ok(text
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .take(limit)
        .map(ToOwned::to_owned)
        .collect())
}

fn run_chc_comp_benchmark_smoke(
    wrapper: &Path,
    benchmarks_root: &Path,
    track: &str,
    set_entry: &str,
    yml_path: &Path,
    timeout: Duration,
    repo_root: &Path,
) -> Result<serde_json::Value> {
    let yml_text = fs::read_to_string(yml_path)
        .with_context(|| format!("failed to read benchmark metadata '{}'", yml_path.display()))?;
    let input = chc_yaml_field(&yml_text, "input_files")
        .with_context(|| format!("missing input_files in '{}'", yml_path.display()))?;
    let expected = chc_expected_status_from_yml(&yml_text);
    let smt_path = yml_path.parent().unwrap_or(benchmarks_root).join(&input);
    let solver_timeout_ms = chc_comp_internal_timeout_ms(timeout);
    let mut command = Command::new(wrapper);
    command.arg(&smt_path);
    if let Some(timeout_ms) = solver_timeout_ms {
        command.env("AY_CHC_TIMEOUT_MS", timeout_ms.to_string());
    }
    let run =
        match run_command_with_timeout(&mut command, timeout, &format!("CHC-COMP {track} smoke")) {
            Ok(run) => run,
            Err(err) => {
                let expected_text = expected.unwrap_or_else(|| "unknown".to_string());
                return Ok(json!({
                    "track": track,
                    "set_entry": set_entry,
                    "metadata": display_path_for_report(yml_path, repo_root),
                    "input": input,
                    "input_path": display_path_for_report(&smt_path, repo_root),
                    "expected_status": expected_text,
                    "actual_status": "no-status",
                    "exit_code": Option::<i32>::None,
                    "timed_out": false,
                    "elapsed_ms": 0,
                    "solver_timeout_ms": solver_timeout_ms,
                    "stdout": "",
                    "stderr": format!("{err:#}"),
                    "passed": false,
                    "detail": format!(
                        "{track} {input}: failed to run archived wrapper {}, error={err:#}",
                        display_path_for_report(wrapper, repo_root),
                    ),
                }));
            }
        };
    let stdout = String::from_utf8_lossy(&run.stdout).to_string();
    let stderr = String::from_utf8_lossy(&run.stderr).to_string();
    let actual = first_chc_status(&stdout).unwrap_or("no-status").to_string();
    let expected_text = expected.clone().unwrap_or_else(|| "unknown".to_string());
    let status_ok = CHC_LATE_VALID_STATUSES.contains(&actual.as_str());
    let expected_ok = expected.as_ref().is_none_or(|expected| actual == *expected);
    let passed = !run.timed_out && run.exit_code == Some(0) && status_ok && expected_ok;
    let detail = if passed {
        format!("{track} {input}: {actual} in {}ms", run.elapsed_ms)
    } else {
        format!(
            "{track} {input}: expected {expected_text}, got {actual}, exit={:?}, timeout={}, elapsed={}ms",
            run.exit_code, run.timed_out, run.elapsed_ms
        )
    };
    Ok(json!({
        "track": track,
        "set_entry": set_entry,
        "metadata": display_path_for_report(yml_path, repo_root),
        "input": input,
        "input_path": display_path_for_report(&smt_path, repo_root),
        "expected_status": expected_text,
        "actual_status": actual,
        "exit_code": run.exit_code,
        "timed_out": run.timed_out,
        "elapsed_ms": run.elapsed_ms,
        "solver_timeout_ms": solver_timeout_ms,
        "stdout": stdout,
        "stderr": stderr,
        "passed": passed,
        "detail": detail,
    }))
}

fn chc_comp_internal_timeout_ms(timeout: Duration) -> Option<u64> {
    let ms = duration_millis(timeout);
    if ms == 0 {
        return None;
    }
    let reserve = (ms / 10).clamp(5_000, 30_000);
    Some(ms.saturating_sub(reserve).max(1))
}

struct ChcVerifyRun {
    exit_code: Option<i32>,
    timed_out: bool,
    elapsed_ms: u64,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
}

fn run_command_with_timeout(
    command: &mut Command,
    timeout: Duration,
    context: &str,
) -> Result<ChcVerifyRun> {
    let start = Instant::now();
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("failed to spawn {context}"))?;
    loop {
        if child
            .try_wait()
            .with_context(|| format!("failed waiting for {context}"))?
            .is_some()
        {
            let output = child
                .wait_with_output()
                .with_context(|| format!("failed to collect {context} output"))?;
            return Ok(ChcVerifyRun {
                exit_code: output.status.code(),
                timed_out: false,
                elapsed_ms: duration_millis(start.elapsed()),
                stdout: output.stdout,
                stderr: output.stderr,
            });
        }
        if start.elapsed() >= timeout {
            kill_chc_verify_child(&mut child);
            let output = child
                .wait_with_output()
                .with_context(|| format!("failed to collect timed-out {context} output"))?;
            return Ok(ChcVerifyRun {
                exit_code: output.status.code(),
                timed_out: true,
                elapsed_ms: duration_millis(start.elapsed()),
                stdout: output.stdout,
                stderr: output.stderr,
            });
        }
        thread::sleep(Duration::from_millis(10));
    }
}

fn kill_chc_verify_child(child: &mut std::process::Child) {
    #[cfg(unix)]
    {
        kill_descendant_processes(child.id());
    }
    let _ = child.kill();
}

#[cfg(unix)]
fn kill_descendant_processes(pid: u32) {
    let children = child_process_ids(pid);
    for child_pid in &children {
        kill_descendant_processes(*child_pid);
    }
    for child_pid in children {
        let _ = nix::sys::signal::kill(
            nix::unistd::Pid::from_raw(child_pid as i32),
            nix::sys::signal::Signal::SIGKILL,
        );
    }
}

#[cfg(unix)]
fn child_process_ids(pid: u32) -> Vec<u32> {
    let Ok(output) = Command::new("pgrep")
        .arg("-P")
        .arg(pid.to_string())
        .output()
    else {
        return Vec::new();
    };
    if !output.status.success() {
        return Vec::new();
    }
    String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(|line| line.trim().parse::<u32>().ok())
        .collect()
}

fn duration_millis(duration: Duration) -> u64 {
    duration.as_millis().min(u64::MAX as u128) as u64
}

fn first_chc_status(stdout: &str) -> Option<&'static str> {
    stdout.lines().find_map(|line| match line.trim() {
        "sat" => Some("sat"),
        "unsat" => Some("unsat"),
        "unknown" => Some("unknown"),
        _ => None,
    })
}

fn chc_yaml_field(text: &str, key: &str) -> Option<String> {
    let prefix = format!("{key}:");
    let lines: Vec<_> = text.lines().collect();
    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim();
        if let Some(value) = trimmed.strip_prefix(&prefix) {
            let value = clean_yaml_scalar(value);
            if !value.is_empty() {
                return Some(value);
            }
            for next in lines.iter().skip(idx + 1) {
                let next = next.trim();
                if let Some(item) = next.strip_prefix("- ") {
                    return Some(clean_yaml_scalar(item));
                }
                if !next.is_empty() && !next.starts_with('#') {
                    break;
                }
            }
        }
    }
    None
}

fn clean_yaml_scalar(value: &str) -> String {
    value
        .trim()
        .trim_matches('"')
        .trim_matches('\'')
        .to_string()
}

fn chc_expected_status_from_yml(text: &str) -> Option<String> {
    if let Some(status) = chc_yaml_field(text, "majority_vote_verdict") {
        if matches!(status.as_str(), "sat" | "unsat" | "unknown") {
            return Some(status);
        }
    }
    if text.contains("placeholder verdict (auto-added)") {
        return None;
    }
    match chc_yaml_field(text, "expected_verdict")?.as_str() {
        "true" => Some("sat".to_string()),
        "false" => Some("unsat".to_string()),
        _ => None,
    }
}

fn count_checks(checks: &[serde_json::Value], status: &str) -> usize {
    checks
        .iter()
        .filter(|check| check["status"].as_str() == Some(status))
        .count()
}

fn push_check(
    checks: &mut Vec<serde_json::Value>,
    name: impl Into<String>,
    status: &'static str,
    detail: impl Into<String>,
) {
    checks.push(json!({
        "name": name.into(),
        "status": status,
        "detail": detail.into(),
    }));
}

fn create_chc_late_entry_stub_package(package_parent: &Path) -> Result<()> {
    let ay_root = package_parent.join("ay");
    fs::create_dir_all(&ay_root)
        .with_context(|| format!("failed to create '{}'", ay_root.display()))?;
    write_text(&ay_root.join("ay"), chc_late_entry_fake_ay_text(), true)?;
    write_chc_run_solver(&ay_root)?;
    write_text(
        &ay_root.join("LICENSE"),
        "Apache License 2.0 placeholder for local-only preflight stub.\n",
        false,
    )?;
    write_text(
        &ay_root.join("README.md"),
        "# ay CHC-COMP 2026 local preflight stub\n\nThis is not a submission artifact. It exists only to validate wrapper and archive checks when a Linux x86_64 ay archive is unavailable.\n",
        false,
    )
}

// The embedded bash script's `${1:-}`/`${2:-}` parameter expansions are not
// Rust formatting arguments.
#[allow(clippy::literal_string_with_formatting_args)]
fn chc_late_entry_fake_ay_text() -> &'static str {
    r#"#!/usr/bin/env bash
set -u

if [ "${1:-}" = "--version" ]; then
  printf '%s\n' "ay-chccomp-local-stub 0"
  exit 0
fi

if [ "${1:-}" != "--chc" ]; then
  printf '%s\n' "unexpected invocation" >&2
  exit 2
fi

benchmark="${2:-}"
case "$(basename -- "$benchmark")" in
  sat-extra.smt2)
    printf '%s\n' "solver banner" "sat" "(model after status)"
    ;;
  unsat-extra.smt2)
    printf '%s\n' "unsat" "certificate after status"
    ;;
  no-status.smt2)
    printf '%s\n' "solver banner without a bare status"
    ;;
  crash.smt2)
    printf '%s\n' "simulated solver crash" >&2
    exit 42
    ;;
  first-status-wins.smt2)
    printf '%s\n' "unsat" "sat"
    ;;
  *)
    printf '%s\n' "unknown"
    ;;
esac
"#
}

fn validate_chc_late_entry_archive_layout(
    archive: &Path,
    checks: &mut Vec<serde_json::Value>,
) -> Result<Vec<String>> {
    let names = match archive_member_names(archive) {
        Ok(names) => names,
        Err(err) => {
            push_check(checks, "archive_readable", "fail", err.to_string());
            return Ok(Vec::new());
        }
    };
    let verbose = archive_verbose_listing(archive).unwrap_or_default();
    let mut entries = HashSet::new();
    let mut safe_failed = false;
    let mut regular_failed = false;
    let mut root_failed = false;

    for raw in &names {
        let name = normalize_archive_member_name(raw);
        if !is_safe_archive_member(&name) {
            safe_failed = true;
            push_check(
                checks,
                "archive_safe_paths",
                "fail",
                format!("unsafe member: {raw:?}"),
            );
            continue;
        }
        if !entries.insert(name.clone()) {
            push_check(
                checks,
                "archive_unique_members",
                "fail",
                format!("duplicate member: {name}"),
            );
        }
        if name != "ay" && !name.starts_with("ay/") {
            root_failed = true;
            push_check(
                checks,
                "archive_root",
                "fail",
                format!("member outside ay/ root: {name}"),
            );
        }
    }
    for entry in &verbose {
        if !matches!(entry.kind, '-' | 'd') {
            regular_failed = true;
            push_check(
                checks,
                "archive_regular_entries",
                "fail",
                format!("non-file/non-dir member: {}", entry.name),
            );
        }
    }
    if !safe_failed {
        push_check(
            checks,
            "archive_safe_paths",
            "pass",
            "all member paths are relative and normalized",
        );
    }
    if !regular_failed {
        push_check(
            checks,
            "archive_regular_entries",
            "pass",
            "all members are regular files or directories",
        );
    }
    if !root_failed {
        push_check(checks, "archive_root", "pass", "all members are under ay/");
    }

    for &(required, mode) in CHC_LATE_REQUIRED_ARCHIVE_MEMBERS {
        let Some(entry) = verbose.iter().find(|entry| entry.name == required) else {
            push_check(
                checks,
                format!("archive_member:{required}"),
                "fail",
                "missing required member",
            );
            continue;
        };
        if entry.kind != '-' {
            push_check(
                checks,
                format!("archive_member:{required}"),
                "fail",
                "required member is not a file",
            );
            continue;
        }
        if mode & 0o111 != 0 && !entry.mode_text.contains('x') {
            push_check(
                checks,
                format!("archive_member:{required}"),
                "fail",
                format!("required executable bit missing: mode={}", entry.mode_text),
            );
        } else {
            push_check(
                checks,
                format!("archive_member:{required}"),
                "pass",
                format!("present with mode {}", entry.mode_text),
            );
        }
    }

    let mut members: Vec<_> = entries.into_iter().collect();
    members.sort();
    let extras: Vec<_> = members
        .iter()
        .filter(|name| {
            !matches!(
                name.as_str(),
                "ay" | "ay/ay" | "ay/run_solver.sh" | "ay/LICENSE" | "ay/README.md"
            )
        })
        .cloned()
        .collect();
    if extras.is_empty() {
        push_check(
            checks,
            "archive_extra_members",
            "pass",
            "no extra archive members",
        );
    } else {
        push_check(
            checks,
            "archive_extra_members",
            "warn",
            format!(
                "extra members are not submission blockers if CHC-COMP accepts them: {}",
                extras.join(", ")
            ),
        );
    }
    Ok(members)
}

struct ArchiveListingEntry {
    name: String,
    mode_text: String,
    kind: char,
}

fn archive_member_names(archive: &Path) -> Result<Vec<String>> {
    let output = Command::new("tar")
        .arg("-tzf")
        .arg(archive)
        .output()
        .with_context(|| format!("failed to list archive '{}'", archive.display()))?;
    if !output.status.success() {
        bail!(
            "tar -tzf failed for '{}': stdout={} stderr={}",
            archive.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .map(ToOwned::to_owned)
        .collect())
}

fn archive_verbose_listing(archive: &Path) -> Result<Vec<ArchiveListingEntry>> {
    let output = Command::new("tar")
        .arg("-tvzf")
        .arg(archive)
        .output()
        .with_context(|| format!("failed to inspect archive '{}'", archive.display()))?;
    if !output.status.success() {
        bail!(
            "tar -tvzf failed for '{}': stdout={} stderr={}",
            archive.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter_map(parse_archive_listing_entry)
        .collect())
}

fn parse_archive_listing_entry(line: &str) -> Option<ArchiveListingEntry> {
    let mut fields = line.split_whitespace();
    let mode_text = fields.next()?.to_string();
    let raw_name = fields.last()?;
    Some(ArchiveListingEntry {
        name: normalize_archive_member_name(raw_name),
        kind: mode_text.chars().next().unwrap_or('?'),
        mode_text,
    })
}

fn is_safe_archive_member(name: &str) -> bool {
    if name.is_empty() || name == "." || name.starts_with('/') || name.contains("//") {
        return false;
    }
    Path::new(name).components().all(|component| {
        matches!(
            component,
            std::path::Component::Normal(_) | std::path::Component::CurDir
        )
    })
}

fn validate_chc_late_entry_strip_layout(
    archive: &Path,
    work_dir: &Path,
    checks: &mut Vec<serde_json::Value>,
) -> Result<()> {
    let destination = work_dir.join("strip-components-1").join("tools").join("ay");
    if destination.exists() {
        fs::remove_dir_all(&destination)
            .with_context(|| format!("failed to remove '{}'", destination.display()))?;
    }
    fs::create_dir_all(&destination)
        .with_context(|| format!("failed to create '{}'", destination.display()))?;
    let output = Command::new("tar")
        .arg("-xzf")
        .arg(archive)
        .arg("-C")
        .arg(&destination)
        .arg("--strip-components=1")
        .output()
        .with_context(|| format!("failed to extract archive '{}'", archive.display()))?;
    if !output.status.success() {
        push_check(
            checks,
            "strip_components_layout",
            "fail",
            format!(
                "tar extraction failed: stdout={} stderr={}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ),
        );
        return Ok(());
    }
    if let Err(err) = reject_symlinks_recursive(&destination) {
        push_check(checks, "strip_components_layout", "fail", err.to_string());
        return Ok(());
    }
    for rel in ["ay", "run_solver.sh", "LICENSE", "README.md"] {
        if destination.join(rel).is_file() {
            push_check(
                checks,
                format!("strip_member:{rel}"),
                "pass",
                format!("extracted {rel}"),
            );
        } else {
            push_check(
                checks,
                format!("strip_member:{rel}"),
                "fail",
                format!("missing after strip: {rel}"),
            );
        }
    }
    Ok(())
}

fn preflight_file_output(path: &Path) -> String {
    match Command::new("file").arg(path).output() {
        Ok(output) => {
            let text = format!(
                "{}{}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
            let trimmed = text.trim();
            if trimmed.is_empty() {
                format!("file exited {:?} without output", output.status.code())
            } else {
                trimmed.to_string()
            }
        }
        Err(err) => format!("file unavailable: {err}"),
    }
}

fn preflight_binary_platform(path: &Path) -> String {
    let bytes = fs::read(path).unwrap_or_default();
    if bytes.starts_with(b"#!") {
        return "script-stub".to_string();
    }
    match binary_platform(path) {
        Ok(platform) if platform.starts_with("linux-elf-x86_64") => "linux-elf-x86_64".to_string(),
        Ok(platform) if platform == "mach-o" => "macos-mach-o".to_string(),
        Ok(platform) => platform,
        Err(_) => "unknown".to_string(),
    }
}

fn prepare_chc_late_entry_wrapper_harness(
    source_root: &Path,
    harness_root: &Path,
) -> Result<PathBuf> {
    if harness_root.exists() {
        fs::remove_dir_all(harness_root)
            .with_context(|| format!("failed to remove '{}'", harness_root.display()))?;
    }
    fs::create_dir_all(harness_root)
        .with_context(|| format!("failed to create '{}'", harness_root.display()))?;
    fs::copy(
        source_root.join("run_solver.sh"),
        harness_root.join("run_solver.sh"),
    )
    .with_context(|| format!("failed to copy wrapper into '{}'", harness_root.display()))?;
    set_executable(&harness_root.join("run_solver.sh"))?;
    write_text(
        &harness_root.join("ay"),
        chc_late_entry_fake_ay_text(),
        true,
    )?;
    Ok(harness_root.to_path_buf())
}

fn run_chc_late_entry_wrapper_cases(
    wrapper_root: &Path,
    work_dir: &Path,
    checks: &mut Vec<serde_json::Value>,
) -> Result<Vec<serde_json::Value>> {
    let parse = Command::new("bash")
        .arg("-n")
        .arg(wrapper_root.join("run_solver.sh"))
        .output()
        .context("failed to parse CHC wrapper with bash")?;
    if parse.status.success() {
        push_check(
            checks,
            "wrapper_bash_parse",
            "pass",
            "bash -n accepted run_solver.sh",
        );
    } else {
        push_check(
            checks,
            "wrapper_bash_parse",
            "fail",
            format!(
                "exit={:?} stdout={:?} stderr={:?}",
                parse.status.code(),
                String::from_utf8_lossy(&parse.stdout),
                String::from_utf8_lossy(&parse.stderr)
            ),
        );
        return Ok(Vec::new());
    }

    let bench_dir = work_dir.join("wrapper-benchmarks");
    fs::create_dir_all(&bench_dir)
        .with_context(|| format!("failed to create '{}'", bench_dir.display()))?;
    for filename in [
        "sat-extra.smt2",
        "unsat-extra.smt2",
        "no-status.smt2",
        "crash.smt2",
        "first-status-wins.smt2",
    ] {
        fs::write(bench_dir.join(filename), "(set-logic HORN)\n(check-sat)\n")
            .with_context(|| format!("failed to write wrapper benchmark {filename}"))?;
    }

    let raw_cases: Vec<(&str, &str, Vec<PathBuf>)> = vec![
        (
            "missing-argument",
            "unknown",
            vec![wrapper_root.join("run_solver.sh")],
        ),
        (
            "sat-extra-lines",
            "sat",
            vec![
                wrapper_root.join("run_solver.sh"),
                bench_dir.join("sat-extra.smt2"),
            ],
        ),
        (
            "unsat-extra-lines",
            "unsat",
            vec![
                wrapper_root.join("run_solver.sh"),
                bench_dir.join("unsat-extra.smt2"),
            ],
        ),
        (
            "no-status-fallback",
            "unknown",
            vec![
                wrapper_root.join("run_solver.sh"),
                bench_dir.join("no-status.smt2"),
            ],
        ),
        (
            "crash-fallback",
            "unknown",
            vec![
                wrapper_root.join("run_solver.sh"),
                bench_dir.join("crash.smt2"),
            ],
        ),
        (
            "missing-file-fallback",
            "unknown",
            vec![
                wrapper_root.join("run_solver.sh"),
                work_dir.join("missing.smt2"),
            ],
        ),
        (
            "first-status-wins",
            "unsat",
            vec![
                wrapper_root.join("run_solver.sh"),
                bench_dir.join("first-status-wins.smt2"),
            ],
        ),
    ];

    let mut results = Vec::new();
    for (name, expected, command_paths) in raw_cases {
        let mut command = Command::new(&command_paths[0]);
        for arg in &command_paths[1..] {
            command.arg(arg);
        }
        let output = command
            .output()
            .with_context(|| format!("failed to run wrapper case {name}"))?;
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        let passed = output.status.success()
            && stdout == format!("{expected}\n")
            && stderr.is_empty()
            && CHC_LATE_VALID_STATUSES.contains(&expected);
        if passed {
            push_check(
                checks,
                format!("wrapper_case:{name}"),
                "pass",
                format!("stdout={expected:?}"),
            );
        } else {
            push_check(
                checks,
                format!("wrapper_case:{name}"),
                "fail",
                format!(
                    "exit={:?} stdout={stdout:?} stderr={stderr:?}",
                    output.status.code()
                ),
            );
        }
        results.push(json!({
            "name": name,
            "expected": expected,
            "exit_code": output.status.code().unwrap_or(-1),
            "stdout": stdout,
            "stderr": stderr,
            "command": command_paths.iter().map(|path| path.display().to_string()).collect::<Vec<_>>(),
            "passed": passed,
        }));
    }
    Ok(results)
}

fn write_json_report(path: &Path, payload: &serde_json::Value) -> Result<()> {
    let text =
        serde_json::to_string_pretty(payload).context("failed to serialize preflight JSON")?;
    write_text(path, &format!("{text}\n"), false)
}

fn write_chc_comp_verify_markdown(
    path: &Path,
    payload: &serde_json::Value,
    root: &Path,
) -> Result<()> {
    let checks = payload["checks"].as_array().cloned().unwrap_or_default();
    let smokes = payload["benchmarks"]["smokes"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let blockers = payload["blockers"].as_array().cloned().unwrap_or_default();
    let summary = &payload["summary"];
    let package = &payload["package"];
    let benchmarks = &payload["benchmarks"];

    let mut lines = vec![
        "# CHC-COMP 2026 Verify".to_string(),
        String::new(),
        "This report is local-only evidence. It did not publish, upload, open a PR, or email organizers.".to_string(),
        String::new(),
        "## Summary".to_string(),
        format!(
            "- Actual prove-ready: {}",
            summary["actual_prove_ready"].as_bool().unwrap_or(false)
        ),
        format!("- Failed checks: {}", summary["fail_count"].as_u64().unwrap_or(0)),
        format!("- Warnings: {}", summary["warn_count"].as_u64().unwrap_or(0)),
        format!("- Skipped checks: {}", summary["skip_count"].as_u64().unwrap_or(0)),
        String::new(),
        "## Package".to_string(),
        format!(
            "- Package: {}",
            package["path"].as_str().unwrap_or("unknown")
        ),
        format!(
            "- Archive SHA256: {}",
            package["archive"]["sha256"].as_str().unwrap_or("unavailable")
        ),
        format!(
            "- Packaged binary platform: {}",
            package["packaged_binary_platform"]
                .as_str()
                .unwrap_or("unknown")
        ),
        format!(
            "- Archived binary platform: {}",
            package["archived_binary_platform"]
                .as_str()
                .unwrap_or("unknown")
        ),
        String::new(),
        "## Benchmarks".to_string(),
        format!(
            "- Root: {}",
            benchmarks["root"].as_str().unwrap_or("not supplied")
        ),
        format!(
            "- Samples per local set-file category: {}",
            benchmarks["samples_per_track"].as_u64().unwrap_or(0)
        ),
        format!(
            "- Timeout ms: {}",
            benchmarks["benchmark_timeout_ms"].as_u64().unwrap_or(0)
        ),
        String::new(),
        "## Checks".to_string(),
        "| Check | Status | Detail |".to_string(),
        "| --- | --- | --- |".to_string(),
    ];
    let package_section = lines
        .iter()
        .position(|line| line == "## Package")
        .expect("CHC verify report should have a Package section");
    let mut track_model = Vec::new();
    push_chc_track_model_markdown(&mut track_model);
    drop(lines.splice(package_section..package_section, track_model));
    for check in checks {
        lines.push(format!(
            "| `{}` | `{}` | {} |",
            markdown_cell(check["name"].as_str().unwrap_or("unnamed")),
            markdown_cell(check["status"].as_str().unwrap_or("unknown")),
            markdown_cell(check["detail"].as_str().unwrap_or(""))
        ));
    }

    lines.extend([
        String::new(),
        "## Benchmark Smokes".to_string(),
        "| Local category | Input | Expected | Actual | Exit | Timeout | Elapsed ms | Result |"
            .to_string(),
        "| --- | --- | --- | --- | ---: | --- | ---: | --- |".to_string(),
    ]);
    for smoke in smokes {
        lines.push(format!(
            "| `{}` | `{}` | `{}` | `{}` | {} | {} | {} | `{}` |",
            markdown_cell(smoke["track"].as_str().unwrap_or("unknown")),
            markdown_cell(smoke["input"].as_str().unwrap_or("unknown")),
            markdown_cell(smoke["expected_status"].as_str().unwrap_or("unknown")),
            markdown_cell(smoke["actual_status"].as_str().unwrap_or("unknown")),
            smoke["exit_code"]
                .as_i64()
                .map(|code| code.to_string())
                .unwrap_or_else(|| "null".to_string()),
            smoke["timed_out"].as_bool().unwrap_or(false),
            smoke["elapsed_ms"].as_u64().unwrap_or(0),
            if smoke["passed"].as_bool() == Some(true) {
                "pass"
            } else {
                "fail"
            }
        ));
    }

    lines.extend([String::new(), "## Blockers".to_string()]);
    if blockers.is_empty() {
        lines.push("- None.".to_string());
    } else {
        for blocker in blockers {
            lines.push(format!(
                "- {}",
                blocker.as_str().unwrap_or("unknown blocker")
            ));
        }
    }
    lines.extend([
        String::new(),
        "## Replay".to_string(),
        format!(
            "- Command: `ay submission preflight chc-comp-verify --package {} --benchmarks-root <chc-comp26-benchmarks>`",
            display_path_for_report(
                Path::new(package["path"].as_str().unwrap_or("target/submission-packages/chc-comp-2026")),
                root,
            )
        ),
        String::new(),
    ]);
    write_text(path, &lines.join("\n"), false)
}

fn write_pb_comp_verify_markdown(
    path: &Path,
    payload: &serde_json::Value,
    root: &Path,
) -> Result<()> {
    let checks = payload["checks"].as_array().cloned().unwrap_or_default();
    let blockers = payload["blockers"].as_array().cloned().unwrap_or_default();
    let summary = &payload["summary"];
    let package = &payload["package"];
    let checker = &payload["checker"];
    let command = checker["command"]
        .as_array()
        .map(|parts| {
            parts
                .iter()
                .filter_map(|part| part.as_str())
                .collect::<Vec<_>>()
                .join(" ")
        })
        .unwrap_or_else(|| "unavailable".to_string());

    let mut lines = vec![
        "# PB-COMP 2026 Verify".to_string(),
        String::new(),
        "This report is local-only evidence. It did not publish, upload, or contact organizers."
            .to_string(),
        String::new(),
        "## Summary".to_string(),
        format!(
            "- Actual submission-ready: {}",
            summary["actual_submission_ready"]
                .as_bool()
                .unwrap_or(false)
        ),
        format!(
            "- Archive validated: {}",
            summary["archive_validated"].as_bool().unwrap_or(false)
        ),
        format!(
            "- Failed checks: {}",
            summary["fail_count"].as_u64().unwrap_or(0)
        ),
        format!(
            "- Warnings: {}",
            summary["warn_count"].as_u64().unwrap_or(0)
        ),
        format!(
            "- Skipped checks: {}",
            summary["skip_count"].as_u64().unwrap_or(0)
        ),
        String::new(),
        "## Package".to_string(),
        format!(
            "- Package: {}",
            package["path"].as_str().unwrap_or("unknown")
        ),
        format!(
            "- Archive: {}",
            package["archive"]["path"]
                .as_str()
                .unwrap_or("not validated")
        ),
        String::new(),
        "## Checker".to_string(),
        format!("- Command: `{}`", markdown_cell(&command)),
        format!(
            "- Exit code: {}",
            checker["exit_code"]
                .as_i64()
                .map(|code| code.to_string())
                .unwrap_or_else(|| "null".to_string())
        ),
        format!(
            "- Timed out: {}",
            checker["timed_out"].as_bool().unwrap_or(false)
        ),
        format!(
            "- Elapsed ms: {}",
            checker["elapsed_ms"].as_u64().unwrap_or(0)
        ),
        String::new(),
        "## Checks".to_string(),
        "| Check | Status | Detail |".to_string(),
        "| --- | --- | --- |".to_string(),
    ];
    for check in checks {
        lines.push(format!(
            "| `{}` | `{}` | {} |",
            markdown_cell(check["name"].as_str().unwrap_or("unnamed")),
            markdown_cell(check["status"].as_str().unwrap_or("unknown")),
            markdown_cell(check["detail"].as_str().unwrap_or(""))
        ));
    }

    lines.extend([String::new(), "## Blockers".to_string()]);
    if blockers.is_empty() {
        lines.push("- None.".to_string());
    } else {
        for blocker in blockers {
            lines.push(format!(
                "- {}",
                blocker.as_str().unwrap_or("unknown blocker")
            ));
        }
    }
    lines.extend([
        String::new(),
        "## Replay".to_string(),
        format!(
            "- Command: `ay submission preflight pb-comp-verify --package {}`",
            display_path_for_report(
                Path::new(
                    package["path"]
                        .as_str()
                        .unwrap_or("competition/pb26/dist/ay-pb26")
                ),
                root,
            )
        ),
        String::new(),
    ]);
    write_text(path, &lines.join("\n"), false)
}

fn write_chc_late_entry_markdown(
    path: &Path,
    payload: &serde_json::Value,
    root: &Path,
) -> Result<()> {
    let checks = payload["checks"].as_array().cloned().unwrap_or_default();
    let wrapper_cases = payload["wrapper_cases"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    let blockers = payload["blockers"].as_array().cloned().unwrap_or_default();
    let mut lines = vec![
        "# CHC-COMP 2026 Late-Entry Local Preflight".to_string(),
        String::new(),
        "This report is local-only evidence. It did not publish, upload, open a PR, or email organizers.".to_string(),
        String::new(),
        "## Scope".to_string(),
        String::new(),
        format!("- Official source checked: {CHC_OFFICIAL_SOURCE_URL}"),
        format!(
            "- Normal solver/benchmark deadline: {CHC_NORMAL_SOLVER_BENCHMARK_DEADLINE}"
        ),
        format!(
            "- Technical solver resubmission deadline: {CHC_TECHNICAL_SOLVER_RESUBMISSION_DEADLINE}"
        ),
        format!("- Validation mode: {}", json_str(payload, "validation_mode")),
        format!(
            "- Actual submission ready: {}",
            payload["actual_submission_ready"].as_bool().unwrap_or(false)
        ),
        format!(
            "- Real Linux x86_64 artifact available: {}",
            payload["real_linux_artifact_available"].as_bool().unwrap_or(false)
        ),
    ];
    push_chc_track_model_markdown(&mut lines);
    lines.extend([
        String::new(),
        "## Inputs".to_string(),
        String::new(),
        format!(
            "- Archive: {}",
            payload["archive"]["path"].as_str().unwrap_or("")
        ),
        format!(
            "- Archive SHA256: {}",
            payload["archive"]["sha256"].as_str().unwrap_or("")
        ),
        format!(
            "- Binary platform: {}",
            payload["binary"]["platform"].as_str().unwrap_or("")
        ),
        format!(
            "- Binary file output: `{}`",
            payload["binary"]["file_output"].as_str().unwrap_or("")
        ),
        String::new(),
        "## Checks".to_string(),
        String::new(),
        "| Check | Status | Detail |".to_string(),
        "| --- | --- | --- |".to_string(),
    ]);
    for check in checks {
        lines.push(format!(
            "| `{}` | {} | {} |",
            check["name"].as_str().unwrap_or(""),
            check["status"].as_str().unwrap_or(""),
            markdown_cell(check["detail"].as_str().unwrap_or(""))
        ));
    }
    lines.extend([
        String::new(),
        "## Wrapper Matrix".to_string(),
        String::new(),
        "| Case | Expected | Exit | Stdout | Stderr |".to_string(),
        "| --- | --- | ---: | --- | --- |".to_string(),
    ]);
    for case in wrapper_cases {
        lines.push(format!(
            "| `{}` | `{}` | {} | `{}` | `{}` |",
            case["name"].as_str().unwrap_or(""),
            case["expected"].as_str().unwrap_or(""),
            case["exit_code"].as_i64().unwrap_or(-1),
            markdown_cell(&format!("{:?}", case["stdout"].as_str().unwrap_or(""))),
            markdown_cell(&format!("{:?}", case["stderr"].as_str().unwrap_or("")))
        ));
    }
    lines.extend([String::new(), "## Blockers".to_string(), String::new()]);
    if blockers.is_empty() {
        lines.push("- None for local-only preflight.".to_string());
    } else {
        for blocker in blockers {
            lines.push(format!("- {}", blocker.as_str().unwrap_or("")));
        }
    }
    lines.extend([
        String::new(),
        "## Submission Boundary".to_string(),
        String::new(),
        "- No publish/upload/PR/email action was performed.".to_string(),
        "- A stub archive is never submission evidence for the real solver binary.".to_string(),
        "- A real package still needs a clean Linux x86_64 ay archive and CHC-COMP repository discovery validation before external approval.".to_string(),
        String::new(),
        "## Reproduce".to_string(),
        String::new(),
        "```sh".to_string(),
        "ay submission preflight chc-late-entry".to_string(),
        format!(
            "# compatibility wrapper: python3 {}",
            display_path_for_report(&workspace_root().join("scripts/chccomp_late_entry_preflight.py"), root)
        ),
        "```".to_string(),
        String::new(),
    ]);
    write_text(path, &lines.join("\n"), false)
}

fn read_json_value(path: &Path) -> Result<JsonValue> {
    let text =
        fs::read_to_string(path).with_context(|| format!("failed to read '{}'", path.display()))?;
    serde_json::from_str(&text).with_context(|| format!("failed to parse '{}'", path.display()))
}

fn expect_json_str(value: &JsonValue, field: &str, expected: &str, path: &Path) -> Result<()> {
    let actual = value[field]
        .as_str()
        .with_context(|| format!("{} field {field} is missing", path.display()))?;
    if actual != expected {
        bail!(
            "{} field {field} expected {expected}, got {actual}",
            path.display()
        );
    }
    Ok(())
}

fn write_json_pretty(path: &Path, value: &JsonValue) -> Result<()> {
    let text = serde_json::to_string_pretty(value)
        .with_context(|| format!("failed to serialize '{}'", path.display()))?;
    write_text(path, &format!("{text}\n"), false)
}

fn prefixed_sha256_file(path: &Path) -> Result<String> {
    Ok(format!("sha256:{}", sha256_file(path)?))
}

fn json_str<'a>(payload: &'a serde_json::Value, key: &str) -> &'a str {
    payload[key].as_str().unwrap_or("")
}

fn markdown_cell(text: &str) -> String {
    text.replace('|', "\\|")
}

fn chc_track_model_json() -> JsonValue {
    let local_to_official_category_map = CHC_TRACK_MODEL_ROWS
        .iter()
        .map(|row| {
            json!({
                "local_category": row.0,
                "official_track": row.1,
                "role": row.2,
                "note": row.3,
            })
        })
        .collect::<Vec<_>>();

    json!({
        "official_source_url": CHC_OFFICIAL_SOURCE_URL,
        "official_chc_comp_2026_tracks": CHC_OFFICIAL_2026_TRACKS,
        "official_track_count": CHC_OFFICIAL_2026_TRACKS.len(),
        "local_set_file_categories": CHC_ALLOWED_TRACKS,
        "local_set_file_category_count": CHC_ALLOWED_TRACKS.len(),
        "local_to_official_category_map": local_to_official_category_map,
        "claim_policy": CHC_TRACK_MODEL_CLAIM_POLICY,
        "legacy_tracks_field_note": CHC_TRACK_MODEL_LEGACY_FIELD_NOTE,
    })
}

fn push_chc_track_model_markdown(lines: &mut Vec<String>) {
    lines.extend([
        "## Track Model".to_string(),
        String::new(),
        format!(
            "Official CHC-COMP 2026 planned tracks: {} ({}).",
            CHC_OFFICIAL_2026_TRACKS.len(),
            CHC_OFFICIAL_2026_TRACKS.join(", ")
        ),
        format!(
            "Local chc-comp26 set-file categories used by this CLI: {} ({}).",
            CHC_ALLOWED_TRACKS.len(),
            CHC_ALLOWED_TRACKS.join(", ")
        ),
        String::new(),
        CHC_TRACK_MODEL_CLAIM_POLICY.to_string(),
        CHC_TRACK_MODEL_LEGACY_FIELD_NOTE.to_string(),
        String::new(),
        "| Local category | Official 2026 track | Role | Note |".to_string(),
        "| --- | --- | --- | --- |".to_string(),
    ]);
    for &(local, official, role, note) in CHC_TRACK_MODEL_ROWS {
        lines.push(format!(
            "| `{}` | `{}` | `{}` | {} |",
            markdown_cell(local),
            markdown_cell(official.unwrap_or("none")),
            markdown_cell(role),
            markdown_cell(note)
        ));
    }
    lines.push(String::new());
}

fn chc_track_model_markdown() -> String {
    let mut lines = Vec::new();
    push_chc_track_model_markdown(&mut lines);
    lines.join("\n")
}

fn print_chc_track_model_summary() {
    println!(
        "track-model official_chc_comp_2026_tracks={} local_set_file_categories={} local_category_smokes_are_not_full_suite=true",
        CHC_OFFICIAL_2026_TRACKS.len(),
        CHC_ALLOWED_TRACKS.len()
    );
    println!(
        "track-aliases BV=BV-Nonlin LIA=LIA-Nonlin LIA-Arrays=LIA-Nonlin-Arrays BOOL=internal-smoke-category mixed_LIA_LRA=internal-smoke-category"
    );
}

fn display_path_for_report(path: &Path, root: &Path) -> String {
    let absolute = fs::canonicalize(path).unwrap_or_else(|_| path.to_path_buf());
    let root = fs::canonicalize(root).unwrap_or_else(|_| root.to_path_buf());
    absolute
        .strip_prefix(&root)
        .map(|path| path.display().to_string())
        .unwrap_or_else(|_| absolute.display().to_string())
}

fn repo_relative_path(root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        root.join(path)
    }
}

fn absolute_path_for_report(path: &Path) -> String {
    fs::canonicalize(path)
        .unwrap_or_else(|_| path.to_path_buf())
        .display()
        .to_string()
}

fn generate_sat(output: &Path) -> Result<()> {
    let build_sh = r#"#!/usr/bin/env bash
set -euo pipefail

if [[ -x ./ay ]]; then
  chmod +x ./ay
  exit 0
fi

if [[ ! -f Cargo.toml ]]; then
  echo "SAT-COMP package must contain either ./ay or the ay source tree" >&2
  exit 1
fi

cargo build --locked --release -p ay
cp target/release/ay ./ay
chmod +x ./ay
"#;

    let run_sh = r#"#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 BENCHMARK PROOF_DIR" >&2
  exit 2
fi

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCHMARK="$1"
PROOF_DIR="$2"
PROOF_FILE="$PROOF_DIR/proof.out"

mkdir -p "$PROOF_DIR"

is_uint() {
  [[ "$1" =~ ^[0-9]+$ ]]
}

timeout_with_margin_ms() {
  local ms="$1"
  local reserve=$((ms / 10))
  if [ "$reserve" -lt 5000 ]; then
    reserve=5000
  fi
  if [ "$reserve" -gt 30000 ]; then
    reserve=30000
  fi
  if [ "$ms" -gt "$reserve" ]; then
    printf '%s\n' "$((ms - reserve))"
  else
    printf '%s\n' "$ms"
  fi
}

TIMEOUT_MS="${AY_SAT_TIMEOUT_MS:-${AY_TIMEOUT_MS:-}}"
if ! is_uint "${TIMEOUT_MS:-}"; then
  TIMEOUT_MS=""
fi
if [ -z "$TIMEOUT_MS" ]; then
  RAW_TIMEOUT="${TIMELIMIT:-${TIMEOUT:-${STAREXEC_WALLCLOCK_LIMIT:-}}}"
  if is_uint "${RAW_TIMEOUT:-}"; then
    TIMEOUT_MS="$(timeout_with_margin_ms "$((RAW_TIMEOUT * 1000))")"
  fi
fi

SOLVER_ARGS=(--sat-variant default --proof-format drat --proof "$PROOF_FILE")
if is_uint "${TIMEOUT_MS:-}" && [ "$TIMEOUT_MS" -gt 0 ]; then
  SOLVER_ARGS+=(--timeout "$TIMEOUT_MS")
fi
SOLVER_ARGS+=("$BENCHMARK")

FMLA_AUTHORITY_REPLAY="${AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY:-}"
FMLA_CURRENT_PROOF_OUT="${AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT:-}"
if [[ "${AY_SATCOMP_MATRIX:-}" == "1" \
  && -n "$FMLA_AUTHORITY_REPLAY" \
  && -f "$FMLA_AUTHORITY_REPLAY" \
  && "$FMLA_CURRENT_PROOF_OUT" == "$PROOF_FILE" ]]; then
  exec env -u AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE \
    "$DIR/ay" "${SOLVER_ARGS[@]}"
fi

exec env -u AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE \
  -u AY_SAT_FMLA_LEARNED_LRAT_MAIN_PROOF_AUTHORITY_REPLAY \
  -u AY_SAT_FMLA_LEARNED_LRAT_CURRENT_PROOF_OUT \
  "$DIR/ay" "${SOLVER_ARGS[@]}"
"#;

    let readme = format!(
        r#"# ay SAT-COMP 2026 Skeleton

Generated by ay {} from commit {}.

This directory is a private-repository skeleton for the SAT-COMP 2026 sequential solver submission.

Required files:
- `build.sh`: zero-argument build hook.
- `run.sh`: two-argument run hook: `run.sh BENCHMARK PROOF_DIR`.
- UNSAT proof output: `PROOF_DIR/proof.out`.

Before submission:
- Copy or build a Linux `ay` executable into this directory, or include the source tree so `build.sh` can build it.
- Confirm the SAT-COMP system-description form declares the proof checker as `drat-trim` for DRAT.
- Confirm stdout has exactly one final `s ...` result line and SAT models use `v ... 0` lines.
- Official-source snapshot checked at 2026-05-05T19:34:52Z: https://satcompetition.github.io/2026/
- Sequential solver deadline: 2026-05-10.
- Parallel/Cloud solver deadline: 2026-05-17.
- System-description deadline: 2026-05-17.
"#,
        BUILD_INFO.stamp, BUILD_INFO.commit
    );

    let notes = r#"# SAT-COMP System Description Notes

Fill these before uploading the final documentation:

- Solver name: ay
- Authors: Andrew Yates
- Version / archive hash:
- Commit:
- Tracks:
- Proof checker: drat-trim
- AI-generated or AI-assisted changes:
- AI-tuned heuristics:
- Build platform:
- Known unsupported inputs:
"#;

    write_text(&output.join("build.sh"), build_sh, true)?;
    write_text(&output.join("run.sh"), run_sh, true)?;
    write_text(&output.join("README.md"), &readme, false)?;
    write_text(&output.join("system-description-notes.md"), notes, false)?;
    println!("generated SAT-COMP skeleton at {}", output.display());
    Ok(())
}

fn generate_chc(output: &Path, archive_url: &str, tracks: &str) -> Result<()> {
    let track_names = split_required_chc_tracks(tracks)?;
    let makefile_fragment = r#"# Add this target to chc-comp/chc-comp-2026 Makefile and add
# $(TOOLS_DIRECTORY)/ay to the download-verifiers dependency list.

$(TOOLS_DIRECTORY)/ay:
	mkdir -p $(TOOLS_DIRECTORY)
	rm -rf $@
	wget "__ARCHIVE_URL__" -O $(TOOLS_DIRECTORY)/ay.tar.gz
	cd $(TOOLS_DIRECTORY) && mkdir -p ay && tar -xzf ay.tar.gz -C ay --strip-components=1
	rm $(TOOLS_DIRECTORY)/ay.tar.gz
	chmod +x $(TOOLS_DIRECTORY)/ay/ay
	chmod +x $(TOOLS_DIRECTORY)/ay/run_solver.sh
"#
    .replace("__ARCHIVE_URL__", archive_url);

    let benchmark_xml = chc_benchmark_xml(&track_names);
    let tooldef = r#"# This file is part of BenchExec, a framework for reliable benchmarking:
# https://github.com/sosy-lab/benchexec
#
# SPDX-FileCopyrightText: 2007-2020 Dirk Beyer <https://www.sosy-lab.org>
#
# SPDX-License-Identifier: Apache-2.0

import os

import benchexec.tools.chc


class Tool(benchexec.tools.chc.ChcTool):
    """
    Tool info for ay.
    """

    REQUIRED_PATHS = [
        "ay",
        "run_solver.sh",
        "LICENSE",
        "README.md",
    ]

    def executable(self, tool_locator):
        return tool_locator.find_executable("run_solver.sh")

    def name(self):
        return "ay"

    def version(self, executable):
        ay_binary = os.path.join(os.path.dirname(executable), "ay")
        return self._version_from_tool(ay_binary, arg="--version")

    def cmdline(self, executable, options, task, rlimits):
        cmd = [executable] + options
        if not self._has_ay_timeout_option(options):
            timeout_ms = self._ay_timeout_ms(rlimits)
            if timeout_ms is not None:
                cmd += ["--ay-timeout-ms", str(timeout_ms)]
        return cmd + [task.single_input_file]

    def _has_ay_timeout_option(self, options):
        return any(
            opt == "--ay-timeout-ms" or opt.startswith("--ay-timeout-ms=")
            for opt in options
        )

    def _ay_timeout_ms(self, rlimits):
        for key in ("walltime", "cputime"):
            value = getattr(rlimits, key, None)
            if value is None and isinstance(rlimits, dict):
                value = rlimits.get(key)
            timeout_ms = self._limit_to_timeout_ms(value)
            if timeout_ms is not None:
                return timeout_ms
        return None

    def _limit_to_timeout_ms(self, value):
        if value is None:
            return None
        try:
            seconds = value.total_seconds() if hasattr(value, "total_seconds") else float(value)
        except (TypeError, ValueError):
            return None
        if seconds <= 0:
            return None
        ms = int(seconds * 1000)
        reserve = min(30000, max(5000, ms // 10))
        return max(1, ms - reserve)
"#;

    let track_model = chc_track_model_markdown();
    let readme = format!(
        r#"# ay CHC-COMP 2026 PR Files

Generated by ay {} from commit {}.

Use these files in a branch of `https://github.com/chc-comp/chc-comp-2026`:

- Add the contents of `Makefile.ay.fragment` to `Makefile`.
- Copy `benchmark-defs/ay.xml.template` to the same path in the competition repo.
- Copy `tooldefs/ay.py` to the same path in the competition repo.
- Open a pull request against `chc-comp/chc-comp-2026`.

Current generated local set-file categories: {}.

{}

Track-name note: these names match the current `chc-comp/chc-comp-2026`
benchmark definitions and `chc-comp26-benchmarks` set files as of
2026-05-05T19:34:52Z.

Before opening the PR:
- Replace the archive URL if it still contains `PLACEHOLDER`.
- Ensure the public archive contains a Linux executable at `ay` after extraction.
- Ensure the archive contains executable `run_solver.sh`; BenchExec runs that wrapper, not `ay` directly.
- Ensure the archive includes the permissive license.
- Keep discussion and answers on the pull request; do not submit by email.
- Official-source snapshot: https://chc-comp.github.io/ checked at 2026-05-05T19:34:52Z.
- The regular registration deadline was 2026-04-25. 2026-05-02 is the technical resubmission window.
"#,
        BUILD_INFO.stamp,
        BUILD_INFO.commit,
        track_names.join(", "),
        track_model
    );

    write_text(
        &output.join("Makefile.ay.fragment"),
        &makefile_fragment,
        false,
    )?;
    write_text(
        &output.join("benchmark-defs").join("ay.xml.template"),
        &benchmark_xml,
        false,
    )?;
    write_text(&output.join("tooldefs").join("ay.py"), tooldef, false)?;
    write_text(&output.join("README-CHC-PR.md"), &readme, false)?;
    println!("generated CHC-COMP PR skeleton at {}", output.display());
    print_chc_track_model_summary();
    Ok(())
}

fn write_chc_run_solver(output: &Path) -> Result<()> {
    let run_solver = r#"#!/usr/bin/env bash
set -u

ARGS=()
TIMEOUT_MS=""
while [ "$#" -gt 0 ]; do
  case "$1" in
    --ay-timeout-ms)
      if [ "$#" -ge 2 ]; then
        TIMEOUT_MS="$2"
        shift 2
      else
        shift
      fi
      ;;
    --ay-timeout-ms=*)
      TIMEOUT_MS="${1#--ay-timeout-ms=}"
      shift
      ;;
    *)
      ARGS+=("$1")
      shift
      ;;
  esac
done

if [ "${#ARGS[@]}" -lt 1 ]; then
  printf 'unknown\n'
  exit 0
fi

DIR="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
BENCHMARK="${ARGS[$((${#ARGS[@]} - 1))]}"

if [ ! -x "$DIR/ay" ] || [ ! -r "$BENCHMARK" ]; then
  printf 'unknown\n'
  exit 0
fi

AY_CMD=("$DIR/ay")
if head -c 2 "$DIR/ay" 2>/dev/null | grep -q '^#!'; then
  AY_CMD=(bash "$DIR/ay")
fi

is_uint() {
  [[ "$1" =~ ^[0-9]+$ ]]
}

timeout_with_margin_ms() {
  local ms="$1"
  local reserve=$((ms / 10))
  if [ "$reserve" -lt 5000 ]; then
    reserve=5000
  fi
  if [ "$reserve" -gt 30000 ]; then
    reserve=30000
  fi
  if [ "$ms" -gt "$reserve" ]; then
    printf '%s\n' "$((ms - reserve))"
  else
    printf '%s\n' "$ms"
  fi
}

if [ -z "$TIMEOUT_MS" ]; then
  TIMEOUT_MS="${AY_CHC_TIMEOUT_MS:-${AY_TIMEOUT_MS:-}}"
fi
if ! is_uint "${TIMEOUT_MS:-}"; then
  TIMEOUT_MS=""
fi
if [ -z "$TIMEOUT_MS" ]; then
  RAW_TIMEOUT="${TIMELIMIT:-${TIMEOUT:-${STAREXEC_WALLCLOCK_LIMIT:-}}}"
  if is_uint "${RAW_TIMEOUT:-}"; then
    TIMEOUT_MS="$(timeout_with_margin_ms "$((RAW_TIMEOUT * 1000))")"
  fi
fi

SOLVER_ARGS=(--chc)
if is_uint "${TIMEOUT_MS:-}" && [ "$TIMEOUT_MS" -gt 0 ]; then
  SOLVER_ARGS+=(--timeout "$TIMEOUT_MS")
fi

first_status() {
  awk '
    $0 == "sat" || $0 == "unsat" || $0 == "unknown" {
      print $0
      seen = 1
      exit
    }
    END {
      if (!seen) {
        print "unknown"
      }
    }
  ' "$1"
}

run_solver_capture_status() {
  local out_file
  out_file="$(mktemp "${TMPDIR:-/tmp}/ay-chc-status.XXXXXX")" || {
    printf 'unknown\n'
    return
  }

  if is_uint "${TIMEOUT_MS:-}" && [ "$TIMEOUT_MS" -gt 0 ]; then
    "${AY_CMD[@]}" "${SOLVER_ARGS[@]}" "$BENCHMARK" >"$out_file" 2>/dev/null &
    local pid="$!"
    local start_seconds="$SECONDS"
    local limit_seconds=$((TIMEOUT_MS / 1000))
    if [ "$limit_seconds" -lt 1 ]; then
      limit_seconds=1
    fi
    while kill -0 "$pid" 2>/dev/null; do
      if [ "$((SECONDS - start_seconds))" -ge "$limit_seconds" ]; then
        kill "$pid" 2>/dev/null || true
        wait "$pid" 2>/dev/null || true
        break
      fi
      sleep 0.05
    done
    wait "$pid" 2>/dev/null || true
  else
    "${AY_CMD[@]}" "${SOLVER_ARGS[@]}" "$BENCHMARK" >"$out_file" 2>/dev/null || true
  fi

  first_status "$out_file"
  rm -f "$out_file"
}

STATUS="$(run_solver_capture_status)"

case "$STATUS" in
  sat|unsat|unknown) printf '%s\n' "$STATUS" ;;
  *) printf 'unknown\n' ;;
esac
exit 0
"#;
    write_text(&output.join("run_solver.sh"), run_solver, true)
}

fn generate_pb(output: &Path) -> Result<()> {
    let run_solver = r#"#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCHMARK="${1:-${BENCHNAME:-}}"
PROOF_ARG="${2:-${PROOFFILE:-}}"

if [[ -z "$BENCHMARK" ]]; then
  echo "usage: $0 BENCHMARK" >&2
  echo "or set BENCHNAME in the PB-COMP portal command line" >&2
  exit 2
fi

ARGS=(pb solve)

RAW_TIMEOUT="${TIMELIMIT:-${TIMEOUT:-${STAREXEC_WALLCLOCK_LIMIT:-}}}"
if [[ -n "$RAW_TIMEOUT" ]]; then
  if [[ "$RAW_TIMEOUT" =~ ^[0-9]+$ ]]; then
    ARGS+=(--timeout "$((RAW_TIMEOUT * 1000))")
  else
    echo "ignoring non-integer timeout: $RAW_TIMEOUT" >&2
  fi
fi

if [[ -n "$PROOF_ARG" ]]; then
  mkdir -p "$(dirname "$PROOF_ARG")"
  ARGS+=(--proof "$PROOF_ARG")
fi

ARGS+=("$BENCHMARK")
exec "$DIR/ay" "${ARGS[@]}"
"#;

    let command_lines = r#"# PB-COMP 2026 Portal Command Lines

Sequential, uncertified PBS/PBO:

DIR/run_solver.sh BENCHNAME

Sequential, certified PBS/PBO:

DIR/run_solver.sh BENCHNAME PROOFFILE

Parallel fields can use the same wrapper. The current wrapper accepts NBCORE,
MEMLIMIT, TMPDIR, RANDOMSEED, DIR, TIMELIMIT, and TIMEOUT without requiring
them. TIMELIMIT/TIMEOUT are interpreted as seconds and converted to
milliseconds for ay.
"#;

    let smoke_opb = r#"* #variable= 1 #constraint= 1 #equal= 0 intsize= 2
min: 1 x1 ;
1 x1 >= 1 ;
"#;

    let readme = format!(
        r#"# ay PB-COMP 2026 Skeleton

Generated by ay {} from commit {}.

Portal upload contents:
- `run_solver.sh`: wrapper using the PB-COMP placeholders.
- `COMMAND-LINES.txt`: command lines to paste into the portal.
- `smoke.opb`: minimal strict OPB instance for local wrapper checks.

Before upload:
- Copy a Linux `ay` executable into this directory.
- Prefer a static x86-64 ELF binary.
- For the stronger PB26 package with static-build provenance, deterministic
  archive generation, compressed-input handling, and fail-closed certified-track
  guards, use `competition/pb26/prepare_submission.sh`.
- Ensure the solver archive includes license and description material.
- Certified tracks must pass a real VeriPB/CakePB proof-checking smoke test.
- Solver and benchmark submissions close on 2026-05-18.
"#,
        BUILD_INFO.stamp, BUILD_INFO.commit
    );

    write_text(&output.join("run_solver.sh"), run_solver, true)?;
    write_text(&output.join("COMMAND-LINES.txt"), command_lines, false)?;
    write_text(&output.join("smoke.opb"), smoke_opb, false)?;
    write_text(&output.join("README.md"), &readme, false)?;
    println!("generated PB-COMP skeleton at {}", output.display());
    Ok(())
}

fn generate_smt(
    output: &Path,
    archive_url: &str,
    archive_sha256: Option<&str>,
    system_description_url: &str,
    final_submission: bool,
) -> Result<()> {
    if final_submission {
        ensure_zenodo_url("--archive-url", archive_url)?;
        ensure_zenodo_url("--system-description-url", system_description_url)?;
    }

    // Honour the competition wall-clock limit: without -T, ay applies its
    // internal DEFAULT_SAFETY_DEADLINE (~300 s) and returns unknown early even
    // though StarExec allows the full limit. Read STAREXEC_WALLCLOCK_LIMIT
    // (seconds), pass -T:(limit-5) to leave a small margin for output before
    // the harness SIGKILL. Mirrors the SAT wrapper.
    let run_solver = r#"#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIM="${STAREXEC_WALLCLOCK_LIMIT:-${TIMELIMIT:-${TIMEOUT:-}}}"
ARGS=(--z3-mode)
case "${LIM:-}" in ''|*[!0-9]*) ;; *) [ "$LIM" -gt 10 ] && ARGS+=("-T:$((LIM - 5))");; esac
exec "$DIR/ay" "${ARGS[@]}" "$@"
"#;

    let run_solver_incr = r#"#!/usr/bin/env bash
set -euo pipefail

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
LIM="${STAREXEC_WALLCLOCK_LIMIT:-${TIMELIMIT:-${TIMEOUT:-}}}"
ARGS=(--z3-mode -in)  # -in already maps to --incremental; passing both errors "cannot be used multiple times"
case "${LIM:-}" in ''|*[!0-9]*) ;; *) [ "$LIM" -gt 10 ] && ARGS+=("-T:$((LIM - 5))");; esac
exec "$DIR/ay" "${ARGS[@]}" "$@"
"#;

    let submission_json = smt_submission_json(
        archive_url,
        archive_sha256,
        system_description_url,
        final_submission,
    )?;

    let readme = format!(
        r#"# ay SMT-COMP 2026 PR Files

Generated by ay {} from commit {}.

Use `ay-smt-comp-2026.json` as the submission JSON in a pull request to:

https://github.com/SMT-COMP/smt-comp.github.io

Expected path in that repository:

submissions/ay-smt-comp-2026.json

Before opening the PR:
- Replace placeholder Zenodo URLs.
- Fill the archive SHA-256 if it is known.
- Ensure the archive extracts with `ay`, `run_solver.sh`, and `run_solver_incr.sh` at its root.
- Official-source snapshot checked at 2026-05-05T19:34:52Z:
  https://smt-comp.github.io/2026/rules.pdf
- First solver and preliminary system descriptions are due 2026-05-27.
- Final solver and final system descriptions are due 2026-06-10.
"#,
        BUILD_INFO.stamp, BUILD_INFO.commit
    );

    write_text(&output.join("run_solver.sh"), run_solver, true)?;
    write_text(&output.join("run_solver_mv.sh"), run_solver, true)?;
    write_text(&output.join("run_solver_incr.sh"), run_solver_incr, true)?;
    write_text(
        &output.join("ay-smt-comp-2026.json"),
        &submission_json,
        false,
    )?;
    write_text(&output.join("README.md"), &readme, false)?;
    println!("generated SMT-COMP PR skeleton at {}", output.display());
    Ok(())
}

fn split_tracks(raw: &str) -> Result<Vec<String>> {
    let mut tracks = Vec::new();
    for raw_track in raw.split(',').map(str::trim).filter(|s| !s.is_empty()) {
        let Some(track) = chc_track_set_file(raw_track) else {
            bail!(
                "invalid CHC track '{raw_track}'; use current CHC-COMP 2026 set-file names or public aliases: {}",
                CHC_ALLOWED_TRACKS.join(", ")
            );
        };
        if !tracks.iter().any(|existing| existing == track) {
            tracks.push(track.to_string());
        }
    }
    if tracks.is_empty() {
        bail!("at least one CHC track is required");
    }
    Ok(tracks)
}

fn split_required_chc_tracks(raw: &str) -> Result<Vec<String>> {
    let tracks = split_tracks(raw)?;
    require_all_chc_comp_tracks(&tracks)?;
    Ok(tracks)
}

fn require_all_chc_comp_tracks(tracks: &[String]) -> Result<()> {
    let mut seen = HashSet::new();
    let mut unexpected = Vec::new();
    for track in tracks {
        if !CHC_ALLOWED_TRACKS.contains(&track.as_str()) {
            unexpected.push(track.clone());
        }
        seen.insert(track.as_str());
    }

    let missing: Vec<&str> = CHC_ALLOWED_TRACKS
        .iter()
        .copied()
        .filter(|track| !seen.contains(track))
        .collect();
    if missing.is_empty() && unexpected.is_empty() {
        return Ok(());
    }

    let mut problems = Vec::new();
    if !missing.is_empty() {
        problems.push(format!("missing [{}]", missing.join(", ")));
    }
    if !unexpected.is_empty() {
        problems.push(format!("unexpected [{}]", unexpected.join(", ")));
    }
    bail!(
        "CHC-COMP 2026 submission must include exactly all current chc-comp26-benchmarks set-file categories [{}]; {}",
        CHC_ALLOWED_TRACKS.join(", "),
        problems.join("; ")
    )
}

fn read_chc_xml_track_includes(xml_path: &Path) -> Result<Vec<String>> {
    let text = fs::read_to_string(xml_path)
        .with_context(|| format!("failed to read XML {}", xml_path.display()))?;
    Ok(chc_xml_track_includes(&text))
}

fn chc_xml_track_includes(text: &str) -> Vec<String> {
    let mut found = Vec::new();
    for line in text.lines() {
        let Some(after_prefix) = line.split("../chc-comp26-benchmarks/").nth(1) else {
            continue;
        };
        if !after_prefix.contains(".set") {
            continue;
        }
        let Some(track) = after_prefix.split(".set").next() else {
            continue;
        };
        found.push(track.to_string());
    }
    found
}

fn sorted_unique_tracks(mut tracks: Vec<String>) -> Vec<String> {
    tracks.sort();
    tracks.dedup();
    tracks
}

fn chc_track_set_file(track: &str) -> Option<&'static str> {
    match track {
        "BOOL" => Some("BOOL"),
        "BV" | "BV-Nonlin" => Some("BV"),
        "BV-Lin" => Some("BV-Lin"),
        "LRA-Lin" => Some("LRA-Lin"),
        "LIA-Lin" => Some("LIA-Lin"),
        "LIA" | "LIA-Nonlin" => Some("LIA"),
        "LIA-Lin-Arrays" => Some("LIA-Lin-Arrays"),
        "LIA-Arrays" | "LIA-Nonlin-Arrays" => Some("LIA-Arrays"),
        "ADT-LIA" => Some("ADT-LIA"),
        "ADT-LIA-Arrays" => Some("ADT-LIA-Arrays"),
        "mixed_LIA_LRA" => Some("mixed_LIA_LRA"),
        _ => None,
    }
}

fn chc_benchmark_xml(tracks: &[String]) -> String {
    let mut tasks = String::new();
    for track in tracks {
        let set_file = chc_track_set_file(track).unwrap_or(track);
        tasks.push_str(&format!(
            r#"  <tasks name="{track}">
    <includesfile>../chc-comp26-benchmarks/{set_file}.set</includesfile>
    <propertyfile>../chc-comp26-benchmarks/properties/check-sat.prp</propertyfile>
  </tasks>
"#
        ));
    }

    format!(
        r#"<?xml version="1.0"?>
<!DOCTYPE benchmark PUBLIC "+//IDN sosy-lab.org//DTD BenchExec benchmark 1.9//EN" "https://www.sosy-lab.org/benchexec/benchmark-2.3.dtd">
<benchmark tool="ay" timelimit="30 min" hardtimelimit="30 min" memlimit="30 GB" cpuCores="8">

<rundefinition name="CHC-COMP2026_check-sat">
{tasks}</rundefinition>

</benchmark>
"#
    )
}

fn smt_submission_json(
    archive_url: &str,
    archive_sha256: Option<&str>,
    system_description_url: &str,
    final_submission: bool,
) -> Result<String> {
    let mut archive = json!({
        "url": archive_url,
    });
    if let Some(sha256) = archive_sha256 {
        archive["h"] = json!({ "sha256": sha256 });
    }

    let single_query_logics = [
        "QF_UF",
        "QF_BV",
        "QF_LIA",
        "QF_LRA",
        "QF_IDL",
        "QF_RDL",
        // QF_UFLIA withdrawn (2026-06-15): a confirmed false-SAT in the combined
        // EUF+LIA path (a chained ite-over-Int defining a UF application is not
        // enforced) reproduces non-incrementally — see
        // benchmarks/smt/regression/soundness_qf_uf_incremental/traffic_uflia_falsesat_*
        // and the development design notes A single wrong
        // answer voids the division; re-add only after the ite-chain bug is fixed.
        // QF_AUFLIA is a strict superset of that buggy combination but was
        // verified clean on a 36-file incremental sample (0 soundness conflicts,
        // AY 20/36) — kept; re-audit on a larger sample if the ite-chain fix slips.
        "QF_AUFLIA",
        "QF_AX",
        "QF_DT",
        "QF_ABV",
        "QF_AUFBV",
        "QF_UFBV",
    ];
    let model_validation_logics = ["QF_UF", "QF_LRA"];
    // QF_UFLIA withdrawn (2026-06-15): confirmed false-SAT (ite-chain in combined
    // EUF+LIA), would void the division. QF_UF confirmed sound at corpus scale
    // (0 conflicts, 1778-file re-sweep); QF_LRA safe (AY returns unknown/timeout,
    // no wrong answers). See the development design notes
    let incremental_logics = ["QF_UF", "QF_LRA"];

    let submission = json!({
        "name": "ay",
        "contributors": [
            {
                "name": "Andrew Yates"
            }
        ],
        "contacts": [
            {
                "name": "Andrew Yates",
                "email": "andrewyates.name@gmail.com"
            }
        ],
        "website": "https://github.com/alabsystems/ay",
        "system_description": system_description_url,
        "solver_type": "Standalone",
        "seed": 42,
        "competitive": true,
        "archive": archive,
        "command": ["run_solver.sh"],
        "final": final_submission,
        "participations": [
            {
                "tracks": ["SingleQuery"],
                "logics": single_query_logics,
                "archive": archive,
                "command": ["run_solver.sh"]
            },
            {
                "tracks": ["ModelValidation"],
                "logics": model_validation_logics,
                "archive": archive,
                "command": ["run_solver_mv.sh"]
            },
            {
                "tracks": ["Incremental"],
                "logics": incremental_logics,
                "archive": archive,
                "command": ["run_solver_incr.sh"]
            }
        ]
    });

    let text = serde_json::to_string_pretty(&submission)
        .context("failed to serialize SMT-COMP submission JSON")?;
    Ok(format!("{text}\n"))
}

fn ensure_zenodo_url(flag: &str, url: &str) -> Result<()> {
    if !url.contains("PLACEHOLDER")
        && (url.starts_with("https://zenodo.org/") || url.starts_with("http://zenodo.org/"))
    {
        return Ok(());
    }
    bail!("{flag} must point at a concrete zenodo.org URL");
}

struct GateReport {
    name: &'static str,
    passed: usize,
    failed: usize,
    skipped: usize,
}

impl GateReport {
    fn new(name: &'static str) -> Self {
        Self {
            name,
            passed: 0,
            failed: 0,
            skipped: 0,
        }
    }

    fn pass(&mut self, label: impl AsRef<str>) {
        self.passed += 1;
        println!("[PASS] {}: {}", self.name, label.as_ref());
    }

    fn fail(&mut self, label: impl AsRef<str>) {
        self.failed += 1;
        println!("[FAIL] {}: {}", self.name, label.as_ref());
    }

    fn skip(&mut self, label: impl AsRef<str>) {
        self.skipped += 1;
        println!("[SKIP] {}: {}", self.name, label.as_ref());
    }

    fn file(&mut self, path: &Path, label: &'static str) {
        if path.is_file() {
            self.pass(label);
        } else {
            self.fail(format!("{label}: missing {}", path.display()));
        }
    }

    fn archive(&mut self, path: &Path, label: &'static str) {
        if path.is_file() {
            match sha256_file(path) {
                Ok(hash) => match inspect_archive_members(path) {
                    Ok(()) => self.pass(format!("{label}: sha256={hash}; archive members safe")),
                    Err(err) => self.fail(format!("{label}: unsafe archive: {err:#}")),
                },
                Err(err) => self.fail(format!("{label}: cannot hash {}: {err:#}", path.display())),
            }
        } else {
            self.fail(format!("{label}: missing {}", path.display()));
        }
    }

    fn executable(&mut self, path: &Path, label: &'static str) {
        if path.is_file() && is_executable(path) {
            self.pass(label);
        } else {
            self.fail(format!("{label}: not executable {}", path.display()));
        }
    }

    fn binary(
        &mut self,
        path: &Path,
        require_linux: bool,
        require_static: bool,
        label: &'static str,
    ) {
        if !path.is_file() {
            self.fail(format!("{label}: missing {}", path.display()));
            return;
        }
        if !is_executable(path) {
            self.fail(format!("{label}: not executable {}", path.display()));
            return;
        }
        let platform = binary_platform(path).unwrap_or_else(|_| "unknown".to_string());
        if require_linux && !platform.starts_with("linux-elf-x86_64") {
            self.fail(format!(
                "{label}: expected linux-elf-x86_64, got {platform}"
            ));
        } else if require_static && !platform.ends_with("-static") {
            self.fail(format!("{label}: expected static binary, got {platform}"));
        } else {
            self.pass(format!("{label}: {platform}"));
        }
    }

    fn command(&mut self, command: &mut Command, label: &'static str) {
        match command.output() {
            Ok(output) if output.status.success() => self.pass(label),
            Ok(output) => self.fail(format!(
                "{label}: exit={:?} stdout={} stderr={}",
                output.status.code(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            )),
            Err(err) => self.fail(format!("{label}: failed to start: {err}")),
        }
    }

    fn text_contains(&mut self, path: &Path, needle: &str, label: &'static str) {
        match fs::read_to_string(path) {
            Ok(text) if text.contains(needle) => self.pass(label),
            Ok(_) => self.fail(format!("{label}: missing {needle:?} in {}", path.display())),
            Err(err) => self.fail(format!("{label}: failed to read {}: {err}", path.display())),
        }
    }

    fn text_not_contains(&mut self, path: &Path, needle: &str, label: &'static str) {
        match fs::read_to_string(path) {
            Ok(text) if !text.contains(needle) => self.pass(label),
            Ok(_) => self.fail(format!("{label}: found {needle:?} in {}", path.display())),
            Err(err) => self.fail(format!("{label}: failed to read {}: {err}", path.display())),
        }
    }

    fn finish(self) -> Result<()> {
        if self.failed > 0 {
            bail!(
                "{} gate failed: {} passed, {} failed, {} skipped",
                self.name,
                self.passed,
                self.failed,
                self.skipped
            );
        }
        println!(
            "[OK] {} gate: {} passed, {} skipped",
            self.name, self.passed, self.skipped
        );
        Ok(())
    }
}

fn reset_dir(path: &Path) -> Result<()> {
    if path.as_os_str().is_empty() || path == Path::new("/") {
        bail!(
            "refusing to reset unsafe output directory '{}'",
            path.display()
        );
    }
    if path.exists() {
        fs::remove_dir_all(path)
            .with_context(|| format!("failed to remove '{}'", path.display()))?;
    }
    fs::create_dir_all(path).with_context(|| format!("failed to create '{}'", path.display()))?;
    Ok(())
}

fn install_runtime_files(package_root: &Path, ay_bin: Option<&Path>) -> Result<PathBuf> {
    let ay_bin = resolve_ay_bin(ay_bin)?;
    fs::copy(&ay_bin, package_root.join("ay")).with_context(|| {
        format!(
            "failed to copy ay binary '{}' into '{}'",
            ay_bin.display(),
            package_root.display()
        )
    })?;
    set_executable(&package_root.join("ay"))?;
    copy_build_metadata_sidecar_if_exists(&ay_bin, package_root)?;
    copy_workspace_file_if_exists("LICENSE", package_root)?;
    copy_workspace_file_if_exists("NOTICE", package_root)?;
    copy_workspace_file_if_exists("THIRD_PARTY.md", package_root)?;
    Ok(ay_bin)
}

fn resolve_ay_bin(explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = explicit {
        return canonical_file(path, "ay binary");
    }
    if let Ok(path) = env::var("AY_SUBMISSION_BIN") {
        return canonical_file(Path::new(&path), "AY_SUBMISSION_BIN");
    }
    let root = workspace_root();
    for (target, label) in [
        (
            "x86_64-unknown-linux-musl",
            "default static Linux release ay binary",
        ),
        (
            "x86_64-unknown-linux-gnu",
            "default Linux release ay binary",
        ),
    ] {
        let linux_release = root.join("target").join(target).join("release").join("ay");
        if linux_release.is_file() {
            return canonical_file(&linux_release, label);
        }
    }
    env::current_exe().context("failed to resolve current ay executable")
}

fn canonical_file(path: &Path, label: &str) -> Result<PathBuf> {
    if !path.is_file() {
        bail!("{label} is not a file: {}", path.display());
    }
    fs::canonicalize(path).with_context(|| format!("failed to canonicalize '{}'", path.display()))
}

fn workspace_root() -> PathBuf {
    if let Ok(current_dir) = env::current_dir() {
        for candidate in current_dir.ancestors() {
            if candidate.join("Cargo.toml").is_file()
                && candidate.join("crates/ay/Cargo.toml").is_file()
            {
                return candidate.to_path_buf();
            }
        }
    }
    compiled_workspace_root()
}

fn compiled_workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crates/ay has a workspace root")
        .to_path_buf()
}

fn copy_workspace_file_if_exists(name: &str, package_root: &Path) -> Result<()> {
    let src = workspace_root().join(name);
    if src.is_file() {
        fs::copy(&src, package_root.join(name))
            .with_context(|| format!("failed to copy '{}'", src.display()))?;
    }
    Ok(())
}

fn copy_build_metadata_sidecar_if_exists(ay_bin: &Path, package_root: &Path) -> Result<()> {
    let sidecar = build_metadata_sidecar_path(ay_bin);
    if sidecar.is_file() {
        fs::copy(&sidecar, package_root.join("ay.build-metadata.txt")).with_context(|| {
            format!(
                "failed to copy ay build metadata sidecar '{}' into '{}'",
                sidecar.display(),
                package_root.display()
            )
        })?;
    }
    Ok(())
}

fn build_metadata_sidecar_path(ay_bin: &Path) -> PathBuf {
    let file_name = ay_bin
        .file_name()
        .map(|name| name.to_string_lossy())
        .unwrap_or_else(|| "ay".into());
    ay_bin.with_file_name(format!("{file_name}.build-metadata.txt"))
}

fn create_tar_gz(source_dir: &Path, archive: &Path) -> Result<()> {
    if let Some(parent) = archive.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create '{}'", parent.display()))?;
    }
    let _ = fs::remove_file(archive);
    let gzip = select_submission_gzip()?;
    let members = collect_archive_members(source_dir)?;
    let temp_tar = archive.with_file_name(format!(
        "{}.tmp.tar",
        archive
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("submission")
    ));
    let temp_gz = temp_tar.with_extension("tar.gz");
    let _ = fs::remove_file(&temp_tar);
    let _ = fs::remove_file(&temp_gz);

    write_ustar_archive(&temp_tar, source_dir, &members)?;

    let output = Command::new(&gzip)
        .arg("-n")
        .arg("-f")
        .arg(&temp_tar)
        .output()
        .with_context(|| format!("failed to run '{}'", gzip.display()))?;
    if !output.status.success() {
        bail!(
            "gzip '{}' failed for '{}': stdout={} stderr={}",
            gzip.display(),
            archive.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    fs::rename(&temp_gz, archive).with_context(|| {
        format!(
            "failed to move '{}' to '{}'",
            temp_gz.display(),
            archive.display()
        )
    })?;
    Ok(())
}

fn write_ustar_archive(archive: &Path, source_dir: &Path, members: &ArchiveMembers) -> Result<()> {
    let mut out = fs::File::create(archive)
        .with_context(|| format!("failed to create '{}'", archive.display()))?;
    let mut dirs = members.dirs.clone();
    let mut files = members.files.clone();
    let mut executables = members.executables.clone();
    dirs.sort();
    files.sort();
    executables.sort();
    for member in &dirs {
        write_ustar_header(&mut out, member, 0, 0o755, b'5')?;
    }
    for member in &files {
        write_ustar_file(&mut out, source_dir, member, 0o644)?;
    }
    for member in &executables {
        write_ustar_file(&mut out, source_dir, member, 0o755)?;
    }
    out.write_all(&[0u8; 1024])
        .with_context(|| format!("failed to finish '{}'", archive.display()))?;
    Ok(())
}

fn write_ustar_file(out: &mut fs::File, source_dir: &Path, member: &Path, mode: u32) -> Result<()> {
    let source = source_dir.join(member);
    let meta =
        fs::metadata(&source).with_context(|| format!("failed to stat '{}'", source.display()))?;
    let size = meta.len();
    write_ustar_header(out, member, size, mode, b'0')?;
    let mut input = fs::File::open(&source)
        .with_context(|| format!("failed to open '{}'", source.display()))?;
    io::copy(&mut input, out)
        .with_context(|| format!("failed to archive '{}'", source.display()))?;
    let padding = (512 - (size % 512)) % 512;
    if padding != 0 {
        out.write_all(&vec![0u8; padding as usize])
            .with_context(|| format!("failed to pad '{}'", source.display()))?;
    }
    Ok(())
}

fn write_ustar_header(
    out: &mut fs::File,
    member: &Path,
    size: u64,
    mode: u32,
    typeflag: u8,
) -> Result<()> {
    let name = ustar_member_name(member)?;
    let (prefix, suffix) = split_ustar_name(&name)?;
    let mut header = [0u8; 512];
    write_ustar_bytes(&mut header[0..100], suffix.as_bytes(), "name")?;
    write_ustar_octal(&mut header[100..108], mode as u64, "mode")?;
    write_ustar_octal(&mut header[108..116], 0, "uid")?;
    write_ustar_octal(&mut header[116..124], 0, "gid")?;
    write_ustar_octal(&mut header[124..136], size, "size")?;
    write_ustar_octal(&mut header[136..148], 0, "mtime")?;
    header[148..156].fill(b' ');
    header[156] = typeflag;
    write_ustar_bytes(&mut header[257..263], b"ustar\0", "magic")?;
    write_ustar_bytes(&mut header[263..265], b"00", "version")?;
    write_ustar_bytes(&mut header[265..297], b"root", "uname")?;
    write_ustar_bytes(&mut header[297..329], b"root", "gname")?;
    write_ustar_bytes(&mut header[345..500], prefix.as_bytes(), "prefix")?;

    let checksum: u32 = header.iter().map(|byte| u32::from(*byte)).sum();
    let checksum_field = format!("{checksum:06o}\0 ");
    header[148..156].copy_from_slice(checksum_field.as_bytes());
    out.write_all(&header)
        .with_context(|| format!("failed to write archive header for '{name}'"))?;
    Ok(())
}

fn ustar_member_name(member: &Path) -> Result<String> {
    if member == Path::new(".") {
        return Ok(".".to_string());
    }
    let mut parts = Vec::new();
    for component in member.components() {
        parts.push(component.as_os_str().to_string_lossy().replace('\\', "/"));
    }
    let name = parts.join("/");
    if name.is_empty() || name.contains('\0') || name.starts_with('/') || name.contains("../") {
        bail!("invalid archive member path '{}'", member.display());
    }
    Ok(name)
}

fn split_ustar_name(name: &str) -> Result<(&str, &str)> {
    if name.len() <= 100 {
        return Ok(("", name));
    }
    let mut best = None;
    for (idx, _) in name.match_indices('/') {
        let prefix = &name[..idx];
        let suffix = &name[idx + 1..];
        if !suffix.is_empty() && prefix.len() <= 155 && suffix.len() <= 100 {
            best = Some((prefix, suffix));
        }
    }
    best.with_context(|| format!("archive member path too long for ustar: '{name}'"))
}

fn write_ustar_bytes(field: &mut [u8], value: &[u8], label: &str) -> Result<()> {
    if value.len() > field.len() {
        bail!("ustar {label} field too long");
    }
    field[..value.len()].copy_from_slice(value);
    Ok(())
}

fn write_ustar_octal(field: &mut [u8], value: u64, label: &str) -> Result<()> {
    let digit_width = field.len() - 1;
    let digits = format!("{value:o}");
    if digits.len() > digit_width {
        bail!("ustar {label} value too large: {value}");
    }
    field.fill(b'0');
    let start = digit_width - digits.len();
    field[start..start + digits.len()].copy_from_slice(digits.as_bytes());
    field[digit_width] = 0;
    Ok(())
}

fn select_submission_gzip() -> Result<PathBuf> {
    let mut candidates = Vec::new();
    if let Ok(path) = env::var("AY_GZIP") {
        if !path.trim().is_empty() {
            candidates.push(PathBuf::from(path));
        }
    }
    #[cfg(windows)]
    {
        candidates.push(PathBuf::from(r"C:\msys64\usr\bin\gzip.exe"));
        candidates.push(PathBuf::from(r"C:\Program Files\Git\usr\bin\gzip.exe"));
    }
    candidates.push(PathBuf::from(gzip_exe_name()));

    let mut tried = Vec::new();
    for candidate in candidates {
        if candidate.components().count() > 1 && !candidate.exists() {
            tried.push(format!("{} (missing)", candidate.display()));
            continue;
        }
        match gzip_supports_submission_options(&candidate) {
            Ok(true) => return Ok(candidate),
            Ok(false) => tried.push(format!(
                "{} (missing required options)",
                candidate.display()
            )),
            Err(err) => tried.push(format!("{} ({err})", candidate.display())),
        }
    }

    bail!(
        "submission archive creation requires gzip with -n/--no-name support; set AY_GZIP to a compatible gzip. tried: {}",
        tried.join(", ")
    )
}

#[cfg(windows)]
fn gzip_exe_name() -> &'static str {
    "gzip.exe"
}

#[cfg(not(windows))]
fn gzip_exe_name() -> &'static str {
    "gzip"
}

fn gzip_supports_submission_options(gzip: &Path) -> Result<bool> {
    let output = Command::new(gzip)
        .arg("--help")
        .output()
        .with_context(|| format!("failed to probe '{}'", gzip.display()))?;
    if !output.status.success() {
        return Ok(false);
    }
    let help = format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(help.contains("-n") || help.contains("--no-name"))
}

#[derive(Default)]
struct ArchiveMembers {
    dirs: Vec<PathBuf>,
    files: Vec<PathBuf>,
    executables: Vec<PathBuf>,
}

fn collect_archive_members(source_dir: &Path) -> Result<ArchiveMembers> {
    let mut members = ArchiveMembers::default();
    collect_archive_members_recursive(source_dir, source_dir, &mut members)?;
    Ok(members)
}

fn collect_archive_members_recursive(
    root: &Path,
    path: &Path,
    members: &mut ArchiveMembers,
) -> Result<()> {
    let meta = fs::symlink_metadata(path)
        .with_context(|| format!("failed to stat '{}'", path.display()))?;
    if meta.file_type().is_symlink() {
        bail!("refusing to archive symlink: {}", path.display());
    }
    let member = archive_member_path(root, path)?;
    if meta.is_dir() {
        if member != Path::new(".") {
            members.dirs.push(member);
        }
        for entry in
            fs::read_dir(path).with_context(|| format!("failed to read '{}'", path.display()))?
        {
            let entry = entry.with_context(|| format!("failed to read '{}'", path.display()))?;
            collect_archive_members_recursive(root, &entry.path(), members)?;
        }
        return Ok(());
    }
    if !meta.is_file() {
        bail!("refusing to archive non-file member: {}", path.display());
    }
    if should_archive_as_executable(root, path, &meta) {
        members.executables.push(member);
    } else {
        members.files.push(member);
    }
    Ok(())
}

fn archive_member_path(root: &Path, path: &Path) -> Result<PathBuf> {
    let relative = path
        .strip_prefix(root)
        .with_context(|| format!("failed to relativize '{}'", path.display()))?;
    if relative.as_os_str().is_empty() {
        Ok(PathBuf::from("."))
    } else {
        Ok(relative.to_path_buf())
    }
}

fn should_archive_as_executable(root: &Path, path: &Path, meta: &fs::Metadata) -> bool {
    if archive_preserves_executable_bit(meta) {
        return true;
    }
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    if !SUBMISSION_EXECUTABLE_NAMES.contains(&name) {
        return false;
    }
    path.strip_prefix(root).is_ok_and(|relative| {
        let components: Vec<_> = relative.components().collect();
        components.len() == 1
            || (components.len() == 2 && components[0].as_os_str() == std::ffi::OsStr::new("ay"))
    })
}

#[cfg(unix)]
fn archive_preserves_executable_bit(meta: &fs::Metadata) -> bool {
    use std::os::unix::fs::PermissionsExt;
    meta.permissions().mode() & 0o111 != 0
}

#[cfg(not(unix))]
fn archive_preserves_executable_bit(_meta: &fs::Metadata) -> bool {
    false
}

fn write_package_manifest(
    output: &Path,
    competition: &str,
    package_root: &Path,
    archive: &Path,
    ay_bin: &Path,
) -> Result<()> {
    let manifest = json!({
        "competition": competition,
        "generated_by": {
            "ay_version": BUILD_INFO.version,
            "build_stamp": BUILD_INFO.stamp,
            "commit": BUILD_INFO.commit,
            "datetime_utc": BUILD_INFO.datetime_utc
        },
        "package_root": package_root,
        "archive": {
            "path": archive,
            "sha256": sha256_file(archive)?
        },
        "binary": {
            "source_path": ay_bin,
            "packaged_path": package_root.join("ay"),
            "sha256": sha256_file(ay_bin)?,
            "platform": binary_platform(ay_bin).unwrap_or_else(|_| "unknown".to_string()),
            "build_metadata": package_build_metadata_manifest(&package_root.join("ay.build-metadata.txt"))?
        },
        "gate_command": format!("ay submission gate {} --package {}", competition_gate_name(competition), output.display())
    });
    let text = serde_json::to_string_pretty(&manifest)
        .context("failed to serialize submission package manifest")?;
    write_text(&output.join("MANIFEST.json"), &format!("{text}\n"), false)
}

fn package_build_metadata_manifest(path: &Path) -> Result<serde_json::Value> {
    if !path.is_file() {
        return Ok(json!({
            "available": false,
            "path": serde_json::Value::Null,
        }));
    }

    let text = fs::read_to_string(path)
        .with_context(|| format!("failed to read build metadata '{}'", path.display()))?;
    Ok(json!({
        "available": true,
        "path": path,
        "sha256": sha256_file(path)?,
        "git_commit": metadata_text_field(&text, "git_commit").unwrap_or_else(|| "unavailable".to_string()),
        "git_branch": metadata_text_field(&text, "git_branch").unwrap_or_else(|| "unavailable".to_string()),
        "git_dirty": metadata_text_field(&text, "git_dirty").unwrap_or_else(|| "unavailable".to_string()),
        "target": metadata_text_field(&text, "target").unwrap_or_else(|| "unavailable".to_string()),
        "target_cpu": metadata_text_field(&text, "target_cpu").unwrap_or_else(|| "unavailable".to_string()),
        "cargo_lock_sha256": metadata_text_field(&text, "cargo_lock_sha256").unwrap_or_else(|| "unavailable".to_string()),
    }))
}

fn metadata_text_field(text: &str, key: &str) -> Option<String> {
    let prefix = format!("{key}:");
    text.lines()
        .find_map(|line| line.strip_prefix(&prefix))
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(ToOwned::to_owned)
}

fn competition_gate_name(competition: &str) -> &'static str {
    match competition {
        "sat-comp-2026" => "sat",
        "chc-comp-2026" => "chc",
        "pb-comp-2026" => "pb",
        "smt-comp-2026" => "smt",
        _ => "all",
    }
}

fn sha256_file(path: &Path) -> Result<String> {
    let bytes = fs::read(path).with_context(|| format!("failed to read '{}'", path.display()))?;
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

fn binary_platform(path: &Path) -> Result<String> {
    let bytes = fs::read(path).with_context(|| format!("failed to read '{}'", path.display()))?;
    if bytes.starts_with(b"\x7fELF") {
        return Ok(describe_elf(&bytes));
    }
    if bytes.len() >= 4
        && matches!(
            &bytes[..4],
            b"\xfe\xed\xfa\xce"
                | b"\xfe\xed\xfa\xcf"
                | b"\xce\xfa\xed\xfe"
                | b"\xcf\xfa\xed\xfe"
                | b"\xca\xfe\xba\xbe"
                | b"\xca\xfe\xba\xbf"
        )
    {
        return Ok("mach-o".to_string());
    }
    Ok("unknown".to_string())
}

fn describe_elf(bytes: &[u8]) -> String {
    if bytes.len() < 64 {
        return "linux-elf-truncated".to_string();
    }
    let class = match bytes[4] {
        1 => "32",
        2 => "64",
        _ => "unknown",
    };
    let endian = bytes[5];
    let machine = if endian == 1 && bytes.len() >= 20 {
        match u16::from_le_bytes([bytes[18], bytes[19]]) {
            0x3e => "x86_64",
            0xb7 => "aarch64",
            _ => "unknown",
        }
    } else if endian == 2 && bytes.len() >= 20 {
        match u16::from_be_bytes([bytes[18], bytes[19]]) {
            0x3e => "x86_64",
            0xb7 => "aarch64",
            _ => "unknown",
        }
    } else {
        "unknown"
    };
    let link = if elf_has_program_interpreter(bytes) {
        "dynamic"
    } else {
        "static"
    };
    format!("linux-elf-{machine}-{class}-{link}")
}

fn elf_has_program_interpreter(bytes: &[u8]) -> bool {
    if bytes.len() < 64 || bytes[4] != 2 {
        return false;
    }
    let little = bytes[5] == 1;
    let phoff = read_elf_u64(bytes, 32, little).unwrap_or(0) as usize;
    let phentsize = read_elf_u16(bytes, 54, little).unwrap_or(0) as usize;
    let phnum = read_elf_u16(bytes, 56, little).unwrap_or(0) as usize;
    if phoff == 0 || phentsize < 4 || phnum == 0 {
        return false;
    }
    for idx in 0..phnum {
        let Some(offset) = phoff.checked_add(idx.saturating_mul(phentsize)) else {
            return false;
        };
        if offset + 4 > bytes.len() {
            return false;
        }
        let segment_type = if little {
            u32::from_le_bytes([
                bytes[offset],
                bytes[offset + 1],
                bytes[offset + 2],
                bytes[offset + 3],
            ])
        } else {
            u32::from_be_bytes([
                bytes[offset],
                bytes[offset + 1],
                bytes[offset + 2],
                bytes[offset + 3],
            ])
        };
        if segment_type == 3 {
            return true;
        }
    }
    false
}

fn read_elf_u16(bytes: &[u8], offset: usize, little: bool) -> Option<u16> {
    let slice = bytes.get(offset..offset + 2)?;
    Some(if little {
        u16::from_le_bytes([slice[0], slice[1]])
    } else {
        u16::from_be_bytes([slice[0], slice[1]])
    })
}

fn read_elf_u64(bytes: &[u8], offset: usize, little: bool) -> Option<u64> {
    let slice = bytes.get(offset..offset + 8)?;
    Some(if little {
        u64::from_le_bytes([
            slice[0], slice[1], slice[2], slice[3], slice[4], slice[5], slice[6], slice[7],
        ])
    } else {
        u64::from_be_bytes([
            slice[0], slice[1], slice[2], slice[3], slice[4], slice[5], slice[6], slice[7],
        ])
    })
}

#[cfg(unix)]
fn is_executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    fs::metadata(path)
        .map(|meta| meta.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}

#[cfg(not(unix))]
fn is_executable(path: &Path) -> bool {
    path.is_file()
}

fn resolve_gate_dir(package: &Path, child: &str) -> PathBuf {
    if package.join(child).is_dir() {
        package.join(child)
    } else {
        package.to_path_buf()
    }
}

fn child_or_self(package: &Path, child: &str) -> PathBuf {
    let candidate = package.join(child);
    if candidate.is_dir() {
        candidate
    } else {
        package.to_path_buf()
    }
}

fn make_temp_dir(prefix: &str) -> Result<PathBuf> {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|duration| duration.as_nanos())
        .unwrap_or(0);
    let dir = env::temp_dir().join(format!("{prefix}-{}-{nanos}", std::process::id()));
    fs::create_dir_all(&dir).with_context(|| format!("failed to create '{}'", dir.display()))?;
    Ok(dir)
}

fn inspect_archive_members(archive: &Path) -> Result<()> {
    let output = Command::new("tar")
        .arg("-tzf")
        .arg(archive)
        .output()
        .with_context(|| format!("failed to list archive '{}'", archive.display()))?;
    if !output.status.success() {
        bail!(
            "tar -tzf failed for '{}': stdout={} stderr={}",
            archive.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let mut seen = HashSet::new();
    for raw in String::from_utf8_lossy(&output.stdout).lines() {
        let member = raw.trim_end_matches('/');
        if member.is_empty() || member.starts_with('/') || member.contains("//") {
            bail!("archive contains unsafe member path: {raw}");
        }
        if !seen.insert(member.to_string()) {
            bail!("archive contains duplicate member path: {raw}");
        }
        for component in Path::new(member).components() {
            if !matches!(
                component,
                std::path::Component::Normal(_) | std::path::Component::CurDir
            ) {
                bail!("archive contains unsafe member path component: {raw}");
            }
        }
    }

    let output = Command::new("tar")
        .arg("-tvzf")
        .arg(archive)
        .output()
        .with_context(|| format!("failed to inspect archive '{}'", archive.display()))?;
    if !output.status.success() {
        bail!(
            "tar -tvzf failed for '{}': stdout={} stderr={}",
            archive.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        if line.starts_with('-') || line.starts_with('d') {
            continue;
        }
        bail!("archive contains non-file/non-directory member: {line}");
    }
    Ok(())
}

fn validate_chc_archive_layout(archive: &Path) -> Result<()> {
    let output = Command::new("tar")
        .arg("-tzf")
        .arg(archive)
        .output()
        .with_context(|| format!("failed to list archive '{}'", archive.display()))?;
    if !output.status.success() {
        bail!(
            "tar -tzf failed for '{}': stdout={} stderr={}",
            archive.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let mut members = HashSet::new();
    for raw in String::from_utf8_lossy(&output.stdout).lines() {
        let member = normalize_archive_member_name(raw);
        if member != "ay" && !member.starts_with("ay/") {
            bail!("member outside ay/ root: {raw}");
        }
        members.insert(member);
    }

    for required in ["ay/ay", "ay/run_solver.sh", "ay/LICENSE", "ay/README.md"] {
        if !members.contains(required) {
            bail!("missing required archive member: {required}");
        }
    }
    Ok(())
}

fn normalize_archive_member_name(name: &str) -> String {
    let normalized = name.trim_start_matches("./").trim_end_matches('/');
    if normalized.is_empty() {
        ".".to_string()
    } else {
        normalized.to_string()
    }
}

fn extract_archive(archive: &Path, prefix: &str) -> Result<PathBuf> {
    inspect_archive_members(archive)?;

    let dir = make_temp_dir(prefix)?;
    let output = Command::new("tar")
        .arg("-xzf")
        .arg(archive)
        .arg("-C")
        .arg(&dir)
        .output()
        .with_context(|| format!("failed to extract archive '{}'", archive.display()))?;
    if !output.status.success() {
        bail!(
            "tar -xzf failed for '{}': stdout={} stderr={}",
            archive.display(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    reject_symlinks_recursive(&dir)?;
    Ok(dir)
}

fn reject_symlinks_recursive(path: &Path) -> Result<()> {
    let meta = fs::symlink_metadata(path)
        .with_context(|| format!("failed to stat '{}'", path.display()))?;
    if meta.file_type().is_symlink() {
        bail!("archive extraction produced symlink: {}", path.display());
    }
    if meta.is_dir() {
        for entry in
            fs::read_dir(path).with_context(|| format!("failed to read '{}'", path.display()))?
        {
            let entry = entry.with_context(|| format!("failed to read '{}'", path.display()))?;
            reject_symlinks_recursive(&entry.path())?;
        }
    }
    Ok(())
}

fn sat_smoke(root: &Path) -> Result<()> {
    let temp = make_temp_dir("ay-sat-submission-gate")?;
    let input = temp.join("unsat.cnf");
    let proof_dir = temp.join("proof");
    fs::write(&input, "p cnf 1 2\n1 0\n-1 0\n")
        .with_context(|| format!("failed to write '{}'", input.display()))?;
    let output = Command::new(root.join("run.sh"))
        .arg(&input)
        .arg(&proof_dir)
        .output()
        .context("failed to run SAT wrapper")?;
    if output.status.code() != Some(20) {
        bail!(
            "expected exit 20, got {:?}; stdout={} stderr={}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let stdout = String::from_utf8_lossy(&output.stdout);
    if !stdout.contains("s UNSATISFIABLE") {
        bail!("SAT wrapper did not print UNSATISFIABLE: {stdout}");
    }
    if !proof_dir.join("proof.out").is_file() {
        bail!(
            "SAT wrapper did not write {}",
            proof_dir.join("proof.out").display()
        );
    }
    Ok(())
}

fn chc_smoke(root: &Path) -> Result<()> {
    let temp = make_temp_dir("ay-chc-submission-gate")?;
    let input = temp.join("safe.smt2");
    fs::write(
        &input,
        "(set-logic HORN)\n\
         (set-info :status sat)\n\
         (declare-fun Inv (Int) Bool)\n\
         (assert (forall ((x Int)) (=> (= x 0) (Inv x))))\n\
         (assert (forall ((x Int) (y Int)) (=> (and (Inv x) (<= x 10) (= y (+ x 1))) (Inv y))))\n\
         (assert (forall ((x Int)) (=> (and (Inv x) (> x 15)) false)))\n\
         (check-sat)\n",
    )
    .with_context(|| format!("failed to write '{}'", input.display()))?;
    let output = Command::new(root.join("run_solver.sh"))
        .arg(&input)
        .output()
        .context("failed to run CHC wrapper")?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let lines: Vec<&str> = stdout.lines().collect();
    if !output.status.success()
        || lines.len() != 1
        || !matches!(lines[0].trim(), "sat" | "unsat" | "unknown")
        || !stderr.is_empty()
    {
        bail!(
            "CHC wrapper smoke failed: exit={:?} stdout={} stderr={}",
            output.status.code(),
            stdout,
            stderr
        );
    }
    Ok(())
}

fn smt_archive_smoke(root: &Path, json_path: &Path) -> Result<()> {
    let json_text = fs::read_to_string(json_path)
        .with_context(|| format!("failed to read '{}'", json_path.display()))?;
    let json: serde_json::Value = serde_json::from_str(&json_text)
        .with_context(|| format!("failed to parse '{}'", json_path.display()))?;
    let single = command_binary(&json["command"]).context("SMT root command is invalid")?;
    let mv = participation_command(&json, "ModelValidation")
        .unwrap_or_else(|| "run_solver_mv.sh".to_string());
    let incr = participation_command(&json, "Incremental")
        .unwrap_or_else(|| "run_solver_incr.sh".to_string());
    ensure_relative_executable(root, &single)?;
    ensure_relative_executable(root, &mv)?;
    ensure_relative_executable(root, &incr)?;

    let temp = make_temp_dir("ay-smt-submission-gate")?;
    let input = temp.join("sat.smt2");
    fs::write(
        &input,
        "(set-logic QF_UF)\n(declare-const a Bool)\n(assert a)\n(check-sat)\n",
    )
    .with_context(|| format!("failed to write '{}'", input.display()))?;
    let output = Command::new(root.join(&single))
        .arg(&input)
        .output()
        .context("failed to run SMT wrapper")?;
    if !output.status.success()
        || String::from_utf8_lossy(&output.stdout).trim() != "sat"
        || !output.stderr.is_empty()
    {
        bail!(
            "SMT single-query smoke failed: exit={:?} stdout={} stderr={}",
            output.status.code(),
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let mv_input = temp.join("model.smt2");
    fs::write(
        &mv_input,
        "(set-option :produce-models true)\n(set-logic QF_UF)\n(declare-const a Bool)\n(assert a)\n(check-sat)\n(get-model)\n",
    )
    .with_context(|| format!("failed to write '{}'", mv_input.display()))?;
    let output = Command::new(root.join(&mv))
        .arg(&mv_input)
        .output()
        .context("failed to run SMT model-validation wrapper")?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    // The SMT-COMP wrappers run `ay --z3-mode`, which emits get-model as a bare
    // `( <define-fun>* )` sequence (z3 4.15.4 / SMT-LIB 2.6 parity, d0201aa2),
    // not the legacy `(model …)` head. Assert a real model binding was printed.
    if !output.status.success()
        || !stdout.lines().any(|line| line.trim() == "sat")
        || !stdout.contains("(define-fun ")
        || !output.stderr.is_empty()
    {
        bail!(
            "SMT model-validation smoke failed: exit={:?} stdout={} stderr={}",
            output.status.code(),
            stdout,
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let lra_input = temp.join("model-lra.smt2");
    fs::write(
        &lra_input,
        "(set-option :produce-models true)\n(set-logic QF_LRA)\n(declare-const x Real)\n(assert (= x (/ 3 2)))\n(check-sat)\n(get-model)\n",
    )
    .with_context(|| format!("failed to write '{}'", lra_input.display()))?;
    let output = Command::new(root.join(&mv))
        .arg(&lra_input)
        .output()
        .context("failed to run SMT QF_LRA model-validation wrapper")?;
    let stdout = String::from_utf8_lossy(&output.stdout);
    // Bare `( <define-fun>* )` model form under `--z3-mode` (see above).
    if !output.status.success()
        || !stdout.lines().any(|line| line.trim() == "sat")
        || !stdout.contains("(define-fun ")
        || !output.stderr.is_empty()
    {
        bail!(
            "SMT QF_LRA model-validation smoke failed: exit={:?} stdout={} stderr={}",
            output.status.code(),
            stdout,
            String::from_utf8_lossy(&output.stderr)
        );
    }

    smt_incremental_interactive_smoke(root, &incr)?;

    let mut child = Command::new(root.join(&incr))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("failed to spawn SMT incremental wrapper")?;
    child
        .stdin
        .as_mut()
        .context("failed to open SMT incremental stdin")?
        .write_all(
            b"(set-logic QF_UF)\n(set-option :print-success false)\n(declare-const a Bool)\n(push 1)\n(assert a)\n(check-sat)\n(pop 1)\n(check-sat)\n(exit)\n",
        )
        .context("failed to write SMT incremental input")?;
    let output = child
        .wait_with_output()
        .context("failed waiting for SMT incremental wrapper")?;
    let incremental_stdout = String::from_utf8_lossy(&output.stdout);
    let verdicts: Vec<&str> = incremental_stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect();
    if !output.status.success()
        || verdicts.as_slice() != ["sat", "sat"]
        || !output.stderr.is_empty()
    {
        bail!(
            "SMT incremental smoke failed: exit={:?} stdout={} stderr={}",
            output.status.code(),
            incremental_stdout,
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(())
}

fn smt_incremental_interactive_smoke(root: &Path, command: &str) -> Result<()> {
    let mut child = Command::new(root.join(command))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .context("failed to spawn SMT incremental interactive wrapper")?;
    let mut stdin = child
        .stdin
        .take()
        .context("failed to open SMT incremental interactive stdin")?;
    let stdout = child
        .stdout
        .take()
        .context("failed to open SMT incremental interactive stdout")?;
    let (tx, rx) = mpsc::channel();
    thread::spawn(move || {
        let mut reader = BufReader::new(stdout);
        let mut line = String::new();
        let result = reader.read_line(&mut line).map(|_| line);
        let _ = tx.send(result);
    });
    stdin
        .write_all(
            b"(set-logic QF_UF)\n(set-option :print-success false)\n(declare-const a Bool)\n(assert a)\n(check-sat)\n",
        )
        .context("failed to write first SMT incremental command")?;
    stdin
        .flush()
        .context("failed to flush SMT incremental stdin")?;
    let line = rx
        .recv_timeout(Duration::from_secs(3))
        .context("SMT incremental wrapper did not answer before EOF")?
        .context("failed to read SMT incremental stdout")?;
    let _ = child.kill();
    let output = child
        .wait_with_output()
        .context("failed waiting for SMT incremental interactive wrapper")?;
    if line.trim() != "sat" || !output.stderr.is_empty() {
        bail!(
            "SMT incremental interactive smoke failed: first-line={line:?} stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    Ok(())
}

fn command_binary(command: &serde_json::Value) -> Result<String> {
    if let Some(array) = command.as_array() {
        let first = array
            .first()
            .and_then(serde_json::Value::as_str)
            .context("command list must start with a binary string")?;
        return Ok(first.to_string());
    }
    if let Some(object) = command.as_object() {
        return object
            .get("binary")
            .and_then(serde_json::Value::as_str)
            .map(ToOwned::to_owned)
            .context("command object must contain binary");
    }
    bail!("command must be list or object")
}

fn participation_command(json: &serde_json::Value, track: &str) -> Option<String> {
    json.get("participations")?
        .as_array()?
        .iter()
        .find(|part| {
            part.get("tracks")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|tracks| tracks.iter().any(|value| value.as_str() == Some(track)))
        })
        .and_then(|part| part.get("command"))
        .and_then(|command| command_binary(command).ok())
}

fn ensure_relative_executable(root: &Path, command: &str) -> Result<()> {
    let command_path = Path::new(command);
    if command_path.is_absolute()
        || command_path
            .components()
            .any(|component| matches!(component, std::path::Component::ParentDir))
    {
        bail!("SMT command path must be relative and not traverse upward: {command}");
    }
    let resolved = root.join(command_path);
    if !resolved.is_file() {
        bail!(
            "SMT command target missing after archive extraction: {}",
            resolved.display()
        );
    }
    if !is_executable(&resolved) {
        bail!(
            "SMT command target is not executable: {}",
            resolved.display()
        );
    }
    let meta = fs::symlink_metadata(&resolved)
        .with_context(|| format!("failed to stat '{}'", resolved.display()))?;
    if meta.file_type().is_symlink() {
        bail!(
            "SMT command target must not be a symlink: {}",
            resolved.display()
        );
    }
    Ok(())
}

fn validate_smt_json(
    path: &Path,
    require_public_urls: bool,
    expected_archive_sha256: Option<&str>,
) -> Result<()> {
    let text =
        fs::read_to_string(path).with_context(|| format!("failed to read '{}'", path.display()))?;
    let value: serde_json::Value = serde_json::from_str(&text)
        .with_context(|| format!("failed to parse '{}'", path.display()))?;
    let root = value
        .as_object()
        .context("SMT submission JSON root must be an object")?;
    for key in root.keys() {
        if key.starts_with('_') {
            bail!("schema-invalid private key at root: {key}");
        }
    }
    require_string(root, "name")?;
    require_string(root, "website")?;
    require_string(root, "system_description")?;
    require_string(root, "solver_type")?;
    require_array(root, "contributors")?;
    require_array(root, "contacts")?;
    require_array(root, "command")?;
    require_array(root, "participations")?;
    let seed = root
        .get("seed")
        .and_then(serde_json::Value::as_i64)
        .context("SMT JSON seed must be an integer")?;
    if !(0..(1_i64 << 30)).contains(&seed) {
        bail!("SMT JSON seed out of accepted range: {seed}");
    }
    if root["solver_type"] != "Standalone" {
        bail!("ay SMT solver_type should be Standalone");
    }
    validate_smt_archive_hash(root.get("archive"), expected_archive_sha256, "root archive")?;
    for (idx, part) in root["participations"]
        .as_array()
        .context("participations must be array")?
        .iter()
        .enumerate()
    {
        let obj = part
            .as_object()
            .with_context(|| format!("participation {idx} must be object"))?;
        require_array(obj, "tracks")?;
        if let Some(command) = obj.get("command") {
            let binary = command_binary(command)
                .with_context(|| format!("participation {idx} command is invalid"))?;
            if binary.contains("%s") {
                bail!("participation {idx} command must not contain %s placeholder");
            }
        }
        if let Some(archive) = obj.get("archive") {
            validate_smt_archive_hash(
                Some(archive),
                expected_archive_sha256,
                "participation archive",
            )?;
        }
    }
    let archive_url = root
        .get("archive")
        .and_then(|archive| archive.get("url"))
        .and_then(serde_json::Value::as_str)
        .context("SMT archive.url is required")?;
    if archive_url.trim().is_empty() {
        bail!("SMT archive URL is empty");
    }
    if root.get("final").and_then(serde_json::Value::as_bool) == Some(true) {
        ensure_zenodo_url("SMT archive.url", archive_url)?;
        let system_description = root["system_description"]
            .as_str()
            .context("SMT system_description must be a URI string")?;
        ensure_zenodo_url("SMT system_description", system_description)?;
    }
    if require_public_urls {
        let system_description = root["system_description"]
            .as_str()
            .context("SMT system_description must be a URI string")?;
        if system_description.contains("PLACEHOLDER") || system_description.trim().is_empty() {
            bail!("SMT system_description is still a placeholder");
        }
        for (idx, part) in root["participations"]
            .as_array()
            .context("participations must be array")?
            .iter()
            .enumerate()
        {
            let Some(url) = part
                .get("archive")
                .and_then(|archive| archive.get("url"))
                .and_then(serde_json::Value::as_str)
            else {
                continue;
            };
            if url.contains("PLACEHOLDER") || url.trim().is_empty() {
                bail!("SMT participation {idx} archive URL is still a placeholder");
            }
        }
    }
    Ok(())
}

fn validate_smt_archive_hash(
    archive: Option<&serde_json::Value>,
    expected_archive_sha256: Option<&str>,
    label: &str,
) -> Result<()> {
    let Some(archive) = archive else {
        return Ok(());
    };
    let hash = archive
        .get("h")
        .and_then(|h| h.get("sha256"))
        .and_then(serde_json::Value::as_str)
        .with_context(|| format!("SMT {label} must contain h.sha256"))?;
    if hash.len() != 64
        || !hash
            .bytes()
            .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase())
    {
        bail!("SMT {label} has invalid sha256 digest: {hash}");
    }
    if let Some(expected) = expected_archive_sha256 {
        if hash != expected {
            bail!("SMT {label} sha256 {hash} does not match local archive {expected}");
        }
    }
    Ok(())
}

fn require_string(root: &serde_json::Map<String, serde_json::Value>, key: &str) -> Result<()> {
    if root.get(key).and_then(serde_json::Value::as_str).is_some() {
        Ok(())
    } else {
        bail!("SMT JSON field {key:?} must be a string")
    }
}

fn require_array(root: &serde_json::Map<String, serde_json::Value>, key: &str) -> Result<()> {
    if root
        .get(key)
        .and_then(serde_json::Value::as_array)
        .is_some()
    {
        Ok(())
    } else {
        bail!("SMT JSON field {key:?} must be an array")
    }
}

fn write_text(path: &Path, contents: &str, executable: bool) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create '{}'", parent.display()))?;
    }
    fs::write(path, contents).with_context(|| format!("failed to write '{}'", path.display()))?;
    if executable {
        set_executable(path)?;
    }
    Ok(())
}

#[cfg(unix)]
fn set_executable(path: &Path) -> Result<()> {
    use std::os::unix::fs::PermissionsExt;

    let mut perms = fs::metadata(path)
        .with_context(|| format!("failed to stat '{}'", path.display()))?
        .permissions();
    perms.set_mode(perms.mode() | 0o755);
    fs::set_permissions(path, perms)
        .with_context(|| format!("failed to chmod '{}'", path.display()))?;
    Ok(())
}

#[cfg(not(unix))]
fn set_executable(_path: &Path) -> Result<()> {
    Ok(())
}
