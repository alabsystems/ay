// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native launch benchmark packet metadata producer.

use anyhow::{bail, Context, Result};
use clap::{Args, Subcommand};
use serde_json::{json, Value};
use sha2::{Digest, Sha256};
use std::collections::HashSet;
use std::env;
use std::fmt::Write as _;
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::{Command as ProcessCommand, Stdio};

#[derive(Args, Clone)]
pub(crate) struct LaunchPacketCommand {
    #[command(subcommand)]
    command: Option<LaunchPacketSubcommand>,

    #[command(flatten)]
    run_args: LaunchPacketArgs,
}

#[derive(Subcommand, Clone)]
enum LaunchPacketSubcommand {
    /// Generate reviewer-facing INDEX.md for an evidence packet.
    Index(LaunchPacketIndexArgs),
}

#[derive(Args, Clone)]
#[command(after_help = "\
Native dry-run and metadata-only producer for launch benchmark packet sidecars.
Real benchmark execution still uses the full benchmark runner path; launch-gate
requires a run-mode summary.json for blocker clearance.")]
struct LaunchPacketArgs {
    /// Repository root to use for packet sidecars.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// ay binary to benchmark or describe.
    #[arg(long, default_value = "./target/release/ay")]
    ay: PathBuf,

    /// Per-benchmark timeout in seconds.
    #[arg(long, default_value = "30")]
    timeout: String,

    /// Runs per benchmark.
    #[arg(long, default_value_t = 1)]
    runs: u64,

    /// SMT reference solver for Z3-compat evals.
    #[arg(long, default_value = "z3")]
    reference_solver: String,

    /// Packet output directory.
    #[arg(long)]
    out_dir: Option<PathBuf>,

    /// Run only this launch eval; repeat for a subset.
    #[arg(long = "eval")]
    evals: Vec<String>,

    /// Omit this launch eval from the default packet; repeatable.
    #[arg(long)]
    exclude_eval: Vec<String>,

    /// Accepted for compatibility with the shell producer.
    #[arg(long)]
    skip_build: bool,

    /// Validate metadata, print planned commands, skip benchmarks.
    #[arg(long)]
    dry_run: bool,

    /// Validate metadata and write packet summaries, skip benchmarks.
    #[arg(long)]
    metadata_only: bool,

    /// Accepted for compatibility with the shell producer.
    #[arg(long)]
    resume: bool,
}

#[derive(Args, Clone)]
struct LaunchPacketIndexArgs {
    /// Evidence packet directory to index.
    #[arg(long)]
    packet_dir: PathBuf,

    /// AY repository root used for documentation link checks.
    #[arg(long)]
    repo_root: Option<PathBuf>,

    /// Index path to write. Defaults to PACKET_DIR/INDEX.md.
    #[arg(long)]
    output: Option<PathBuf>,

    /// Exact release commit. Defaults to packet evidence, then repo HEAD.
    #[arg(long)]
    release_commit: Option<String>,

    /// Human-readable public claim to record in the index.
    #[arg(long, default_value = "HN/Z3-successor public launch")]
    public_claim: String,

    /// UTC timestamp to record, mainly for deterministic tests.
    #[arg(long)]
    generated_at: Option<String>,

    /// Exit nonzero when required packet artifacts are missing.
    #[arg(long)]
    fail_on_missing: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FastPacketMode {
    DryRun,
    MetadataOnly,
}

impl FastPacketMode {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::DryRun => "dry-run",
            Self::MetadataOnly => "metadata-only",
        }
    }
}

pub(crate) struct FastPacketConfig {
    pub(crate) repo_root: PathBuf,
    pub(crate) ay: PathBuf,
    pub(crate) timeout: String,
    pub(crate) runs: u64,
    pub(crate) reference_solver: String,
    pub(crate) out_dir: Option<PathBuf>,
    pub(crate) requested_evals: Vec<String>,
    pub(crate) excluded_evals: Vec<String>,
    pub(crate) mode: FastPacketMode,
}

#[derive(Clone)]
struct EvalSpec {
    id: &'static str,
    uses_reference: bool,
}

const LAUNCH_EVALS: &[EvalSpec] = &[
    EvalSpec {
        id: "smt-local-suite",
        uses_reference: false,
    },
    EvalSpec {
        id: "smt-smtcomp-qf-lia",
        uses_reference: true,
    },
    EvalSpec {
        id: "smt-smtcomp-qf-lra",
        uses_reference: true,
    },
    EvalSpec {
        id: "smt-smtcomp-qf-bv",
        uses_reference: true,
    },
    EvalSpec {
        id: "smt-smtcomp-qf-abv",
        uses_reference: true,
    },
    EvalSpec {
        id: "chccomp-2025-extra-small-lia",
        uses_reference: false,
    },
    EvalSpec {
        id: "sat-par2-dev",
        uses_reference: false,
    },
    EvalSpec {
        id: "z3-perf-cliffs",
        uses_reference: true,
    },
];

pub(crate) fn run(command: &LaunchPacketCommand) -> Result<i32> {
    match &command.command {
        Some(LaunchPacketSubcommand::Index(args)) => run_index(args),
        None => run_packet(&command.run_args),
    }
}

fn run_packet(args: &LaunchPacketArgs) -> Result<i32> {
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    let mode = match (args.dry_run, args.metadata_only) {
        (true, false) => FastPacketMode::DryRun,
        (false, true) => FastPacketMode::MetadataOnly,
        (true, true) => bail!("launch packet: choose only one of --dry-run or --metadata-only"),
        (false, false) => {
            bail!(
                "launch packet: native benchmark execution is not enabled here; pass --dry-run or --metadata-only"
            )
        }
    };
    let out_dir = write_fast_packet(FastPacketConfig {
        repo_root: repo_root.clone(),
        ay: resolve_path_arg(&repo_root, &args.ay),
        timeout: args.timeout.clone(),
        runs: args.runs,
        reference_solver: args.reference_solver.clone(),
        out_dir: args
            .out_dir
            .as_ref()
            .map(|path| resolve_path_arg(&repo_root, path)),
        requested_evals: args.evals.clone(),
        excluded_evals: args.exclude_eval.clone(),
        mode,
    })?;
    eprintln!(
        "launch packet: {} complete; commands in {}/commands.log",
        mode.as_str(),
        out_dir.display()
    );
    Ok(0)
}

#[derive(Clone, Copy)]
struct ArtifactGroup {
    label: &'static str,
    candidates: &'static [&'static str],
    required: bool,
}

const STANDARD_DOCS: &[(&str, &str)] = &[
    ("HN launch readiness", "the development design notes"),
    (
        "Launch evidence packet checklist",
        "the development design notes",
    ),
    ("Z3 compatibility ledger", "the development design notes"),
    ("Proof trust boundary", "the development design notes"),
    ("Verification audit", "the development design notes"),
];

const ARTIFACT_GROUPS: &[ArtifactGroup] = &[
    ArtifactGroup {
        label: "public mirror evidence",
        candidates: &[
            "ay-public-commit-evidence.json",
            "public_ay_commit.json",
            "public-ay-commit.json",
        ],
        required: true,
    },
    ArtifactGroup {
        label: "release manifest",
        candidates: &["ay-release-manifest.json", "release-manifest.json"],
        required: true,
    },
    ArtifactGroup {
        label: "release manifest verification",
        candidates: &[
            "ay-release-manifest-verification.json",
            "release-manifest-verification.json",
        ],
        required: true,
    },
    ArtifactGroup {
        label: "HN launch gate summary",
        candidates: &[
            "hn-launch-gate-summary.json",
            "ay-hn-launch-gate-summary.json",
        ],
        required: true,
    },
    ArtifactGroup {
        label: "HN launch gate log",
        candidates: &["hn-launch-gate.log"],
        required: true,
    },
    ArtifactGroup {
        label: "benchmark packet summary",
        candidates: &["summary.json", "benchmark-summary.json"],
        required: true,
    },
    ArtifactGroup {
        label: "benchmark raw results",
        candidates: &["raw/*.json", "raw/**/*.json"],
        required: true,
    },
    ArtifactGroup {
        label: "downstream smoke summary",
        candidates: &[
            "consumer-smoke-summary.json",
            "downstream-smoke.json",
            "downstream-summary.json",
        ],
        required: true,
    },
    ArtifactGroup {
        label: "CLI proof verification evidence",
        candidates: &["z3-cli-proof-verify.json", "proof-cli-verify.json"],
        required: true,
    },
    ArtifactGroup {
        label: "CLI proof verification log",
        candidates: &["z3-cli-proof-verify.log", "proof-cli-verify.log"],
        required: true,
    },
    ArtifactGroup {
        label: "Alethe external replay summary",
        candidates: &["smt-alethe-external-replay.json", "alethe-replay.json"],
        required: true,
    },
    ArtifactGroup {
        label: "Lean proof replay summary",
        candidates: &["lean-proof-replay.json"],
        required: true,
    },
    ArtifactGroup {
        label: "CHC certificate replay summary",
        candidates: &["chc-certificate-replay.json"],
        required: true,
    },
    ArtifactGroup {
        label: "AUFLIA evidence or blocker note",
        candidates: &[
            "auflia-evidence.json",
            "auflia-evidence.md",
            "auflia-blocker.md",
        ],
        required: false,
    },
    ArtifactGroup {
        label: "copy-readiness note",
        candidates: &["copy-readiness.md", "launch-copy.md"],
        required: false,
    },
    ArtifactGroup {
        label: "skip log",
        candidates: &["skips.md", "skip-reasons.md", "skips.json"],
        required: false,
    },
];

fn run_index(args: &LaunchPacketIndexArgs) -> Result<i32> {
    let packet_dir = args
        .packet_dir
        .canonicalize()
        .unwrap_or_else(|_| args.packet_dir.clone());
    let repo_root = resolve_repo_root(args.repo_root.as_deref())?;
    if !packet_dir.is_dir() {
        eprintln!(
            "launch packet index: packet dir not found: {}",
            packet_dir.display()
        );
        return Ok(2);
    }

    let release_commit = args
        .release_commit
        .clone()
        .or_else(|| release_commit_from_packet(&packet_dir))
        .or_else(|| git_output(&repo_root, &["rev-parse", "HEAD"]))
        .unwrap_or_else(|| "<unknown>".to_string());
    let generated_at = args.generated_at.clone().unwrap_or_else(utc_timestamp);
    let output_path = args
        .output
        .clone()
        .unwrap_or_else(|| packet_dir.join("INDEX.md"));
    let (content, missing_required) = render_index(
        &packet_dir,
        &repo_root,
        &release_commit,
        &generated_at,
        &args.public_claim,
    );

    if let Some(parent) = output_path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .with_context(|| format!("failed to create {}", parent.display()))?;
        }
    }
    fs::write(&output_path, format!("{content}\n"))
        .with_context(|| format!("failed to write {}", output_path.display()))?;

    if args.fail_on_missing && !missing_required.is_empty() {
        eprintln!(
            "launch packet index: missing required artifacts: {}",
            missing_required.join(", ")
        );
        return Ok(1);
    }
    Ok(0)
}

fn render_index(
    packet_dir: &Path,
    repo_root: &Path,
    release_commit: &str,
    generated_at: &str,
    public_claim: &str,
) -> (String, Vec<String>) {
    let mut missing_required = Vec::new();
    let mut lines = vec![
        "# AY Launch Evidence Packet Index".to_string(),
        String::new(),
        format!("- Generated: `{generated_at}`"),
        format!("- Packet directory: `{}`", packet_dir.display()),
        format!("- Release commit: `{release_commit}`"),
        format!("- Intended public claim: {public_claim}"),
        String::new(),
        "## Required Reading".to_string(),
        String::new(),
    ];

    for (label, doc_path) in STANDARD_DOCS {
        if repo_root.join(doc_path).exists() {
            lines.push(format!("- {label}: `{doc_path}`"));
        } else {
            lines.push(format!("- {label}: MISSING `{doc_path}`"));
        }
    }

    lines.extend([
        String::new(),
        "## Artifact Inventory".to_string(),
        String::new(),
        "| Artifact | Status | Paths |".to_string(),
        "|----------|--------|-------|".to_string(),
    ]);

    for group in ARTIFACT_GROUPS {
        let matches = first_existing(packet_dir, group.candidates);
        if matches.is_empty() {
            let status = if group.required {
                "MISSING"
            } else {
                "not supplied"
            };
            lines.push(format!(
                "| {} | `{status}` | Expected one of `{}` |",
                group.label,
                group.candidates.join(", ")
            ));
            if group.required {
                missing_required.push(group.label.to_string());
            }
            continue;
        }

        let status = json_status(&matches[0]);
        let mut shown = matches
            .iter()
            .take(8)
            .map(|path| markdown_link(&rel_path(path, packet_dir)))
            .collect::<Vec<_>>()
            .join(", ");
        if matches.len() > 8 {
            shown.push_str(&format!(", and {} more", matches.len() - 8));
        }
        lines.push(format!("| {} | `{status}` | {shown} |", group.label));
    }

    lines.extend([String::new(), "## Gate Summary".to_string(), String::new()]);
    lines.extend(render_blocker_summary(packet_dir));
    lines.extend([
        String::new(),
        "## Final Copy Guardrail".to_string(),
        String::new(),
        "Do not publish a public HN/Z3-successor claim from this packet until `hn-launch-gate-summary.json` reports `status: pass`, `evidence_gate_failures: 0`, and `launch_blocker_count: 0`, and the public mirror evidence plus release manifest both name the exact release commit above. If any required artifact is missing, stale, or blocked, describe the packet as private or public-candidate evidence.".to_string(),
        String::new(),
        "## Native Gate Replay".to_string(),
        String::new(),
        "A third-party reviewer with the packet and repo checkout can replay the portable gate with `ay launch-gate --help` for option details. The packet files above are evidence inputs except public mirror evidence, which must be regenerated with `--check-public-mirror` for the final public release check.".to_string(),
        String::new(),
    ]);

    (lines.join("\n"), missing_required)
}

fn render_blocker_summary(packet_dir: &Path) -> Vec<String> {
    for path in first_existing(
        packet_dir,
        &[
            "hn-launch-gate-summary.json",
            "ay-hn-launch-gate-summary.json",
        ],
    ) {
        let Some(value) = read_json_object(&path) else {
            continue;
        };
        let status = json_text(value.get("status"), "unknown");
        let blocker_count = json_text(value.get("launch_blocker_count"), "null");
        let evidence_failures = json_text(value.get("evidence_gate_failures"), "null");
        let advisory_failures = json_text(value.get("advisory_failures"), "null");
        let mut lines = vec![format!(
            "- HN gate summary {}: status `{status}`, launch blockers `{blocker_count}`, evidence failures `{evidence_failures}`, advisory failures `{advisory_failures}`.",
            markdown_link(&rel_path(&path, packet_dir))
        )];
        if let Some(blockers) = value.get("blockers").and_then(Value::as_array) {
            if !blockers.is_empty() {
                lines.extend([
                    String::new(),
                    "| Blocker | Detail |".to_string(),
                    "|---------|--------|".to_string(),
                ]);
                for row in blockers {
                    let Some(row) = row.as_object() else {
                        continue;
                    };
                    let name = json_text(row.get("name"), "<unnamed>");
                    let detail = json_text(row.get("detail").or_else(|| row.get("reason")), "")
                        .replace('\n', " ");
                    let detail = if detail.is_empty() {
                        "See summary JSON.".to_string()
                    } else {
                        detail
                    };
                    lines.push(format!("| `{name}` | {detail} |"));
                }
            }
        }
        return lines;
    }
    vec!["- No HN launch gate summary JSON found in this packet.".to_string()]
}

fn release_commit_from_packet(packet_dir: &Path) -> Option<String> {
    for path in first_existing(
        packet_dir,
        &["ay-release-manifest.json", "release-manifest.json"],
    ) {
        let Some(value) = read_json_object(&path) else {
            continue;
        };
        for keys in [
            &["private", "ay_commit"][..],
            &["release", "private_commit"][..],
            &["public", "ay_commit"][..],
        ] {
            if let Some(commit) = nested_json_string(&value, keys) {
                return Some(commit);
            }
        }
    }

    for path in first_existing(
        packet_dir,
        &[
            "ay-public-commit-evidence.json",
            "public_ay_commit.json",
            "public-ay-commit.json",
        ],
    ) {
        let Some(value) = read_json_object(&path) else {
            continue;
        };
        for key in ["expected_commit", "commit", "ref_commit"] {
            if let Some(commit) = value.get(key).and_then(Value::as_str) {
                if !commit.is_empty() {
                    return Some(commit.to_string());
                }
            }
        }
    }
    None
}

fn nested_json_string(value: &Value, keys: &[&str]) -> Option<String> {
    let mut current = value;
    for key in keys {
        current = current.get(*key)?;
    }
    current
        .as_str()
        .filter(|text| !text.is_empty())
        .map(str::to_string)
}

fn json_status(path: &Path) -> String {
    let Some(value) = read_json_object(path) else {
        return "present".to_string();
    };
    value
        .get("status")
        .and_then(Value::as_str)
        .filter(|status| !status.is_empty())
        .or_else(|| {
            value
                .get("schema")
                .and_then(Value::as_str)
                .filter(|schema| !schema.is_empty())
        })
        .unwrap_or("present")
        .to_string()
}

fn read_json_object(path: &Path) -> Option<Value> {
    let value: Value = serde_json::from_slice(&fs::read(path).ok()?).ok()?;
    value.is_object().then_some(value)
}

fn first_existing(packet_dir: &Path, candidates: &[&str]) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let mut seen = HashSet::new();
    for candidate in candidates {
        for path in matching_candidate_paths(packet_dir, candidate) {
            let resolved = path.canonicalize().unwrap_or_else(|_| path.clone());
            if seen.insert(resolved) {
                found.push(path);
            }
        }
    }
    found
}

fn matching_candidate_paths(packet_dir: &Path, candidate: &str) -> Vec<PathBuf> {
    let mut paths = match candidate {
        "raw/*.json" => json_files_in_dir(&packet_dir.join("raw"), false),
        "raw/**/*.json" => json_files_in_dir(&packet_dir.join("raw"), true),
        _ if candidate.contains('*') => Vec::new(),
        _ => {
            let path = packet_dir.join(candidate);
            if path.is_file() {
                vec![path]
            } else {
                Vec::new()
            }
        }
    };
    paths.sort();
    paths
}

fn json_files_in_dir(dir: &Path, recursive: bool) -> Vec<PathBuf> {
    let mut paths = Vec::new();
    collect_json_files(dir, recursive, &mut paths);
    paths
}

fn collect_json_files(dir: &Path, recursive: bool, paths: &mut Vec<PathBuf>) {
    let Ok(entries) = fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_file()
            && path
                .extension()
                .is_some_and(|extension| extension == "json")
        {
            paths.push(path);
        } else if recursive && path.is_dir() {
            collect_json_files(&path, true, paths);
        }
    }
}

fn rel_path(path: &Path, root: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .replace(std::path::MAIN_SEPARATOR, "/")
}

fn markdown_link(path: &str) -> String {
    format!("[{path}]({path})")
}

fn json_text(value: Option<&Value>, default: &str) -> String {
    match value {
        Some(Value::String(text)) => text.clone(),
        Some(Value::Number(number)) => number.to_string(),
        Some(Value::Bool(value)) => value.to_string(),
        Some(Value::Null) | None => default.to_string(),
        Some(other) => other.to_string(),
    }
}

pub(crate) fn write_fast_packet(config: FastPacketConfig) -> Result<PathBuf> {
    validate_positive_timeout(&config.timeout)?;
    if config.runs == 0 {
        bail!("launch packet: --runs must be a positive integer");
    }
    if !is_executable(&config.ay) {
        bail!(
            "launch packet: fast metadata modes require an executable --ay: {}",
            config.ay.display()
        );
    }
    let reference_solver_path =
        resolve_command_or_path_from(&config.repo_root, &config.reference_solver).with_context(
            || {
                format!(
                    "launch packet: reference solver not found: {}",
                    config.reference_solver
                )
            },
        )?;

    let out_dir = config.out_dir.clone().unwrap_or_else(|| {
        config
            .repo_root
            .join("evals/launch-packets")
            .join(compact_timestamp())
    });
    fs::create_dir_all(out_dir.join("raw"))
        .with_context(|| format!("failed to create {}", out_dir.display()))?;

    let active_evals = active_evals(&config.requested_evals, &config.excluded_evals)?;
    let registry_validation =
        validate_registered_evals(&config.repo_root, &config.ay, &active_evals)?;
    let launch_scope = if config.requested_evals.is_empty() && config.excluded_evals.is_empty() {
        "default"
    } else {
        fs::write(out_dir.join("packet_scope.txt"), "subset\n")?;
        "subset"
    };

    let repo_commit = git_output(&config.repo_root, &["rev-parse", "HEAD"]);
    let git_status_short = git_output(&config.repo_root, &["status", "--short"])
        .unwrap_or_default()
        .lines()
        .map(str::to_string)
        .collect::<Vec<_>>();
    let git_clean = git_status_short.is_empty();
    let ay_sha256 = sha256_file_hex(&config.ay)?;
    let ay_version = command_output(&config.repo_root, &config.ay, &["--version"]);
    let reference_version = command_output(
        &config.repo_root,
        Path::new(&reference_solver_path),
        &["--version"],
    );
    let bench_progress_every = bench_progress_every_value()?;

    let planned_rows = active_evals
        .iter()
        .map(|eval| {
            let command = eval_command(
                &config.ay,
                eval,
                &config.timeout,
                config.runs,
                &config.reference_solver,
            );
            (eval.clone(), command)
        })
        .collect::<Vec<_>>();

    write_planned_evals(&out_dir, &planned_rows)?;
    write_input_inventory(&out_dir, &config.repo_root, &planned_rows)?;
    write_commands_log(&out_dir, &planned_rows)?;
    if config.mode == FastPacketMode::DryRun {
        for (eval, command) in &planned_rows {
            eprintln!("launch packet: {}", eval.id);
            eprintln!("dry-run: {}", shell_command_without_prompt(command));
        }
    } else {
        for (eval, _) in &planned_rows {
            eprintln!("launch packet: {}", eval.id);
        }
    }

    let launch_command = launch_command_string(&config);
    let provenance = json!({
        "schema": "ay-launch-benchmark-provenance/v1",
        "generated_at_utc": utc_timestamp(),
        "mode": config.mode.as_str(),
        "evidence_role": "wiring-only: benchmarks were not executed",
        "launch_command": launch_command,
        "repo": {
            "root": config.repo_root,
            "commit": repo_commit,
            "clean": git_clean,
            "git_status_short": git_status_short,
        },
        "tools": {
            "ay": {
                "command": config.ay,
                "resolved_path": canonical_display(&config.ay),
                "sha256": ay_sha256,
                "version": ay_version,
            },
            "reference_solver": {
                "command": config.reference_solver,
                "resolved_path": reference_solver_path,
                "version": reference_version,
            },
        },
        "parameters": {
            "timeout_seconds": config.timeout,
            "runs": config.runs,
            "results_root": env::var("AY_LAUNCH_RESULTS_DIR").unwrap_or_else(|_| "evals/results".to_string()),
            "bench_progress_every": bench_progress_every,
            "parallelism": "ay bench default",
            "seed_policy": "no explicit seed; solver defaults",
        },
        "selection": {
            "launch_scope": launch_scope,
            "requested_evals": config.requested_evals,
            "excluded_evals": config.excluded_evals.iter().map(|eval_id| {
                json!({"eval_id": eval_id, "reason": exclusion_reason(eval_id)})
            }).collect::<Vec<_>>(),
            "registry_validation": registry_validation,
            "active_eval_count": planned_rows.len(),
            "active_evals": planned_rows.iter().map(|(eval, command)| {
                json!({
                    "eval_id": eval.id,
                    "uses_reference_solver": eval.uses_reference,
                    "command": shell_command_line(command),
                })
            }).collect::<Vec<_>>(),
            "subset_reason": if !config.requested_evals.is_empty() {
                "operator-requested explicit eval subset"
            } else if !config.excluded_evals.is_empty() {
                "operator-requested eval exclusion"
            } else {
                "default launch eval set"
            },
        },
        "artifact_paths": artifact_paths_json(&out_dir),
    });
    write_json(&out_dir.join("provenance.json"), &provenance)?;
    write_provenance_txt(
        &out_dir,
        &launch_command,
        &provenance,
        &config,
        launch_scope,
    )?;

    let summary = fast_summary(
        &out_dir,
        &provenance,
        &planned_rows,
        config.mode,
        launch_scope,
    );
    write_json(&out_dir.join("summary.json"), &summary)?;
    write_summary_md(&out_dir, config.mode, &summary)?;
    add_artifact_index_and_self_validation(&out_dir)?;
    Ok(out_dir)
}

fn active_evals(requested: &[String], excluded: &[String]) -> Result<Vec<EvalSpec>> {
    for eval_id in requested.iter().chain(excluded) {
        if !LAUNCH_EVALS.iter().any(|spec| spec.id == eval_id) {
            bail!("launch packet: eval is not in the launch packet allow-list: {eval_id}");
        }
    }
    let active = LAUNCH_EVALS
        .iter()
        .filter(|spec| requested.is_empty() || requested.iter().any(|eval| eval == spec.id))
        .filter(|spec| !excluded.iter().any(|eval| eval == spec.id))
        .cloned()
        .collect::<Vec<_>>();
    if active.is_empty() {
        bail!("launch packet: selected launch packet subset is empty");
    }
    Ok(active)
}

fn validate_registered_evals(repo_root: &Path, ay: &Path, active: &[EvalSpec]) -> Result<Value> {
    let command = vec![
        ay.display().to_string(),
        "bench".to_string(),
        "list".to_string(),
    ];
    let Some(registered) = registered_eval_ids(repo_root, ay) else {
        bail!(
            "launch packet: could not load registered evals from {} bench list at {}",
            ay.display(),
            repo_root.display()
        );
    };
    let missing = active
        .iter()
        .filter(|eval| !registered.contains(eval.id))
        .map(|eval| eval.id)
        .collect::<Vec<_>>();
    if !missing.is_empty() {
        bail!(
            "launch packet: eval not registered by {}: {}",
            ay.display(),
            missing.join(", ")
        );
    }
    Ok(json!({
        "source": "ay bench list",
        "command": shell_command_line(&command),
        "status": "pass",
        "registered_eval_count": registered.len(),
        "validated_eval_count": active.len(),
    }))
}

fn registered_eval_ids(repo_root: &Path, ay: &Path) -> Option<HashSet<String>> {
    let output = ProcessCommand::new(ay)
        .current_dir(repo_root)
        .args(["bench", "list"])
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .output()
        .ok()?;
    if !output.status.success() {
        return registered_eval_ids_from_registry(repo_root);
    }
    let mut ids = HashSet::new();
    for line in String::from_utf8_lossy(&output.stdout).lines() {
        let trimmed = line.trim();
        if trimmed.is_empty()
            || trimmed.starts_with('-')
            || trimmed.starts_with("Eval ID")
            || trimmed.starts_with("No evals found")
        {
            continue;
        }
        if let Some(eval_id) = trimmed.split_whitespace().next() {
            ids.insert(eval_id.to_string());
        }
    }
    if !ids.is_empty() {
        return Some(ids);
    }
    registered_eval_ids_from_registry(repo_root)
}

fn registered_eval_ids_from_registry(repo_root: &Path) -> Option<HashSet<String>> {
    let registry_dir =
        env::var("AY_LAUNCH_REGISTRY_DIR").unwrap_or_else(|_| "evals/registry".to_string());
    let registry_path = resolve_path_arg(repo_root, Path::new(&registry_dir));
    let entries = fs::read_dir(&registry_path).ok()?;
    let mut ids = HashSet::new();
    for entry in entries.flatten() {
        let path = entry.path();
        let extension = path.extension().and_then(|extension| extension.to_str());
        if !matches!(extension, Some("yaml" | "yml")) {
            continue;
        }
        if let Some(eval_id) = registry_eval_id(&path) {
            ids.insert(eval_id);
        }
    }
    (!ids.is_empty()).then_some(ids)
}

fn registry_eval_id(path: &Path) -> Option<String> {
    let text = fs::read_to_string(path).ok()?;
    for line in text.lines() {
        let trimmed = line.trim();
        let Some(raw_id) = trimmed.strip_prefix("id:") else {
            continue;
        };
        let eval_id = raw_id.trim().trim_matches('"').trim_matches('\'');
        if !eval_id.is_empty() {
            return Some(eval_id.to_string());
        }
    }
    path.file_stem()
        .and_then(|stem| stem.to_str())
        .filter(|stem| !stem.is_empty())
        .map(str::to_string)
}

fn bench_progress_every_value() -> Result<u64> {
    let raw = env::var("AY_BENCH_PROGRESS_EVERY").unwrap_or_else(|_| "1".to_string());
    if raw.is_empty() || raw.starts_with('0') || !raw.bytes().all(|byte| byte.is_ascii_digit()) {
        bail!("launch packet: AY_BENCH_PROGRESS_EVERY must be a positive integer: {raw}");
    }
    raw.parse::<u64>().with_context(|| {
        format!("launch packet: AY_BENCH_PROGRESS_EVERY must be an integer: {raw}")
    })
}

fn eval_command(
    ay: &Path,
    eval: &EvalSpec,
    timeout: &str,
    runs: u64,
    reference_solver: &str,
) -> Vec<String> {
    let mut command = vec![
        ay.display().to_string(),
        "bench".to_string(),
        "run".to_string(),
        eval.id.to_string(),
        "--ay".to_string(),
        ay.display().to_string(),
        "--timeout".to_string(),
        timeout.to_string(),
        "--runs".to_string(),
        runs.to_string(),
    ];
    if eval.uses_reference {
        command.push("--reference-solver".to_string());
        command.push(reference_solver.to_string());
    }
    command
}

fn write_planned_evals(out_dir: &Path, rows: &[(EvalSpec, Vec<String>)]) -> Result<()> {
    let text = rows.iter().fold(String::new(), |mut out, (eval, _)| {
        let _ = writeln!(out, "{}\t{}", eval.id, eval.uses_reference);
        out
    });
    fs::write(out_dir.join("planned_evals.tsv"), text)?;
    Ok(())
}

#[derive(Default)]
struct RegistryInput {
    benchmarks_dir: Option<String>,
    suite_dirs: Vec<String>,
    setup_download: Option<String>,
    setup_note: Option<String>,
    public_source: Option<String>,
}

#[derive(Default)]
struct FileCounts {
    file_count: u64,
    smt2_count: u64,
    cnf_count: u64,
    yml_count: u64,
}

fn parse_registry_input(registry_path: &Path) -> Result<RegistryInput> {
    let text = match fs::read_to_string(registry_path) {
        Ok(text) => text,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            return Ok(RegistryInput::default());
        }
        Err(error) => {
            return Err(error).with_context(|| format!("read {}", registry_path.display()));
        }
    };

    let mut benchmarks_dir = None;
    let mut suite_dirs = Vec::new();
    let mut setup_download = None;
    let mut setup_note_lines = Vec::new();
    let mut in_suite_dirs = false;
    let mut in_setup_note = false;

    for line in text.lines() {
        let trimmed_start = line.trim_start();
        let trimmed = line.trim();
        if let Some(value) = yaml_scalar_after(trimmed_start, "benchmarks_dir:") {
            benchmarks_dir = Some(value);
            in_suite_dirs = false;
            in_setup_note = false;
            continue;
        }
        if let Some(value) = yaml_scalar_after(trimmed_start, "download:") {
            setup_download = Some(value);
            in_suite_dirs = false;
            in_setup_note = false;
            continue;
        }
        if let Some(value) = yaml_note_after(trimmed_start) {
            if !value.is_empty() {
                setup_note_lines.push(value);
            }
            in_suite_dirs = false;
            in_setup_note = true;
            continue;
        }
        if trimmed_start == "suite_dirs:" {
            in_suite_dirs = true;
            in_setup_note = false;
            continue;
        }
        if in_suite_dirs {
            if let Some(value) = trimmed_start.strip_prefix("- ") {
                suite_dirs.push(strip_yaml_quotes(value.trim()));
                continue;
            }
            if !trimmed.is_empty() && !is_indented(line) {
                in_suite_dirs = false;
            }
        }
        if in_setup_note {
            if is_indented(line) && !trimmed.is_empty() {
                setup_note_lines.push(trimmed.to_string());
                continue;
            }
            if !trimmed.is_empty() && !is_indented(line) {
                in_setup_note = false;
            }
        }
    }

    let public_source = benchmarks_dir
        .as_deref()
        .and_then(public_source_for_benchmarks_dir);
    Ok(RegistryInput {
        benchmarks_dir,
        suite_dirs,
        setup_download,
        setup_note: (!setup_note_lines.is_empty()).then(|| setup_note_lines.join(" ")),
        public_source,
    })
}

fn yaml_scalar_after(line: &str, key: &str) -> Option<String> {
    line.strip_prefix(key)
        .map(str::trim)
        .filter(|value| !value.is_empty())
        .map(strip_yaml_quotes)
}

fn yaml_note_after(line: &str) -> Option<String> {
    let raw = line.strip_prefix("note:")?.trim();
    let value = raw.strip_prefix('>').unwrap_or(raw).trim();
    Some(strip_yaml_quotes(value))
}

fn strip_yaml_quotes(value: &str) -> String {
    value
        .trim()
        .trim_matches(|ch| ch == '"' || ch == '\'')
        .to_string()
}

fn is_indented(line: &str) -> bool {
    line.starts_with(' ') || line.starts_with('\t')
}

fn public_source_for_benchmarks_dir(benchmarks_dir: &str) -> Option<String> {
    let logic = benchmarks_dir
        .split_once("benchmarks/smtcomp/")?
        .1
        .split('/')
        .next()
        .filter(|logic| !logic.is_empty())?;
    Some(format!(
        "https://zenodo.org/api/records/11061097/files/{logic}.tar.zst/content"
    ))
}

fn input_dir_records(repo_root: &Path, registry: &RegistryInput) -> Vec<Value> {
    let mut records = Vec::new();
    if let Some(benchmarks_dir) = &registry.benchmarks_dir {
        records.push(dir_record(
            repo_root,
            Some(benchmarks_dir),
            "benchmarks_dir",
        ));
        for suite_dir in &registry.suite_dirs {
            let display_path = Path::new(benchmarks_dir)
                .join(suite_dir)
                .display()
                .to_string();
            records.push(dir_record(repo_root, Some(&display_path), "suite_dir"));
        }
    } else {
        records.push(dir_record(repo_root, None, "benchmarks_dir"));
    }
    records
}

fn dir_record(repo_root: &Path, display_path: Option<&str>, role: &str) -> Value {
    let actual_path = display_path.map(|path| {
        let path = Path::new(path);
        if path.is_absolute() {
            path.to_path_buf()
        } else {
            repo_root.join(path)
        }
    });
    let exists = actual_path.as_deref().map(Path::is_dir).unwrap_or(false);
    let counts = actual_path
        .as_deref()
        .filter(|_| exists)
        .map(count_files_recursive)
        .unwrap_or_default();
    json!({
        "path": display_path,
        "role": role,
        "exists": exists,
        "file_count": counts.file_count,
        "smt2_count": counts.smt2_count,
        "cnf_count": counts.cnf_count,
        "yml_count": counts.yml_count,
    })
}

fn count_files_recursive(path: &Path) -> FileCounts {
    let mut counts = FileCounts::default();
    count_files_recursive_into(path, &mut counts);
    counts
}

fn count_files_recursive_into(path: &Path, counts: &mut FileCounts) {
    let Ok(entries) = fs::read_dir(path) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        let Ok(metadata) = entry.metadata() else {
            continue;
        };
        if metadata.is_dir() {
            count_files_recursive_into(&path, counts);
        } else if metadata.is_file() {
            counts.file_count += 1;
            match path.extension().and_then(|extension| extension.to_str()) {
                Some("smt2") => counts.smt2_count += 1,
                Some("cnf") => counts.cnf_count += 1,
                Some("yml" | "yaml") => counts.yml_count += 1,
                _ => {}
            }
        }
    }
}

fn write_input_inventory(
    out_dir: &Path,
    repo_root: &Path,
    rows: &[(EvalSpec, Vec<String>)],
) -> Result<()> {
    let registry_dir =
        env::var("AY_LAUNCH_REGISTRY_DIR").unwrap_or_else(|_| "evals/registry".to_string());
    let registry_dir_display = PathBuf::from(&registry_dir);
    let mut text = String::new();
    for (eval, _) in rows {
        let registry_display_path = registry_dir_display.join(format!("{}.yaml", eval.id));
        let registry_path = resolve_path_arg(repo_root, &registry_display_path);
        let registry = parse_registry_input(&registry_path)?;
        let input_dirs = input_dir_records(repo_root, &registry);
        let root = input_dirs.first();
        text.push_str(&serde_json::to_string(&json!({
            "eval_id": eval.id,
            "registry": registry_display_path.display().to_string(),
            "registry_path": registry_path,
            "registry_exists": registry_path.exists(),
            "benchmarks_dir": registry.benchmarks_dir,
            "suite_dirs": registry.suite_dirs,
            "setup_download": registry.setup_download,
            "setup_note": registry.setup_note,
            "public_source": registry.public_source,
            "benchmarks_dir_exists": root.and_then(|row| row.get("exists")).and_then(Value::as_bool).unwrap_or(false),
            "file_count": root.and_then(|row| row.get("file_count")).and_then(Value::as_u64).unwrap_or(0),
            "smt2_count": root.and_then(|row| row.get("smt2_count")).and_then(Value::as_u64).unwrap_or(0),
            "cnf_count": root.and_then(|row| row.get("cnf_count")).and_then(Value::as_u64).unwrap_or(0),
            "yml_count": root.and_then(|row| row.get("yml_count")).and_then(Value::as_u64).unwrap_or(0),
            "input_dirs": input_dirs,
        }))?);
        text.push('\n');
    }
    fs::write(out_dir.join("input_inventory.jsonl"), text)?;
    Ok(())
}

fn write_commands_log(out_dir: &Path, rows: &[(EvalSpec, Vec<String>)]) -> Result<()> {
    let text = rows.iter().fold(String::new(), |mut out, (_, command)| {
        let _ = writeln!(out, "{}", shell_command_line(command));
        out
    });
    fs::write(out_dir.join("commands.log"), text)?;
    Ok(())
}

fn fast_summary(
    out_dir: &Path,
    provenance: &Value,
    rows: &[(EvalSpec, Vec<String>)],
    mode: FastPacketMode,
    launch_scope: &str,
) -> Value {
    let commands = rows
        .iter()
        .map(|(_, command)| shell_command_line(command))
        .collect::<Vec<_>>();
    let planned = rows
        .iter()
        .enumerate()
        .map(|(index, (eval, _))| {
            json!({
                "eval_id": eval.id,
                "uses_reference_solver": eval.uses_reference,
                "command": commands[index],
            })
        })
        .collect::<Vec<_>>();
    json!({
        "schema": "ay-launch-benchmark-packet/v1",
        "mode": mode.as_str(),
        "benchmarks_executed": false,
        "launch_scope": launch_scope,
        "failure_policy": "not evaluated: this packet records provenance, registry validation, and planned commands only",
        "failure_count": Value::Null,
        "planned_eval_count": planned.len(),
        "planned_evals": planned,
        "commands": commands,
        "provenance_json": out_dir.join("provenance.json"),
        "git_commit": provenance.pointer("/repo/commit").cloned().unwrap_or(Value::Null),
        "git_clean": provenance.pointer("/repo/clean").cloned().unwrap_or(Value::Null),
        "tools": provenance.get("tools").cloned().unwrap_or(Value::Null),
        "selection": provenance.get("selection").cloned().unwrap_or(Value::Null),
        "artifact_paths": provenance.get("artifact_paths").cloned().unwrap_or(Value::Null),
    })
}

fn write_summary_md(out_dir: &Path, mode: FastPacketMode, summary: &Value) -> Result<()> {
    let title_mode = match mode {
        FastPacketMode::DryRun => "Dry Run",
        FastPacketMode::MetadataOnly => "Metadata Only",
    };
    let mut lines = vec![
        format!("# AY Launch Benchmark Packet ({title_mode})"),
        String::new(),
        "- Benchmarks executed: no".to_string(),
        "- Failure count: not evaluated".to_string(),
        format!(
            "- Git clean: {}",
            summary
                .get("git_clean")
                .and_then(Value::as_bool)
                .map(|value| value.to_string())
                .unwrap_or_else(|| "null".to_string())
        ),
        format!(
            "- Provenance JSON: `{}`",
            out_dir.join("provenance.json").display()
        ),
        format!(
            "- Planned evals: {}",
            summary
                .get("planned_eval_count")
                .and_then(Value::as_u64)
                .unwrap_or_default()
        ),
        String::new(),
        "| Eval | Reference solver |".to_string(),
        "|------|------------------|".to_string(),
    ];
    if let Some(planned) = summary.get("planned_evals").and_then(Value::as_array) {
        for row in planned {
            lines.push(format!(
                "| {} | {} |",
                row.get("eval_id").and_then(Value::as_str).unwrap_or(""),
                if row
                    .get("uses_reference_solver")
                    .and_then(Value::as_bool)
                    .unwrap_or(false)
                {
                    "yes"
                } else {
                    "no"
                }
            ));
        }
    }
    lines.extend([
        String::new(),
        "Commands are in `commands.log`; provenance is in `provenance.txt` and `provenance.json`."
            .to_string(),
    ]);
    fs::write(out_dir.join("summary.md"), lines.join("\n") + "\n")?;
    Ok(())
}

fn artifact_paths_json(out_dir: &Path) -> Value {
    json!({
        "provenance_txt": out_dir.join("provenance.txt"),
        "provenance_json": out_dir.join("provenance.json"),
        "commands_log": out_dir.join("commands.log"),
        "planned_evals_tsv": out_dir.join("planned_evals.tsv"),
        "input_inventory_jsonl": out_dir.join("input_inventory.jsonl"),
        "summary_json": out_dir.join("summary.json"),
        "summary_md": out_dir.join("summary.md"),
        "raw_dir": out_dir.join("raw"),
    })
}

fn add_artifact_index_and_self_validation(out_dir: &Path) -> Result<()> {
    let summary_path = out_dir.join("summary.json");
    let mut summary = read_json(&summary_path)?;
    let sidecars = [
        ("provenance_txt", "provenance.txt"),
        ("provenance_json", "provenance.json"),
        ("commands_log", "commands.log"),
        ("planned_evals_tsv", "planned_evals.tsv"),
        ("input_inventory_jsonl", "input_inventory.jsonl"),
        ("summary_md", "summary.md"),
    ];
    let mut artifacts = Vec::new();
    for (role, file_name) in sidecars {
        artifacts.push(artifact_record(&out_dir.join(file_name), role, None)?);
    }
    let missing_count = artifacts
        .iter()
        .filter(|row| row.get("exists").and_then(Value::as_bool) != Some(true))
        .count();
    let index = json!({
        "schema": "ay-launch-benchmark-artifact-index/v1",
        "hash_algorithm": "sha256",
        "summary_json_self_hash": "excluded: summary.json carries this index",
        "artifact_count": artifacts.len(),
        "missing_count": missing_count,
        "raw_result_count": 0,
        "raw_result_sha256s": {},
        "artifacts": artifacts,
    });
    summary["artifact_index"] = index;
    summary["raw_artifact_count"] = json!(0);
    summary["raw_artifact_sha256s"] = json!({});
    let checks = json!({
        "artifact_index_missing_count_zero": missing_count == 0,
        "artifact_count_matches_rows": true,
        "all_existing_artifacts_have_sha256": missing_count == 0,
        "raw_artifact_count_matches_expected_eval_rows": true,
        "raw_artifact_eval_ids_match_expected": true,
        "raw_artifact_sha256s_match_index": true,
        "required_sidecars_hashed": missing_count == 0,
        "eval_results_json_paths_match_index": true,
    });
    summary["self_validation"] = json!({
        "schema": "ay-launch-benchmark-self-validation/v1",
        "status": if missing_count == 0 { "pass" } else { "fail" },
        "checks": checks,
        "errors": if missing_count == 0 { json!([]) } else { json!(["missing artifacts"]) },
    });
    write_json(&summary_path, &summary)
}

fn artifact_record(path: &Path, role: &str, eval_id: Option<&str>) -> Result<Value> {
    let exists = path.exists();
    let mut record = serde_json::Map::new();
    record.insert("path".to_string(), json!(path));
    record.insert("role".to_string(), json!(role));
    record.insert("exists".to_string(), json!(exists));
    if let Some(eval_id) = eval_id {
        record.insert("eval_id".to_string(), json!(eval_id));
    }
    if path.is_file() {
        record.insert("size_bytes".to_string(), json!(fs::metadata(path)?.len()));
        record.insert("sha256".to_string(), json!(sha256_file_hex(path)?));
    }
    Ok(Value::Object(record))
}

fn write_provenance_txt(
    out_dir: &Path,
    launch_command: &str,
    provenance: &Value,
    config: &FastPacketConfig,
    launch_scope: &str,
) -> Result<()> {
    let mut text = String::new();
    text.push_str(&format!("timestamp_utc={}\n", utc_timestamp()));
    text.push_str(&format!("repo_root={}\n", config.repo_root.display()));
    text.push_str(&format!("launch_command={launch_command}\n"));
    text.push_str(&format!(
        "git_commit={}\n",
        provenance
            .pointer("/repo/commit")
            .and_then(Value::as_str)
            .unwrap_or("")
    ));
    text.push_str(&format!(
        "git_clean={}\n",
        provenance
            .pointer("/repo/clean")
            .and_then(Value::as_bool)
            .unwrap_or(false)
    ));
    text.push_str("git_status_short:\n");
    if let Some(rows) = provenance
        .pointer("/repo/git_status_short")
        .and_then(Value::as_array)
    {
        for row in rows {
            if let Some(row) = row.as_str() {
                text.push_str(row);
                text.push('\n');
            }
        }
    }
    text.push('\n');
    text.push_str(&format!("ay_path={}\n", canonical_display(&config.ay)));
    text.push_str(&format!(
        "ay_sha256={}\n",
        provenance
            .pointer("/tools/ay/sha256")
            .and_then(Value::as_str)
            .unwrap_or("")
    ));
    text.push_str("ay_version:\n");
    if let Some(rows) = provenance
        .pointer("/tools/ay/version/output")
        .and_then(Value::as_array)
    {
        for row in rows {
            if let Some(row) = row.as_str() {
                text.push_str(row);
                text.push('\n');
            }
        }
    }
    text.push('\n');
    text.push_str(&format!("reference_solver={}\n", config.reference_solver));
    text.push_str(&format!(
        "reference_solver_path={}\n",
        provenance
            .pointer("/tools/reference_solver/resolved_path")
            .and_then(Value::as_str)
            .unwrap_or("")
    ));
    text.push_str("reference_solver_version:\n");
    if let Some(rows) = provenance
        .pointer("/tools/reference_solver/version/output")
        .and_then(Value::as_array)
    {
        for row in rows {
            if let Some(row) = row.as_str() {
                text.push_str(row);
                text.push('\n');
            }
        }
    }
    text.push('\n');
    text.push_str(&format!("timeout={}\n", config.timeout));
    text.push_str(&format!("runs={}\n", config.runs));
    text.push_str(&format!(
        "results_root={}\n",
        env::var("AY_LAUNCH_RESULTS_DIR").unwrap_or_else(|_| "evals/results".to_string())
    ));
    text.push_str(&format!(
        "bench_progress_every={}\n",
        env::var("AY_BENCH_PROGRESS_EVERY").unwrap_or_else(|_| "1".to_string())
    ));
    text.push_str(&format!("launch_scope={launch_scope}\n"));
    if !config.requested_evals.is_empty() {
        text.push_str(&format!(
            "requested_evals={}\n",
            config.requested_evals.join(",")
        ));
    }
    if !config.excluded_evals.is_empty() {
        text.push_str(&format!(
            "excluded_evals={}\n",
            config.excluded_evals.join(",")
        ));
        for eval_id in &config.excluded_evals {
            text.push_str(&format!(
                "excluded_eval_reason[{eval_id}]={}\n",
                exclusion_reason(eval_id)
            ));
        }
    }
    text.push_str(&format!("mode={}\n", config.mode.as_str()));
    text.push_str("parallelism=ay bench default\n");
    text.push_str("seed_policy=no explicit seed; solver defaults\n");
    text.push_str(&format!(
        "provenance_json={}\n",
        out_dir.join("provenance.json").display()
    ));
    fs::write(out_dir.join("provenance.txt"), text)?;
    Ok(())
}

fn launch_command_string(config: &FastPacketConfig) -> String {
    let mut parts = vec!["ay".to_string(), "launch-packet".to_string()];
    parts.push(format!("--{}", config.mode.as_str()));
    parts.push("--ay".to_string());
    parts.push(config.ay.display().to_string());
    parts.push("--timeout".to_string());
    parts.push(config.timeout.clone());
    parts.push("--runs".to_string());
    parts.push(config.runs.to_string());
    parts.push("--reference-solver".to_string());
    parts.push(config.reference_solver.clone());
    if let Some(out_dir) = &config.out_dir {
        parts.push("--out-dir".to_string());
        parts.push(out_dir.display().to_string());
    }
    for eval in &config.requested_evals {
        parts.push("--eval".to_string());
        parts.push(eval.clone());
    }
    for eval in &config.excluded_evals {
        parts.push("--exclude-eval".to_string());
        parts.push(eval.clone());
    }
    shell_command_without_prompt(&parts)
}

fn exclusion_reason(eval_id: &str) -> &'static str {
    if eval_id == "sat-par2-dev" {
        "SAT launch eval excluded for this non-SAT/non-PB/non-JIT HN packet; run separate SAT evidence before SAT claims"
    } else {
        "operator-requested exclusion; packet is subset evidence and cannot clear broad launch benchmark evidence unless the gate policy accepts this exact exclusion"
    }
}

fn validate_positive_timeout(timeout: &str) -> Result<()> {
    let value = timeout
        .parse::<f64>()
        .with_context(|| format!("launch packet: --timeout must be positive: {timeout}"))?;
    if value <= 0.0 {
        bail!("launch packet: --timeout must be positive: {timeout}");
    }
    Ok(())
}

fn command_output(cwd: &Path, program: &Path, args: &[&str]) -> Value {
    let command = std::iter::once(program.display().to_string())
        .chain(args.iter().map(|arg| (*arg).to_string()))
        .collect::<Vec<_>>();
    let output = ProcessCommand::new(program)
        .current_dir(cwd)
        .args(args)
        .output();
    match output {
        Ok(output) => json!({
            "command": shell_command_without_prompt(&command),
            "exit_code": output.status.code().unwrap_or(1),
            "output": String::from_utf8_lossy(if output.stdout.is_empty() {
                &output.stderr
            } else {
                &output.stdout
            }).lines().map(str::to_string).collect::<Vec<_>>(),
        }),
        Err(error) => json!({
            "command": shell_command_without_prompt(&command),
            "exit_code": 1,
            "output": [error.to_string()],
        }),
    }
}

fn resolve_command_or_path_from(repo_root: &Path, command: &str) -> Option<String> {
    let path = Path::new(command);
    if path.is_absolute() {
        return is_executable(path).then(|| canonical_display(path));
    }
    if path.components().count() > 1 {
        let repo_relative = repo_root.join(path);
        return is_executable(&repo_relative).then(|| canonical_display(&repo_relative));
    }
    let output = ProcessCommand::new("sh")
        .arg("-c")
        .arg(format!("command -v {}", shell_quote(command)))
        .stdout(Stdio::piped())
        .stderr(Stdio::null())
        .output()
        .ok()?;
    if !output.status.success() {
        let repo_local = repo_root.join(path);
        return is_executable(&repo_local).then(|| canonical_display(&repo_local));
    }
    let text = String::from_utf8_lossy(&output.stdout).trim().to_string();
    if text.is_empty() {
        let repo_local = repo_root.join(path);
        return is_executable(&repo_local).then(|| canonical_display(&repo_local));
    }
    Some(text)
}

fn shell_command_line(command: &[String]) -> String {
    format!("$ {}", shell_command_without_prompt(command))
}

fn shell_command_without_prompt(command: &[String]) -> String {
    command
        .iter()
        .map(|arg| shell_quote(arg))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(value: &str) -> String {
    if value.is_empty() {
        return "''".to_string();
    }
    if value
        .bytes()
        .all(|byte| matches!(byte, b'A'..=b'Z' | b'a'..=b'z' | b'0'..=b'9' | b'_' | b'@' | b'%' | b'+' | b'=' | b':' | b',' | b'.' | b'/' | b'-'))
    {
        return value.to_string();
    }
    format!("'{}'", value.replace('\'', "'\\''"))
}

#[cfg(unix)]
fn is_executable(path: &Path) -> bool {
    use std::os::unix::fs::PermissionsExt;
    fs::metadata(path)
        .map(|metadata| metadata.is_file() && metadata.permissions().mode() & 0o111 != 0)
        .unwrap_or(false)
}

#[cfg(not(unix))]
fn is_executable(path: &Path) -> bool {
    fs::metadata(path)
        .map(|metadata| metadata.is_file())
        .unwrap_or(false)
}

fn canonical_display(path: &Path) -> String {
    path.canonicalize()
        .unwrap_or_else(|_| path.to_path_buf())
        .display()
        .to_string()
}

fn sha256_file_hex(path: &Path) -> Result<String> {
    let mut file = File::open(path).with_context(|| format!("open {}", path.display()))?;
    let mut hasher = Sha256::new();
    let mut buffer = [0_u8; 8192];
    loop {
        let read = file.read(&mut buffer)?;
        if read == 0 {
            break;
        }
        hasher.update(&buffer[..read]);
    }
    Ok(format!("{:x}", hasher.finalize()))
}

fn read_json(path: &Path) -> Result<Value> {
    Ok(serde_json::from_slice(&fs::read(path)?)?)
}

fn write_json(path: &Path, value: &Value) -> Result<()> {
    fs::write(path, serde_json::to_vec_pretty(value)?)?;
    Ok(())
}

fn git_output(path: &Path, args: &[&str]) -> Option<String> {
    let output = ProcessCommand::new("git")
        .arg("-C")
        .arg(path)
        .args(args)
        .output()
        .ok()?;
    if !output.status.success() {
        return None;
    }
    Some(
        String::from_utf8_lossy(&output.stdout)
            .trim_end()
            .to_string(),
    )
}

fn utc_timestamp() -> String {
    let output = ProcessCommand::new("date")
        .args(["-u", "+%Y-%m-%dT%H:%M:%SZ"])
        .output();
    if let Ok(output) = output {
        if output.status.success() {
            let text = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !text.is_empty() {
                return text;
            }
        }
    }
    "1970-01-01T00:00:00Z".to_string()
}

fn compact_timestamp() -> String {
    let output = ProcessCommand::new("date")
        .args(["-u", "+%Y%m%dT%H%M%SZ"])
        .output();
    if let Ok(output) = output {
        if output.status.success() {
            let text = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !text.is_empty() {
                return text;
            }
        }
    }
    "19700101T000000Z".to_string()
}

fn resolve_repo_root(explicit: Option<&Path>) -> Result<PathBuf> {
    if let Some(path) = explicit {
        return Ok(path.canonicalize().unwrap_or_else(|_| path.to_path_buf()));
    }
    let cwd = env::current_dir()?;
    if let Some(root) = git_output(&cwd, &["rev-parse", "--show-toplevel"]) {
        return Ok(PathBuf::from(root));
    }
    Ok(cwd)
}

fn resolve_path_arg(repo_root: &Path, path: &Path) -> PathBuf {
    if path.is_absolute() {
        path.to_path_buf()
    } else {
        repo_root.join(path)
    }
}
