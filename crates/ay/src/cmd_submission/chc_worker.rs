// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CHC-competition worker subcommands (bootstrap / shard-plan / benchmark-plan /
//! run / audit) extracted from `cmd_submission.rs`. The `run_chc_comp_worker`
//! dispatcher and the shared `ChcCompBenchmarkCase` are re-exported by the parent.

use super::*;
use std::fs;
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use anyhow::{bail, Result};
use serde_json::{json, Value as JsonValue};

use crate::build_info::BUILD_INFO;

pub(super) fn run_chc_comp_worker(cmd: ChcCompWorkerCommand) -> Result<()> {
    match cmd {
        ChcCompWorkerCommand::Bootstrap(opts) => chc_worker_bootstrap(&opts),
        ChcCompWorkerCommand::ShardPlan(opts) => chc_worker_shard_plan(&opts),
        ChcCompWorkerCommand::Run(opts) => chc_worker_run(&opts),
        ChcCompWorkerCommand::Audit(opts) => chc_worker_audit(&opts),
    }
}

fn chc_worker_bootstrap(opts: &ChcWorkerBootstrapOptions) -> Result<()> {
    let root = workspace_root();
    let host = machine_hostname();
    let (json_path, report_path) = chc_worker_report_paths(
        "bootstrap",
        None,
        &host,
        Path::new(CHC_WORKER_DEFAULT_REPORT_DIR),
        opts.json.as_deref(),
        opts.report.as_deref(),
    );

    let mut checks = Vec::new();
    let repo = collect_chc_worker_git_state(&root, &mut checks, opts.allow_dirty);
    let package = resolve_gate_dir(&opts.package, CHC_DEFAULT_DIR);
    let archive = package.join("ay-chccomp-2026-linux-x86_64.tar.gz");
    if archive.is_file() {
        push_check(
            &mut checks,
            "package:archive",
            "pass",
            format!("found {}", display_path_for_report(&archive, &root)),
        );
    } else {
        push_check(
            &mut checks,
            "package:archive",
            "warn",
            format!(
                "missing {}; run ay submission package chc before worker run",
                display_path_for_report(&archive, &root)
            ),
        );
    }
    if let Some(benchmarks_root) = &opts.benchmarks_root {
        if benchmarks_root.is_dir() {
            push_check(
                &mut checks,
                "benchmarks:root",
                "pass",
                format!("found {}", display_path_for_report(benchmarks_root, &root)),
            );
        } else {
            push_check(
                &mut checks,
                "benchmarks:root",
                "warn",
                format!("missing benchmark root {}", benchmarks_root.display()),
            );
        }
    } else {
        push_check(
            &mut checks,
            "benchmarks:root",
            "warn",
            "no --benchmarks-root supplied",
        );
    }
    if opts.no_gh {
        push_check(
            &mut checks,
            "gh:auth",
            "skip",
            "GitHub probe skipped by --no-gh",
        );
    } else {
        probe_chc_worker_command(&mut checks, "gh:auth", "gh", &["auth", "status"]);
    }
    for (name, program, args) in [
        ("tool:rustc", "rustc", &["--version"][..]),
        ("tool:cargo", "cargo", &["--version"][..]),
        ("tool:tar", "tar", &["--version"][..]),
        ("tool:z3", "z3", &["--version"][..]),
    ] {
        probe_chc_worker_command(&mut checks, name, program, args);
    }

    let fail_count = count_checks(&checks, "fail");
    let warn_count = count_checks(&checks, "warn");
    let skip_count = count_checks(&checks, "skip");
    let machine_ready = fail_count == 0 && archive.is_file() && opts.benchmarks_root.is_some();
    let payload = json!({
        "schema_version": CHC_WORKER_REPORT_SCHEMA,
        "schema": CHC_WORKER_REPORT_SCHEMA,
        "kind": "bootstrap",
        "generated_at_utc": BUILD_INFO.datetime_utc,
        "host": host,
        "repo": repo,
        "package": {
            "path": display_path_for_report(&package, &root),
            "archive": display_path_for_report(&archive, &root),
        },
        "benchmarks_root": opts.benchmarks_root.as_ref().map(|path| display_path_for_report(path, &root)),
        "target_dir": display_path_for_report(&opts.target_dir, &root),
        "summary": {
            "machine_ready": machine_ready,
            "fail_count": fail_count,
            "warn_count": warn_count,
            "skip_count": skip_count,
        },
        "checks": checks,
        "cases": [],
        "github_actions": [],
        "blockers": [],
    });
    let payload = with_worker_blockers(payload)?;
    write_json_report(&json_path, &payload)?;
    write_chc_worker_markdown(&report_path, &payload)?;
    println!("wrote {}", display_path_for_report(&json_path, &root));
    println!("wrote {}", display_path_for_report(&report_path, &root));
    println!("status=pass machine_ready={machine_ready} local_only=true");
    Ok(())
}

fn chc_worker_shard_plan(opts: &ChcWorkerShardPlanOptions) -> Result<()> {
    let tracks = split_tracks(&opts.tracks)?;
    if opts.machines == 0 {
        bail!("--machines must be positive");
    }
    let mut lanes = Vec::new();
    for (idx, lane) in CHC_WORKER_FIXED_LANES.iter().enumerate() {
        lanes.push(json!({
            "lane": lane,
            "worker_index": idx % opts.machines,
            "kind": "known-blocker",
        }));
    }
    for (idx, track) in tracks.iter().enumerate() {
        lanes.push(json!({
            "lane": format!("track-{track}"),
            "worker_index": (idx + CHC_WORKER_FIXED_LANES.len()) % opts.machines,
            "kind": "track-smoke",
            "track": track,
        }));
    }
    let payload = json!({
        "schema_version": "ay.chccomp-worker-shard-plan/v1",
        "machines": opts.machines,
        "tracks": tracks,
        "track_model": chc_track_model_json(),
        "lanes": lanes,
    });
    if opts.json {
        println!("{}", serde_json::to_string_pretty(&payload)?);
    } else {
        if let Some(lanes) = payload["lanes"].as_array() {
            for lane in lanes {
                println!(
                    "worker[{}] {} {}",
                    lane["worker_index"].as_u64().unwrap_or(0),
                    lane["kind"].as_str().unwrap_or("lane"),
                    lane["lane"].as_str().unwrap_or("unknown")
                );
            }
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct ChcCompBenchmarkCase {
    pub(super) track: String,
    pub(super) set_entry: String,
}

impl ChcCompBenchmarkCase {
    pub(super) fn new(track: impl Into<String>, set_entry: impl Into<String>) -> Self {
        Self {
            track: track.into(),
            set_entry: set_entry.into(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum ChcWorkerBenchmarkPlan {
    PackageOnly(&'static str),
    FixedCases(Vec<ChcCompBenchmarkCase>),
    TrackSamples {
        tracks: Vec<String>,
        samples_per_track: usize,
    },
}

impl ChcWorkerBenchmarkPlan {
    fn report_json(&self) -> JsonValue {
        match self {
            ChcWorkerBenchmarkPlan::PackageOnly(reason) => json!({
                "mode": "package-only",
                "reason": reason,
            }),
            ChcWorkerBenchmarkPlan::FixedCases(cases) => json!({
                "mode": "fixed-cases",
                "cases": cases
                    .iter()
                    .map(|case| json!({
                        "track": &case.track,
                        "set_entry": &case.set_entry,
                    }))
                    .collect::<Vec<_>>(),
            }),
            ChcWorkerBenchmarkPlan::TrackSamples {
                tracks,
                samples_per_track,
            } => json!({
                "mode": "track-samples",
                "tracks": tracks,
                "samples_per_track": samples_per_track,
            }),
        }
    }
}

pub(super) fn chc_worker_benchmark_plan(
    lane: &str,
    tracks: &[String],
    samples_per_track: usize,
) -> Result<ChcWorkerBenchmarkPlan> {
    match lane {
        "triangle-location" => Ok(ChcWorkerBenchmarkPlan::FixedCases(vec![
            ChcCompBenchmarkCase::new(
                "BV",
                "./eldarica-misc/BV/Consistency/ch-triangle-location-nr.1-bv_000.yml",
            ),
            ChcCompBenchmarkCase::new(
                "LIA",
                "./eldarica-misc/LIA/Consistency/ch-triangle-location-nr.1_000.yml",
            ),
        ])),
        "o0-arrays" => Ok(ChcWorkerBenchmarkPlan::FixedCases(vec![
            ChcCompBenchmarkCase::new(
                "LIA-Arrays",
                "./hcai-bench/svcomp/O0/O0_eureka_01_true-unreach-call_000.yml",
            ),
            ChcCompBenchmarkCase::new(
                "LIA-Lin-Arrays",
                "./hcai-bench/svcomp/O0/O0_compact_false-unreach-call_000.yml",
            ),
        ])),
        "recursive-adt" => Ok(ChcWorkerBenchmarkPlan::FixedCases(vec![
            ChcCompBenchmarkCase::new("ADT-LIA", "./ADTRem/clam/goal21_000.yml"),
        ])),
        "erc777-safe" => Ok(ChcWorkerBenchmarkPlan::FixedCases(vec![
            ChcCompBenchmarkCase::new(
                "ADT-LIA-Arrays",
                "./solidity/larger/erc777/erc777_safe_000.yml",
            ),
        ])),
        "package-preflight" => Ok(ChcWorkerBenchmarkPlan::PackageOnly(
            "package-preflight validates archive/package structure; use a score lane for benchmark smoke",
        )),
        "reference-verdict-audit" => Ok(ChcWorkerBenchmarkPlan::PackageOnly(
            "reference-verdict-audit consumes worker reports; use audit over run JSON for verdict checks",
        )),
        lane => {
            if let Some(track) = lane.strip_prefix("track-") {
                let Some(track) = chc_track_set_file(track) else {
                    bail!(
                        "invalid CHC worker lane '{lane}'; expected known lane or track-<CHC track>"
                    );
                };
                Ok(ChcWorkerBenchmarkPlan::TrackSamples {
                    tracks: vec![track.to_string()],
                    samples_per_track,
                })
            } else {
                Ok(ChcWorkerBenchmarkPlan::TrackSamples {
                    tracks: tracks.to_vec(),
                    samples_per_track,
                })
            }
        }
    }
}

fn chc_worker_run(opts: &ChcWorkerRunOptions) -> Result<()> {
    let root = workspace_root();
    let host = machine_hostname();
    let (json_path, report_path) = chc_worker_report_paths(
        "run",
        Some(opts.issue),
        &opts.lane,
        &opts.report_dir,
        opts.json.as_deref(),
        opts.report.as_deref(),
    );
    let mut checks = Vec::new();
    let mut github_actions = Vec::new();
    if let Some(owner) = &opts.claim {
        github_actions.push(chc_worker_gh(
            opts.no_gh,
            vec![
                "issue".to_string(),
                "edit".to_string(),
                opts.issue.to_string(),
                "--add-label".to_string(),
                "in-progress".to_string(),
                "--add-label".to_string(),
                owner.clone(),
            ],
        ));
    }

    let repo = collect_chc_worker_git_state(&root, &mut checks, opts.allow_dirty);
    let tracks = split_tracks(&opts.tracks)?;
    let benchmark_plan = chc_worker_benchmark_plan(&opts.lane, &tracks, opts.samples_per_track)?;
    let package = resolve_gate_dir(&opts.package, CHC_DEFAULT_DIR);
    let archive = package.join("ay-chccomp-2026-linux-x86_64.tar.gz");
    let archive_sha256 = if archive.is_file() {
        match sha256_file(&archive) {
            Ok(hash) => {
                push_check(
                    &mut checks,
                    "package:archive",
                    "pass",
                    format!("archive sha256={hash}"),
                );
                Some(hash)
            }
            Err(err) => {
                push_check(
                    &mut checks,
                    "package:archive",
                    "fail",
                    format!("failed to hash archive: {err:#}"),
                );
                None
            }
        }
    } else {
        push_check(
            &mut checks,
            "package:archive",
            "fail",
            format!("missing archive {}", archive.display()),
        );
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

    let manifest_path = package.join("MANIFEST.json");
    let manifest = read_json_file(&manifest_path, &mut checks, "manifest:read", &root);
    let manifest_commit = manifest
        .as_ref()
        .and_then(|value| value["generated_by"]["commit"].as_str())
        .unwrap_or("unavailable")
        .to_string();
    let mut wrapper = None;
    let mut binary_path = None;
    match extract_archive(&archive, "ay-chc-worker-archive") {
        Ok(extracted) => {
            let archived_root = extracted.join("ay");
            let candidate_wrapper = archived_root.join("run_solver.sh");
            let candidate_binary = archived_root.join("ay");
            if candidate_wrapper.is_file() && is_executable(&candidate_wrapper) {
                push_check(
                    &mut checks,
                    "archive:run_solver",
                    "pass",
                    "archived run_solver.sh is executable",
                );
                wrapper = Some(candidate_wrapper);
            } else {
                push_check(
                    &mut checks,
                    "archive:run_solver",
                    "fail",
                    "archived run_solver.sh missing or not executable",
                );
            }
            if candidate_binary.is_file() && is_executable(&candidate_binary) {
                push_check(
                    &mut checks,
                    "archive:ay",
                    "pass",
                    "archived ay binary is executable",
                );
                binary_path = Some(candidate_binary);
            } else {
                push_check(
                    &mut checks,
                    "archive:ay",
                    "fail",
                    "archived ay binary missing or not executable",
                );
            }
        }
        Err(err) => push_check(
            &mut checks,
            "archive:extract",
            "fail",
            format!("failed to extract archive: {err:#}"),
        ),
    }

    let binary_sha256 = binary_path
        .as_ref()
        .and_then(|path| sha256_file(path).ok())
        .unwrap_or_else(|| "unavailable".to_string());
    let binary_platform = binary_path
        .as_ref()
        .and_then(|path| binary_platform(path).ok())
        .unwrap_or_else(|| "unknown".to_string());
    let mut cases = Vec::new();
    if opts.skip_benchmark_smoke {
        push_check(
            &mut checks,
            "benchmarks:smoke",
            "skip",
            "benchmark smoke skipped by --skip-benchmark-smoke",
        );
    } else {
        match &benchmark_plan {
            ChcWorkerBenchmarkPlan::PackageOnly(reason) => push_check(
                &mut checks,
                "benchmarks:smoke",
                "skip",
                (*reason).to_string(),
            ),
            ChcWorkerBenchmarkPlan::TrackSamples {
                tracks: _,
                samples_per_track,
            } if *samples_per_track == 0 => {
                push_check(
                    &mut checks,
                    "benchmarks:samples_per_track",
                    "fail",
                    "--samples-per-track must be positive unless --skip-benchmark-smoke is set",
                );
            }
            ChcWorkerBenchmarkPlan::TrackSamples {
                tracks,
                samples_per_track,
            } => {
                if let Some(benchmarks_root) = &opts.benchmarks_root {
                    if let Some(wrapper) = &wrapper {
                        let smokes = run_chc_comp_benchmark_smokes(
                            &mut checks,
                            wrapper,
                            benchmarks_root,
                            tracks,
                            *samples_per_track,
                            Duration::from_millis(opts.benchmark_timeout_ms),
                            &root,
                        )?;
                        cases = smokes
                            .iter()
                            .map(chc_worker_case_from_smoke)
                            .collect::<Vec<_>>();
                    } else {
                        push_check(
                            &mut checks,
                            "benchmarks:smoke",
                            "fail",
                            "archived wrapper unavailable; benchmark smoke not run",
                        );
                    }
                } else {
                    push_check(
                        &mut checks,
                        "benchmarks:root",
                        "fail",
                        "missing --benchmarks-root; pass a chc-comp26-benchmarks checkout or use --skip-benchmark-smoke",
                    );
                }
            }
            ChcWorkerBenchmarkPlan::FixedCases(fixed_cases) => {
                if let Some(benchmarks_root) = &opts.benchmarks_root {
                    if let Some(wrapper) = &wrapper {
                        let smokes = run_chc_comp_benchmark_fixed_smokes(
                            &mut checks,
                            wrapper,
                            benchmarks_root,
                            fixed_cases,
                            Duration::from_millis(opts.benchmark_timeout_ms),
                            &root,
                        )?;
                        cases = smokes
                            .iter()
                            .map(chc_worker_case_from_smoke)
                            .collect::<Vec<_>>();
                    } else {
                        push_check(
                            &mut checks,
                            "benchmarks:smoke",
                            "fail",
                            "archived wrapper unavailable; benchmark smoke not run",
                        );
                    }
                } else {
                    push_check(
                        &mut checks,
                        "benchmarks:root",
                        "fail",
                        "missing --benchmarks-root; pass a chc-comp26-benchmarks checkout or use --skip-benchmark-smoke",
                    );
                }
            }
        }
    }

    let summary = summarize_chc_worker_cases(&cases, &checks);
    let promotion_ready = summary["failed_cases"].as_u64().unwrap_or(0) == 0
        && summary["total_cases"].as_u64().unwrap_or(0) > 0
        && count_checks(&checks, "fail") == 0;
    let replay_command = format!(
        "ay submission worker chc-comp run --issue {} --lane {} --package {} --tracks {} --samples-per-track {} --benchmark-timeout-ms {}",
        opts.issue,
        opts.lane,
        opts.package.display(),
        opts.tracks,
        opts.samples_per_track,
        opts.benchmark_timeout_ms
    );
    let mut payload = json!({
        "schema_version": CHC_WORKER_REPORT_SCHEMA,
        "schema": CHC_WORKER_REPORT_SCHEMA,
        "kind": "run",
        "generated_at_utc": BUILD_INFO.datetime_utc,
        "host": host,
        "issue": opts.issue,
        "lane": opts.lane,
        "repo_commit": repo["commit"].as_str().unwrap_or("unavailable"),
        "dirty": repo["dirty"].as_bool().unwrap_or(false),
        "repo": repo,
        "package_manifest_commit": manifest_commit,
        "binary_sha256": binary_sha256,
        "command": replay_command,
        "benchmarks_root": opts.benchmarks_root.as_ref().map(|path| display_path_for_report(path, &root)),
        "benchmark_plan": benchmark_plan.report_json(),
        "timeout_ms": opts.benchmark_timeout_ms,
        "target_dir": opts.target_dir.as_ref().map(|path| display_path_for_report(path, &root)),
        "package": {
            "path": display_path_for_report(&package, &root),
            "manifest": manifest,
            "archive": {
                "path": display_path_for_report(&archive, &root),
                "sha256": archive_sha256,
            },
            "binary": {
                "sha256": binary_sha256,
                "platform": binary_platform,
            },
        },
        "tracks": tracks,
        "track_model": chc_track_model_json(),
        "cases": cases,
        "summary": summary,
        "checks": checks,
        "github_actions": github_actions,
    });
    payload = with_worker_blockers(payload)?;
    write_json_report(&json_path, &payload)?;
    write_chc_worker_markdown(&report_path, &payload)?;

    let mut github_actions = payload["github_actions"]
        .as_array()
        .cloned()
        .unwrap_or_default();
    if opts.comment_issue {
        github_actions.push(chc_worker_gh(
            opts.no_gh,
            vec![
                "issue".to_string(),
                "comment".to_string(),
                opts.issue.to_string(),
                "--body-file".to_string(),
                report_path.display().to_string(),
            ],
        ));
    }
    if opts.move_do_audit && promotion_ready {
        github_actions.push(chc_worker_gh(
            opts.no_gh,
            vec![
                "issue".to_string(),
                "edit".to_string(),
                opts.issue.to_string(),
                "--add-label".to_string(),
                "do-audit".to_string(),
                "--remove-label".to_string(),
                "in-progress".to_string(),
            ],
        ));
    }
    payload["github_actions"] = json!(github_actions);
    write_json_report(&json_path, &payload)?;
    write_chc_worker_markdown(&report_path, &payload)?;

    println!("wrote {}", display_path_for_report(&json_path, &root));
    println!("wrote {}", display_path_for_report(&report_path, &root));
    if payload["summary"]["fail_count"].as_u64().unwrap_or(1) == 0 {
        println!("status=pass promotion_ready={promotion_ready} local_only=true");
        Ok(())
    } else {
        bail!("status=fail promotion_ready=false local_only=true")
    }
}

fn chc_worker_audit(opts: &ChcWorkerAuditOptions) -> Result<()> {
    let root = workspace_root();
    let mut checks = Vec::new();
    let mut reports = Vec::new();
    for path in &opts.reports {
        match fs::read_to_string(path) {
            Ok(text) => match serde_json::from_str::<JsonValue>(&text) {
                Ok(report) => {
                    audit_chc_worker_report(path, &report, opts, &mut checks, &root);
                    reports.push(report);
                }
                Err(err) => push_check(
                    &mut checks,
                    format!("report:{}:json", path.display()),
                    "fail",
                    format!("failed to parse JSON: {err:#}"),
                ),
            },
            Err(err) => push_check(
                &mut checks,
                format!("report:{}:read", path.display()),
                "fail",
                format!("failed to read report: {err:#}"),
            ),
        }
    }
    let fail_count = count_checks(&checks, "fail");
    let warn_count = count_checks(&checks, "warn");
    let payload = json!({
        "schema_version": CHC_WORKER_AUDIT_SCHEMA,
        "generated_at_utc": BUILD_INFO.datetime_utc,
        "reports": reports,
        "summary": {
            "audit_ready": fail_count == 0,
            "report_count": opts.reports.len(),
            "fail_count": fail_count,
            "warn_count": warn_count,
        },
        "checks": checks,
    });
    if let Some(path) = &opts.json {
        write_json_report(path, &payload)?;
        println!("wrote {}", display_path_for_report(path, &root));
    }
    if let Some(path) = &opts.report {
        write_chc_worker_audit_markdown(path, &payload)?;
        println!("wrote {}", display_path_for_report(path, &root));
    }
    if fail_count == 0 {
        println!("status=pass audit_ready=true local_only=true");
        Ok(())
    } else {
        bail!("status=fail audit_ready=false local_only=true")
    }
}

fn audit_chc_worker_report(
    path: &Path,
    report: &JsonValue,
    opts: &ChcWorkerAuditOptions,
    checks: &mut Vec<JsonValue>,
    root: &Path,
) {
    let label = display_path_for_report(path, root);
    let schema = report["schema_version"]
        .as_str()
        .or_else(|| report["schema"].as_str())
        .unwrap_or("missing");
    if schema == CHC_WORKER_REPORT_SCHEMA && report["kind"].as_str() == Some("run") {
        push_check(
            checks,
            format!("report:{label}:schema"),
            "pass",
            "worker run report schema accepted",
        );
    } else {
        push_check(
            checks,
            format!("report:{label}:schema"),
            "fail",
            format!("expected {CHC_WORKER_REPORT_SCHEMA} run report, got {schema}"),
        );
    }
    let dirty = report["repo"]["dirty"]
        .as_bool()
        .or_else(|| report["dirty"].as_bool())
        .unwrap_or(true);
    if dirty && !opts.allow_dirty {
        push_check(
            checks,
            format!("report:{label}:dirty"),
            "fail",
            "report was captured from a dirty worktree",
        );
    } else {
        push_check(
            checks,
            format!("report:{label}:dirty"),
            if dirty { "warn" } else { "pass" },
            format!("dirty={dirty}"),
        );
    }
    let repo_commit = report["repo"]["commit"]
        .as_str()
        .or_else(|| report["repo_commit"].as_str())
        .unwrap_or("unavailable");
    if repo_commit == "unavailable" || repo_commit.is_empty() {
        push_check(
            checks,
            format!("report:{label}:repo_commit"),
            "fail",
            "missing repo commit",
        );
    }
    let binary_sha = report["binary_sha256"]
        .as_str()
        .or_else(|| report["package"]["binary"]["sha256"].as_str())
        .unwrap_or("unavailable");
    if binary_sha.len() == 64 && binary_sha.bytes().all(|byte| byte.is_ascii_hexdigit()) {
        push_check(
            checks,
            format!("report:{label}:binary_sha256"),
            "pass",
            format!("binary sha256={binary_sha}"),
        );
    } else {
        push_check(
            checks,
            format!("report:{label}:binary_sha256"),
            "fail",
            format!("missing or invalid binary sha256: {binary_sha}"),
        );
    }
    let package_commit = report["package_manifest_commit"]
        .as_str()
        .unwrap_or("unavailable");
    let package_commit_matches = package_commit == repo_commit
        || (opts.allow_dirty
            && package_commit
                .strip_suffix("-dirty")
                .is_some_and(|clean| clean == repo_commit));
    if !opts.allow_stale_package
        && package_commit != "unavailable"
        && repo_commit != "unavailable"
        && !package_commit_matches
    {
        push_check(
            checks,
            format!("report:{label}:package_commit"),
            "fail",
            format!("package commit {package_commit} differs from repo commit {repo_commit}"),
        );
    }
    let summary = &report["summary"];
    for (key, description) in [
        ("wrong", "wrong verdicts"),
        ("invalid", "invalid transcript statuses"),
        ("stdout_clean_failures", "status-unclean stdout transcripts"),
        ("failed_cases", "failed benchmark cases"),
    ] {
        let value = summary[key].as_u64().unwrap_or(0);
        if value == 0 {
            push_check(
                checks,
                format!("report:{label}:summary:{key}"),
                "pass",
                format!("{description}=0"),
            );
        } else {
            push_check(
                checks,
                format!("report:{label}:summary:{key}"),
                "fail",
                format!("{description}={value}"),
            );
        }
    }
    let total = summary["total_cases"].as_u64().unwrap_or(0);
    if total == 0 {
        push_check(
            checks,
            format!("report:{label}:cases"),
            "fail",
            "worker report has no benchmark cases",
        );
    }
    let solved = summary["solved"].as_u64().unwrap_or(0);
    if solved == 0 && total > 0 {
        push_check(
            checks,
            format!("report:{label}:timeout_only"),
            "fail",
            "worker report has no solved sat/unsat case",
        );
    }
}

fn collect_chc_worker_git_state(
    root: &Path,
    checks: &mut Vec<JsonValue>,
    allow_dirty: bool,
) -> JsonValue {
    let commit = git_stdout(root, &["rev-parse", "HEAD"]).unwrap_or_else(|| "unavailable".into());
    let branch = git_stdout(root, &["rev-parse", "--abbrev-ref", "HEAD"])
        .unwrap_or_else(|| "unavailable".into());
    let origin_main = git_stdout(root, &["rev-parse", "--verify", "origin/main"]);
    let status = git_stdout(root, &["status", "--porcelain"]).unwrap_or_default();
    let dirty = !status.trim().is_empty();
    if commit == "unavailable" {
        push_check(checks, "repo:commit", "fail", "git commit unavailable");
    } else {
        push_check(checks, "repo:commit", "pass", format!("HEAD={commit}"));
    }
    if dirty && !allow_dirty {
        push_check(
            checks,
            "repo:clean",
            "fail",
            "worktree is dirty; pass --allow-dirty only for local exploratory evidence",
        );
    } else {
        push_check(
            checks,
            "repo:clean",
            if dirty { "warn" } else { "pass" },
            format!("dirty={dirty}"),
        );
    }
    let remote_aligned = origin_main.as_ref().is_some_and(|remote| remote == &commit);
    if remote_aligned {
        push_check(
            checks,
            "repo:origin_main",
            "pass",
            "HEAD matches origin/main",
        );
    } else if let Some(remote) = &origin_main {
        push_check(
            checks,
            "repo:origin_main",
            "warn",
            format!("HEAD {commit} differs from origin/main {remote}"),
        );
    } else {
        push_check(
            checks,
            "repo:origin_main",
            "warn",
            "origin/main is unavailable",
        );
    }
    if branch == "main" {
        push_check(checks, "repo:branch", "pass", "on main");
    } else {
        push_check(
            checks,
            "repo:branch",
            "warn",
            format!("worker is on branch {branch}, expected main"),
        );
    }
    json!({
        "root": display_path_for_report(root, root),
        "commit": commit,
        "branch": branch,
        "origin_main": origin_main,
        "remote_aligned": remote_aligned,
        "dirty": dirty,
        "status_porcelain": status,
    })
}

fn git_stdout(root: &Path, args: &[&str]) -> Option<String> {
    let output = Command::new("git")
        .args(args)
        .current_dir(root)
        .output()
        .ok()?;
    output
        .status
        .success()
        .then(|| String::from_utf8_lossy(&output.stdout).trim().to_string())
}
