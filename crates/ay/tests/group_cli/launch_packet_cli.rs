// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI coverage for native launch-packet metadata sidecars.

use std::fs;
use std::path::Path;
use std::path::PathBuf;
use std::process::Command;

use ntest::timeout;
use serde_json::{json, Value};
use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

#[test]
#[timeout(30_000)]
fn launch_packet_dry_run_writes_metadata_sidecars() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &launch_eval_ids());
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--dry-run", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--exclude-eval", "sat-par2-dev", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --dry-run");

    assert!(
        output.status.success(),
        "dry-run should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    for file in [
        "commands.log",
        "input_inventory.jsonl",
        "planned_evals.tsv",
        "provenance.json",
        "provenance.txt",
        "summary.json",
        "summary.md",
    ] {
        assert!(out_dir.join(file).is_file(), "missing sidecar {file}");
    }
    let summary = read_json(&out_dir.join("summary.json"));
    assert_eq!(summary["schema"], "ay-launch-benchmark-packet/v1");
    assert_eq!(summary["mode"], "dry-run");
    assert_eq!(summary["benchmarks_executed"], false);
    assert_eq!(summary["planned_eval_count"], 7);
    assert_eq!(
        summary["artifact_index"]["schema"],
        "ay-launch-benchmark-artifact-index/v1"
    );
    assert_eq!(summary["self_validation"]["status"], "pass");
}

#[test]
#[timeout(30_000)]
fn launch_packet_quotes_commands_across_sidecars() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-smtcomp-qf-lia"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet with space");
    let ay_with_space = repo.path().join("bin dir").join("ay tool");
    fs::create_dir_all(ay_with_space.parent().expect("ay parent")).expect("mkdir ay parent");
    fs::copy(ay_binary(), &ay_with_space).expect("copy ay");
    make_executable(&ay_with_space);
    let reference_solver = write_fake_reference_solver(&repo, "ref solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--dry-run", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(&ay_with_space)
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-smtcomp-qf-lia", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --dry-run");

    assert_success(&output, "quoted dry run should succeed");
    let command_line = fs::read_to_string(out_dir.join("commands.log"))
        .expect("read commands.log")
        .lines()
        .next()
        .expect("commands.log row")
        .to_string();
    assert!(
        command_line.starts_with("$ '"),
        "path with spaces should be shell-quoted: {command_line}"
    );
    assert!(
        command_line.contains("--reference-solver '"),
        "reference solver path should be shell-quoted: {command_line}"
    );

    let provenance = read_json(&out_dir.join("provenance.json"));
    let summary = read_json(&out_dir.join("summary.json"));
    assert_eq!(
        provenance["selection"]["active_evals"][0]["command"],
        command_line
    );
    assert_eq!(summary["planned_evals"][0]["command"], command_line);
    assert_eq!(summary["commands"][0], command_line);
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("dry-run: '"),
        "dry-run stderr should be shell-quoted:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_inventory_matches_shell_metadata_contract() {
    let repo = TempDir::new().expect("temp repo");
    write_eval_registry(
        repo.path(),
        "smt-smtcomp-qf-lia",
        r#"
id: smt-smtcomp-qf-lia
inputs:
  benchmarks_dir: benchmarks/smtcomp/QF_LIA
  timeout_sec: 30
setup:
  download: scripts/download_smtcomp_benchmarks.sh --logic QF_LIA
  note: >
    Run scripts/download_smtcomp_benchmarks.sh --logic QF_LIA to populate
    benchmarks/smtcomp/QF_LIA/ from the Zenodo SMT-LIB 2024 release.
"#,
    );
    let benchmark_dir = repo.path().join("benchmarks/smtcomp/QF_LIA");
    fs::create_dir_all(&benchmark_dir).expect("mkdir benchmarks");
    fs::write(benchmark_dir.join("sample.smt2"), "(check-sat)\n").expect("write smt2");
    fs::write(repo.path().join("Cargo.toml"), "[workspace]\n").expect("write Cargo.toml");
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-smtcomp-qf-lia", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let inventory = read_jsonl_first(&out_dir.join("input_inventory.jsonl"));
    assert_eq!(
        inventory["registry"],
        "evals/registry/smt-smtcomp-qf-lia.yaml"
    );
    assert_eq!(inventory["registry_exists"], true);
    assert_eq!(inventory["benchmarks_dir"], "benchmarks/smtcomp/QF_LIA");
    assert_eq!(
        inventory["setup_download"],
        "scripts/download_smtcomp_benchmarks.sh --logic QF_LIA"
    );
    assert!(inventory["setup_note"]
        .as_str()
        .expect("setup note")
        .contains("Zenodo SMT-LIB 2024 release"));
    assert_eq!(
        inventory["public_source"],
        "https://zenodo.org/api/records/11061097/files/QF_LIA.tar.zst/content"
    );
    assert_eq!(inventory["benchmarks_dir_exists"], true);
    assert_eq!(inventory["file_count"], 1);
    assert_eq!(inventory["smt2_count"], 1);
    assert_eq!(inventory["input_dirs"][0]["role"], "benchmarks_dir");

    let provenance = read_json(&out_dir.join("provenance.json"));
    assert_eq!(
        provenance["selection"]["registry_validation"]["status"],
        "pass"
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_inventory_records_suite_dirs() {
    let repo = TempDir::new().expect("temp repo");
    write_eval_registry(
        repo.path(),
        "smt-local-suite",
        r#"
id: smt-local-suite
inputs:
  benchmarks_dir: benchmarks/smt
  suite_dirs:
    - QF_LIA
    - QF_BV
  timeout_sec: 30
"#,
    );
    let qf_lia_dir = repo.path().join("benchmarks/smt/QF_LIA");
    let qf_bv_dir = repo.path().join("benchmarks/smt/QF_BV");
    fs::create_dir_all(&qf_lia_dir).expect("mkdir QF_LIA");
    fs::create_dir_all(&qf_bv_dir).expect("mkdir QF_BV");
    fs::write(qf_lia_dir.join("lia.smt2"), "(check-sat)\n").expect("write lia smt2");
    fs::write(qf_bv_dir.join("bv.smt2"), "(check-sat)\n").expect("write bv smt2");
    fs::write(repo.path().join("Cargo.toml"), "[workspace]\n").expect("write Cargo.toml");
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-local-suite", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let inventory = read_jsonl_first(&out_dir.join("input_inventory.jsonl"));
    assert_eq!(inventory["benchmarks_dir"], "benchmarks/smt");
    assert_eq!(
        inventory["suite_dirs"],
        serde_json::json!(["QF_LIA", "QF_BV"])
    );
    assert_eq!(inventory["benchmarks_dir_exists"], true);
    assert_eq!(inventory["file_count"], 2);
    assert_eq!(inventory["smt2_count"], 2);
    assert_eq!(
        inventory["input_dirs"]
            .as_array()
            .expect("input dirs")
            .len(),
        3
    );
    assert_eq!(inventory["input_dirs"][0]["role"], "benchmarks_dir");
    assert_eq!(inventory["input_dirs"][0]["path"], "benchmarks/smt");
    assert_eq!(inventory["input_dirs"][1]["role"], "suite_dir");
    assert_eq!(inventory["input_dirs"][1]["path"], "benchmarks/smt/QF_LIA");
    assert_eq!(inventory["input_dirs"][1]["file_count"], 1);
    assert_eq!(inventory["input_dirs"][1]["smt2_count"], 1);
    assert_eq!(inventory["input_dirs"][2]["role"], "suite_dir");
    assert_eq!(inventory["input_dirs"][2]["path"], "benchmarks/smt/QF_BV");
    assert_eq!(inventory["input_dirs"][2]["file_count"], 1);
    assert_eq!(inventory["input_dirs"][2]["smt2_count"], 1);
}

#[test]
#[timeout(30_000)]
fn launch_packet_bench_progress_every_is_numeric() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .env("AY_BENCH_PROGRESS_EVERY", "7")
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-local-suite", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let provenance = read_json(&out_dir.join("provenance.json"));
    assert_eq!(provenance["parameters"]["bench_progress_every"], 7);
}

#[test]
#[timeout(30_000)]
fn launch_packet_rejects_invalid_bench_progress_every_like_shell() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .env("AY_BENCH_PROGRESS_EVERY", "0")
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-local-suite", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert!(
        !output.status.success(),
        "invalid progress interval should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("AY_BENCH_PROGRESS_EVERY must be a positive integer"),
        "stderr should explain the invalid progress interval:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_rejects_eval_missing_from_ay_bench_list() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = write_fake_reference_solver(&repo, "ref-solver");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .arg("--reference-solver")
        .arg(&reference_solver)
        .args(["--eval", "smt-smtcomp-qf-lia", "--out-dir"])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert!(
        !output.status.success(),
        "unregistered eval should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("eval not registered"),
        "stderr should explain registry failure:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_resolves_reference_solver_relative_to_repo_root() {
    let repo = TempDir::new().expect("temp repo");
    write_minimal_launch_registry(repo.path(), &["smt-local-suite"]);
    init_git_repo(repo.path());
    let out_dir = repo.path().join("packet");
    let reference_solver = repo.path().join("tools/ref-solver");
    write_executable(
        &reference_solver,
        "#!/usr/bin/env sh\nif [ \"$1\" = \"--version\" ]; then echo repo-ref 1.0; exit 0; fi\nexit 0\n",
    );

    let output = Command::new(ay_binary())
        .args(["launch-packet", "--metadata-only", "--repo-root"])
        .arg(repo.path())
        .arg("--ay")
        .arg(ay_binary())
        .args([
            "--reference-solver",
            "tools/ref-solver",
            "--eval",
            "smt-local-suite",
            "--out-dir",
        ])
        .arg(&out_dir)
        .output()
        .expect("spawn ay launch-packet --metadata-only");

    assert_success(&output, "metadata-only should succeed");
    let provenance = read_json(&out_dir.join("provenance.json"));
    assert_eq!(
        provenance["tools"]["reference_solver"]["resolved_path"],
        reference_solver
            .canonicalize()
            .expect("canonical ref solver")
            .display()
            .to_string()
    );
    assert_eq!(
        provenance["tools"]["reference_solver"]["version"]["output"][0],
        "repo-ref 1.0"
    );
}

#[test]
#[timeout(30_000)]
fn launch_packet_index_summarizes_packet_artifacts() {
    let repo = TempDir::new().expect("temp repo");
    write_standard_docs(repo.path());
    let packet = repo.path().join("packet");
    fs::create_dir_all(packet.join("raw")).expect("mkdir packet");
    fs::write(packet.join("raw/smt-local-suite.json"), "{}\n").expect("write raw result");
    fs::write(
        packet.join("release-gate.log"),
        "release-gate: FAIL broad broad public-launch launch is blocked\n",
    )
    .expect("write gate log");
    let commit = "94b1811a4ecf9ddf7ed04c5eb78d3c4cb50c2f89";
    write_json(
        &packet.join("release-gate-summary.json"),
        &json!({
            "schema": "ay-release-gate-summary/v1",
            "status": "fail",
            "evidence_gate_failures": 0,
            "advisory_failures": 0,
            "launch_blocker_count": 2,
            "blockers": [
                {"name": "public_mirror", "detail": "public object not fetchable"},
                {"name": "release_manifest", "detail": "public mirror not synced"}
            ]
        }),
    );
    write_json(
        &packet.join("ay-release-manifest.json"),
        &json!({
            "schema": "ay-release-manifest/v1",
            "status": "fail",
            "private": {"ay_commit": commit},
            "release": {"private_commit": commit}
        }),
    );
    write_json(
        &packet.join("ay-public-commit-evidence.json"),
        &json!({
            "schema": "ay-public-commit-evidence/v1",
            "status": "fail",
            "commit": commit,
            "expected_commit": commit
        }),
    );
    write_json(
        &packet.join("ay-release-manifest-verification.json"),
        &json!({
            "schema": "ay-release-manifest-verification/v1",
            "status": "fail"
        }),
    );
    for file in [
        "summary.json",
        "consumer-smoke-summary.json",
        "z3-cli-proof-verify.json",
        "smt-alethe-external-replay.json",
        "lean-proof-replay.json",
        "chc-certificate-replay.json",
    ] {
        fs::write(packet.join(file), "{}\n").expect("write json artifact");
    }
    fs::write(packet.join("z3-cli-proof-verify.log"), "test ok\n").expect("write proof log");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "index", "--packet-dir"])
        .arg(&packet)
        .arg("--repo-root")
        .arg(repo.path())
        .args(["--generated-at", "2026-04-28T00:00:00Z"])
        .output()
        .expect("spawn ay launch-packet index");

    assert_success(&output, "launch-packet index should succeed");
    let index = fs::read_to_string(packet.join("INDEX.md")).expect("read index");
    assert!(
        index.contains(&format!("- Release commit: `{commit}`")),
        "{index}"
    );
    assert!(
        index.contains("| public mirror evidence | `fail` |"),
        "{index}"
    );
    assert!(
        index.contains("| benchmark raw results | `present` | [raw/smt-local-suite.json]"),
        "{index}"
    );
    assert!(
        index.contains("| `public_mirror` | public object not fetchable |"),
        "{index}"
    );
    assert!(
        index.contains(
            "public mirror evidence plus release manifest both name the exact release commit"
        ),
        "{index}"
    );
    assert!(
        index.contains("Do not publish a broad public-launch claim"),
        "{index}"
    );
    assert!(!index.contains("public broad public-launch"), "{index}");
}

#[test]
#[timeout(30_000)]
fn launch_packet_index_can_fail_on_missing_required_artifacts() {
    let repo = TempDir::new().expect("temp repo");
    write_standard_docs(repo.path());
    let packet = repo.path().join("packet");
    fs::create_dir_all(&packet).expect("mkdir packet");

    let output = Command::new(ay_binary())
        .args(["launch-packet", "index", "--packet-dir"])
        .arg(&packet)
        .arg("--repo-root")
        .arg(repo.path())
        .args([
            "--release-commit",
            "94b1811a4ecf9ddf7ed04c5eb78d3c4cb50c2f89",
            "--fail-on-missing",
        ])
        .output()
        .expect("spawn ay launch-packet index --fail-on-missing");

    assert_eq!(
        output.status.code(),
        Some(1),
        "missing required artifacts should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("missing required artifacts"),
        "stderr should name missing artifacts"
    );
    let index = fs::read_to_string(packet.join("INDEX.md")).expect("read index");
    assert!(
        index.contains("| public mirror evidence | `MISSING` |"),
        "{index}"
    );
    assert!(
        index.contains("| AUFLIA evidence or blocker note | `not supplied` |"),
        "{index}"
    );
}

fn init_git_repo(path: &Path) {
    fs::write(path.join("README.md"), "# launch packet fixture\n").expect("write readme");
    for args in [
        vec!["init"],
        vec!["config", "user.email", "ay-launch-packet-test@example.com"],
        vec!["config", "user.name", "AY Launch Packet Test"],
        vec!["add", "."],
        vec!["commit", "-m", "initial fixture"],
    ] {
        let output = Command::new("git")
            .current_dir(path)
            .args(args)
            .output()
            .expect("spawn git");
        assert!(
            output.status.success(),
            "git failed:\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn read_json(path: &Path) -> Value {
    serde_json::from_slice(&fs::read(path).expect("read json")).expect("parse json")
}

fn write_json(path: &Path, value: &Value) {
    fs::write(
        path,
        serde_json::to_vec_pretty(value).expect("serialize json"),
    )
    .expect("write json");
}

fn read_jsonl_first(path: &Path) -> Value {
    let text = fs::read_to_string(path).expect("read jsonl");
    serde_json::from_str(text.lines().next().expect("jsonl row")).expect("parse jsonl row")
}

fn assert_success(output: &std::process::Output, context: &str) {
    assert!(
        output.status.success(),
        "{context}:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn write_fake_reference_solver(repo: &TempDir, name: &str) -> PathBuf {
    let path = repo.path().join("bin").join(name);
    write_executable(
        &path,
        "#!/usr/bin/env sh\nif [ \"$1\" = \"--version\" ]; then echo fake-ref 1.0; exit 0; fi\nexit 0\n",
    );
    path
}

fn write_standard_docs(repo: &Path) {
    for path in [
        "the development design notes",
        "the development design notes",
        "the development design notes",
        "the development design notes",
        "the development design notes",
    ] {
        let path = repo.join(path);
        fs::create_dir_all(path.parent().expect("doc parent")).expect("mkdir docs");
        fs::write(path, "# fixture\n").expect("write doc");
    }
}

fn write_eval_registry(repo: &Path, eval_id: &str, body: &str) {
    let registry_dir = repo.join("evals/registry");
    fs::create_dir_all(&registry_dir).expect("mkdir registry");
    fs::write(
        registry_dir.join(format!("{eval_id}.yaml")),
        body.trim_start(),
    )
    .expect("write registry");
}

fn write_minimal_launch_registry(repo: &Path, eval_ids: &[&str]) {
    fs::write(repo.join("Cargo.toml"), "[workspace]\n").expect("write Cargo.toml");
    for eval_id in eval_ids {
        write_eval_registry(
            repo,
            eval_id,
            &format!(
                "id: {eval_id}\ninputs:\n  benchmarks_dir: benchmarks/{eval_id}\n  timeout_sec: 30\n"
            ),
        );
    }
}

fn launch_eval_ids() -> [&'static str; 8] {
    [
        "smt-local-suite",
        "smt-smtcomp-qf-lia",
        "smt-smtcomp-qf-lra",
        "smt-smtcomp-qf-bv",
        "smt-smtcomp-qf-abv",
        "chccomp-2025-extra-small-lia",
        "sat-par2-dev",
        "z3-perf-cliffs",
    ]
}

fn write_executable(path: &Path, body: &str) {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent).expect("mkdir executable parent");
    }
    fs::write(path, body).expect("write executable");
    make_executable(path);
}

fn make_executable(path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let mut permissions = fs::metadata(path).expect("metadata").permissions();
        permissions.set_mode(0o755);
        fs::set_permissions(path, permissions).expect("chmod executable");
    }
}
