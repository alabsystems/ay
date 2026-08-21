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

include!("launch_packet_cli/core_packet_tests.rs");

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
