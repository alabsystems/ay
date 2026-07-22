// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI coverage for `ay bench chc-gate`.

#![cfg(unix)]

use ntest::timeout;
use serde_json::Value;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn write_case(dir: &Path, name: &str) -> PathBuf {
    let path = dir.join(name);
    fs::write(&path, "(set-logic HORN)\n(check-sat)\n").expect("write CHC case");
    path
}

fn write_manifest(dir: &Path, rows: Value) -> PathBuf {
    let manifest = dir.join("manifest.json");
    fs::write(
        &manifest,
        serde_json::json!({ "benchmarks": rows }).to_string(),
    )
    .expect("write manifest");
    manifest
}

fn write_stub(dir: &Path, body: &str) -> PathBuf {
    let stub = dir.join("ay-chc-stub.sh");
    fs::write(&stub, body).expect("write stub");
    let mut permissions = fs::metadata(&stub).expect("stub metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&stub, permissions).expect("chmod stub");
    stub
}

fn base_stub() -> &'static str {
    r#"#!/bin/sh
if [ "$1" = "--version" ]; then
  echo "ay chc-gate stub"
  exit 0
fi
input=""
for arg in "$@"; do
  input="$arg"
done
case "$input" in
  *unsafe*)
    echo "unsat"
    echo '{"mode":"portfolio","result":"unsat","wall_time_ms":1,"chc.validation.safe_attempts":0,"chc.validation.safe_successes":0,"chc.validation.safe_failures":0,"chc.validation.unsafe_attempts":1,"chc.validation.unsafe_successes":1,"chc.validation.unsafe_failures":0,"chc.transform_memory.reversible_count":1,"chc.transform_memory.obligation_count":1,"chc.route.name":"stub","chc.route.accepted_by_firewall":true,"chc.route.fail_closed_reason":"","chc.demo_route_hits":1}' >&2
    ;;
  *)
    echo "sat"
    echo '{"mode":"portfolio","result":"sat","wall_time_ms":1,"chc.validation.safe_attempts":1,"chc.validation.safe_successes":1,"chc.validation.safe_failures":0,"chc.validation.unsafe_attempts":0,"chc.validation.unsafe_successes":0,"chc.validation.unsafe_failures":0,"chc.transform_memory.reversible_count":1,"chc.transform_memory.obligation_count":1,"chc.route.name":"stub","chc.route.accepted_by_firewall":true,"chc.route.fail_closed_reason":"","chc.demo_route_hits":1}' >&2
    ;;
esac
"#
}

#[test]
#[timeout(30_000)]
fn chc_gate_accepts_valid_safe_and_unsafe_stub_rows() {
    let dir = TempDir::new().expect("tempdir");
    let safe = write_case(dir.path(), "safe.smt2");
    let unsafe_case = write_case(dir.path(), "unsafe.smt2");
    let manifest = write_manifest(
        dir.path(),
        serde_json::json!([
            {
                "id": "safe-row",
                "path": safe,
                "category": "LIA-Lin",
                "family": "stub/safe",
                "expected_status": "sat"
            },
            {
                "id": "unsafe-row",
                "path": unsafe_case,
                "category": "BV-Lin",
                "family": "stub/unsafe",
                "expected_status": "unsat"
            }
        ]),
    );
    let stub = write_stub(dir.path(), base_stub());
    let out_dir = dir.path().join("out");

    let output = Command::new(ay_binary())
        .current_dir(dir.path())
        .args(["bench", "chc-gate", "--manifest"])
        .arg(&manifest)
        .arg("--out-dir")
        .arg(&out_dir)
        .arg("--ay")
        .arg(&stub)
        .args([
            "--timeout",
            "2",
            "--fail-on-wrong",
            "--fail-on-invalid",
            "--require-route-counter",
            "chc.demo_route_hits",
        ])
        .output()
        .expect("spawn ay bench chc-gate");

    assert!(
        output.status.success(),
        "chc-gate should pass:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let summary: Value =
        serde_json::from_str(&fs::read_to_string(out_dir.join("summary.json")).unwrap())
            .expect("parse summary");
    assert_eq!(summary["summary"]["solved"], 2, "{summary:#}");
    assert_eq!(summary["summary"]["wrong"], 0, "{summary:#}");
    assert_eq!(summary["summary"]["invalid"], 0, "{summary:#}");
    assert!(out_dir.join("cases.jsonl").is_file());
    assert!(out_dir.join("category-summary.csv").is_file());
    assert!(out_dir.join("route-counters.json").is_file());
    assert!(out_dir.join("admission.md").is_file());
}

#[test]
#[timeout(30_000)]
fn chc_gate_fail_on_wrong_rejects_definitive_disagreement() {
    let dir = TempDir::new().expect("tempdir");
    let safe = write_case(dir.path(), "safe.smt2");
    let manifest = write_manifest(
        dir.path(),
        serde_json::json!([{
            "id": "wrong-row",
            "path": safe,
            "category": "LIA",
            "expected_status": "unsat"
        }]),
    );
    let stub = write_stub(dir.path(), base_stub());

    let output = Command::new(ay_binary())
        .current_dir(dir.path())
        .args(["bench", "chc-gate", "--manifest"])
        .arg(&manifest)
        .arg("--out-dir")
        .arg(dir.path().join("out"))
        .arg("--ay")
        .arg(&stub)
        .args(["--timeout", "2", "--fail-on-wrong"])
        .output()
        .expect("spawn ay bench chc-gate wrong");

    assert!(
        !output.status.success(),
        "wrong row should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn chc_gate_fail_on_invalid_rejects_missing_validation_success() {
    let dir = TempDir::new().expect("tempdir");
    let safe = write_case(dir.path(), "safe.smt2");
    let manifest = write_manifest(
        dir.path(),
        serde_json::json!([{
            "id": "invalid-row",
            "path": safe,
            "category": "LIA",
            "expected_status": "sat"
        }]),
    );
    let stub = write_stub(
        dir.path(),
        r#"#!/bin/sh
if [ "$1" = "--version" ]; then echo "ay invalid stub"; exit 0; fi
echo "sat"
echo '{"mode":"portfolio","result":"sat","wall_time_ms":1,"chc.validation.safe_attempts":1,"chc.validation.safe_successes":0,"chc.validation.safe_failures":1,"chc.route.name":"stub","chc.route.accepted_by_firewall":true,"chc.route.fail_closed_reason":""}' >&2
"#,
    );

    let output = Command::new(ay_binary())
        .current_dir(dir.path())
        .args(["bench", "chc-gate", "--manifest"])
        .arg(&manifest)
        .arg("--out-dir")
        .arg(dir.path().join("out"))
        .arg("--ay")
        .arg(&stub)
        .args(["--timeout", "2", "--fail-on-invalid"])
        .output()
        .expect("spawn ay bench chc-gate invalid");

    assert!(
        !output.status.success(),
        "invalid row should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn chc_gate_requires_route_counter_exercise() {
    let dir = TempDir::new().expect("tempdir");
    let safe = write_case(dir.path(), "safe.smt2");
    let manifest = write_manifest(
        dir.path(),
        serde_json::json!([{
            "id": "route-row",
            "path": safe,
            "category": "LIA",
            "expected_status": "sat"
        }]),
    );
    let stub = write_stub(dir.path(), base_stub());

    let output = Command::new(ay_binary())
        .current_dir(dir.path())
        .args(["bench", "chc-gate", "--manifest"])
        .arg(&manifest)
        .arg("--out-dir")
        .arg(dir.path().join("out"))
        .arg("--ay")
        .arg(&stub)
        .args([
            "--timeout",
            "2",
            "--require-route-counter",
            "chc.never_exercised",
        ])
        .output()
        .expect("spawn ay bench chc-gate missing route");

    assert!(
        !output.status.success(),
        "missing route counter should fail:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[timeout(30_000)]
fn chc_gate_rejects_dirty_provenance_without_allow_dirty() {
    let dir = TempDir::new().expect("tempdir");
    let safe = write_case(dir.path(), "safe.smt2");
    let manifest = write_manifest(
        dir.path(),
        serde_json::json!([{
            "id": "dirty-row",
            "path": safe,
            "category": "LIA",
            "expected_status": "sat"
        }]),
    );
    let stub = write_stub(dir.path(), base_stub());

    let output = Command::new(ay_binary())
        .current_dir(dir.path())
        .env("AY_BENCH_CHC_GATE_FORCE_DIRTY", "1")
        .args(["bench", "chc-gate", "--manifest"])
        .arg(&manifest)
        .arg("--out-dir")
        .arg(dir.path().join("out"))
        .arg("--ay")
        .arg(&stub)
        .args(["--timeout", "2"])
        .output()
        .expect("spawn ay bench chc-gate dirty");

    assert!(
        !output.status.success(),
        "dirty evidence should fail without --allow-dirty:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
