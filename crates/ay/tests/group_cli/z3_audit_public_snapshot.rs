// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for running `ay z3-audit` from the docs-free public tree.

use std::fs;
use std::path::Path;
use std::process::Command;

#[test]
fn scoped_z3_audit_runs_without_private_docs() {
    let source_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let snapshot = tempfile::tempdir().expect("public snapshot tempdir");
    let cache_dir = snapshot.path().join("tests/z3-audit");
    let benchmark_dir = snapshot.path().join("benchmarks/chc");
    let ay_crate_dir = snapshot.path().join("crates/ay");
    fs::create_dir_all(&cache_dir).expect("reference cache directory");
    fs::create_dir_all(&benchmark_dir).expect("CHC benchmark directory");
    fs::create_dir_all(&ay_crate_dir).expect("ay crate directory");
    fs::create_dir_all(snapshot.path().join("ci")).expect("reference pin directory");
    fs::copy(
        source_root.join("ci/z3.pin"),
        snapshot.path().join("ci/z3.pin"),
    )
    .expect("copy actual reference pin");
    fs::write(snapshot.path().join("Cargo.toml"), "[workspace]\n").expect("workspace manifest");
    fs::write(
        ay_crate_dir.join("Cargo.toml"),
        "[package]\nname = \"ay\"\nversion = \"0.0.0\"\n",
    )
    .expect("ay crate manifest");
    fs::copy(
        source_root.join("tests/z3-audit/reference-cache.json"),
        cache_dir.join("reference-cache.json"),
    )
    .expect("copy reference cache");
    fs::copy(
        source_root.join("benchmarks/chc/counter_safe_chccomp.smt2"),
        benchmark_dir.join("counter_safe_chccomp.smt2"),
    )
    .expect("copy CHC canary");

    assert!(
        !snapshot.path().join("docs").exists(),
        "fixture must model the docs-free public snapshot"
    );

    let summary = snapshot.path().join("audit.json");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["z3-audit", "--scope", "cli-subset", "--inventory-only"])
        .arg("--summary-json")
        .arg(&summary)
        .current_dir(snapshot.path())
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .output()
        .expect("run z3-audit from docs-free snapshot");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.code() == Some(1),
        "inventory-only must remain incomplete\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    let report: serde_json::Value = serde_json::from_slice(&fs::read(summary).unwrap()).unwrap();
    assert_eq!(report["verdict"], "incomplete");
    assert_eq!(report["reference_cache_loaded"], true);
    assert_eq!(report["full_replacement_ready"], false);
    for id in [
        "reference_cache",
        "z3_version",
        "basic_smt_transcript",
        "compatibility_inventory",
    ] {
        let check = report["checks"]
            .as_array()
            .unwrap()
            .iter()
            .find(|check| check["id"] == id)
            .expect("required semantic check");
        assert_eq!(check["status"], "pass", "{check}");
    }
    let alethe = report["proof_inventory"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["id"] == "smt_alethe_external_replay")
        .unwrap();
    assert_eq!(alethe["status"], "not_run");
}
