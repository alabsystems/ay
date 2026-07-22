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

    let help = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["z3-audit", "--help"])
        .output()
        .expect("read z3-audit help");
    let help_stdout = String::from_utf8_lossy(&help.stdout);
    assert!(
        help.status.success(),
        "help stderr: {}",
        String::from_utf8_lossy(&help.stderr)
    );
    assert!(
        help_stdout.contains("AY workspace root containing Cargo.toml and crates/ay/Cargo.toml"),
        "help:\n{help_stdout}"
    );
    assert!(
        help_stdout.contains("explicitly inventoried"),
        "help:\n{help_stdout}"
    );
    assert!(
        !help_stdout.contains("Repository root containing docs/"),
        "help must not require private docs:\n{help_stdout}"
    );

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["z3-audit", "--scope", "cli-subset", "--inventory-only"])
        .current_dir(snapshot.path())
        .env("AY_INTERNAL_PROVENANCE_CHILD", "1")
        .output()
        .expect("run z3-audit from docs-free snapshot");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "z3-audit failed without docs\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(stdout.contains("scope=cli-subset"), "stdout:\n{stdout}");
    assert!(stdout.contains("verdict=pass"), "stdout:\n{stdout}");
    assert!(
        stdout.contains("compatibility_inventory"),
        "stdout:\n{stdout}"
    );
    assert!(
        stdout.contains("private compatibility prose is not shipped"),
        "stdout:\n{stdout}"
    );
}
