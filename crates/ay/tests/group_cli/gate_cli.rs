// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI coverage for native CI/release gates.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("ay crate should live under crates/ay")
        .to_path_buf()
}

#[test]
fn gate_help_exposes_solver_and_publish() {
    let output = Command::new(ay_binary())
        .arg("gate")
        .arg("--help")
        .output()
        .expect("spawn ay gate --help");

    assert!(
        output.status.success(),
        "gate help should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("health"),
        "missing health subcommand:\n{stdout}"
    );
    assert!(
        stdout.contains("precommit"),
        "missing precommit subcommand:\n{stdout}"
    );
    assert!(
        stdout.contains("solver"),
        "missing solver subcommand:\n{stdout}"
    );
    assert!(
        stdout.contains("publish"),
        "missing publish subcommand:\n{stdout}"
    );
}

#[test]
fn health_gate_can_list_checks_without_running_smoke() {
    let output = Command::new(ay_binary())
        .args(["gate", "health", "--list-checks"])
        .current_dir(repo_root())
        .output()
        .expect("spawn ay gate health --list-checks");

    assert!(
        output.status.success(),
        "health list-checks should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    for expected in [
        "[health-gate] checks",
        "Git Rebase State",
        "Submodule Metadata",
        "Reports Directory",
        "Compile",
        "SMT SAT",
        "SMT UNSAT",
        "CHC Safe",
    ] {
        assert!(stdout.contains(expected), "missing {expected:?}:\n{stdout}");
    }
}

#[test]
fn precommit_gate_can_list_checks_without_reading_index() {
    let output = Command::new(ay_binary())
        .args(["gate", "precommit", "--list-checks"])
        .current_dir(repo_root())
        .output()
        .expect("spawn ay gate precommit --list-checks");

    assert!(
        output.status.success(),
        "precommit list-checks should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    for expected in [
        "[precommit-gate] checks",
        "theory-verification",
        "todo-issue-refs",
        "reject-colon-filenames",
        "reject-transient-worktree-paths",
    ] {
        assert!(stdout.contains(expected), "missing {expected:?}:\n{stdout}");
    }
}

#[test]
fn solver_gate_can_list_native_steps_without_running_heavy_gate() {
    let output = Command::new(ay_binary())
        .args(["gate", "solver", "--list-steps"])
        .current_dir(repo_root())
        .output()
        .expect("spawn ay gate solver --list-steps");

    assert!(
        output.status.success(),
        "solver list-steps should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    for expected in [
        "[solver-gate] Root:",
        "solver_gate_wiring\t<native>",
        "critical_solver_policy\tbash scripts/check_critical_solver_policy.sh",
        "debug_ay_smtlib_conformance_summary\tcargo test --locked -p ay --features cli --test group_smt",
        "release_ay_dpll_qf_bv_differential_strict\tZ3_DIFFERENTIAL_REQUIRED=1 cargo test",
    ] {
        assert!(stdout.contains(expected), "missing {expected:?}:\n{stdout}");
    }
}

#[test]
fn publish_gate_can_list_native_steps_without_running_heavy_gate() {
    let output = Command::new(ay_binary())
        .args(["gate", "publish", "--list-steps"])
        .current_dir(repo_root())
        .output()
        .expect("spawn ay gate publish --list-steps");

    assert!(
        output.status.success(),
        "publish list-steps should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    for expected in [
        "[publish-gate] Root:",
        "release_gate_wiring\t<native>",
        "release_public_crate_metadata\t<native>",
        "repository_health\t<native>",
        "critical_solver_policy\tbash scripts/check_critical_solver_policy.sh",
        "cargo_check_workspace\tcargo check --workspace",
    ] {
        assert!(stdout.contains(expected), "missing {expected:?}:\n{stdout}");
    }
}

fn run_critical_solver_policy(command: &str) -> Output {
    let tmp = TempDir::new().expect("tempdir");
    let paths = tmp.path().join("paths.txt");
    let message = tmp.path().join("message.txt");
    fs::write(&paths, "crates/ay/src/cmd_gate.rs\n").expect("write paths");
    fs::write(
        &message,
        format!("native gate test\n\n## Verified\n- solver-gate: {command}\n"),
    )
    .expect("write message");

    Command::new("bash")
        .args([
            "scripts/check_critical_solver_policy.sh",
            "--paths-file",
            paths.to_str().expect("paths utf8"),
            "--message-file",
            message.to_str().expect("message utf8"),
        ])
        .current_dir(repo_root())
        .output()
        .expect("spawn critical solver policy")
}

#[test]
fn critical_solver_policy_requires_canonical_cargo_evidence() {
    let canonical = "cargo run --locked -p ay --features cli -- gate solver";
    let output = run_critical_solver_policy(canonical);
    assert!(
        output.status.success(),
        "policy rejected canonical command: {canonical}\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let rejected = [
        (
            "old command without cli",
            "cargo run --locked -p ay -- gate solver",
        ),
        (
            "missing locked",
            "cargo run -p ay --features cli -- gate solver",
        ),
        (
            "missing package",
            "cargo run --locked --features cli -- gate solver",
        ),
        (
            "wrong package",
            "cargo run --locked -p ay-client --features cli -- gate solver",
        ),
        (
            "long package spelling",
            "cargo run --locked --package ay --features cli -- gate solver",
        ),
        (
            "package equals spelling",
            "cargo run --locked --package=ay --features cli -- gate solver",
        ),
        (
            "feature equals spelling",
            "cargo run --locked -p ay --features=cli -- gate solver",
        ),
        (
            "short feature spelling",
            "cargo run --locked -p ay -F cli -- gate solver",
        ),
        (
            "quoted feature",
            "cargo run --locked -p ay --features 'cli' -- gate solver",
        ),
        (
            "all features spelling",
            "cargo run --locked -p ay --all-features -- gate solver",
        ),
        (
            "extra solver feature",
            "cargo run --locked -p ay --features cli,solver -- gate solver",
        ),
        (
            "solver feature only",
            "cargo run --locked -p ay --features solver -- gate solver",
        ),
        (
            "environment wrapper",
            "env cargo run --locked -p ay --features cli -- gate solver",
        ),
        (
            "environment assignment",
            "CARGO_TERM_COLOR=never cargo run --locked -p ay --features cli -- gate solver",
        ),
        ("direct binary", "target/release/ay gate solver"),
        ("path binary", "./target/debug/ay gate solver"),
        (
            "client feature substring",
            "cargo run --locked -p ay --features client -- gate solver",
        ),
        (
            "cli-disabled feature substring",
            "cargo run --locked -p ay --features cli-disabled -- gate solver",
        ),
        (
            "feature after separator",
            "cargo run --locked -p ay -- gate solver --features cli",
        ),
        (
            "feature in comment",
            "cargo run --locked -p ay -- gate solver # --features cli",
        ),
        (
            "comment after canonical command",
            "cargo run --locked -p ay --features cli -- gate solver # local gate",
        ),
        (
            "all-features false",
            "cargo run --locked -p ay --all-features=false -- gate solver",
        ),
        (
            "all-features false beside cli",
            "cargo run --locked -p ay --features cli --all-features=false -- gate solver",
        ),
        (
            "package after separator",
            "cargo run --locked --features cli -- gate solver -p ay",
        ),
        (
            "extra gate argument",
            "cargo run --locked -p ay --features cli -- gate solver --list-steps",
        ),
        (
            "manifest path",
            "cargo run --locked -p ay --features cli --manifest-path Cargo.toml -- gate solver",
        ),
        (
            "example target",
            "cargo run --locked -p ay --features cli --example demo -- gate solver",
        ),
        (
            "binary target",
            "cargo run --locked -p ay --features cli --bin ay -- gate solver",
        ),
        (
            "positional Cargo argument",
            "cargo run --locked -p ay --features cli unexpected -- gate solver",
        ),
        (
            "unknown Cargo flag",
            "cargo run --locked -p ay --features cli --unknown -- gate solver",
        ),
        (
            "reordered canonical flags",
            "cargo run -p ay --locked --features cli -- gate solver",
        ),
        (
            "duplicate interior whitespace",
            "cargo run  --locked -p ay --features cli -- gate solver",
        ),
        (
            "solver suffix",
            "cargo run --locked -p ay --features cli -- gate solver-extra",
        ),
        (
            "shell control operator",
            "cargo run --locked -p ay --features cli && echo -- gate solver",
        ),
    ];
    for (case, command) in rejected {
        let output = run_critical_solver_policy(command);
        assert!(
            !output.status.success(),
            "policy accepted {case}: {command}"
        );
    }
}
