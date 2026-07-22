// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CLI coverage for native release evidence tooling.

use ntest::timeout;
use serde_json::{json, Value};
use std::fs;
use std::path::Path;
use std::process::Command;
use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

#[test]
#[timeout(30_000)]
fn release_verify_public_ay_commit_rejects_invalid_commit_before_git() {
    let output = Command::new(ay_binary())
        .args(["release", "verify-public-ay-commit", "not-a-sha"])
        .output()
        .expect("spawn ay release verify-public-ay-commit");

    assert_eq!(
        output.status.code(),
        Some(2),
        "invalid commit should be a usage-shaped verifier failure:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let payload: Value =
        serde_json::from_slice(&output.stdout).expect("parse invalid commit evidence");
    assert_eq!(payload["schema"], "ay-public-commit-evidence/v1");
    assert_eq!(payload["status"], "fail");
    assert_eq!(payload["failure_kind"], "invalid-commit");
    assert_eq!(payload["url"], "https://github.com/alabsystems/ay.git");
}

#[test]
#[timeout(30_000)]
fn release_verify_public_pins_no_fetch_reports_native_schema() {
    // Drive the verifier against a self-contained fixture repo whose Cargo.lock
    // pins the private EXTERNAL_CODEGEN/external_codegen_ir release sources. The live workspace only
    // vendors these git dependencies in the private tree, so a normal/public
    // checkout would otherwise have nothing to pin-verify here.
    let repo = TempDir::new().expect("temp release pins repo");
    fs::write(
        repo.path().join("Cargo.lock"),
        concat!(
            "# release-pin verification fixture lockfile.\n\n",
            "[[package]]\n",
            "name = \"external_codegen-ir\"\n",
            "version = \"0.1.0\"\n",
            "source = \"git+ssh://git@github.com/example/EXTERNAL_CODEGEN.git?rev=",
            "1111111111111111111111111111111111111111#",
            "1111111111111111111111111111111111111111\"\n\n",
            "[[package]]\n",
            "name = \"external_codegen_ir\"\n",
            "version = \"0.1.0\"\n",
            "source = \"git+ssh://git@github.com:22/example/external_codegen_ir.git#",
            "2222222222222222222222222222222222222222\"\n",
        ),
    )
    .expect("write release pins fixture lockfile");

    let output = Command::new(ay_binary())
        .args([
            "release",
            "verify-public-pins",
            "--repo-root",
            repo.path().to_str().expect("repo path utf8"),
            "--no-fetch",
            "--json",
        ])
        .output()
        .expect("spawn ay release verify-public-pins");

    assert!(
        output.status.success(),
        "public pins no-fetch should pass:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    let payload: Value = serde_json::from_slice(&output.stdout).expect("parse pins evidence");
    assert_eq!(payload["schema"], "ay-public-release-pins/v1");
    assert_eq!(payload["status"], "pass");
    assert_eq!(payload["source"]["public_fetch_checked"], false);
    assert!(payload["pins"]
        .as_array()
        .is_some_and(|pins| !pins.is_empty()));
}

#[cfg(unix)]
#[test]
#[timeout(30_000)]
fn release_manifest_generate_and_verify_round_trip() {
    let temp = TempDir::new().expect("temp release evidence");
    let commit = "0123456789abcdef0123456789abcdef01234567";
    let public_evidence = temp.path().join("public.json");
    let dependency_pins = temp.path().join("pins.json");
    let version_file = temp.path().join("version.txt");
    let status_log = temp.path().join("release-manifest-inputs.log");
    let artifact = temp.path().join("ay-release");
    let manifest = temp.path().join("manifest.json");

    write_json(&public_evidence, &public_commit_evidence(commit));
    write_json(&dependency_pins, &dependency_pin_evidence(commit));
    let version = format!(
        "build.version=0.10.0\nbuild.commit={}\nbuild.stamp=release-cli-test",
        &commit[..12]
    );
    fs::write(&version_file, format!("{version}\n")).expect("write version file");
    fs::write(&status_log, "release-manifest-inputs: PASS\n").expect("write status log");
    write_executable(
        &artifact,
        &format!(
            "#!/usr/bin/env sh\nif [ \"${{1:-}}\" = \"--version\" ]; then cat <<'EOF'\n{version}\nEOF\nexit 0\nfi\nexit 0\n"
        ),
    );

    let generate = Command::new(ay_binary())
        .args([
            "release",
            "generate-manifest",
            "--repo-root",
            temp.path().to_str().expect("temp path utf8"),
            "--channel",
            "public",
            "--private-commit",
            commit,
            "--public-evidence",
        ])
        .arg(&public_evidence)
        .arg("--dependency-pins")
        .arg(&dependency_pins)
        .args(["--build-command", "cargo build --release -p ay --locked"])
        .arg("--artifact-path")
        .arg(&artifact)
        .arg("--binary-version-file")
        .arg(&version_file)
        .arg("--launch-gate-status")
        .arg(format!(
            "release_manifest_inputs={}",
            status_log.to_string_lossy()
        ))
        .args(["--generated-at", "2026-05-07T00:00:00Z", "--output"])
        .arg(&manifest)
        .output()
        .expect("spawn ay release generate-manifest");

    assert_success(&generate, "generate manifest");
    let manifest_payload: Value =
        serde_json::from_slice(&fs::read(&manifest).expect("read manifest"))
            .expect("parse manifest");
    assert_eq!(manifest_payload["schema"], "ay-release-manifest/v1");
    assert_eq!(manifest_payload["status"], "pass");
    assert_eq!(
        manifest_payload["release"]["claim_status"],
        "public-release-ready"
    );

    let verify = Command::new(ay_binary())
        .args(["release", "verify-manifest", "--manifest"])
        .arg(&manifest)
        .arg("--artifact")
        .arg(&artifact)
        .arg("--run-version")
        .output()
        .expect("spawn ay release verify-manifest");

    assert_success(&verify, "verify manifest");
    let verification: Value =
        serde_json::from_slice(&verify.stdout).expect("parse manifest verification");
    assert_eq!(
        verification["schema"],
        "ay-release-manifest-verification/v1"
    );
    assert_eq!(verification["status"], "pass");
    assert_eq!(
        verification["checks"]["artifact_version_matches_manifest"],
        true
    );
}

fn public_commit_evidence(commit: &str) -> Value {
    json!({
        "schema": "ay-public-commit-evidence/v1",
        "status": "pass",
        "url": "https://github.com/alabsystems/ay.git",
        "public_ref": "refs/heads/main",
        "commit": commit,
        "expected_commit": commit,
        "fetchable": true,
        "fetched_commit": commit,
        "fetch_exit": 0,
        "rev_parse_exit": 0,
        "ref_checked": true,
        "ref_commit": commit,
        "ref_matches_commit": true,
        "ls_remote_exit": 0,
        "failure_kind": null,
        "git_env": {
            "GIT_CONFIG_GLOBAL": "/dev/null",
            "GIT_CONFIG_NOSYSTEM": "1",
            "GIT_TERMINAL_PROMPT": "0"
        },
        "fetch_command": [
            "git",
            "fetch",
            "--depth",
            "1",
            "https://github.com/alabsystems/ay.git",
            commit
        ],
        "ls_remote_command": [
            "git",
            "ls-remote",
            "--exit-code",
            "https://github.com/alabsystems/ay.git",
            "refs/heads/main"
        ]
    })
}

fn dependency_pin_evidence(commit: &str) -> Value {
    json!({
        "schema": "ay-public-release-pins/v1",
        "status": "pass",
        "source": {
            "cargo_wrapper": "cargo_wrapper.toml",
            "lockfile": "Cargo.lock",
            "manifests": ["Cargo.toml"],
            "public_fetch_checked": true,
            "ay_commit": commit
        },
        "auto_bump": [],
        "pins": [
            {
                "name": "EXTERNAL_CODEGEN",
                "url": "ssh://git@github.com/example/EXTERNAL_CODEGEN.git",
                "commit": "1111111111111111111111111111111111111111",
                "rev": "1111111111111111111111111111111111111111",
                "component_version": "0.1.0",
                "packages": ["external_codegen"],
                "package_versions": {"external_codegen": "0.1.0"}
            },
            {
                "name": "ExternalCodegenIr",
                "url": "ssh://git@github.com/example/external_codegen_ir.git",
                "commit": "2222222222222222222222222222222222222222",
                "rev": null,
                "component_version": "0.1.0",
                "packages": ["external_codegen_ir"],
                "package_versions": {"external_codegen_ir": "0.1.0"}
            }
        ]
    })
}

fn write_json(path: &Path, value: &Value) {
    fs::write(
        path,
        serde_json::to_vec_pretty(value).expect("serialize json"),
    )
    .expect("write json");
}

#[cfg(unix)]
fn write_executable(path: &Path, contents: &str) {
    use std::os::unix::fs::PermissionsExt;

    fs::write(path, contents).expect("write executable");
    let mut permissions = fs::metadata(path).expect("metadata").permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("chmod executable");
}

fn assert_success(output: &std::process::Output, context: &str) {
    assert!(
        output.status.success(),
        "{context} should succeed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}
