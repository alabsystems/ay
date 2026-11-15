// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The shim's contract, pinned against a stand-in Cargo that reports where it
//! ran, what it was asked and which compiler it was given.

use super::*;
use std::os::unix::fs::PermissionsExt as _;
use std::process::{Command, Output};

/// Prints its working directory, then each argument, then `RUSTC` and
/// `CARGO_TARGET_DIR`.
const RECORDING_CARGO: &str = "#!/bin/sh\npwd -P\nfor argument do printf '%s\\n' \"$argument\"; done\nprintf 'RUSTC=%s\\n' \"$RUSTC\"\nprintf 'CARGO_TARGET_DIR=%s\\n' \"${CARGO_TARGET_DIR-unset}\"\n";

struct Fixture {
    _root: tempfile::TempDir,
    shim: PathBuf,
    /// Holds the `Cargo.toml`; the shim is run from a directory below it.
    package: PathBuf,
    caller: PathBuf,
    working_directory: PathBuf,
    rustc: PathBuf,
}

fn write_executable(path: &Path, text: &str) {
    filesystem::write(path, text).expect("write test executable");
    filesystem::set_permissions(path, filesystem::Permissions::from_mode(0o755))
        .expect("mark test executable");
}

fn fixture(driver: CargoDriver) -> Fixture {
    let root = tempfile::tempdir().expect("temporary directory");
    let base = root
        .path()
        .canonicalize()
        .expect("canonical temporary directory");
    // A space and a quote in the path exercise the shim's quoting.
    let tools = base.join("tool's dir");
    filesystem::create_dir_all(&tools).expect("tools directory");
    let cargo = tools.join("cargo");
    write_executable(&cargo, RECORDING_CARGO);
    let rustc = tools.join("rustc");
    let working_directory = base.join("chosen");
    filesystem::create_dir_all(&working_directory).expect("working directory");
    let package = base.join("package");
    let caller = package.join("nested");
    filesystem::create_dir_all(&caller).expect("caller directory");
    filesystem::write(package.join("Cargo.toml"), "").expect("manifest");
    let shim = base.join("shim");
    write_executable(
        &shim,
        &shim_script(&cargo, driver, &rustc, &working_directory),
    );
    Fixture {
        _root: root,
        shim,
        package,
        caller,
        working_directory,
        rustc,
    }
}

fn run_shim(fixture: &Fixture, arguments: &[&str]) -> Output {
    Command::new(&fixture.shim)
        .args(arguments)
        .current_dir(&fixture.caller)
        .env("RUSTC", "ambient-rustc")
        .env_remove("CARGO_TARGET_DIR")
        .output()
        .expect("run shim")
}

/// What the stand-in Cargo recorded: working directory, arguments, compiler.
fn recorded(fixture: &Fixture, arguments: &[&str]) -> Vec<String> {
    let output = run_shim(fixture, arguments);
    assert!(
        output.status.success(),
        "shim failed for {arguments:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("UTF-8 record")
        .lines()
        .map(str::to_owned)
        .collect()
}

fn expected(fixture: &Fixture, arguments: &[&str]) -> Vec<String> {
    let mut lines = vec![fixture.working_directory.display().to_string()];
    lines.extend(arguments.iter().map(|argument| (*argument).to_owned()));
    lines.push(format!("RUSTC={}", fixture.rustc.display()));
    lines.push("CARGO_TARGET_DIR=unset".to_owned());
    lines
}

#[test]
fn a_compiling_subcommand_takes_the_lane_and_runs_from_the_chosen_directory() {
    let targo = fixture(CargoDriver::Targo);
    let manifest = targo.package.join("Cargo.toml");
    let manifest = manifest.to_str().expect("UTF-8 manifest");
    // The argv shape trybuild's `build_test` produces.
    let config = r#"--config=target.x.rustflags=["--cfg", "trybuild"]"#;
    assert_eq!(
        recorded(
            &targo,
            &[
                "--offline",
                config,
                "check",
                "--target",
                "x",
                "--bin",
                "case"
            ]
        ),
        expected(
            &targo,
            &[
                "--unverified",
                "--offline",
                config,
                "check",
                "--manifest-path",
                manifest,
                "--target",
                "x",
                "--bin",
                "case"
            ]
        ),
        "the lane precedes everything, the manifest follows the subcommand, and Cargo \
         runs from the chosen directory with the paired compiler, not the ambient one"
    );
    for subcommand in COMPILING_SUBCOMMANDS {
        let record = recorded(&targo, &["--offline", *subcommand]);
        assert_eq!(record[1], "--unverified", "{subcommand} must take the lane");
    }
}

#[test]
fn a_non_compiling_subcommand_takes_no_lane() {
    let targo = fixture(CargoDriver::Targo);
    let manifest = targo.package.join("Cargo.toml");
    let manifest = manifest.to_str().expect("UTF-8 manifest");
    // trybuild's `metadata` call, from the test's own package directory.
    assert_eq!(
        recorded(&targo, &["metadata", "--no-deps", "--format-version=1"]),
        expected(
            &targo,
            &[
                "metadata",
                "--manifest-path",
                manifest,
                "--no-deps",
                "--format-version=1"
            ]
        )
    );
    for subcommand in NON_COMPILING_SUBCOMMANDS {
        let record = recorded(&targo, &[*subcommand]);
        assert!(
            !record.iter().any(|line| line == "--unverified"),
            "targo refuses the lane on {subcommand}"
        );
    }
    // A global option's VALUE is not the subcommand, even when it spells one.
    assert_eq!(
        recorded(&targo, &["--config", "build", "clean", "--package", "p"]),
        expected(
            &targo,
            &[
                "--config",
                "build",
                "clean",
                "--manifest-path",
                manifest,
                "--package",
                "p"
            ]
        )
    );
}

#[test]
fn stock_cargo_is_never_given_a_lane() {
    let cargo = fixture(CargoDriver::Cargo);
    let manifest = cargo.package.join("Cargo.toml");
    let manifest = manifest.to_str().expect("UTF-8 manifest");
    assert_eq!(
        recorded(&cargo, &["build", "--bin", "case"]),
        expected(
            &cargo,
            &["build", "--manifest-path", manifest, "--bin", "case"]
        )
    );
}

#[test]
fn a_named_manifest_is_kept_and_an_unknown_subcommand_is_refused() {
    let targo = fixture(CargoDriver::Targo);
    assert_eq!(
        recorded(
            &targo,
            &["build", "--manifest-path", "/elsewhere/Cargo.toml"]
        ),
        expected(
            &targo,
            &[
                "--unverified",
                "build",
                "--manifest-path",
                "/elsewhere/Cargo.toml"
            ]
        )
    );
    let refused = run_shim(&targo, &["install", "anything"]);
    assert_eq!(refused.status.code(), Some(2));
    assert!(
        refused.stdout.is_empty(),
        "an unknown subcommand must never reach Cargo"
    );
    assert!(String::from_utf8_lossy(&refused.stderr).contains("refusing subcommand 'install'"));
}

#[test]
fn a_relative_target_directory_keeps_meaning_the_callers() {
    let targo = fixture(CargoDriver::Targo);
    let output = Command::new(&targo.shim)
        .args(["metadata", "--no-deps"])
        .current_dir(&targo.caller)
        .env("CARGO_TARGET_DIR", "relative-target")
        .output()
        .expect("run shim");
    assert!(output.status.success());
    let record = String::from_utf8(output.stdout).expect("UTF-8 record");
    assert_eq!(
        record.lines().last(),
        Some(
            format!(
                "CARGO_TARGET_DIR={}/relative-target",
                targo.caller.display()
            )
            .as_str()
        )
    );
}

#[test]
fn the_working_directory_must_discover_no_semantic_cargo_config() {
    let root = tempfile::tempdir().expect("temporary directory");
    let base = root
        .path()
        .canonicalize()
        .expect("canonical temporary directory");
    let cargo_home = base.join("cargo-home");
    filesystem::create_dir_all(&cargo_home).expect("cargo home");

    let clean = base.join("clean");
    filesystem::create_dir_all(clean.join(".cargo")).expect("clean base");
    // Non-semantic configuration is allowed, exactly as the funnel allows it.
    filesystem::write(
        clean.join(".cargo").join("config.toml"),
        "[net]\ngit-fetch-with-cli = true\n",
    )
    .expect("non-semantic config");
    let chosen = chosen_working_directory(&clean, &cargo_home);
    assert_eq!(chosen, clean.join(WORKING_DIRECTORY_NAME));
    assert!(chosen.is_dir());

    let posture = base.join("checkout");
    filesystem::create_dir_all(posture.join(".cargo")).expect("checkout base");
    filesystem::write(
        posture.join(".cargo").join("config.toml"),
        "[host]\nrustflags = [\"--cfg\", \"posture\"]\n",
    )
    .expect("semantic config");
    let refused = std::panic::catch_unwind(|| chosen_working_directory(&posture, &cargo_home))
        .expect_err("a directory that discovers a [host] table must be refused");
    let message = refused
        .downcast_ref::<String>()
        .map(String::as_str)
        .unwrap_or_default();
    assert!(
        message.contains("semantic key \"host\""),
        "the refusal names the key: {message}"
    );
}
