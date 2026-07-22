// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_test_support::{
    build_ay_cli, build_bound_target_name, BuiltWorkspaceBinary, AY_CLI_TARGET_NAME,
};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::sync::OnceLock;

fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("AY workspace root")
        .canonicalize()
        .expect("AY workspace root should be canonicalizable")
}

fn exact_ay_cli() -> &'static BuiltWorkspaceBinary {
    static AY_CLI: OnceLock<BuiltWorkspaceBinary> = OnceLock::new();
    AY_CLI.get_or_init(|| build_ay_cli(&workspace_root()))
}

pub(crate) fn ay_command() -> Command {
    exact_ay_cli().command()
}

#[test]
fn exact_cli_lane_runs_without_ay_path_or_ambient_target_binary() {
    let built = exact_ay_cli();
    let target_root = workspace_root().join("target");
    assert_eq!(
        built.target_dir.parent(),
        Some(target_root.as_path()),
        "FlatZinc tests must use an AY-workspace isolated target"
    );
    let target_name = built
        .target_dir
        .file_name()
        .and_then(std::ffi::OsStr::to_str)
        .expect("isolated target name should be UTF-8");
    let expected_target_name = build_bound_target_name(
        AY_CLI_TARGET_NAME,
        &built.source_identity,
        &built.build_identity,
    );
    assert!(
        target_name == expected_target_name
            || target_name.starts_with(&format!("{expected_target_name}-nested-")),
        "unexpected isolated AY CLI target {target_name:?}"
    );

    let mut child = built
        .command()
        .args(["-smt2", "-in"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run exact-source AY CLI");
    child
        .stdin
        .as_mut()
        .expect("AY stdin")
        .write_all(b"(set-logic QF_LIA)\n(check-sat)\n")
        .expect("write AY stdin");
    let output = child.wait_with_output().expect("wait for AY CLI");
    assert!(
        output.status.success(),
        "exact-source AY CLI failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "sat");
}
