// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for removing orphan CLI flags (#8833).

use std::process::Command;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

#[test]
fn test_removed_orphan_flags_absent_from_solve_help() {
    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--help")
        .output()
        .expect("spawn ay solve --help");

    assert!(
        output.status.success(),
        "expected help to succeed, got {:?}",
        output.status
    );

    let help = String::from_utf8_lossy(&output.stdout);
    for flag in ["--annotated-core", "--model-provenance", "--core-evolution"] {
        assert!(
            !help.contains(flag),
            "{flag} must not appear in solve help after #8833; help={help}"
        );
    }
}

#[test]
fn test_removed_orphan_flags_are_rejected() {
    for flag in ["--annotated-core", "--model-provenance", "--core-evolution"] {
        let output = Command::new(ay_binary())
            .arg("solve")
            .arg(flag)
            .arg("/dev/null")
            .output()
            .expect("spawn ay solve with removed flag");

        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            !output.status.success(),
            "{flag} must be rejected; stderr={stderr}"
        );
        assert!(
            stderr.contains("unexpected argument"),
            "{flag} should fail during clap parsing; stderr={stderr}"
        );
    }
}
