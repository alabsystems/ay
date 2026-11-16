// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Reduced rust-horn BMC unsafe canaries for #9618.
//!
//! The original rust-horn files named in #9618 were not present locally, so the
//! checked-in fixtures under tests/chc/regression/rust-horn preserve the exact
//! filenames while reducing the obligation to reachable unsafe HORN systems.
//! This test guards the launch-gate result contract on the real CLI path:
//! first-line `unsat` and an UNSAFE CHC certificate marker. Z3 Spacer is used
//! only when available.

use ntest::timeout;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

#[derive(Clone, Copy)]
struct Canary {
    id: &'static str,
    rel_path: &'static str,
}

const CANARIES: &[Canary] = &[
    Canary {
        id: "bmc-1-unsafe",
        rel_path: "tests/chc/regression/rust-horn/bmc-1-test-bmc-1-unsafe_000.smt2",
    },
    Canary {
        id: "bmc-3-unsafe",
        rel_path: "tests/chc/regression/rust-horn/bmc-3-test-bmc-3-unsafe_000.smt2",
    },
];

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn first_result_token(output: &str) -> Option<&str> {
    output.lines().map(str::trim).find(|line| {
        matches!(
            *line,
            "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
        )
    })
}

fn assert_ay_unsafe_contract(case: Canary, path: &Path) {
    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--chc")
        .arg("--timeout")
        .arg("12000")
        .arg(path)
        .output()
        .expect("spawn ay solve --chc");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{}: ay exited with {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        case.id,
        output.status
    );

    let first_line = stdout.lines().next().unwrap_or("").trim();
    assert_ne!(
        first_line, "sat",
        "{}: reduced unsafe rust-horn canary returned SAFE/sat\nstdout:\n{stdout}",
        case.id
    );
    assert_eq!(
        first_line, "unsat",
        "{}: expected first-line unsat for unsafe canary\nstdout:\n{stdout}",
        case.id
    );
    assert!(
        stdout.contains(";; AY CHC Certificate: UNSAFE"),
        "{}: missing UNSAFE certificate marker\nstdout:\n{stdout}",
        case.id
    );
    assert!(
        !stdout.lines().any(|line| line.trim() == "unknown"),
        "{}: unsafe canary must not return unknown\nstdout:\n{stdout}",
        case.id
    );
}

/// The optional Spacer cross-check. z3 is reached by path and must prove it is
/// z3 (`ay_test_support::z3`); with none usable the check is skipped visibly.
fn maybe_assert_z3_spacer_unsat(case: Canary, path: &Path) {
    let Some(z3) = ay_test_support::z3::optional_z3("ay rust_horn_bmc_canaries_9618 Spacer") else {
        return;
    };
    let output = z3
        .command()
        .arg("fp.engine=spacer")
        .arg(path)
        .output()
        .unwrap_or_else(|error| panic!("{}: failed to run z3 Spacer: {error}", case.id));

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{}: z3 Spacer exited with {:?}\nstdout:\n{stdout}\nstderr:\n{stderr}",
        case.id,
        output.status
    );
    assert_eq!(
        first_result_token(&stdout),
        Some("unsat"),
        "{}: expected z3 Spacer unsat for reduced unsafe canary\nstdout:\n{stdout}\nstderr:\n{stderr}",
        case.id
    );
}

#[test]
#[timeout(60_000)]
fn rust_horn_bmc_reduced_unsafe_canaries_emit_unsat_and_certificate_9618() {
    let root = repo_root();
    let scratch = tempfile::tempdir().expect("create isolated rust-horn canary directory");
    for case in CANARIES {
        let source_path = root.join(case.rel_path);
        assert!(
            source_path.is_file(),
            "{}: missing reduced fixture at {}",
            case.id,
            source_path.display()
        );
        let path = scratch.path().join(
            source_path
                .file_name()
                .expect("rust-horn canary fixture has a file name"),
        );
        fs::copy(&source_path, &path).unwrap_or_else(|error| {
            panic!(
                "{}: copy reduced fixture to isolated directory: {error}",
                case.id
            )
        });
        assert_ay_unsafe_contract(*case, &path);
        maybe_assert_z3_spacer_unsat(*case, &path);
    }
}
