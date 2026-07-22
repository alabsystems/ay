// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! E2E tests for the root EDAC/VAC-lite WCSP probe wiring in the `ay-pb`
//! binary (campaign soft-1, opt-in via `AY_PB_WCSP_EDAC=1`, default OFF).
//!
//! The probe may assert `s UNSATISFIABLE` ONLY when its trail-checked floor
//! `c0` reaches the WBO top cost. These tests pin: the firing case, the
//! non-firing (c0 < top) case falling through to the normal solve, the
//! default-OFF case, and the fail-closed decline on a real instance whose
//! softs are out of shape (arity 4).

use std::process::Command;

/// Two one-hot domains, every cross combination costs 5: every assignment
/// satisfying the domain rows pays exactly 5, so the probe's fixpoint floor
/// is c0 = 5.
const UNIFORM_COST_5_ROWS: &str = concat!(
    "+1 x1 +1 x2 = 1 ;\n",
    "+1 x3 +1 x4 = 1 ;\n",
    "[5] -1 x1 -1 x3 >= -1 ;\n",
    "[5] -1 x1 -1 x4 >= -1 ;\n",
    "[5] -1 x2 -1 x3 >= -1 ;\n",
    "[5] -1 x2 -1 x4 >= -1 ;\n",
);

fn write_instance(case: &str, text: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("ay-wcsp-edac-e2e-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("temp dir");
    let path = dir.join(format!("{case}.wbo"));
    std::fs::write(&path, text).expect("write instance");
    path
}

fn solve(path: &std::path::Path, edac: bool) -> String {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_ay-pb"));
    cmd.args(["pb", "solve", "--timeout", "10000"])
        .arg(path)
        // Never inherit the flag from the caller's environment: each case
        // states its own gate explicitly.
        .env_remove("AY_PB_WCSP_EDAC");
    if edac {
        cmd.env("AY_PB_WCSP_EDAC", "1");
    }
    let output = cmd.output().expect("run ay-pb");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

fn s_lines(stdout: &str) -> Vec<&str> {
    stdout.lines().filter(|l| l.starts_with("s ")).collect()
}

#[test]
fn probe_proves_unsat_when_floor_reaches_top() {
    let text = format!("soft: 5 ;\n{UNIFORM_COST_5_ROWS}");
    let path = write_instance("binding-top", &text);
    let stdout = solve(&path, true);
    assert_eq!(
        s_lines(&stdout),
        vec!["s UNSATISFIABLE"],
        "stdout: {stdout:?}"
    );
    assert!(
        stdout.contains("c wcsp edac root probe: c0=5 top=5"),
        "probe comment missing: {stdout:?}"
    );
    assert!(
        stdout.contains("c wcsp edac trail-checked floor reaches top cost"),
        "verdict comment missing: {stdout:?}"
    );
}

#[test]
fn probe_reports_floor_but_defers_when_below_top() {
    // Same costs, top = 6: c0 = 5 < 6, so the probe must NOT claim UNSAT;
    // the normal solve finds the (any) cost-5 model.
    let text = format!("soft: 6 ;\n{UNIFORM_COST_5_ROWS}");
    let path = write_instance("non-binding-top", &text);
    let stdout = solve(&path, true);
    assert!(
        stdout.contains("c wcsp edac root probe: c0=5 top=6"),
        "probe comment missing: {stdout:?}"
    );
    assert!(
        !stdout.contains("trail-checked floor reaches top cost"),
        "probe must not assert a verdict below top: {stdout:?}"
    );
    let s = s_lines(&stdout);
    assert_eq!(s.len(), 1, "stdout: {stdout:?}");
    assert!(
        s[0] == "s OPTIMUM FOUND" || s[0] == "s SATISFIABLE",
        "expected a solved status, got {s:?}; stdout: {stdout:?}"
    );
    assert!(
        stdout.lines().any(|l| l.trim() == "o 5"),
        "expected the true optimum o 5: {stdout:?}"
    );
}

#[test]
fn probe_stays_off_by_default() {
    // Default OFF: identical binding-top instance, no probe comments; the
    // verdict still comes out UNSATISFIABLE through the ordinary converted
    // solve (the top-cost budget row is infeasible), which doubles as a
    // ground-truth cross-check of the probe's verdict in the firing test.
    let text = format!("soft: 5 ;\n{UNIFORM_COST_5_ROWS}");
    let path = write_instance("default-off", &text);
    let stdout = solve(&path, false);
    assert!(
        !stdout.contains("wcsp edac"),
        "probe must be opt-in: {stdout:?}"
    );
    assert_eq!(
        s_lines(&stdout),
        vec!["s UNSATISFIABLE"],
        "stdout: {stdout:?}"
    );
}

#[test]
fn probe_declines_out_of_shape_softs_and_solve_proceeds() {
    // Real corpus instance with quaternary softs (normalized-4queens): the
    // reconstruction declines fail-closed, no probe comment appears, and the
    // instance solves normally (4-queens has conflict-free placements, so a
    // cost-0 model exists below top = 1).
    let path = std::path::PathBuf::from(format!(
        "{}/tests/instances/wcsp_4queens.wbo",
        env!("CARGO_MANIFEST_DIR")
    ));
    let stdout = solve(&path, true);
    assert!(
        !stdout.contains("wcsp edac"),
        "declined probe must stay silent: {stdout:?}"
    );
    let s = s_lines(&stdout);
    assert_eq!(s.len(), 1, "stdout: {stdout:?}");
    assert!(
        s[0] == "s OPTIMUM FOUND" || s[0] == "s SATISFIABLE",
        "expected a solved status, got {s:?}; stdout: {stdout:?}"
    );
}
