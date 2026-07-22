// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end SAT-COMP matrix CLI acceptance fixtures.

use std::collections::BTreeMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use serde_json::Value;
use tempfile::tempdir;

use crate::spawn::OutputTimeout;

const TINY_MULTIPLIER_EQUIV_UNSAT: &str = "\
c tiny 1x1 multiplier equivalence miter
c 1=a 2=b 3=left_product 4=right_product
p cnf 4 8
-1 -2 3 0
1 -3 0
2 -3 0
-1 -2 4 0
1 -4 0
2 -4 0
3 4 0
-3 -4 0
";

#[test]
fn tiny_multiplier_equiv_original_dimacs_drat_is_accepted_by_sat_matrix_cli() {
    let workspace = tempdir().expect("create SAT matrix CLI tempdir");
    let instance = workspace.path().join("tiny-multiplier-equiv.cnf");
    fs::write(&instance, TINY_MULTIPLIER_EQUIV_UNSAT).expect("write tiny multiplier CNF");

    let solver_root = workspace.path().join("solver");
    fs::create_dir_all(&solver_root).expect("create solver root");
    copy_ay_binary(&solver_root);
    write_run_sh(&solver_root);
    let checker = write_checker_wrapper(&solver_root);

    let output_dir = workspace.path().join("matrix");
    let output = Command::new(ay_binary())
        .args([
            "submission",
            "preflight",
            "sat-matrix",
            "run",
            "--suite",
            "satcomp-matrix-cli-fixture",
            "--track",
            "main",
            "--ai-class",
            "regular",
            "--variants",
            "default",
            "--proof-format",
            "drat",
            "--run-sh",
        ])
        .arg(solver_root.join("run.sh"))
        .arg("--output")
        .arg(&output_dir)
        .arg("--instance")
        .arg(&instance)
        .args([
            "--expected",
            "unsat",
            "--family",
            "multiplier-equivalence",
            "--category",
            "original-dimacs",
            "--timeout-sec",
            "20",
            "--soundness",
            "--fail-on-wrong",
            "--proof-checker",
        ])
        .arg(&checker)
        .args(["--require-total", "1"])
        .output_timeout(Duration::from_secs(55))
        .expect("run ay submission preflight sat-matrix run");

    assert!(
        output.status.success(),
        "sat-matrix run should accept tiny DRAT fixture; status={:?}\nstdout={}\nstderr={}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );

    let scoreboard_path = output_dir.join("scoreboard.json");
    let scoreboard: Value = serde_json::from_str(
        &fs::read_to_string(&scoreboard_path).expect("read sat-matrix scoreboard"),
    )
    .expect("parse sat-matrix scoreboard");
    let summary = &scoreboard["variants"]["default"]["summary"];
    assert_eq!(summary["total"].as_u64(), Some(1));
    assert_eq!(summary["wrong"].as_u64(), Some(0));
    assert_eq!(summary["invalid"].as_u64(), Some(0));
    assert_eq!(summary["unsat_proof_valid"].as_u64(), Some(1));

    let raw_tsv = scoreboard["variants"]["default"]["raw_tsv"]
        .as_str()
        .expect("scoreboard records default raw_tsv path");
    let row = read_single_raw_row(Path::new(raw_tsv));

    assert_eq!(row.get("actual").map(String::as_str), Some("unsat"));
    assert_eq!(
        row.get("verdict").map(String::as_str),
        Some("UNSATISFIABLE")
    );
    assert_eq!(row.get("wrong").map(String::as_str), Some("0"));
    assert_eq!(row.get("invalid").map(String::as_str), Some("0"));
    assert_eq!(row.get("proof_status").map(String::as_str), Some("valid"));
    assert_eq!(row.get("ay_lrat_status").map(String::as_str), Some("ok"));
    assert_eq!(
        row.get("proof_checker_status").map(String::as_str),
        Some("ok")
    );
    assert_eq!(
        row.get("external_proof_checker_verdict")
            .map(String::as_str),
        Some("VERIFIED_UNSAT")
    );
    assert!(
        row.get("proof_bytes")
            .and_then(|bytes| bytes.parse::<u64>().ok())
            .is_some_and(|bytes| bytes > 0),
        "expected retained proof.out with positive size; row={row:?}"
    );
}

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn copy_ay_binary(solver_root: &Path) {
    let target = solver_root.join("ay");
    fs::copy(ay_binary(), &target).expect("copy ay binary into solver root");
    chmod_executable(&target);
}

fn write_run_sh(solver_root: &Path) {
    let run_sh = solver_root.join("run.sh");
    fs::write(
        &run_sh,
        r#"#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 BENCHMARK PROOF_DIR" >&2
  exit 2
fi

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BENCHMARK="$1"
PROOF_DIR="$2"
PROOF_FILE="$PROOF_DIR/proof.out"

mkdir -p "$PROOF_DIR"
exec env -u AY_SAT_FMLA_DECOMPOSE_LRAT_PREFLIGHT_ROUTE \
  "$DIR/ay" solve --sat-variant default --proof-format drat --proof "$PROOF_FILE" "$BENCHMARK"
"#,
    )
    .expect("write run.sh");
    chmod_executable(&run_sh);
}

fn write_checker_wrapper(solver_root: &Path) -> PathBuf {
    let checker = solver_root.join("check-lrat-verified.sh");
    fs::write(
        &checker,
        r#"#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 2 ]]; then
  echo "usage: $0 FORMULA PROOF" >&2
  exit 2
fi

DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
"$DIR/ay" check drat "$1" "$2" >/dev/null 2>/dev/null
printf 's VERIFIED UNSAT\n'
"#,
    )
    .expect("write checker wrapper");
    chmod_executable(&checker);
    checker
}

fn chmod_executable(path: &Path) {
    fs::set_permissions(path, fs::Permissions::from_mode(0o755))
        .unwrap_or_else(|err| panic!("chmod {}: {err}", path.display()));
}

fn read_single_raw_row(path: &Path) -> BTreeMap<String, String> {
    let text = fs::read_to_string(path)
        .unwrap_or_else(|err| panic!("read raw TSV {}: {err}", path.display()));
    let mut lines = text.lines();
    let headers: Vec<&str> = lines
        .next()
        .expect("raw TSV has header")
        .split('\t')
        .collect();
    let values: Vec<&str> = lines
        .next()
        .expect("raw TSV has one data row")
        .split('\t')
        .collect();
    assert!(
        lines.next().is_none(),
        "expected exactly one raw TSV row in {}:\n{text}",
        path.display()
    );
    headers
        .into_iter()
        .enumerate()
        .map(|(idx, header)| {
            (
                header.to_string(),
                values.get(idx).copied().unwrap_or_default().to_string(),
            )
        })
        .collect()
}
