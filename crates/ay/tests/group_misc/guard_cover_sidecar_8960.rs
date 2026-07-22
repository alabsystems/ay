// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::path::Path;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

const HALL_THEOREM: &str =
    "SatCompStructural.checked_syntactic_sparse_selected_capacity_hall_sinz_deficit_one_clause_sound";
const GUARD_COVER_THEOREM: &str =
    "SatCompStructural.checked_remapped_sparse_hall_guard_cover_packing_unsat";
const SEPARATOR_COVER_THEOREM: &str = "SatCompStructural.checked_dimacs_separator_cover_unsat";

fn sha256_hex(bytes: &[u8]) -> String {
    let digest = Sha256::digest(bytes);
    let mut out = String::with_capacity(64);
    for byte in digest {
        out.push_str(&format!("{byte:02x}"));
    }
    out
}

fn write_guard_cover_fixture(dir: &Path, formula_sha256: &str) {
    let hall_path = dir.join("case.core-000.hall.json");
    let guard_path = dir.join("case.guard-cover.json");
    std::fs::write(
        &hall_path,
        json!({
            "version": 1,
            "lane": "hall-sinz-escape",
            "formula_sha256": formula_sha256,
            "theorems": [HALL_THEOREM],
            "witness": {
                "objects": ["p0", "p1"],
                "resources": ["h0"],
                "capacity": {"h0": 1},
                "allowed": {"p0": ["h0"], "p1": ["h0"]},
                "edge_lits": {"p0": {"h0": 1}, "p1": {"h0": 2}},
                "forbid_lits": {"p0": [3], "p1": [4]},
                "sinz_rows": {
                    "h0": {
                        "width": 1,
                        "zero": [5],
                        "steps": [
                            {"input": 1, "row": [6]},
                            {"input": 2, "row": [7]}
                        ]
                    }
                }
            }
        })
        .to_string(),
    )
    .expect("write Hall sidecar");
    std::fs::write(
        &guard_path,
        json!({
            "version": 1,
            "lane": "guard-cover-packing",
            "formula_sha256": formula_sha256,
            "theorem": GUARD_COVER_THEOREM,
            "depends_on": [{
                "cut_id": "core-000",
                "witness": "case.core-000.hall.json",
                "accepted_theorem": HALL_THEOREM
            }],
            "guards": [
                {"id": "core-000:p0", "lit": 3, "beta": 1},
                {"id": "core-000:p1", "lit": 4, "beta": 1}
            ],
            "cuts": [{
                "id": "core-000",
                "deficit": 1,
                "scale": 1,
                "coeff": {"core-000:p0": 1, "core-000:p1": 1},
                "escape_clause": [3, 4],
                "source": "hall-sinz-sidecar"
            }],
            "budget": {
                "rhs": 0,
                "terms": [
                    {"guard": "core-000:p0", "lit": 3, "weight": 1},
                    {"guard": "core-000:p1", "lit": 4, "weight": 1}
                ],
                "evidence": {"kind": "negative-units", "rhs": 0}
            },
            "packing": {
                "packed_deficit": 1,
                "packed_coeff": {"core-000:p0": 1, "core-000:p1": 1},
                "coeff_dominated_by_beta": true,
                "contradiction": "budget.rhs < packed_deficit"
            }
        })
        .to_string(),
    )
    .expect("write guard-cover sidecar");
}

fn write_separator_cover_sidecar(cnf_path: &Path, cnf: &[u8], var: i32) {
    let sidecar_path = cnf_path.with_extension("separator-cover.json");
    let formula_sha256 = sha256_hex(cnf);
    std::fs::write(
        &sidecar_path,
        json!({
            "version": 1,
            "lane": "separator-cover",
            "formula_sha256": formula_sha256,
            "theorem": SEPARATOR_COVER_THEOREM,
            "separator_vars": [var],
            "cubes": [
                {"id": "x=true", "lits": [var], "refuted_by": [-var]},
                {"id": "x=false", "lits": [-var], "refuted_by": [var]}
            ]
        })
        .to_string(),
    )
    .expect("write separator-cover sidecar");
}

#[test]
#[timeout(60_000)]
fn dimacs_cli_uses_accepted_guard_cover_sidecar_as_unsat_cut() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let cnf = b"p cnf 7 10\n\
1 3 0\n\
2 4 0\n\
-1 6 0\n\
-5 6 0\n\
-1 -5 0\n\
-2 7 0\n\
-6 7 0\n\
-2 -6 0\n\
-3 0\n\
-4 0\n";
    let formula_sha256 = sha256_hex(cnf);
    let cnf_path = temp.path().join("case.cnf");
    let hall_path = temp.path().join("case.core-000.hall.json");
    let guard_path = temp.path().join("case.guard-cover.json");

    std::fs::write(&cnf_path, cnf).expect("write CNF");
    std::fs::write(
        &hall_path,
        json!({
            "version": 1,
            "lane": "hall-sinz-escape",
            "formula_sha256": formula_sha256,
            "theorems": [HALL_THEOREM],
            "witness": {
                "objects": ["p0", "p1"],
                "resources": ["h0"],
                "capacity": {"h0": 1},
                "allowed": {"p0": ["h0"], "p1": ["h0"]},
                "edge_lits": {"p0": {"h0": 1}, "p1": {"h0": 2}},
                "forbid_lits": {"p0": [3], "p1": [4]},
                "sinz_rows": {
                    "h0": {
                        "width": 1,
                        "zero": [5],
                        "steps": [
                            {"input": 1, "row": [6]},
                            {"input": 2, "row": [7]}
                        ]
                    }
                }
            }
        })
        .to_string(),
    )
    .expect("write Hall sidecar");
    std::fs::write(
        &guard_path,
        json!({
            "version": 1,
            "lane": "guard-cover-packing",
            "formula_sha256": formula_sha256,
            "theorem": GUARD_COVER_THEOREM,
            "depends_on": [{
                "cut_id": "core-000",
                "witness": "case.core-000.hall.json",
                "accepted_theorem": HALL_THEOREM
            }],
            "guards": [
                {"id": "core-000:p0", "lit": 3, "beta": 1},
                {"id": "core-000:p1", "lit": 4, "beta": 1}
            ],
            "cuts": [{
                "id": "core-000",
                "deficit": 1,
                "scale": 1,
                "coeff": {"core-000:p0": 1, "core-000:p1": 1},
                "escape_clause": [3, 4],
                "source": "hall-sinz-sidecar"
            }],
            "budget": {
                "rhs": 0,
                "terms": [
                    {"guard": "core-000:p0", "lit": 3, "weight": 1},
                    {"guard": "core-000:p1", "lit": 4, "weight": 1}
                ],
                "evidence": {"kind": "negative-units", "rhs": 0}
            },
            "packing": {
                "packed_deficit": 1,
                "packed_coeff": {"core-000:p0": 1, "core-000:p1": 1},
                "coeff_dominated_by_beta": true,
                "contradiction": "budget.rhs < packed_deficit"
            }
        })
        .to_string(),
    )
    .expect("write guard-cover sidecar");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--stats-json")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected DIMACS UNSAT exit code 20, stdout: {stdout}, stderr: {stderr}"
    );
    assert!(
        stdout.contains("s UNSATISFIABLE"),
        "expected DIMACS UNSAT output, got {stdout}"
    );
    assert!(
        stderr.contains("c guard-cover: accepted"),
        "expected accepted guard-cover banner, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.guard_cover_sidecar_accepted\":1"),
        "expected accepted sidecar stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.guard_cover_sidecar_empty_cut\":1"),
        "expected empty-cut sidecar stat, got {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_cli_parallel_with_separator_sidecar_reroutes_to_checked_sidecar_path() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
    let cnf_path = temp.path().join("case.cnf");
    std::fs::write(&cnf_path, cnf).expect("write CNF");
    write_separator_cover_sidecar(&cnf_path, cnf, 1);

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--parallel")
        .arg("2")
        .arg("--stats-json")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected DIMACS UNSAT exit code 20, stdout: {stdout}, stderr: {stderr}"
    );
    assert!(
        stderr.contains("c structural-sidecar: adjacent sidecar present"),
        "expected structural-sidecar reroute banner, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_accepted\":1"),
        "expected accepted separator-cover stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_empty_cut\":1"),
        "expected separator-cover empty-cut stat, got {stderr}"
    );
    assert!(
        !stderr.contains("\"sat.parallel_threads\""),
        "sidecar reroute should avoid parallel portfolio stats, got {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_cli_cube_and_conquer_with_separator_sidecar_reroutes_to_checked_sidecar_path() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
    let cnf_path = temp.path().join("case.cnf");
    std::fs::write(&cnf_path, cnf).expect("write CNF");
    write_separator_cover_sidecar(&cnf_path, cnf, 1);

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--cube-and-conquer")
        .arg("1")
        .arg("--stats-json")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected DIMACS UNSAT exit code 20, stdout: {stdout}, stderr: {stderr}"
    );
    assert!(
        stderr.contains("c structural-sidecar: adjacent sidecar present"),
        "expected structural-sidecar reroute banner, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_accepted\":1"),
        "expected accepted separator-cover stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_empty_cut\":1"),
        "expected separator-cover empty-cut stat, got {stderr}"
    );
    assert!(
        !stderr.contains("\"sat.cube_and_conquer_depth\""),
        "sidecar reroute should avoid cube-and-conquer stats, got {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_cli_counts_both_accepted_structural_sidecars() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let cnf = b"p cnf 8 12\n\
1 3 0\n\
2 4 0\n\
-1 6 0\n\
-5 6 0\n\
-1 -5 0\n\
-2 7 0\n\
-6 7 0\n\
-2 -6 0\n\
-3 0\n\
-4 0\n\
8 0\n\
-8 0\n";
    let formula_sha256 = sha256_hex(cnf);
    let cnf_path = temp.path().join("case.cnf");
    std::fs::write(&cnf_path, cnf).expect("write CNF");
    write_guard_cover_fixture(temp.path(), &formula_sha256);
    write_separator_cover_sidecar(&cnf_path, cnf, 8);

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--stats-json")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(
        output.status.code(),
        Some(20),
        "expected DIMACS UNSAT exit code 20, stdout: {stdout}, stderr: {stderr}"
    );
    assert!(
        stderr.contains("\"sat.guard_cover_sidecar_accepted\":1"),
        "expected accepted guard-cover stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.guard_cover_sidecar_empty_cut\":0"),
        "guard-cover should not inject the winning empty cut, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_accepted\":1"),
        "expected accepted separator-cover stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_empty_cut\":1"),
        "separator-cover should inject exactly one empty cut, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.structural_sidecar_checked_count\":2"),
        "expected two checked structural sidecars, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.structural_sidecar_accepted_count\":2"),
        "expected two accepted structural sidecars, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.structural_sidecar_empty_cut_count\":1"),
        "expected exactly one structural sidecar empty cut, got {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_cli_uses_accepted_separator_cover_sidecar_as_unsat_cut() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
    let formula_sha256 = sha256_hex(cnf);
    let cnf_path = temp.path().join("case.cnf");
    let sidecar_path = temp.path().join("case.separator-cover.json");

    std::fs::write(&cnf_path, cnf).expect("write CNF");
    std::fs::write(
        &sidecar_path,
        json!({
            "version": 1,
            "lane": "separator-cover",
            "formula_sha256": formula_sha256,
            "theorem": SEPARATOR_COVER_THEOREM,
            "separator_vars": [1],
            "cubes": [
                {"id": "x=true", "lits": [1], "refuted_by": [-1]},
                {"id": "x=false", "lits": [-1], "refuted_by": [1]}
            ]
        })
        .to_string(),
    )
    .expect("write separator-cover sidecar");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--stats-json")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(20),
        "expected DIMACS UNSAT exit code 20, stdout: {stdout}, stderr: {stderr}"
    );
    assert!(
        stdout.contains("s UNSATISFIABLE"),
        "expected DIMACS UNSAT output, got {stdout}"
    );
    assert!(
        stderr.contains("c separator-cover: accepted"),
        "expected accepted separator-cover banner, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_accepted\":1"),
        "expected accepted separator-cover stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_empty_cut\":1"),
        "expected separator-cover empty-cut stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_covered_assignments\":2"),
        "expected separator-cover coverage stat, got {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_cli_rejects_bad_separator_cover_sidecar_without_empty_cut() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let cnf = b"p cnf 1 1\n1 0\n";
    let cnf_path = temp.path().join("case.cnf");
    let sidecar_path = temp.path().join("case.separator-cover.json");

    std::fs::write(&cnf_path, cnf).expect("write CNF");
    std::fs::write(
        &sidecar_path,
        json!({
            "version": 1,
            "lane": "separator-cover",
            "formula_sha256": "0".repeat(64),
            "theorem": SEPARATOR_COVER_THEOREM,
            "separator_vars": [1],
            "cubes": [
                {"id": "x=true", "lits": [1], "refuted_by": [-1]},
                {"id": "x=false", "lits": [-1], "refuted_by": [1]}
            ]
        })
        .to_string(),
    )
    .expect("write separator-cover sidecar");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--stats-json")
        .arg("--no-proof")
        .arg("--no-verify-proof")
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(10),
        "expected DIMACS SAT exit code 10, stdout: {stdout}, stderr: {stderr}"
    );
    assert!(
        stdout.contains("s SATISFIABLE"),
        "expected DIMACS SAT output, got {stdout}"
    );
    assert!(
        stderr.contains("c separator-cover: rejected"),
        "expected rejected separator-cover banner, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_checked\":1"),
        "expected checked separator-cover stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_accepted\":0"),
        "expected rejected separator-cover stat, got {stderr}"
    );
    assert!(
        stderr.contains("\"sat.separator_cover_sidecar_empty_cut\":0"),
        "expected no separator-cover empty cut, got {stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn dimacs_cli_separator_cover_sidecar_fails_closed_in_proof_mode() {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp = tempfile::tempdir().expect("tempdir");
    let cnf = b"p cnf 1 2\n1 0\n-1 0\n";
    let formula_sha256 = sha256_hex(cnf);
    let cnf_path = temp.path().join("case.cnf");
    let sidecar_path = temp.path().join("case.separator-cover.json");
    let proof_path = temp.path().join("case.lrat");

    std::fs::write(&cnf_path, cnf).expect("write CNF");
    std::fs::write(&proof_path, b"stale proof").expect("write stale proof");
    std::fs::write(
        &sidecar_path,
        json!({
            "version": 1,
            "lane": "separator-cover",
            "formula_sha256": formula_sha256,
            "theorem": SEPARATOR_COVER_THEOREM,
            "separator_vars": [1],
            "cubes": [
                {"id": "x=true", "lits": [1], "refuted_by": [-1]},
                {"id": "x=false", "lits": [-1], "refuted_by": [1]}
            ]
        })
        .to_string(),
    )
    .expect("write separator-cover sidecar");

    let output = Command::new(ay_path)
        .arg("solve")
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("lrat")
        .arg("--no-verify-proof")
        .arg(&cnf_path)
        .output_timeout(Duration::from_secs(55))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        output.status.code(),
        Some(0),
        "expected proof-mode fail-closed exit code 0, stdout: {stdout}, stderr: {stderr}"
    );
    assert!(
        stdout.contains("s UNKNOWN"),
        "expected proof-mode UNKNOWN, got {stdout}"
    );
    assert!(
        !stdout.contains("s UNSATISFIABLE"),
        "proof-mode sidecar route must not claim UNSAT without public replay, got {stdout}"
    );
    assert!(
        stderr.contains("c separator-cover: accepted"),
        "expected accepted separator-cover banner, got {stderr}"
    );
    assert!(
        stderr.contains(
            "separator-cover sidecar accepted but proof-mode public artifact replay is not implemented"
        ),
        "expected fail-closed proof-mode reason, got {stderr}"
    );
    assert!(
        !proof_path.exists(),
        "proof-mode fail-closed run must remove stale proof artifact at {}",
        proof_path.display()
    );
}
