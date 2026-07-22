// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::process::Command;
use std::{
    env, fs,
    path::{Path, PathBuf},
};

use tempfile::{tempdir, NamedTempFile};

fn assert_competition_safe_output(rendered: &str) {
    for line in rendered.lines() {
        let prefix = line
            .chars()
            .next()
            .expect("PB CLI output lines should not be empty");
        assert!(
            matches!(prefix, 'c' | 'o' | 's' | 'v'),
            "unexpected PB output prefix in line: {line:?}"
        );
        assert!(
            line.len() == 1 || line.as_bytes()[1] == b' ',
            "PB output lines must use '<prefix><space>...' when non-empty: {line:?}"
        );
    }
}

fn run_pb_solve(args: &[&str], file: &NamedTempFile) -> (std::process::ExitStatus, String, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["pb", "solve"])
        .args(args)
        .arg(file.path())
        .output()
        .expect("ay pb solve should run");

    (
        output.status,
        String::from_utf8(output.stdout).expect("stdout should be utf-8"),
        String::from_utf8(output.stderr).expect("stderr should be utf-8"),
    )
}

fn find_local_veripb() -> Option<PathBuf> {
    for var in ["AY_PB26_VERIPB_BIN", "VERIPB_BIN", "VERIPB"] {
        if let Some(candidate) = env::var_os(var).map(PathBuf::from) {
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }

    for candidate in [Path::new("/tmp/veripb-3/bin/veripb")] {
        if candidate.is_file() {
            return Some(candidate.to_path_buf());
        }
    }

    env::var_os("PATH")
        .into_iter()
        .flat_map(|paths| env::split_paths(&paths).collect::<Vec<_>>())
        .map(|dir| dir.join("veripb"))
        .find(|candidate| candidate.is_file())
}

fn verify_proof_with_local_veripb(test_name: &str, opb_path: &Path, proof_path: &Path) {
    let Some(veripb) = find_local_veripb() else {
        eprintln!("skipping external VeriPB check for {test_name}: no local veripb found");
        return;
    };

    let output = Command::new(veripb)
        .arg("--opb")
        .arg(opb_path)
        .arg(proof_path)
        .output()
        .expect("run local VeriPB checker");

    assert!(
        output.status.success(),
        "{test_name}: VeriPB rejected top-level ay proof\nstatus: {:?}\nstdout: {}\nstderr: {}",
        output.status.code(),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn decompressed_repo_xz_to_temp(relative_path: &str) -> Option<NamedTempFile> {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let path = repo_root.join(relative_path);
    if !path.exists() {
        eprintln!("skipping PB CLI fixture test; fixture unavailable: {relative_path}");
        return None;
    }
    let output = Command::new("xz").arg("-dc").arg(&path).output().ok()?;
    if !output.status.success() {
        eprintln!("skipping PB CLI fixture test; xz failed for {relative_path}");
        return None;
    }
    let file = NamedTempFile::new().ok()?;
    fs::write(file.path(), output.stdout).ok()?;
    Some(file)
}

fn assert_wbo_proof_request_is_unsupported(rendered: &str, proof_path: &Path) {
    assert_proof_request_is_unsupported(
        rendered,
        proof_path,
        "proof logging for WBO is not supported",
        "WBO",
    );
}

fn assert_proof_request_is_unsupported(
    rendered: &str,
    proof_path: &Path,
    expected_comment: &str,
    request_name: &str,
) {
    assert!(
        rendered.contains(expected_comment),
        "expected explicit unsupported {request_name} proof comment, got: {rendered}"
    );
    assert!(
        rendered.contains("s UNSUPPORTED\n"),
        "{request_name} proof request should emit s UNSUPPORTED, got: {rendered}"
    );
    assert!(
        !rendered.lines().any(|line| line.starts_with("o ")),
        "unsupported {request_name} proof request should not emit objective lines: {rendered}"
    );
    assert!(
        !rendered.lines().any(|line| line.starts_with("v ")),
        "unsupported {request_name} proof request should not emit a witness line: {rendered}"
    );
    assert!(
        !proof_path.exists(),
        "{request_name} proof request must not leave a proof file"
    );
    assert_competition_safe_output(rendered);
}

#[test]
fn test_pb_cli_proof_employee_scheduling_sep4_5_certifies_infeasible() {
    let Some(file) = decompressed_repo_xz_to_temp(
        "benchmarks/pb-comp/PB24/normalized-PB15eval/OPT-LIN/EmployeeScheduling/normalized-sep4.5.opb.xz",
    ) else {
        return;
    };
    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("employeescheduling-sep4.5.veripb");
    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");

    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "5000", "--proof", proof_arg], &file);

    // The per-instance fingerprint route this test used to pin (exact-input
    // sha256 match -> canned version-2.0 proof) was REMOVED — the solver's
    // integrity statement forbids per-instance recognizers. What must hold on
    // the GENERIC certified route is the fail-closed contract: either a
    // proven UNSATISFIABLE with a committed, checker-verified proof, or an
    // honest UNKNOWN with no proof file — never a claim without a proof.
    assert_competition_safe_output(&rendered);
    if rendered.contains("s UNSATISFIABLE\n") {
        assert_eq!(
            status.code(),
            Some(20),
            "sep4.5 UNSAT claim should exit 20; stderr: {stderr}; stdout: {rendered}"
        );
        assert!(
            !rendered
                .lines()
                .any(|line| line.starts_with("o ") || line.starts_with("v ")),
            "infeasible certified route must not emit objective or witness lines: {rendered}"
        );
        let proof = fs::read(&proof_path).expect("a claimed UNSAT must commit a proof");
        let proof_text = String::from_utf8(proof).expect("proof should be text");
        assert!(proof_text.starts_with("pseudo-Boolean proof version 3.0\n"));
        assert!(
            proof_text.contains("conclusion BOUNDS INF") || proof_text.contains("conclusion UNSAT"),
            "infeasible-OPT proof should conclude BOUNDS INF (or UNSAT): {proof_text}"
        );
        verify_proof_with_local_veripb("employeescheduling_sep4_5", file.path(), &proof_path);
    } else {
        // Honest inconclusive outcome within the 5s budget: no certificate
        // may remain on disk (fail-closed discipline), and no optimum claim.
        assert!(
            rendered.contains("s UNKNOWN\n") || rendered.contains("s SATISFIABLE\n"),
            "non-UNSAT outcome must be UNKNOWN or incumbent SATISFIABLE: {rendered}"
        );
        assert!(
            !rendered.contains("s OPTIMUM FOUND"),
            "no OPTIMUM claim is possible without a committed proof: {rendered}"
        );
        assert!(
            !proof_path.exists(),
            "inconclusive certified run must not leave a proof file behind"
        );
    }
}

#[test]
fn test_pb_cli_le_opb_decision_emits_sat_competition_output() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 2 #constraint= 2\n+1 x1 +1 x2 <= 1 ;\n+1 x1 >= 1 ;\n",
    )
    .expect("write should succeed");

    let (status, rendered, stderr) = run_pb_solve(&["--timeout", "5000"], &file);
    assert_eq!(
        status.code(),
        Some(10),
        "<= OPB decision instance should exit SAT; stderr: {stderr}; stdout: {rendered}"
    );
    assert!(
        rendered.contains("s SATISFIABLE\n"),
        "<= OPB decision instance should emit SATISFIABLE, got: {rendered}"
    );
    assert!(
        !rendered.contains("\no "),
        "<= OPB decision instance should not emit objective lines: {rendered}"
    );
    assert!(
        rendered.lines().any(|line| line.starts_with("v ")),
        "<= OPB decision instance should emit a witness line: {rendered}"
    );
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_proof_on_le_opb_unsat_verifies_original_source_with_veripb() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("le_unsat.veripb");
    fs::write(
        file.path(),
        "* #variable= 1 #constraint= 2\n+1 x1 <= 0 ;\n+1 x1 >= 1 ;\n",
    )
    .expect("write should succeed");

    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");
    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "5000", "--proof", proof_arg], &file);
    assert_eq!(
        status.code(),
        Some(20),
        "<= OPB UNSAT proof request should exit UNSAT; stderr: {stderr}; stdout: {rendered}"
    );
    assert!(
        rendered.contains("s UNSATISFIABLE\n"),
        "<= OPB UNSAT proof request should emit UNSATISFIABLE, got: {rendered}"
    );
    let proof = fs::read_to_string(&proof_path).expect("proof file should be readable");
    assert!(
        proof.lines().any(|line| line == "output NONE;"),
        "<= UNSAT proof should contain VeriPB output marker: {proof}"
    );
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion UNSAT : ")),
        "<= UNSAT proof should conclude UNSAT: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "<= UNSAT proof should end with VeriPB terminator: {proof}"
    );
    verify_proof_with_local_veripb("top_level_ay_le_unsat", file.path(), &proof_path);
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_le_opb_optimization_emits_optimum_competition_output() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        concat!(
            "* #variable= 2 #constraint= 2\n",
            "min: +1 x1 +2 x2 ;\n",
            "+1 x1 +1 x2 <= 1 ;\n",
            "+1 x1 +1 x2 >= 1 ;\n",
        ),
    )
    .expect("write should succeed");

    let (status, rendered, stderr) = run_pb_solve(&["--timeout", "5000"], &file);
    assert_eq!(
        status.code(),
        Some(30),
        "<= OPB optimization instance should exit OPTIMUM FOUND; stderr: {stderr}; stdout: {rendered}"
    );
    assert!(
        rendered.lines().any(|line| line == "o 1"),
        "<= OPB optimization instance should emit optimum objective 1, got: {rendered}"
    );
    assert!(
        rendered.contains("s OPTIMUM FOUND\n"),
        "<= OPB optimization instance should emit OPTIMUM FOUND, got: {rendered}"
    );
    assert!(
        rendered.lines().any(|line| line.starts_with("v ")),
        "<= OPB optimization instance should emit a witness line: {rendered}"
    );
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_proof_on_le_opb_optimization_verifies_original_source_with_veripb() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("le_opt.veripb");
    fs::write(
        file.path(),
        concat!(
            "* #variable= 2 #constraint= 2\n",
            "min: +1 x1 +2 x2 ;\n",
            "+1 x1 +1 x2 <= 1 ;\n",
            "+1 x1 +1 x2 >= 1 ;\n",
        ),
    )
    .expect("write should succeed");

    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");
    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "5000", "--proof", proof_arg], &file);
    assert_eq!(
        status.code(),
        Some(30),
        "<= OPB optimization proof request should exit OPTIMUM FOUND; stderr: {stderr}; stdout: {rendered}"
    );
    assert!(
        rendered.lines().any(|line| line == "o 1"),
        "<= OPB optimization proof request should emit objective 1, got: {rendered}"
    );
    assert!(
        rendered.contains("s OPTIMUM FOUND\n"),
        "<= OPB optimization proof request should emit OPTIMUM FOUND, got: {rendered}"
    );
    assert!(
        rendered.lines().any(|line| line.starts_with("v ")),
        "<= OPB optimization proof request should emit a witness line: {rendered}"
    );
    let proof = fs::read_to_string(&proof_path).expect("proof file should be readable");
    assert!(
        proof.lines().any(|line| line == "output NONE;"),
        "<= OPT proof should contain VeriPB output marker: {proof}"
    );
    // Hinted conclusion form (`conclusion BOUNDS 1 : <id> 1 : <witness>;`):
    // the hints keep the conclusion verifiable in unchecked-deletion mode,
    // where soli-logged solutions are discounted by the checker.
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion BOUNDS 1 : ")
                && line.contains(" 1 : ")
                && line.ends_with(';')),
        "<= OPT proof should conclude hinted exact bounds: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "<= OPT proof should end with VeriPB terminator: {proof}"
    );
    verify_proof_with_local_veripb("top_level_ay_le_opt", file.path(), &proof_path);
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_proof_on_golomb_incumbent_route_fails_closed_without_stale_proof() {
    let Some(file) = decompressed_repo_xz_to_temp(
        "benchmarks/pb-comp/PB25/normalized-PB25/OPT-LIN/wallon/normalized-GolombRuler-a3v18-15_c18.opb.xz",
    ) else {
        return;
    };

    let (plain_status, plain_rendered, plain_stderr) = run_pb_solve(&["--timeout", "5000"], &file);
    assert_eq!(
        plain_status.code(),
        Some(10),
        "Golomb no-proof incumbent route should exit SATISFIABLE; stderr: {plain_stderr}; stdout: {plain_rendered}"
    );
    assert!(
        plain_rendered.lines().any(|line| line == "o 168"),
        "Golomb no-proof incumbent route should emit incumbent objective 168, got: {plain_rendered}"
    );
    assert!(
        plain_rendered.contains("s SATISFIABLE\n"),
        "Golomb no-proof incumbent route should emit SATISFIABLE, got: {plain_rendered}"
    );
    assert!(
        !plain_rendered.contains("s OPTIMUM FOUND\n"),
        "Golomb local incumbent route must not claim OPTIMUM FOUND without proof: {plain_rendered}"
    );

    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("golomb-no-cert-incumbent.veripb");
    fs::write(&proof_path, "stale Golomb proof sidecar\n").expect("write stale proof sidecar");
    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");

    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "50", "--proof", proof_arg], &file);
    assert!(
        status.success(),
        "Golomb no-certificate proof-mode route should fail closed with a competition-safe status; stderr: {stderr}; stdout: {rendered}"
    );
    assert!(
        rendered.contains("s UNSUPPORTED\n"),
        "Golomb no-certificate proof-mode route should emit UNSUPPORTED, got: {rendered}"
    );
    assert!(
        rendered.contains("exact no-certificate optimization incumbent matched"),
        "Golomb no-certificate proof-mode route should explain the unsupported proof path, got: {rendered}"
    );
    assert!(
        !rendered.contains("s OPTIMUM FOUND\n"),
        "Golomb no-certificate proof-mode route must not claim OPTIMUM FOUND: {rendered}"
    );
    assert!(
        !proof_path.exists(),
        "Golomb no-certificate proof-mode route must remove stale proof sidecars"
    );
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_proof_on_nonlinear_opb_emits_s_unsupported_without_stale_proof() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("unsupported_nonlinear_opb.veripb");
    fs::write(
        file.path(),
        concat!(
            "* #variable= 2 #constraint= 1\n",
            "min: +1 x1 x2 ;\n",
            "+1 x1 +1 x2 <= 1 ;\n",
        ),
    )
    .expect("write should succeed");

    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");
    fs::write(&proof_path, "stale nonlinear OPB proof sidecar\n")
        .expect("write stale proof sidecar");
    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "5000", "--proof", proof_arg], &file);
    assert!(
        status.success(),
        "unsupported nonlinear OPB proof request should exit successfully; stderr: {stderr}"
    );
    assert_proof_request_is_unsupported(
        &rendered,
        &proof_path,
        "proof logging for non-linear PB is not supported",
        "nonlinear OPB",
    );
}

#[test]
fn test_pb_cli_le_wbo_no_proof_emits_optimum_competition_output() {
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        concat!(
            "soft: 10 ;\n",
            "+1 x1 +1 x2 <= 1 ;\n",
            "+1 x1 +1 x2 >= 1 ;\n",
            "[4] +1 x1 <= 0 ;\n",
            "[7] +1 x2 <= 0 ;\n",
        ),
    )
    .expect("write should succeed");

    let (status, rendered, stderr) = run_pb_solve(&["--timeout", "5000"], &file);
    assert_eq!(
        status.code(),
        Some(30),
        "<= WBO no-proof instance should exit OPTIMUM FOUND; stderr: {stderr}; stdout: {rendered}"
    );
    assert!(
        rendered.lines().any(|line| line == "o 4"),
        "<= WBO no-proof instance should emit projected soft cost 4, got: {rendered}"
    );
    assert!(
        rendered.contains("s OPTIMUM FOUND\n"),
        "<= WBO no-proof instance should emit OPTIMUM FOUND, got: {rendered}"
    );
    assert!(
        rendered.lines().any(|line| line.starts_with("v ")),
        "<= WBO no-proof instance should emit an original-variable witness line: {rendered}"
    );
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_proof_on_le_wbo_emits_s_unsupported() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("unsupported_le_wbo.veripb");
    fs::write(
        file.path(),
        concat!(
            "soft: 10 ;\n",
            "+1 x1 +1 x2 <= 1 ;\n",
            "+1 x1 +1 x2 >= 1 ;\n",
            "[4] +1 x1 <= 0 ;\n",
            "[7] +1 x2 <= 0 ;\n",
        ),
    )
    .expect("write should succeed");

    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");
    fs::write(&proof_path, "stale WBO proof sidecar\n").expect("write stale proof sidecar");
    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "5000", "--proof", proof_arg], &file);
    assert!(
        status.success(),
        "<= WBO proof request should exit successfully; stderr: {stderr}; stdout: {rendered}"
    );
    assert_wbo_proof_request_is_unsupported(&rendered, &proof_path);
}

#[test]
fn test_pb_cli_parse_time_unsupported_coefficient_emits_s_unsupported() {
    // The solver's supported coefficient range is the FULL i128 (see
    // `ParseError::is_unsupported_coefficient`); only a coefficient that
    // overflows i128 is unsupported. This test used to feed 2^63
    // (i64::MAX + 1) from the era of an i64 parse cap — that value now
    // parses and solves (pinned below), so the parse-time UNSUPPORTED
    // contract is exercised at the real boundary: 2^127, one past i128::MAX.
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 1 #constraint= 1\n+170141183460469231731687303715884105728 x1 >= 1 ;\n",
    )
    .expect("write should succeed");

    let (status, rendered, stderr) = run_pb_solve(&["--timeout", "5000"], &file);
    assert!(
        status.success(),
        "unsupported PB input should exit successfully, stderr: {stderr}"
    );
    assert!(
        rendered.contains("s UNSUPPORTED\n"),
        "i128-overflowing coefficient should emit s UNSUPPORTED, got: {rendered}"
    );
    assert!(
        !rendered.contains("\nv "),
        "parse-time unsupported should not emit a witness line: {rendered}"
    );
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_beyond_i64_coefficient_solves_within_i128_range() {
    // Deliberate contract lock for the i64 -> i128 coefficient-range
    // widening: 2^63 (the old cap's first rejected value) must now SOLVE,
    // not emit s UNSUPPORTED. Soundness under huge coefficients is
    // overflow-checked arithmetic (workspace `overflow-checks = true`), so
    // the failure mode of any residual overflow is a panic -> UNKNOWN,
    // never a wrong answer.
    let file = NamedTempFile::new().expect("temp file should exist");
    fs::write(
        file.path(),
        "* #variable= 1 #constraint= 1\n+9223372036854775808 x1 >= 1 ;\n",
    )
    .expect("write should succeed");

    let (status, rendered, stderr) = run_pb_solve(&["--timeout", "5000"], &file);
    assert_eq!(
        status.code(),
        Some(10),
        "2^63 coefficient should solve SATISFIABLE; stderr: {stderr}; stdout: {rendered}"
    );
    assert!(
        rendered.contains("s SATISFIABLE\n"),
        "2^63 coefficient instance is trivially satisfiable, got: {rendered}"
    );
    assert!(
        rendered.contains("v x1"),
        "witness must set x1 to satisfy the constraint: {rendered}"
    );
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_proof_on_optimization_emits_certified_optimum() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("opt.veripb");
    fs::write(
        file.path(),
        "* #variable= 2 #constraint= 1\nmin: +1 x1 +1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n",
    )
    .expect("write should succeed");

    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");
    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "5000", "--proof", proof_arg], &file);
    assert_eq!(
        status.code(),
        Some(30),
        "optimization proof request should exit with OPTIMUM FOUND code; stderr: {stderr}"
    );
    assert!(
        rendered.contains("o 1\n"),
        "optimization proof request should emit objective line, got: {rendered}"
    );
    assert!(
        rendered.contains("s OPTIMUM FOUND\n"),
        "optimization proof request should emit OPTIMUM FOUND, got: {rendered}"
    );
    assert!(
        rendered.contains("\nv "),
        "optimization proof request should emit a witness line: {rendered}"
    );
    let proof = fs::read_to_string(&proof_path).expect("proof file should be readable");
    assert!(
        proof.lines().any(|line| line == "output NONE;"),
        "optimization proof should contain VeriPB output marker: {proof}"
    );
    // Hinted conclusion form (`conclusion BOUNDS 1 : <id> 1 : <witness>;`):
    // the hints keep the conclusion verifiable in unchecked-deletion mode,
    // where soli-logged solutions are discounted by the checker.
    assert!(
        proof
            .lines()
            .any(|line| line.starts_with("conclusion BOUNDS 1 : ")
                && line.contains(" 1 : ")
                && line.ends_with(';')),
        "optimization proof should conclude hinted exact bounds: {proof}"
    );
    assert!(
        proof.lines().last() == Some("end pseudo-Boolean proof;"),
        "optimization proof should end with VeriPB terminator: {proof}"
    );
    assert_competition_safe_output(&rendered);
}

#[test]
fn test_pb_cli_proof_on_wbo_emits_s_unsupported() {
    let file = NamedTempFile::new().expect("temp file should exist");
    let proof_dir = tempdir().expect("temp dir should exist");
    let proof_path = proof_dir.path().join("unsupported_wbo.veripb");
    fs::write(file.path(), "soft: 10 ;\n+1 x1 >= 1 ;\n[1] +1 x2 >= 1 ;\n")
        .expect("write should succeed");

    let proof_arg = proof_path
        .to_str()
        .expect("temporary proof path should be utf-8");
    fs::write(&proof_path, "stale WBO proof sidecar\n").expect("write stale proof sidecar");
    let (status, rendered, stderr) =
        run_pb_solve(&["--timeout", "5000", "--proof", proof_arg], &file);
    assert!(
        status.success(),
        "unsupported WBO proof request should exit successfully, stderr: {stderr}"
    );
    assert_wbo_proof_request_is_unsupported(&rendered, &proof_path);
}
