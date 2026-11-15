// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! No proof run may leave a reservation beside the user's input.
//!
//! The synthesized default certificate is staged in a hidden sibling of the
//! input — `.<input>.alethe.tmp-<pid>-<nonce>` — and published by renaming it
//! onto `<input>.alethe`. Every path that does NOT reach that rename used to
//! leave the partial on disk: the emission work budget stopping mid-render, and
//! the no-replace publication losing to an artifact an earlier run had already
//! written. Measured on QF_UF `iso_brn492`, three `--rigor standard` runs left
//! three 29,182,083-byte partials, and this repository's benchmark tree had
//! accumulated roughly 936 such files.
//!
//! That is not only litter. Publication is deliberately no-replace, so an
//! artifact sitting next to an input makes the NEXT run over that directory
//! fail to publish — which means a leak silently under-reports certification on
//! every later measurement of the same corpus. The cases below pin the
//! CLI-observable half of the property; the abandonment seam itself (a partial
//! rendered past the writer's buffer, then given up on) is pinned as a unit
//! test in `crates/ay/src/run.rs`.

use ntest::timeout;
use std::path::Path;
use std::process::Command;

/// A three-clause propositional contradiction: UNSAT in milliseconds, and its
/// Alethe certificate renders well inside the emission budget, so the FIRST run
/// takes the successful publication path.
const UNSAT_INPUT: &str = concat!(
    "(set-logic QF_UF)\n",
    "(declare-fun p () Bool)\n",
    "(declare-fun q () Bool)\n",
    "(assert (or p q))\n",
    "(assert (not p))\n",
    "(assert (not q))\n",
    "(check-sat)\n",
);

/// Every reservation left in `directory`, by name.
fn reservation_debris(directory: &Path) -> Vec<String> {
    std::fs::read_dir(directory)
        .expect("read the input directory")
        .map(|entry| entry.expect("read a directory entry").file_name())
        .filter_map(|name| name.to_str().map(str::to_owned))
        .filter(|name| name.contains(".tmp-"))
        .collect()
}

fn solve_certifying(input: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["--rigor", "standard"])
        .arg(input)
        .output()
        .expect("spawn ay")
}

#[test]
#[timeout(60_000)]
fn repeated_certifying_runs_leave_no_proof_reservation_beside_the_input() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let input = temp.path().join("unsat.smt2");
    std::fs::write(&input, UNSAT_INPUT).expect("write the SMT-LIB input");
    let certificate = temp.path().join("unsat.smt2.alethe");

    // First run: the certificate is published, and nothing else appears.
    let first = solve_certifying(&input);
    let stdout = String::from_utf8_lossy(&first.stdout);
    let stderr = String::from_utf8_lossy(&first.stderr);
    assert!(
        first.status.success(),
        "first run failed; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "first run lost the verdict; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        certificate.is_file(),
        "a successful certifying run must publish {}; stderr={stderr}",
        certificate.display()
    );
    let published = std::fs::read(&certificate).expect("read the published certificate");
    assert!(
        reservation_debris(temp.path()).is_empty(),
        "a successful publication left debris: {:?}",
        reservation_debris(temp.path())
    );

    // Second run: publication loses to the artifact already there. The verdict
    // stands, the earlier certificate is preserved, and — the regression —
    // the reservation for the certificate that could not be published is gone.
    let second = solve_certifying(&input);
    let stdout = String::from_utf8_lossy(&second.stdout);
    let stderr = String::from_utf8_lossy(&second.stderr);
    assert!(
        second.status.success(),
        "second run failed; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "an unpublishable optional certificate must not change the verdict; \
         stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        std::fs::read(&certificate).expect("read the preserved certificate"),
        published,
        "the second run overwrote the earlier certificate"
    );
    assert!(
        reservation_debris(temp.path()).is_empty(),
        "a lost publication left debris: {:?}",
        reservation_debris(temp.path())
    );
}

#[test]
#[timeout(60_000)]
fn explicit_proof_target_collision_leaves_no_reservation() {
    let temp = tempfile::tempdir().expect("temporary directory");
    let input = temp.path().join("unsat.smt2");
    std::fs::write(&input, UNSAT_INPUT).expect("write the SMT-LIB input");
    let proof = temp.path().join("requested.alethe");
    std::fs::write(&proof, "pre-existing certificate").expect("plant the proof target");

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(["solve", "--no-verify-proof", "--proof"])
        .arg(&proof)
        .arg(&input)
        .output()
        .expect("spawn ay with an explicit proof target");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert_eq!(
        std::fs::read_to_string(&proof).expect("read the preserved proof target"),
        "pre-existing certificate",
        "an explicit proof target was replaced; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        reservation_debris(temp.path()).is_empty(),
        "an explicit proof collision left debris: {:?}; stdout={stdout}; stderr={stderr}",
        reservation_debris(temp.path())
    );
}
