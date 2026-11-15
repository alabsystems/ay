// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A 32-bit divider lemma that closes only through its exact-division sweep
//! keeps its admission.
//!
//! `x % 1000003 < 1000003` over a 32-bit `x`: the solver decides it in about
//! 1,400 conflicts, and the strict checker admitted its divider lemma only
//! through the exact-division sweep, after 67,222 conflicts (measured
//! 2026-10-14). A proof-build sweep allowance sized by the solve (20,000
//! conflicts) declined that lemma in review: the default posture fell from
//! `strict-proof` with no unproved step to `discharged-trust` with a hole,
//! and `--rigor strict` from `unsat` to `unknown`. The build's memo of failed
//! exact-division sweeps (`ay_proof::ExactDivisionSweepMemo`) leaves every
//! first sweep its whole envelope.
//!
//! That obligation no longer reaches the sweep: the theorem `d = 0 or x % d <
//! d` closes it with the division abstracted, and it is asked where a pass
//! would pay for the exact divider (`guarded/urem_bound/before_division.rs`;
//! default posture 9.9 s before, 0.9 s after, on f6555db0b). So the sweep is
//! pinned on `x % 1000003 <= x`, which that bound does not imply (it says
//! nothing when `x < 1000003`): the joint is asked and declined, and the
//! divider lemma still closes only through its exact-division sweep (on
//! f6555db0b, gdb samples at 1.5, 4.5 and 7.5 s of a 10.8 s run are all
//! inside `sat_sweep::Sweep`). The remainder bound itself is pinned to the
//! theorem, before any sweep, in the default posture.

use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// Closes only through its exact-division sweep.
const SWEEP_CLOSED: &str = "(set-logic QF_BV)\n\
    (declare-const x (_ BitVec 32))\n\
    (assert (not (bvule (bvurem x #x000f4243) x)))\n\
    (check-sat)\n";

/// Closed by the BvUremBound theorem.
const REMAINDER_BOUND: &str = "(set-logic QF_BV)\n\
    (declare-const x (_ BitVec 32))\n\
    (assert (not (bvult (bvurem x #x000f4243) #x000f4243)))\n\
    (check-sat)\n";

/// `ay <args> <query>`: its stdout and stderr.
fn run(query: &str, args: &[&str]) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("rem32.smt2");
    std::fs::write(&input, query).expect("write the query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg(&input)
        .current_dir(dir.path())
        .output_timeout(Duration::from_secs(300))
        .expect("ay finishes within the child deadline");
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

#[test]
fn the_default_posture_keeps_a_sweep_closed_divider_lemma_strict() {
    let (stdout, stderr) = run(SWEEP_CLOSED, &[]);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "stdout={stdout} stderr={stderr}"
    );
    let certificate = stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .unwrap_or_else(|| panic!("a certificate is emitted; stderr={stderr}"));
    assert!(
        certificate.contains("unsat_admission=strict-proof")
            && certificate.contains("unproved_steps=0"),
        "certificate={certificate}"
    );
}

#[test]
fn rigor_strict_answers_a_sweep_closed_divider_lemma() {
    let (stdout, stderr) = run(SWEEP_CLOSED, &["--rigor", "strict"]);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "stdout={stdout} stderr={stderr}"
    );
}

/// The default posture keeps no SAT-level derivation here, so its proof rests
/// on one Generic lemma, and the joint certifies the bound where the Generic
/// promotion would pay for the exact divider.
#[test]
fn the_default_posture_admits_the_remainder_bound_before_any_sweep() {
    let (stdout, stderr) = run(REMAINDER_BOUND, &["--probe-cert-reject"]);
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "stdout={stdout} stderr={stderr}"
    );
    assert!(
        stderr.contains("urem-bound joint before the Generic promotion's exact divider: installed"),
        "stderr={stderr}"
    );
    assert!(
        stderr.contains("unsat_admission=strict-proof"),
        "stderr={stderr}"
    );
}
