// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE PUBLICATION GATE: a zero exit status reports the VERDICT, never the
//! certificate.
//!
//! Without `--strict-proofs`, AY publishes the certificate it actually
//! derived, including one that still carries unproved (`hole`) steps. An
//! external checker calls such a document *holey* — or *invalid* when a
//! residual step is malformed — never *valid*, and AY's own `--self-check`
//! gate answers `unknown` for the same verdict. Publishing that silently
//! under exit 0 is the hazard; these tests pin the disclosure that removes
//! it, in both directions:
//!
//!  * a fully promoted, trust-free certificate says so
//!    (`trust_free=yes ay_self_checkable=yes`, no warning), and
//!  * a certificate AY's own gate rejects says THAT, in words, on stderr.

use std::process::Command;

use tempfile::TempDir;

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

/// Run `ay <script> --proof <tmp>` and return `(stdout, stderr)`.
fn emit_proof(script: &str) -> (String, String) {
    let dir = TempDir::new().expect("tempdir");
    let input = dir.path().join("problem.smt2");
    std::fs::write(&input, script).expect("write problem");
    let proof = dir.path().join("proof.alethe");
    let out = Command::new(ay_binary())
        .arg(&input)
        .arg("--proof")
        .arg(&proof)
        .output()
        .expect("run ay");
    (
        String::from_utf8_lossy(&out.stdout).into_owned(),
        String::from_utf8_lossy(&out.stderr).into_owned(),
    )
}

/// The QF_AX store-inverse collapse: fully promoted, so the published
/// certificate is trust-free and AY stands behind the verdict.
#[test]
fn trust_free_certificate_is_disclosed_as_self_checkable() {
    let (stdout, stderr) = emit_proof(
        r#"
        (set-logic QF_AX)
        (declare-sort Index 0)
        (declare-sort Element 0)
        (declare-fun a1 () (Array Index Element))
        (declare-fun a2 () (Array Index Element))
        (declare-fun i () Index)
        (declare-fun v0 () (Array Index Element))
        (assert (= v0 (store a2 i (select a1 i))))
        (declare-fun v1 () (Array Index Element))
        (assert (= v1 (store a1 i (select a2 i))))
        (assert (= v0 v1))
        (assert (not (= a1 a2)))
        (check-sat)
        (exit)
    "#,
    );
    // The verdict on this shape is not fixed by this test. Concurrent work on
    // Alethe validity can legitimately move it to `unknown`, in which case NO
    // certificate is published and there is nothing to disclose — which already
    // satisfies what this test exists to guard. Only an `unsat` that publishes a
    // document obliges a disclosure.
    if !stdout.contains("unsat") {
        assert!(
            stdout.contains("unknown"),
            "expected unsat or a fail-closed unknown; stdout={stdout}\nstderr={stderr}"
        );
        assert!(
            !stderr.contains("c ay.proof.certificate"),
            "nothing may be disclosed when nothing is published; stderr={stderr}"
        );
        return;
    }
    assert!(
        stderr.contains("c ay.proof.certificate"),
        "a published certificate must disclose which checks it passed; stderr={stderr}"
    );
    assert!(
        stderr.contains("unproved_steps=0"),
        "the promoted certificate must carry no unproved step; stderr={stderr}"
    );
    assert!(stderr.contains("trust_free=yes"), "stderr={stderr}");
    assert!(stderr.contains("ay_self_checkable=yes"), "stderr={stderr}");
    assert!(
        !stderr.contains("NOT an externally checkable certificate"),
        "a trust-free certificate must not be disclaimed; stderr={stderr}"
    );
}

/// A refutation AY cannot self-check must SAY so next to the file it wrote,
/// so exit 0 cannot be read as "externally checkable".
#[test]
fn certificate_ay_cannot_self_check_is_disclosed_as_not_externally_checkable() {
    // The 2-index cross-swap: still exported with unproved array leaves.
    let (stdout, stderr) = emit_proof(
        r#"
        (set-logic QF_AUFLIA)
        (declare-fun a1 () (Array Int Int))
        (declare-fun a2 () (Array Int Int))
        (declare-fun i1 () Int)
        (declare-fun i2 () Int)
        (declare-fun v0 () (Array Int Int))
        (declare-fun v1 () (Array Int Int))
        (assert (= v0 (store a2 i1 (select a1 i1))))
        (assert (= v1 (store a1 i1 (select a2 i1))))
        (declare-fun lhs () (Array Int Int))
        (declare-fun rhs () (Array Int Int))
        (assert (= lhs (store v1 i2 (select v0 i2))))
        (assert (= rhs (store v0 i2 (select v1 i2))))
        (assert (= lhs rhs))
        (assert (not (= a1 a2)))
        (check-sat)
        (exit)
    "#,
    );
    // The verdict on this shape is NOT fixed by this test. AY's mandatory strict
    // certification can legitimately reject its own proof ("step t4 uses
    // unsupported theory lemma kind Generic in strict mode") and downgrade to
    // `unknown`, in which case NO certificate is published and there is nothing
    // to disclose — which is a stronger outcome than disclosure, and already
    // satisfies what this test guards. Only an `unsat` that publishes a document
    // obliges a disclosure.
    if !stdout.contains("unsat") {
        assert!(
            stdout.contains("unknown"),
            "expected unsat, or a fail-closed unknown; stdout={stdout}\nstderr={stderr}"
        );
        assert!(
            !stderr.contains("c ay.proof.certificate"),
            "nothing may be disclosed when nothing is published; stderr={stderr}"
        );
        return;
    }
    assert!(
        stderr.contains("c ay.proof.certificate"),
        "a published certificate must disclose which checks it passed; stderr={stderr}"
    );
    // Either the certificate is fully promoted (then it must claim so
    // truthfully) or it is not (then it must be disclaimed in words). What is
    // forbidden is a silent exit-0 publication of an uncheckable document.
    let promoted = stderr.contains("ay_self_checkable=yes");
    if promoted {
        assert!(
            stderr.contains("unproved_steps=0") && stderr.contains("trust_free=yes"),
            "a self-checkable claim must be backed by a trust-free report; stderr={stderr}"
        );
    } else {
        assert!(
            stderr.contains("NOT an externally checkable certificate"),
            "an unproved certificate must be disclaimed in words; stderr={stderr}"
        );
        assert!(
            stderr.contains("`--self-check` answers `unknown`"),
            "the disclaimer must name the verdict AY would give; stderr={stderr}"
        );
    }
}
