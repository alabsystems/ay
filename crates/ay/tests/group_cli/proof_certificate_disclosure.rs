// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE PUBLICATION GATE: a zero exit status reports the VERDICT, never the
//! certificate.
//!
//! AY publishes the certificate it actually derived, including one that still
//! carries unproved (`hole`) steps. An external checker calls such a document
//! *holey* — or *invalid* when a residual step is malformed — never *valid*.
//! Publishing that silently under exit 0 is the hazard; these tests pin the
//! disclosure that removes it, in three directions:
//!
//!  * a fully promoted, trust-free certificate says so
//!    (`trust_free=yes ay_self_checkable=yes`, no warning),
//!  * a certificate AY's own gate rejects says THAT, in words, on stderr, and
//!  * `ay_self_checkable=yes` IMPLIES `unproved_steps=0`, so the flag alone is
//!    a safe evidence predicate (#evidence-stage-0).
//!
//! `ay_self_checkable=no` is a fact about the DOCUMENT and never a prediction
//! about the verdict: `--rigor strict` decides on the in-memory derivation, so
//! it publishes verdicts whose printed document the printer alone holed.

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
        // CHANGED by #evidence-stage-0, and NOT a weakening: the disclaimer
        // used to assert unconditionally that `--rigor strict` answers
        // `unknown` here, and that sentence is false for the class of documents
        // holed by the PRINTER alone (a rule AY's own strict checker verified
        // but `ay_core::wire_rule_name` has no external spelling for). The
        // disclosure now names the consequence that actually applies, so what
        // this test pins is that ONE of the two is stated, never neither.
        //
        // CHANGED again by the strict publication gate: `--rigor strict` now
        // withholds EVERY certificate with an unproved step, printer-made holes
        // included, so the consequence is the same for both causes and must
        // always be stated; what still differs is the explanation, and exactly
        // one of the two must be given.
        let refused = stderr.contains("`--rigor strict` (`--strict-proofs`) answers `unknown`");
        assert!(
            refused,
            "an unproved certificate must say that --rigor strict withholds its verdict; stderr={stderr}"
        );
        let derivation_unproved =
            stderr.contains("and so does `--rigor certified` (`--self-check`)");
        let printer_only =
            stderr.contains("these holes are a PRINTER limitation, not an unproved step");
        assert!(
            derivation_unproved ^ printer_only,
            "the disclaimer must give exactly one explanation for the holes, \
             decided rather than left silent; stderr={stderr}"
        );
    }
}

/// The disclaimer must not claim `--self-check` refuses a verdict `--self-check`
/// publishes.
///
/// MEASURED (seeded 60-file smtlib-all sweep, 2026-09-06): two files published
/// `unsat` under bare `--self-check` while the same run printed
/// `ay_self_checkable=no` and the old disclaimer's "so `--self-check` answers
/// `unknown` for this verdict". They are not the same gate: `ay_self_checkable`
/// is the `--rigor strict` terminal-trust screen over the emitted DOCUMENT,
/// while `--rigor certified` accepts a replayed SAT-resolution refutation, a
/// native BV DRAT re-check, or a strict Alethe proof — any one of them.
///
/// The two-store commutation below is the smallest shape that produces it:
/// preprocessing folds the authored assertion to `false` by normalising the
/// store chains, keeps no derivation for the rewrite, and the exported document
/// collapses to the bare `(step t0 (cl) :rule hole)`. The verdict is admitted by
/// `checked-sat-refutation`.
#[test]
fn disclaimer_never_claims_self_check_refuses_a_verdict_it_publishes() {
    let dir = TempDir::new().expect("tempdir");
    let input = dir.path().join("storecomm.smt2");
    std::fs::write(
        &input,
        "(set-logic QF_AUFLIA)\n\
         (declare-fun a () (Array Int Int))\n\
         (declare-fun x () Int)\n\
         (declare-fun y () Int)\n\
         (assert (not (= (store (store a 1 x) 2 y) (store (store a 2 y) 1 x))))\n\
         (check-sat)\n\
         (exit)\n",
    )
    .expect("write problem");
    let out = Command::new(ay_binary())
        .arg(&input)
        .arg("--self-check")
        .arg("-T:30")
        .output()
        .expect("run ay");
    let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
    // A fail-closed `unknown` is always an acceptable outcome here; the hazard
    // is only a published verdict disclaimed as withheld.
    if !stdout.lines().any(|line| line.trim() == "unsat") {
        return;
    }
    assert!(
        !stderr.contains("`--self-check` answers `unknown` for this verdict"),
        "the run published `unsat` under --self-check; nothing may claim it did not: stderr={stderr}"
    );
    assert!(
        stderr.contains("unsat_admission="),
        "a published certificate must name the authority behind the verdict; stderr={stderr}"
    );
    assert!(
        !stderr.contains("unsat_admission=none-recorded"),
        "a published UNSAT always consumed a certification capability; stderr={stderr}"
    );
}

/// #evidence-stage-0 — `ay_self_checkable=yes` must IMPLY `unproved_steps=0`.
///
/// MEASURED at `57fbdb5b14`. `ay --stats-full onehole.smt2`, and equally
/// `ay --rigor strict --stats-full onehole.smt2`, printed
///
///   c ay.proof.certificate path=… unproved_steps=1 foreign_assumes=no
///     trust_free=no ay_self_checkable=yes unsat_admission=strict-proof
///
/// beside the three-line artifact
///
///   (assume t0 (not (or (= #b10 #b10) (= x #b01))))
///   (step t1 (cl (not (not (or (= #b10 #b10) (= x #b01))))) :rule hole)
///   (step t2 (cl) :rule th_resolution :premises (t1 t0))
///
/// whose ONLY inference is a hole. The verdict is right and the admission tag
/// is right — `check_proof_strict_with_datatypes` really did re-derive that
/// step, and it rejects `trust`/`hole` — but the DOCUMENT proves nothing, and
/// the flag a corpus census scores on said it was clean. Both internal
/// predicates behind the old flag read the in-memory proof, so neither can see
/// `ay_core::wire_rule_name` downgrading a rule with no external spelling at
/// print time. At corpus scale that misread 78 certificates carrying up to 148
/// unproved steps as evidence.
///
/// The verdict is deliberately NOT pinned: whether AY refutes this shape is a
/// capability question. What is pinned is that a published document carrying a
/// printed `hole` never reads as self-checkable.
///
/// THE REPRODUCER MOVED, the property did not. The shape above stopped being a
/// one-hole document once the bounded bit-blast circuit refutation lane
/// (`format_bv_circuit_refutation`, first landed in 867189d65) learned to
/// spell it -- holey at 57fbdb5b14, hole-free by 45a092144. At ba16ac467 it
/// prints a `bitblast_*`/`resolution` subproof that
/// pinned Carcara 1.1.0 answers `valid`, disclosed truthfully as
/// `unproved_steps=0 trust_free=yes ay_self_checkable=yes` (and
/// `self_checkable_agrees_with_the_document_in_both_directions` still covers
/// it). The pin now rides `(bvnand x x) = (bvnot x)`, which is still the
/// printer-alone class: the same three-line artifact (`hole` +
/// `resolution`, Carcara: `holey`) under `unsat_admission=strict-proof` with
/// no `trust` on the path; `bvnand` is outside the circuit lane's operator set
/// (`circuit::source::preflight`). Binaries without #evidence-stage-0 (13e3e124e,
/// fd3ac6df6) print `unproved_steps=1 … ay_self_checkable=yes` on it at both
/// rigor levels, which is exactly the lie this test exists to catch. The
/// document is read back so the premise is checked rather than assumed: if the
/// printer ever learns this spelling too, the test says so instead of passing
/// or failing for the wrong reason.
#[test]
fn a_document_whose_only_inference_is_a_hole_is_not_self_checkable() {
    let mut exercised = 0;
    for rigor in [None, Some("strict")] {
        let dir = TempDir::new().expect("tempdir");
        let input = dir.path().join("onehole.smt2");
        std::fs::write(
            &input,
            "(set-logic QF_BV)\n\
             (declare-const x (_ BitVec 8))\n\
             (assert (not (= (bvnand x x) (bvnot x))))\n\
             (check-sat)\n",
        )
        .expect("write problem");
        let mut cmd = Command::new(ay_binary());
        if let Some(level) = rigor {
            cmd.args(["--rigor", level]);
        }
        let out = cmd.arg("-T:30").arg(&input).output().expect("run ay");
        let stdout = String::from_utf8_lossy(&out.stdout).into_owned();
        let stderr = String::from_utf8_lossy(&out.stderr).into_owned();
        let label = rigor.unwrap_or("default");
        if !stdout.lines().any(|line| line.trim() == "unsat") {
            continue;
        }
        let Some(cert) = stderr
            .lines()
            .find(|line| line.starts_with("c ay.proof.certificate "))
        else {
            continue;
        };
        let document_path = cert
            .split_whitespace()
            .find_map(|field| field.strip_prefix("path="))
            .expect("the certificate line names its document");
        let document = std::fs::read_to_string(document_path)
            .unwrap_or_else(|error| panic!("[{label}] read {document_path}: {error}"));
        let printed_holes = document
            .lines()
            .filter(|line| line.contains(":rule hole") || line.contains(":rule trust"))
            .count();
        assert_eq!(
            printed_holes, 1,
            "[{label}] premise: this shape must still print the one-hole artifact. \
             If it prints none, the printer learned its spelling and the pin must \
             move to a shape that is still printer-holed; document:\n{document}"
        );
        exercised += 1;
        assert!(
            cert.contains("unproved_steps=1"),
            "[{label}] this shape's document is the one-hole artifact; cert={cert}"
        );
        assert!(
            cert.contains("ay_self_checkable=no"),
            "[{label}] a document whose only inference is a `hole` must never \
             read as self-checkable; cert={cert}"
        );
        assert!(
            stderr.contains("NOT an externally checkable certificate"),
            "[{label}] and it must say so in words; stderr={stderr}"
        );
        // Last, so the lie above is what a regression reports: this sentence
        // is printed only beside `ay_self_checkable=no`.
        assert!(
            stderr.contains("these holes are a PRINTER limitation"),
            "[{label}] premise: the hole must come from the printer alone -- the \
             class the in-memory predicates call clean; stderr={stderr}"
        );
    }
    assert!(
        exercised > 0,
        "no rigor level published a document for this shape, so this test \
         exercised nothing; pick a shape AY still refutes with a printer-holed document"
    );
}

/// The disclosure's invariant in BOTH directions, on whatever documents the
/// suite happens to publish:
///
///  * `ay_self_checkable=yes` may never appear beside a non-zero
///    `unproved_steps` — the property a corpus census scores on; and
///  * a certificate that is both `unproved_steps=0` and `trust_free=yes` must
///    read `ay_self_checkable=yes`.
///
/// The second direction is a REFUTATION GUARD. #evidence-stage-0 first
/// conjoined the flag with `Executor::unsat_proof_has_known_wire_gap()` — the
/// executor strict-decline gate's second arm — on the theory that the
/// disclosure and that gate should agree. Measured on corpus file
/// `QF_AX/…storeinv_t2_np_nf_ai_00001_001.cvc.smt2`, the predicate answers
/// TRUE at disclosure time on a `unproved_steps=0 trust_free=yes` certificate
/// that the SAME run publishes under `--rigor strict`. The two are sampled at
/// different points of the pipeline, so conjoining them does not make the flag
/// agree with the gate — it makes the flag deny a hole-free document (1 of the
/// 2 hole-free certificates in a seeded 50-file QF_AX/QF_IDL sweep). This
/// assertion fails if that arm is ever reintroduced.
///
/// Pinning either direction on ONE shape is not enough — the campaign's own
/// reproducers landed in three different theories — so assert over several.
///
/// Script 3 keeps the first direction armed. Script 0 now prints a hole-free
/// document (see `a_document_whose_only_inference_is_a_hole_is_not_self_checkable`),
/// and with it no script here published a printer-holed document: with the
/// flag reverted to `!terminal_trust_detected` alone, this test still passed.
/// The printer-alone `bvnand` document makes that mutant fail here too.
#[test]
fn self_checkable_agrees_with_the_document_in_both_directions() {
    let scripts: [&str; 4] = [
        "(set-logic QF_BV)\n\
         (declare-const x (_ BitVec 2))\n\
         (assert (not (or (= #b10 #b10) (= x #b01))))\n\
         (check-sat)\n",
        "(set-logic QF_AUFLIA)\n\
         (declare-fun a () (Array Int Int))\n\
         (declare-fun x () Int)\n\
         (declare-fun y () Int)\n\
         (assert (not (= (store (store a 1 x) 2 y) (store (store a 2 y) 1 x))))\n\
         (check-sat)\n",
        "(set-logic QF_UF)\n\
         (declare-const p Bool)\n\
         (assert p)\n\
         (assert (not p))\n\
         (check-sat)\n",
        "(set-logic QF_BV)\n\
         (declare-const x (_ BitVec 8))\n\
         (assert (not (= (bvnand x x) (bvnot x))))\n\
         (check-sat)\n",
    ];
    for (index, script) in scripts.iter().enumerate() {
        let (_stdout, stderr) = emit_proof(script);
        for cert in stderr
            .lines()
            .filter(|line| line.starts_with("c ay.proof.certificate "))
        {
            if cert.contains("ay_self_checkable=yes") {
                assert!(
                    cert.contains("unproved_steps=0"),
                    "[script {index}] `ay_self_checkable=yes` must imply \
                     `unproved_steps=0`; cert={cert}"
                );
            }
            if cert.contains("unproved_steps=0") && cert.contains("trust_free=yes") {
                assert!(
                    cert.contains("ay_self_checkable=yes"),
                    "[script {index}] a hole-free, trust-free document must not \
                     be denied the flag; cert={cert}"
                );
            }
        }
    }
}

/// A trust-free derivation refused only for its SURFACE is never disclosed as
/// a trust step.
///
/// This branch of the 2026-09-23 fp-strings verifier's `g5_00027` refutes on
/// one `FpGroundEval` lemma, which AY's strict checker validates with the exact
/// IEEE-754 evaluator (`unsat_admission=strict-proof`). The printer has no
/// external spelling for it (one printed `hole`), and pinned Carcara cannot
/// parse a FloatingPoint sort, so `--rigor strict` refuses the document for its
/// surface. The decline used to key trust-freeness on the DOCUMENT's hole
/// count and printed `terminal-trust-step-on-path` — "a step AY's own strict
/// checker refuses" — which is false, and which read to the verifier as a hole
/// in the derivation.
#[test]
fn a_strict_checked_fp_refutation_is_not_disclosed_as_a_trust_step() {
    let (stdout, stderr) = emit_proof(
        "(set-logic ALL)\n\
         (declare-const q Real)\n\
         (declare-const x0 (_ FloatingPoint 3 5))\n\
         (assert (= x0 ((_ to_fp 3 5) RTZ q)))\n\
         (assert (= q 1000.0))\n\
         (assert (fp.isZero (fp.div RTZ (fp #b1 #b110 #b0111) (_ +zero 3 5))))\n\
         (check-sat)\n",
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "unsat"),
        "stdout={stdout} stderr={stderr}"
    );
    let cert = stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .unwrap_or_else(|| panic!("a certificate is emitted; stderr={stderr}"));
    assert!(
        cert.contains("unsat_admission=strict-proof")
            && cert.contains("carcara_surface=unsupported"),
        "the premise: a strict proof whose surface pinned Carcara cannot parse; cert={cert}"
    );
    let decline = stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.decline "))
        .unwrap_or_else(|| panic!("a decline is disclosed; stderr={stderr}"));
    assert!(
        decline.contains("mechanism=pinned-checker-surface-unsupported"),
        "a trust-free derivation refused for its surface only; decline={decline}"
    );
}
