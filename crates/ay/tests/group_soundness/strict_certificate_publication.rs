// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--strict-proofs` publishes `unsat` only together with a certificate that
//! proves it.
//!
//! external-codegen's one-shot argv is `-smt2 FILE --strict-proofs --proof FILE.alethe
//! --proof-format alethe`. Measured on AY 36a5da9d7 (and on 5da8198d1 and
//! cc347ee0a), four of the external-codegen corpus queries were published `unsat` under
//! it with `unproved_steps=1 foreign_assumes=no trust_free=no
//! ay_self_checkable=no unsat_admission=strict-proof`: a three-line document
//! whose only inference is a `hole` (a whole-query bit-blast lemma the printer
//! has no external spelling for). Two of them also `assume` a spelling of the
//! input assertion the input does not contain, so the external checker
//! refuses them at `t0`.
//!
//! Nothing compared the published document with that promise. The driver's
//! strict screen reads the in-memory proof, where AY's own strict checker had
//! validated every step (`unsat_admission=strict-proof`); the printer then
//! downgraded the step it has no external spelling for to `hole`. Over 984
//! benchmark files the same gap published 62 `unsat`s on certificates with
//! unproved steps.

use ntest::timeout;
use std::fmt::Write as _;
use std::io::Write as _;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use crate::spawn::OutputTimeout;

/// `bridge_bounds_check_dom_ult_64_implies_ult_1024_w64`,
/// `sbs_stride1_state_new_ft`,
/// `bridge_bounds_check_dom_ule_1023_implies_ult_1024_w64`,
/// `se_last_split_f0`.
pub(super) const PUBLISHED_ON_A_HOLE: [&str; 4] = [
    "2fedfcfe4439",
    "3ba4bfb85853",
    "5550e46562f2",
    "758d3c8d8705",
];

pub(super) const QUERY_TIMEOUT: Duration = Duration::from_mins(5);

pub(super) fn body(id: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/group_soundness/fixtures/external_codegen_resident_session")
        .join(format!("{id}.smt2"));
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

pub(super) fn verdict_lines(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_string)
        .collect()
}

/// A corpus script without its own `(set-option :timeout N)`.
///
/// The external-codegen queries carry `:timeout 30000`: a wall-clock deadline the
/// INPUT asks for, which makes their verdict a function of machine load rather
/// than of the strict gate. `758d3c8d8705` spends 6-10 s of CPU (by build
/// profile) before the strict refusal, and took 16-60 s of wall time at load
/// averages of 45-85. Past its budget it answers `unknown` with
/// `(:reason-unknown timeout)`, which is neither the `unsat` nor the strict
/// refusal a strict-gate test accepts: that is how
/// `strict_routes_without_a_certificate_file_never_publish_unsat_on_a_hole`
/// failed once in seven runs, and how
/// [`strict_one_shot_never_publishes_unsat_on_an_unproved_certificate`] failed
/// in 6 of 8 full `group_soundness` runs at load averages of 52-68.
///
/// Dropping the script's budget leaves every assertion as strict as before; the
/// harness's own `QUERY_TIMEOUT` still bounds the run, and
/// [`strict_one_shot_past_its_own_deadline_keeps_the_publication_contract`]
/// covers the deadline arm deterministically.
pub(super) fn without_script_timeout(script: &str) -> String {
    let mut filtered = String::new();
    for line in script
        .lines()
        .filter(|line| !line.trim_start().starts_with("(set-option :timeout "))
    {
        writeln!(&mut filtered, "{line}").expect("writing to a String cannot fail");
    }
    filtered
}

/// What external-codegen's one-shot argv published for one script.
struct OneShot {
    success: bool,
    verdicts: Vec<String>,
    stderr: String,
    /// Bytes at the `--proof` path after the run; 0 when absent.
    certificate_bytes: u64,
    context: String,
}

/// Run `ay -smt2 F --strict-proofs --proof F.alethe --proof-format alethe`.
fn run_one_shot(id: &str, script: &str) -> OneShot {
    let dir = tempfile::tempdir().expect("tempdir");
    let smt2 = dir.path().join("query.smt2");
    let proof = dir.path().join("query.smt2.alethe");
    let mut file = std::fs::File::create(&smt2).expect("create query file");
    file.write_all(script.as_bytes()).expect("write query");
    file.write_all(b"(exit)\n").expect("write exit");
    drop(file);
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("-smt2")
        .arg(&smt2)
        .arg("--strict-proofs")
        .arg("--proof")
        .arg(&proof)
        .args(["--proof-format", "alethe"])
        .output_timeout(QUERY_TIMEOUT)
        .expect("run ay one-shot");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    OneShot {
        success: output.status.success(),
        verdicts: verdict_lines(&stdout),
        certificate_bytes: std::fs::metadata(&proof).map_or(0, |m| m.len()),
        context: format!(
            "{id} (exit {:?})\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status
        ),
        stderr,
    }
}

/// The contract a strict one-shot keeps whatever its verdict: `unsat` only
/// with a disclosed certificate on disk that has no unproved step and no
/// foreign `assume`; a withheld verdict leaves no certificate behind, discloses
/// none, and names a reason. Returns that reason line for a withheld verdict.
fn assert_publication_contract(run: &OneShot) -> Option<String> {
    let context = &run.context;
    assert!(run.success, "{context}");
    match run.verdicts.as_slice() {
        [v] if v == "unsat" => {
            let certificate = run
                .stderr
                .lines()
                .find(|l| l.contains("c ay.proof.certificate "))
                .unwrap_or_else(|| panic!("published unsat without a certificate line: {context}"));
            for field in ["unproved_steps=0", "foreign_assumes=no"] {
                assert!(
                    certificate.split_whitespace().any(|w| w == field),
                    "strict published unsat without {field}: {context}"
                );
            }
            assert!(
                run.certificate_bytes > 0,
                "published unsat without its certificate: {context}"
            );
            None
        }
        [v] if v == "unknown" => {
            assert_eq!(
                run.certificate_bytes, 0,
                "a withheld verdict left a certificate behind: {context}"
            );
            assert!(
                !run.stderr.contains("c ay.proof.certificate "),
                "a withheld verdict disclosed a certificate: {context}"
            );
            let reason = run
                .stderr
                .lines()
                .map(str::trim)
                .find(|l| l.starts_with("(:reason-unknown "))
                .unwrap_or_else(|| panic!("a withheld verdict must say why: {context}"));
            Some(reason.to_string())
        }
        other => panic!("expected exactly one of unsat/unknown, got {other:?}: {context}"),
    }
}

/// external-codegen's one-shot argv never publishes `unsat` on a certificate with an
/// unproved step or a foreign `assume`. Withholding the verdict must leave no
/// certificate behind and name the strict reason.
///
/// The scripts run without their own `:timeout` (see
/// [`without_script_timeout`]). With it, this test failed at
/// `a withheld strict verdict must say why: 758d3c8d8705` with
/// `(:reason-unknown timeout)` in 6 of 8 full `group_soundness` runs at load
/// averages of 52-68 (on d9085f057): the query's own deadline ended it before
/// any verdict reached the strict gate.
#[test]
#[timeout(1_200_000)]
fn strict_one_shot_never_publishes_unsat_on_an_unproved_certificate() {
    for id in PUBLISHED_ON_A_HOLE {
        let script = without_script_timeout(&body(id));
        assert!(!script.contains(":timeout"), "{id}: {script}");
        let run = run_one_shot(id, &script);
        if let Some(reason) = assert_publication_contract(&run) {
            assert_eq!(
                reason, "(:reason-unknown (incomplete proof-trusted))",
                "a withheld strict verdict must say why: {}",
                run.context
            );
        }
    }
}

/// The deadline arm of the same argv, pinned instead of left to machine load:
/// with its own budget already spent, a strict one-shot still publishes
/// `unsat` only with a complete certificate, and a verdict the deadline
/// withholds leaves no certificate behind and names its reason.
#[test]
#[timeout(600_000)]
fn strict_one_shot_past_its_own_deadline_keeps_the_publication_contract() {
    let mut timed_out = Vec::new();
    for id in PUBLISHED_ON_A_HOLE {
        let script = without_script_timeout(&body(id));
        let run = run_one_shot(id, &format!("(set-option :timeout 1)\n{script}"));
        if let Some(reason) = assert_publication_contract(&run) {
            if reason == "(:reason-unknown timeout)" {
                timed_out.push(id);
            }
        }
    }
    // `758d3c8d8705` needs seconds of CPU before any verdict, so a 1 ms budget
    // always ends it first; the deadline arm is never vacuous.
    assert!(
        timed_out.contains(&"758d3c8d8705"),
        "the 1 ms budget did not end 758d3c8d8705: {timed_out:?}"
    );
}

/// The same gate on the synthesized default certificate (no `--proof`), for a
/// lane the in-memory screen admits outright: `strict-native-nra-sos-bundle`,
/// whose document keeps an explicit `hole` for the native SOS replay. Each file
/// was published `unsat` under `--strict-proofs` with `unproved_steps=1` on
/// 36a5da9d7.
#[test]
#[timeout(600_000)]
fn strict_default_certificate_never_publishes_unsat_on_an_unproved_step() {
    for relative in [
        "benchmarks/smt/QF_NIA/sign_consistency.smt2",
        "benchmarks/smt/QF_LIA/system_10.smt2",
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let smt2 = dir.path().join("query.smt2");
        std::fs::copy(
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("../..")
                .join(relative),
            &smt2,
        )
        .unwrap_or_else(|e| panic!("copy {relative}: {e}"));
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--strict-proofs")
            .arg(&smt2)
            .output_timeout(QUERY_TIMEOUT)
            .expect("run ay --strict-proofs");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let context = format!("{relative}\nstdout:\n{stdout}\nstderr:\n{stderr}");
        assert!(
            output.status.success(),
            "exit {:?}: {context}",
            output.status
        );
        let written =
            std::fs::metadata(dir.path().join("query.smt2.alethe")).map_or(0, |m| m.len());
        match verdict_lines(&stdout).as_slice() {
            [v] if v == "unsat" => {
                let certificate = stderr
                    .lines()
                    .find(|l| l.contains("c ay.proof.certificate "))
                    .unwrap_or_else(|| {
                        panic!("published unsat without a certificate line: {context}")
                    });
                assert!(
                    certificate
                        .split_whitespace()
                        .any(|w| w == "unproved_steps=0"),
                    "strict published unsat on an unproved certificate: {context}"
                );
                assert!(
                    written > 0,
                    "published unsat without its certificate: {context}"
                );
            }
            [v] if v == "unknown" => {
                assert!(
                    stderr.contains("(:reason-unknown (incomplete proof-trusted))"),
                    "a withheld strict verdict must say why: {context}"
                );
                assert_eq!(
                    written, 0,
                    "a withheld verdict left a certificate behind: {context}"
                );
            }
            other => panic!("expected exactly one of unsat/unknown, got {other:?}: {context}"),
        }
    }
}
