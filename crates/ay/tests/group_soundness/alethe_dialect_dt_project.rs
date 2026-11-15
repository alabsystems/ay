// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The certificate line for a datatype selector over a constructor.
//!
//! REGRESSION (measured 2026-10-02 on 11b79efe7): `(assert (not (= (snd (mk
//! a b)) b)))` printed its projection as `:rule hole` in both dialects,
//! `unproved_steps=1 carcara_surface=supported`, and `--strict-proofs`
//! answered `unknown`, although Clean's vendored Carcara (4dc90e8ea) checks
//! the step as `dt_project`. The default dialect prints that rule now (and
//! `symm` after it for a value written first): `unproved_steps=0
//! trust_free=yes carcara_surface=clean-dialect`, published under
//! `--strict-proofs` and accepted by the strict round-trip self-check
//! (`--proof-self-check 2`, which reads the document in Clean's rule
//! vocabulary); pinned Carcara refuses it at `dt_project`. The pinned dialect
//! keeps the hole: `unproved_steps=1 carcara_surface=supported`, `holey`, and
//! `--strict-proofs` answers `unknown`; its strict self-check reads the
//! document in pinned Carcara's vocabulary and accepts the hole.
//!
//! The library's strict option, `(set-option :check-proofs-strict true)`,
//! agrees with `--strict-proofs` in both dialects. Measured on the dt_project
//! commit it did not: its known-wire-gap screen read the step's wire rule
//! (`hole`) whatever the dialect, and the default dialect answered `unknown
//! (incomplete proof-trusted)`, "its Alethe rendering has a known wire gap no
//! external checker accepts", for the hole-free document Clean passes.

use super::{
    assert_disclosed_and_refused_at, pinned_carcara, run, verdict_lines, Command, OutputTimeout,
    Run, QUERY_TIMEOUT,
};

/// The value on either side: Clean's `dt_project`, which pinned Carcara does
/// not implement.
const SELECTOR_PROJECTION: [&str; 2] = [
    "(set-logic QF_DT)\n(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
     (declare-const a Int)\n(declare-const b Int)\n\
     (assert (not (= (snd (mk a b)) b)))\n(check-sat)\n",
    "(set-logic QF_DT)\n(declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
     (declare-const a Int)\n(declare-const b Int)\n\
     (assert (not (= a (fst (mk a b)))))\n(check-sat)\n",
];

/// The pinned dialect's certificate, which carries its one hole.
fn pinned_run(script: &str, flags: &[&str]) -> Run {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem = dir.path().join("query.smt2");
    let proof = dir.path().join("query.alethe");
    std::fs::write(&problem, script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("-smt2")
        .arg(&problem)
        .args(["--alethe-dialect", "pinned-carcara", "--proof"])
        .arg(&proof)
        .args(["--proof-format", "alethe"])
        .args(flags)
        .output_timeout(QUERY_TIMEOUT)
        .expect("ay answers");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(verdict_lines(&stdout), ["unsat"], "{stdout}\n{stderr}");
    let certificate = stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .unwrap_or_else(|| panic!("no certificate line:\n{stderr}"))
        .to_string();
    Run {
        certificate,
        stderr,
        problem,
        proof,
        _dir: dir,
    }
}

#[test]
fn a_datatype_selector_projection_is_clean_dialect_and_the_pinned_dialect_keeps_its_hole() {
    for script in SELECTOR_PROJECTION {
        for flags in [
            &[][..],
            &["--strict-proofs"][..],
            &["--proof-self-check", "2"][..],
        ] {
            let run = run(script, flags);
            assert_disclosed_and_refused_at(&run, "dt_project");
            assert!(
                run.stderr
                    .lines()
                    .any(|line| line.starts_with("c warning: ")
                        && line.contains("Clean's dt_project rule")),
                "{flags:?}: the warning names the rule:\n{}",
                run.stderr
            );
            let proof = std::fs::read_to_string(&run.proof).expect("read the certificate");
            assert!(proof.contains(":rule dt_project)"), "{flags:?}:\n{proof}");
            assert!(!proof.contains(":rule hole"), "{flags:?}:\n{proof}");
        }

        for flags in [&[][..], &["--proof-self-check", "2"][..]] {
            let pinned = pinned_run(script, flags);
            assert!(
                pinned.certificate.contains(" unproved_steps=1 ")
                    && pinned.certificate.contains(" carcara_surface=supported "),
                "{flags:?}: {}",
                pinned.certificate
            );
            assert!(
                !pinned.stderr.contains("clean-dialect"),
                "{flags:?}: {}",
                pinned.stderr
            );
            assert!(
                !pinned.stderr.contains("self-check rejected"),
                "{flags:?}: {}",
                pinned.stderr
            );
            let proof = std::fs::read_to_string(&pinned.proof).expect("read the certificate");
            assert_eq!(
                proof.matches(":rule hole)").count(),
                1,
                "{flags:?}:\n{proof}"
            );
            assert!(!proof.contains("dt_project"), "{flags:?}:\n{proof}");
            if let Some((verdict, stderr)) = pinned_carcara(&pinned) {
                assert_eq!(verdict, "holey", "{stderr}");
            }
        }
        let pinned = pinned_run(script, &[]);
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("-smt2")
            .arg(&pinned.problem)
            .args(["--strict-proofs", "--alethe-dialect", "pinned-carcara"])
            .output_timeout(QUERY_TIMEOUT)
            .expect("ay answers");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert_eq!(
            verdict_lines(&stdout),
            ["unknown"],
            "the pinned dialect's hole withholds the strict verdict: {stdout}"
        );
    }
}

/// `(set-option :check-proofs-strict true)` publishes the projection exactly
/// where `--strict-proofs` does: in the Clean dialect, whose document is
/// hole-free, and not in the pinned one, whose document carries the hole.
#[test]
fn the_in_script_strict_option_agrees_with_the_flag_in_each_dialect() {
    for script in SELECTOR_PROJECTION {
        let strict = script.replace(
            "(set-logic QF_DT)\n",
            "(set-option :check-proofs-strict true)\n(set-logic QF_DT)\n",
        );
        let dir = tempfile::tempdir().expect("tempdir");
        let problem = dir.path().join("query.smt2");
        std::fs::write(&problem, &strict).expect("write query");
        for (dialect, expected) in [("clean", "unsat"), ("pinned-carcara", "unknown")] {
            let output = Command::new(env!("CARGO_BIN_EXE_ay"))
                .arg("-smt2")
                .arg(&problem)
                .args(["--alethe-dialect", dialect])
                .output_timeout(QUERY_TIMEOUT)
                .expect("ay answers");
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert_eq!(
                verdict_lines(&stdout),
                [expected],
                "{dialect}: {stdout}\n{stderr}\n{strict}"
            );
        }
    }
}
