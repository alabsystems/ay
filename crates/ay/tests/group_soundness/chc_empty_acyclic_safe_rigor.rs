// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A wrong CHC SAFE must not be published at any rigor level.
//!
//! `h3`/`h8` are UNSAFE (z3: `unsat`). Measured on 938ec0327 (MODEL_CHECKER_CONSUMER state
//! report §4-A1): acyclic BMC shared head-only clause variables across clause
//! instances and proved both SAFE; the empty-model validator re-ran BMC and
//! agreed, so the default route and `--rigor certified` printed `sat` with a
//! SAFE certificate while `--rigor strict` answered `unknown`. `h3y`/`h8m`
//! rename the head-only variable and were `unsat` everywhere.
//!
//! A correct engine answers `unsat` for `h3`/`h8`; with the engine defect
//! present the independent empty-model check answers `unknown`. Never `sat`.

use ntest::timeout;
use std::process::Command;

use super::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};
use crate::spawn::OutputTimeout;

const H3: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> true (P (+ x 1)))))
(assert (forall ((a Int) (x Int)) (=> (P a) (Q a (+ x 2)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (= c (+ a 5))) false)))
(check-sat)
";

const H8: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((n Int)) (=> true (P (* 2 n)))))
(assert (forall ((a Int) (n Int)) (=> (P a) (Q a (* 2 n)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (not (= a c))) false)))
(check-sat)
";

const H3Y: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> true (P (+ x 1)))))
(assert (forall ((a Int) (y Int)) (=> (P a) (Q a (+ y 2)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (= c (+ a 5))) false)))
(check-sat)
";

const H8M: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((n Int)) (=> true (P (* 2 n)))))
(assert (forall ((a Int) (m Int)) (=> (P a) (Q a (* 2 m)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (not (= a c))) false)))
(check-sat)
";

/// SAFE twin of `H3`: an empty-model acyclic SAFE (the certificate class the
/// §4-A1 wrong SAFE belonged to).
const H3_SAFE: &str = "(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int Int) Bool)
(assert (forall ((x Int)) (=> true (P (+ x 1)))))
(assert (forall ((a Int)) (=> (P a) (Q a (+ a 2)))))
(assert (forall ((a Int) (c Int)) (=> (and (Q a c) (= c (+ a 5))) false)))
(check-sat)
";

/// Every rigor spelling, the default included.
const LEVELS: [&[&str]; 5] = [
    &[],
    &["--rigor", "fast"],
    &["--rigor", "standard"],
    &["--rigor", "strict"],
    &["--rigor", "certified"],
];

struct Run {
    verdicts: Vec<String>,
    stdout: String,
    stderr: String,
    context: String,
}

fn run(level: &[&str], script: &str) -> Run {
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("horn.smt2");
    std::fs::write(&input, script).expect("write HORN input");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(level)
        .arg(&input)
        .output_timeout(QUERY_TIMEOUT)
        .unwrap_or_else(|e| panic!("{level:?}: run ay: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    Run {
        verdicts: verdict_lines(&stdout),
        context: format!(
            "{level:?} (exit {:?})\nscript:\n{script}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status
        ),
        stdout,
        stderr,
    }
}

#[test]
#[timeout(900_000)]
fn head_only_variable_wrong_safes_are_never_published() {
    for script in [H3, H8] {
        for level in LEVELS {
            let run = run(level, script);
            let context = &run.context;
            assert!(
                run.verdicts == ["unsat"] || run.verdicts == ["unknown"],
                "an UNSAFE problem must be `unsat` or `unknown`: {context}"
            );
            assert!(
                !run.stdout.contains("CHC Certificate: SAFE"),
                "a SAFE certificate was published for an UNSAFE problem: {context}"
            );
        }
    }
}

#[test]
#[timeout(900_000)]
fn head_only_variable_controls_stay_unsafe_at_every_rigor() {
    for script in [H3Y, H8M] {
        for level in LEVELS {
            let run = run(level, script);
            assert_eq!(run.verdicts, ["unsat"], "{}", run.context);
        }
    }
}

/// `--rigor certified` ranks above strict, so it runs strict's SAFE
/// re-discharge and UNSAFE ground check and never publishes a verdict strict
/// demotes; `--rigor standard` runs neither. (Measured on 938ec0327, before
/// this pin: certified printed the §4-A1 wrong SAFE that strict demoted.)
/// Where strict's re-checks pass, certified must still decide: a certified
/// that demotes everything fails here.
#[test]
#[timeout(600_000)]
fn certified_runs_the_strict_chc_rechecks() {
    const SAFE_LOOP: &str = "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 5)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
";
    // Printed by STEP D / STEP C whether the re-check passes or demotes.
    const UNSAFE_GATE: &str = "CHC strict trace check";
    const SAFE_GATE: &str = "CHC strict checked replay";
    for (script, verdict, gate) in [
        (SAFE_LOOP, "sat", SAFE_GATE),
        (H3_SAFE, "sat", SAFE_GATE),
        (H3Y, "unsat", UNSAFE_GATE),
    ] {
        let certified = run(&["--rigor", "certified"], script);
        assert!(
            certified.stderr.contains(gate),
            "certified decided without strict's re-check: {}",
            certified.context
        );
        assert_eq!(certified.verdicts, [verdict], "{}", certified.context);
        let standard = run(&["--rigor", "standard"], script);
        assert_eq!(standard.verdicts, [verdict], "{}", standard.context);
        assert!(
            !standard.stderr.contains(UNSAFE_GATE) && !standard.stderr.contains(SAFE_GATE),
            "a strict re-check ran at standard rigor: {}",
            standard.context
        );
    }
    // A cyclic UNSAFE whose counterexample can arrive without concrete trace
    // values (a witness-less CEGAR win), which the ground check cannot
    // evaluate. Certified still runs the check; the verdict it may keep is
    // strict's (the engine race makes two runs incomparable).
    const UNSAFE_LOOP: &str = "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
";
    let certified = run(&["--rigor", "certified"], UNSAFE_LOOP);
    assert!(
        certified.stderr.contains(UNSAFE_GATE),
        "certified decided without strict's re-check: {}",
        certified.context
    );
    assert!(
        certified.verdicts == ["unsat"] || certified.verdicts == ["unknown"],
        "{}",
        certified.context
    );
}
