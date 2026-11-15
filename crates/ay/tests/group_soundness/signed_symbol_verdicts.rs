// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An UNQUOTED `-N` is the number in every scope, as z3 reads it; only the
//! quoted `|-N|` names a symbol of that spelling.
//!
//! REGRESSION (measured 2026-10-02 against z3 5.1.0, cvc5 1.4.1 and pinned
//! Carcara 1.1.0 git 9a352ee): AY read a bare `-N` as whatever declared,
//! defined or bound `|-N|` was in scope, and answered the OPPOSITE of z3 on
//! each problem below (or, for a24, refused the bare `-1` as "requires
//! arguments"). Each expected verdict is z3 5.1.0's.

use ntest::timeout;
use std::process::Command;

use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};

const SIGNED_SYMBOL_PROBES: [(&str, &str, &str); 6] = [
    (
        "p3: a let named |-1| leaves the bare -1 a number",
        "unsat",
        "(set-logic QF_LIA)
(declare-const x Int)
(assert (let ((|-1| (+ x 1))) (and (> |-1| 4) (< x -1))))
(check-sat)
",
    ),
    (
        "p7: a forall binder named |-3| leaves the bare -3 a number",
        "unsat",
        "(set-logic LIA)
(declare-const x Int)
(assert (forall ((|-3| Int)) (> (+ |-3| x) -3)))
(check-sat)
",
    ),
    (
        "a01: a declared |-2| does not capture the bare -2",
        "sat",
        "(set-logic QF_LIA)
(declare-const |-2| Int)
(declare-const x Int)
(assert (= |-2| 5))
(assert (= x -2))
(assert (< x 0))
(check-sat)
",
    ),
    (
        "a13: (- -2) negates the number, not the declared |-2|",
        "sat",
        "(set-logic QF_LIA)
(declare-const |-2| Int)
(declare-const x Int)
(assert (= |-2| 3))
(assert (= x (- -2)))
(assert (> x 0))
(check-sat)
",
    ),
    (
        "a15: a define-fun parameter named |-1| leaves the bare -1 a number",
        "sat",
        "(set-logic QF_LIA)
(define-fun f ((|-1| Int)) Int (+ |-1| -1))
(assert (not (= (f 3) 6)))
(check-sat)
",
    ),
    (
        "a24: a function named |-1| leaves the bare -1 a number",
        "unsat",
        "(set-logic QF_UFLIA)
(declare-fun |-1| (Int) Int)
(declare-const x Int)
(assert (= (|-1| x) -1))
(assert (= x -1))
(assert (= (|-1| -1) 2))
(check-sat)
",
    ),
];

fn verdicts(script: &str, flags: &[&str]) -> (Vec<String>, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem = dir.path().join("query.smt2");
    std::fs::write(&problem, script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(flags)
        .arg(&problem)
        .output_timeout(QUERY_TIMEOUT)
        .expect("ay answers");
    (
        verdict_lines(&String::from_utf8_lossy(&output.stdout)),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

#[test]
#[timeout(300_000)]
fn a_bare_negative_number_is_never_a_symbol_in_scope() {
    for (label, expected, script) in SIGNED_SYMBOL_PROBES {
        for flags in [&[][..], &["--z3-mode"][..]] {
            let (verdicts, stderr) = verdicts(script, flags);
            assert!(
                verdicts == [expected] || verdicts == ["unknown"],
                "{label} {flags:?}: z3 answers {expected}, AY {verdicts:?}\n{stderr}"
            );
        }
    }
}
