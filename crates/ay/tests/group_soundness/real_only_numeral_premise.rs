// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! In a logic with reals and no integers, pinned Carcara reads the problem's
//! numerals as `Real`s but a certificate's bare numerals as `Int`s. It matches
//! two constants by value, but a `let` variable bound to a numeral term AY kept
//! `Int`-sorted has a different sort on the two sides, so that `assume` is not
//! the premise Carcara parsed and it reports the certificate *invalid* there.
//! The certificate line must not call such a premise verbatim.
//!
//! Measured on the D7 list (2026-10-08): `QF_LRA/.../Carpark2-ausgabe-1.smt2`
//! printed `foreign_assumes=no` and the prediction "holey"; pinned Carcara
//! 1.1.0 answered `invalid` ("could not match term to any of the original
//! problem premises") at the `assume` that printed `(ite ?v_11 4 ...)`.

use ntest::timeout;
use std::process::Command;

use super::strict_admission_routes::premise_assumes;
use super::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};
use crate::spawn::OutputTimeout;

/// `v` is compared only with numerals, so AY keeps it `Int`-sorted and prints
/// `4` and `0`; pinned Carcara reads the problem's `v` as a `Real`.
const REAL_ONLY_INT_NUMERAL: &str = "(set-logic QF_LRA)
(declare-fun x () Real)
(declare-fun b () Bool)
(assert (let ((v (ite b 4 0))) (and b (= x (ite (= v 4) 20 1)) (< x 10))))
(check-sat)
";

/// The `let` binding the fixture exists for, as AY prints it.
const INT_LET_BINDING: &str = "(let ((v (ite b 4 0)))";

#[test]
#[timeout(600_000)]
fn an_int_numeral_in_a_real_only_premise_is_not_called_verbatim() {
    let dir = tempfile::tempdir().expect("tempdir");
    let smt2 = dir.path().join("query.smt2");
    std::fs::write(&smt2, REAL_ONLY_INT_NUMERAL).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg(&smt2)
        .output_timeout(QUERY_TIMEOUT)
        .expect("run ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let context = format!("stdout:\n{stdout}\nstderr:\n{stderr}");
    assert_eq!(verdict_lines(&stdout), ["unsat"], "{context}");
    let document =
        std::fs::read_to_string(dir.path().join("query.smt2.alethe")).unwrap_or_default();
    let assumes = premise_assumes(&document);
    assert!(
        assumes.iter().any(|assume| assume.starts_with(INT_LET_BINDING)),
        "the fixture no longer binds an Int numeral term in a premise `let` ({assumes:?}), so it pins nothing: {context}"
    );
    let line = stderr
        .lines()
        .find(|l| l.contains("c ay.proof.certificate "))
        .unwrap_or_else(|| panic!("no certificate line: {context}"));
    for field in [
        "foreign_assumes=yes",
        "ay_self_checkable=no",
        "trust_free=no",
    ] {
        assert!(
            line.split_whitespace().any(|w| w == field),
            "pinned Carcara cannot match that premise, so the line must say {field}: {context}"
        );
    }
    assert!(
        stderr.contains("reads the `let` variable `v` as a Real"),
        "the warning must name the binder Carcara reads as a Real: {context}"
    );
}
