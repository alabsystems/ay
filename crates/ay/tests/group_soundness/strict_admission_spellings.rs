// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The other spellings of a strict request and of a premise: the in-script
//! `(set-option :check-proofs-strict true)`, and `check-sat-assuming`
//! literals, which a certificate must assume exactly as the caller wrote them.

use ntest::timeout;
use std::process::Command;

use super::strict_admission_routes::{
    authored_assertions, collapse, premise_assumes, run_route, run_route_with, unproved_rules,
    StrictRoute, StrictSpelling, ALL_ROUTES, COMPLETE_CERTIFICATE, HOLED_BY_THE_PRINTER,
};
use super::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};
use crate::spawn::OutputTimeout;

/// `(set-option :check-proofs-strict true)` is the same promise as
/// `--strict-proofs`, on every route: no `unsat` on a holed certificate, and
/// `unsat` with its complete certificate wherever a proof is requested.
///
/// Measured on the round-5 head: with the option set in the script and no
/// strict flag, every route published `unsat` for `HOLED_BY_THE_PRINTER`
/// (`unsat_admission=strict-proof` on the file route), and `(get-proof)`
/// printed its `:rule hole` step. The executor's funnel for the option reads
/// only the in-memory derivation, which has no hole; the printer makes one.
#[test]
#[timeout(600_000)]
fn the_in_script_strict_option_keeps_the_strict_promise_on_every_route() {
    let holed = format!("(set-option :check-proofs-strict true)\n{HOLED_BY_THE_PRINTER}");
    let complete = format!("(set-option :check-proofs-strict true)\n{COMPLETE_CERTIFICATE}");
    for route in ALL_ROUTES {
        let outcome = run_route_with(route, &holed, StrictSpelling::InScript);
        let context = &outcome.context;
        assert_eq!(
            outcome.verdicts,
            ["unknown"],
            "the in-script strict option published a verdict other than unknown: {context}"
        );
        assert!(
            context.contains("(incomplete proof-"),
            "the withheld verdict must say why: {context}"
        );
        assert_eq!(
            unproved_rules(&outcome.document),
            0,
            "a withheld verdict still printed its holed proof: {context}"
        );
        assert!(
            !outcome.document.contains("(assume "),
            "a withheld verdict still published a proof: {context}"
        );

        let outcome = run_route_with(route, &complete, StrictSpelling::InScript);
        let context = &outcome.context;
        if matches!(route, StrictRoute::StdinPlain) {
            // Nothing asks for a proof here: no `:produce-proofs`, no proof
            // file, no strict flag (which would request one). There is no
            // derivation to check, so strict withholds the verdict.
            assert_eq!(outcome.verdicts, ["unknown"], "{context}");
            assert!(
                context.contains("(incomplete proof-unavailable)")
                    && context.contains("no derivation was retained"),
                "{context}"
            );
            continue;
        }
        assert_eq!(outcome.verdicts, ["unsat"], "{context}");
        assert!(
            outcome.document.contains("(assume t0 (= a b))"),
            "the published proof must assume the input's own premise: {context}"
        );
        assert_eq!(unproved_rules(&outcome.document), 0, "{context}");
        assert!(outcome.document.contains("(cl)"), "{context}");
    }
}

/// The problem of the `check-sat-assuming` fixtures below: `a = b` is refuted
/// by the two assertions, so every literal meaning `a = b` makes it `unsat`.
pub(super) const ASSUMING_PREFIX: &str = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (= b c))
(assert (distinct a c))
";

/// A certificate that assumes a REWRITTEN `check-sat-assuming` literal is not
/// published as a strict `unsat`; outside strict mode its certificate line
/// says `foreign_assumes=yes`.
///
/// Measured on the round-5 head: for each literal below, every strict route
/// published `unsat` with `foreign_assumes=no`, on a certificate that assumes
/// `(= a b)`. `clean cert verify-external` (clean main e70251d63) rejected it:
/// "checking failed on step 't2' with rule 'assume': assumption not present in
/// the problem". The comparison read the caller's literals from their
/// ELABORATED terms, which are exactly the rewritten form.
#[test]
#[timeout(600_000)]
fn a_certificate_that_assumes_a_rewritten_assumption_literal_is_not_a_strict_certificate() {
    for literal in [
        "(not (distinct a b))",
        "(let ((x (= a b))) x)",
        "(and (= a b) true)",
    ] {
        let script = format!("{ASSUMING_PREFIX}(check-sat-assuming ({literal}))\n");
        let mut authored = authored_assertions(&script);
        authored.push(collapse(literal));

        for route in ALL_ROUTES {
            let outcome = run_route(route, &script);
            let context = format!("{literal}: {}", outcome.context);
            match outcome.verdicts.as_slice() {
                [v] if v == "unsat" => {
                    if matches!(route, StrictRoute::StdinPlain) {
                        panic!("strict published unsat with no certificate to check: {context}");
                    }
                    let assumes = premise_assumes(&outcome.document);
                    assert!(!assumes.is_empty(), "{context}");
                    for assume in assumes {
                        assert!(
                            authored.contains(&assume),
                            "strict published a certificate assuming `{assume}`, which the input does not state: {context}"
                        );
                    }
                }
                [v] if v == "unknown" => {
                    assert!(
                        context.contains("which is not an assertion of the input as written"),
                        "the refusal must name the foreign premise: {context}"
                    );
                    assert!(!outcome.document.contains("(assume "), "{context}");
                }
                other => panic!("expected exactly one of unsat/unknown, got {other:?}: {context}"),
            }
        }

        // Default mode: the verdict and its certificate are published, and the
        // certificate line agrees with what the document assumes. The fixture
        // is only a regression test while the document really does assume the
        // rewritten form, so that is asserted too.
        let dir = tempfile::tempdir().expect("tempdir");
        let smt2 = dir.path().join("query.smt2");
        std::fs::write(&smt2, &script).expect("write query");
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg(&smt2)
            .output_timeout(QUERY_TIMEOUT)
            .expect("run ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let context = format!("{literal}\nstdout:\n{stdout}\nstderr:\n{stderr}");
        assert_eq!(verdict_lines(&stdout), ["unsat"], "{context}");
        let document =
            std::fs::read_to_string(dir.path().join("query.smt2.alethe")).unwrap_or_default();
        let assumes = premise_assumes(&document);
        assert!(
            assumes.iter().any(|assume| !authored.contains(assume)),
            "the fixture no longer assumes a rewritten literal ({assumes:?}), so it pins nothing: {context}"
        );
        let line = stderr
            .lines()
            .find(|l| l.contains("c ay.proof.certificate "))
            .unwrap_or_else(|| panic!("no certificate line: {context}"));
        for field in ["foreign_assumes=yes", "ay_self_checkable=no"] {
            assert!(
                line.split_whitespace().any(|w| w == field),
                "the document assumes a rewritten literal, so the line must say {field}: {context}"
            );
        }
    }
}

/// The positive control for the literal comparison: a literal the certificate
/// assumes exactly as written (with or without its `!` annotation) is still
/// published under strict on every route that prints a document.
#[test]
#[timeout(600_000)]
fn a_certificate_that_assumes_an_assumption_literal_as_written_is_a_strict_certificate() {
    for literal in ["(= a b)", "(! (= a b) :named h)"] {
        let script = format!("{ASSUMING_PREFIX}(check-sat-assuming ({literal}))\n");
        for route in ALL_ROUTES {
            let outcome = run_route(route, &script);
            let context = format!("{literal}: {}", outcome.context);
            assert_eq!(outcome.verdicts, ["unsat"], "{context}");
            if matches!(route, StrictRoute::StdinPlain) {
                continue;
            }
            assert!(
                premise_assumes(&outcome.document).contains(&"(= a b)".to_string()),
                "{context}"
            );
            assert_eq!(unproved_rules(&outcome.document), 0, "{context}");
        }
    }
}
