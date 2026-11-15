// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--strict-proofs` keeps its promise on EVERY input route, not only where
//! a certificate file is written, and the premises a strict certificate
//! assumes are the input's own.
//!
//! Measured on the round-4 head and again on its merge with origin/main: the
//! file route withheld `unsat` on a holed certificate, while `--stdin`,
//! `--incremental` and `--no-proof F` (each with `(get-proof)` appended)
//! published `unsat` on every one of the same files and printed the holed
//! proof, and plain `--stdin` published `unsat` with no certificate at all
//! (83 of 83 single-query files the file route withheld, on the merge).

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;

use super::strict_certificate_publication::{
    body, verdict_lines, without_script_timeout, PUBLISHED_ON_A_HOLE, QUERY_TIMEOUT,
};
use crate::spawn::OutputTimeout;

/// Every way of running `--strict-proofs` on one SMT-LIB script.
///
/// The file route writes a certificate; the others publish `unsat` with no
/// certificate file, and a `(get-proof)` after `check-sat` prints the document
/// a strict consumer would receive. Measured on the round-4 head (and again on
/// the merge with origin/main), all but the file route published `unsat` for
/// scripts whose certificate carries a `hole`, and printed that `hole` under
/// `(get-proof)`.
#[derive(Clone, Copy, Debug)]
pub(super) enum StrictRoute {
    /// `ay --strict-proofs F`: the synthesized default certificate.
    File,
    /// `ay --strict-proofs --stdin` with `(get-proof)` appended.
    StdinGetProof,
    /// `ay --strict-proofs --stdin`, the script as written.
    StdinPlain,
    /// `ay --incremental --strict-proofs` with `(get-proof)` appended.
    IncrementalGetProof,
    /// `ay --strict-proofs --no-proof F` with `(get-proof)` appended.
    NoProofGetProof,
}

pub(super) const ALL_ROUTES: [StrictRoute; 5] = [
    StrictRoute::File,
    StrictRoute::StdinGetProof,
    StrictRoute::StdinPlain,
    StrictRoute::IncrementalGetProof,
    StrictRoute::NoProofGetProof,
];

pub(super) struct RouteOutcome {
    pub(super) verdicts: Vec<String>,
    /// The `(get-proof)` document, or the certificate file for `File`.
    pub(super) document: String,
    pub(super) context: String,
}

pub(super) fn run_route(route: StrictRoute, script: &str) -> RouteOutcome {
    run_route_with(route, script, StrictSpelling::CommandLine)
}

/// How strict proofs are asked for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum StrictSpelling {
    /// `--strict-proofs` on the command line.
    CommandLine,
    /// Only the script's own `(set-option :check-proofs-strict true)`: no
    /// strict flag is passed.
    InScript,
}

pub(super) fn run_route_with(
    route: StrictRoute,
    script: &str,
    spelling: StrictSpelling,
) -> RouteOutcome {
    let flag: &[&str] = match spelling {
        StrictSpelling::CommandLine => &["--strict-proofs"],
        StrictSpelling::InScript => &[],
    };
    let dir = tempfile::tempdir().expect("tempdir");
    let smt2 = dir.path().join("query.smt2");
    let with_get_proof = format!(
        "(set-option :produce-proofs true)\n{}\n(get-proof)\n",
        script.trim_end()
    );
    let output = match route {
        StrictRoute::File => {
            std::fs::write(&smt2, script).expect("write query");
            Command::new(env!("CARGO_BIN_EXE_ay"))
                .args(flag)
                .arg(&smt2)
                .output_timeout(QUERY_TIMEOUT)
        }
        StrictRoute::StdinGetProof => Command::new(env!("CARGO_BIN_EXE_ay"))
            .args(flag)
            .arg("--stdin")
            .output_timeout_with_stdin(with_get_proof.as_bytes(), QUERY_TIMEOUT),
        StrictRoute::StdinPlain => Command::new(env!("CARGO_BIN_EXE_ay"))
            .args(flag)
            .arg("--stdin")
            .output_timeout_with_stdin(script.as_bytes(), QUERY_TIMEOUT),
        StrictRoute::IncrementalGetProof => Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg("--incremental")
            .args(flag)
            .output_timeout_with_stdin(with_get_proof.as_bytes(), QUERY_TIMEOUT),
        StrictRoute::NoProofGetProof => {
            std::fs::write(&smt2, &with_get_proof).expect("write query");
            Command::new(env!("CARGO_BIN_EXE_ay"))
                .args(flag)
                .arg("--no-proof")
                .arg(&smt2)
                .output_timeout(QUERY_TIMEOUT)
        }
    }
    .unwrap_or_else(|e| panic!("{route:?}: run ay: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let document = match route {
        StrictRoute::File => {
            std::fs::read_to_string(dir.path().join("query.smt2.alethe")).unwrap_or_default()
        }
        _ => stdout.clone(),
    };
    RouteOutcome {
        verdicts: verdict_lines(&stdout),
        document,
        context: format!("{route:?} ({spelling:?})\nstdout:\n{stdout}\nstderr:\n{stderr}"),
    }
}

pub(super) fn unproved_rules(document: &str) -> usize {
    document
        .lines()
        .filter(|l| l.contains(":rule hole") || l.contains(":rule trust"))
        .count()
}

/// A script whose certificate the printer holes: the parameterized
/// `define-fun` `eq2` is applied under its authored name, and carcara has no
/// beta reduction to unfold `(eq2 a b)` into `(= a b)`, so the step through it
/// prints as `:rule hole`. AY's own checker validated that step
/// (`unsat_admission=strict-proof`).
///
/// This was a nullary alias, `(define-fun eqab () Bool (= a b))`, until
/// 32eace1dc: carcara reads a nullary definition as a constant whose defining
/// equality is an original premise, so the printer now assumes that equality
/// and the certificate is complete (carcara `valid`).
pub(super) const HOLED_BY_THE_PRINTER: &str = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(define-fun eq2 ((x U) (y U)) Bool (= x y))
(assert (eq2 a b))
(assert (= b c))
(assert (distinct a c))
(check-sat)
";

/// The same refutation with the alias inlined: its certificate is complete,
/// so every route must still publish `unsat` (the gate is not a blanket
/// refusal).
pub(super) const COMPLETE_CERTIFICATE: &str = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(assert (= a b))
(assert (= b c))
(assert (distinct a c))
(check-sat)
";

/// No route publishes `unsat` for a script whose certificate carries an
/// unproved step, and no `(get-proof)` prints that certificate.
#[test]
#[timeout(600_000)]
fn no_strict_route_publishes_unsat_on_a_holed_certificate() {
    for route in ALL_ROUTES {
        let outcome = run_route(route, HOLED_BY_THE_PRINTER);
        let context = &outcome.context;
        assert_eq!(
            outcome.verdicts,
            ["unknown"],
            "strict published a verdict other than unknown: {context}"
        );
        assert!(
            context.contains("(incomplete proof-trusted)"),
            "the withheld verdict must say why: {context}"
        );
        assert!(
            context.contains("c strict-proofs: strict proof mode rejected UNSAT because")
                || context.contains("c ay.proof.artifact-refused"),
            "the refusal must be named: {context}"
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
    }
}

/// The positive control: a complete certificate is published on every route,
/// and the printed document is the one the gate read.
#[test]
#[timeout(600_000)]
fn every_strict_route_publishes_unsat_on_a_complete_certificate() {
    for route in ALL_ROUTES {
        let outcome = run_route(route, COMPLETE_CERTIFICATE);
        let context = &outcome.context;
        assert_eq!(outcome.verdicts, ["unsat"], "{context}");
        if matches!(route, StrictRoute::StdinPlain) {
            continue;
        }
        assert!(
            outcome.document.contains("(assume t0 (= a b))"),
            "the published proof must assume the input's own premise: {context}"
        );
        assert_eq!(unproved_rules(&outcome.document), 0, "{context}");
        assert!(outcome.document.contains("(cl)"), "{context}");
    }
}

/// The four external-codegen corpus queries that were published on a hole, through
/// every route that has no certificate file.
#[test]
#[timeout(1_200_000)]
fn strict_routes_without_a_certificate_file_never_publish_unsat_on_a_hole() {
    for id in PUBLISHED_ON_A_HOLE {
        let script = without_script_timeout(&body(id));
        assert!(!script.contains(":timeout"), "{id}: {script}");
        for route in [
            StrictRoute::StdinGetProof,
            StrictRoute::IncrementalGetProof,
            StrictRoute::NoProofGetProof,
        ] {
            let outcome = run_route(route, &script);
            let context = format!("{id}: {}", outcome.context);
            match outcome.verdicts.as_slice() {
                [v] if v == "unsat" => {
                    assert!(
                        outcome.document.contains("(cl)"),
                        "unsat published without its proof: {context}"
                    );
                    assert_eq!(
                        unproved_rules(&outcome.document),
                        0,
                        "strict published unsat with a holed proof: {context}"
                    );
                }
                [v] if v == "unknown" => {
                    assert!(
                        context.contains("(incomplete proof-"),
                        "a withheld strict verdict must say why: {context}"
                    );
                    assert!(
                        !outcome.document.contains("(assume "),
                        "a withheld verdict still published a proof: {context}"
                    );
                }
                other => panic!("expected exactly one of unsat/unknown, got {other:?}: {context}"),
            }
        }
    }
}

/// Top-level `(assume ID TERM)` leaves of a document (not `anchor`-local
/// hypotheses), whitespace-collapsed.
pub(super) fn premise_assumes(document: &str) -> Vec<String> {
    let mut anchors: Vec<String> = Vec::new();
    let mut assumes = Vec::new();
    for line in document.lines().map(str::trim) {
        if let Some(rest) = line.strip_prefix("(anchor :step ") {
            anchors.push(rest.split_whitespace().next().unwrap_or("").to_string());
        } else if let Some(rest) = line.strip_prefix("(step ") {
            let id = rest.split_whitespace().next().unwrap_or("");
            if anchors.last().is_some_and(|open| open == id) {
                anchors.pop();
            }
        } else if let Some(rest) = line.strip_prefix("(assume ") {
            if anchors.is_empty() {
                let term = rest
                    .split_once(' ')
                    .map_or("", |(_, term)| term)
                    .trim()
                    .strip_suffix(')')
                    .unwrap_or("");
                assumes.push(collapse(term));
            }
        }
    }
    assumes
}

pub(super) fn collapse(text: &str) -> String {
    text.split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
        .replace("( ", "(")
        .replace(" )", ")")
}

/// The first s-expression (or atom) of `text`.
fn first_sexp(text: &str) -> &str {
    let text = text.trim_start();
    if !text.starts_with('(') {
        return text.split_whitespace().next().unwrap_or("");
    }
    let mut depth = 0usize;
    for (offset, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &text[..=offset];
                }
            }
            _ => {}
        }
    }
    text
}

/// The input's `(assert TERM)` texts, whitespace-collapsed. Every assertion in
/// the fixtures below sits on one logical s-expression per `assert`.
pub(super) fn authored_assertions(script: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = script;
    while let Some(start) = rest.find("(assert ") {
        let text = &rest[start..];
        let mut depth = 0usize;
        let mut end = text.len();
        for (offset, c) in text.char_indices() {
            match c {
                '(' => depth += 1,
                ')' => {
                    depth -= 1;
                    if depth == 0 {
                        end = offset + 1;
                        break;
                    }
                }
                _ => {}
            }
        }
        let inner = collapse(&text["(assert ".len()..end - 1]);
        // `(! TERM :named n)` asserts TERM; a certificate may assume either.
        if let Some(annotated) = inner.strip_prefix("(! ") {
            out.push(collapse(first_sexp(annotated)));
        }
        out.push(inner);
        rest = &text[end..];
    }
    out
}

/// A certificate whose premise `assume` is a normalized form of the input's
/// assertion — a `define-fun` expanded, or a bound variable renamed — is not
/// published as a strict `unsat`, and outside strict mode the disclosure says
/// so.
///
/// Measured on the round-4 head and on its merge with origin/main: these files
/// were published under `--strict-proofs` with `foreign_assumes=no
/// ay_self_checkable=yes`, and the external checker (`clean cert
/// verify-external`) rejected each at its first `assume`: "could not match term
/// to any of the original problem premises". The term-level detector cannot
/// see it: it compares the terms AY stores, which are already normalized.
#[test]
#[timeout(600_000)]
fn a_certificate_that_assumes_a_rewritten_premise_is_not_a_strict_certificate() {
    // (fixture, what a strict refusal of it must name)
    for (relative, refusal) in [
        // `unsat_memory_aliasing.smt2` left this list once its certificate read
        // `mem1` through its definition premise (`strict_definition_premise.rs`),
        // `strict_folded_conjunct_rewritten_premise.smt2` once its
        // certificate assumed the authored conjunction and projected the folded
        // conjunct with `and_pos` (`strict_folded_premise.rs`), and
        // `known_bugs/bv_ite_shared_vars_minimal.smt2` once the definition
        // schema read its `(ite m1 ..)` root as a `cong` head
        // (`strict_definition_premise/ite_guard.rs`).
        //
        // Under `:produce-unsat-cores` the printed leaf renames the authored
        // binder `i_2`; named-core tracking had put the renamed term among the
        // solver's own assumption literals, which the comparison used to
        // accept as a premise. Its document used to carry a `hole` as well
        // (the `qnt_neg_exists` dual), which the strict refusal named first;
        // that dual now prints as a checked `connective_def` derivation, so the
        // refusal names the renamed premise itself.
        (
            "crates/ay-dpll/tests/fixtures/deductive_checks_quantifiers_not_exists_named_core.smt2",
            "which is not an assertion of the input as written",
        ),
    ] {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("../..")
            .join(relative);
        let script = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
        let authored = authored_assertions(&script);
        assert!(!authored.is_empty(), "{relative}: no assertions parsed");

        // Strict: every route either publishes a certificate that assumes only
        // the input's own assertions, or withholds the verdict and says why.
        for route in ALL_ROUTES {
            let outcome = run_route(route, &script);
            let context = format!("{relative}: {}", outcome.context);
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
                            "strict published a certificate assuming `{assume}`, which the input does not assert: {context}"
                        );
                    }
                }
                [v] if v == "unknown" => {
                    assert!(
                        context.contains(refusal),
                        "the refusal must name `{refusal}`: {context}"
                    );
                    assert!(!outcome.document.contains("(assume "), "{context}");
                }
                other => panic!("expected exactly one of unsat/unknown, got {other:?}: {context}"),
            }
        }

        // Default mode publishes the verdict and its certificate, and the
        // certificate line must not call the document clean.
        let dir = tempfile::tempdir().expect("tempdir");
        let smt2 = dir.path().join("query.smt2");
        std::fs::write(&smt2, &script).expect("write query");
        let output = Command::new(env!("CARGO_BIN_EXE_ay"))
            .arg(&smt2)
            .output_timeout(QUERY_TIMEOUT)
            .expect("run ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let context = format!("{relative}\nstdout:\n{stdout}\nstderr:\n{stderr}");
        assert_eq!(verdict_lines(&stdout), ["unsat"], "{context}");
        let document =
            std::fs::read_to_string(dir.path().join("query.smt2.alethe")).unwrap_or_default();
        let foreign = premise_assumes(&document)
            .into_iter()
            .any(|assume| !authored.contains(&assume));
        let line = stderr
            .lines()
            .find(|l| l.contains("c ay.proof.certificate "))
            .unwrap_or_else(|| panic!("no certificate line: {context}"));
        if foreign {
            for field in ["foreign_assumes=yes", "ay_self_checkable=no"] {
                assert!(
                    line.split_whitespace().any(|w| w == field),
                    "the document assumes a rewritten premise, so the line must say {field}: {context}"
                );
            }
        } else {
            assert!(
                line.split_whitespace().any(|w| w == "foreign_assumes=no"),
                "{context}"
            );
        }
    }
}
