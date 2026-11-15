// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `:named` labels used as terms, the twins of the nullary `define-fun`s in
//! `nullary_macro_assertions.rs`.
//!
//! A label binds a nullary definition in the frontend, but pinned carcara
//! 1.1.0 reads it unlike a `define-fun`: it expands the label wherever it is
//! used, in the problem and in the proof, and holds no `(= NAME BODY)`
//! premise for it. While labels had `define-fun` proof authority,
//! `(assert (! (< x 3) :named a))` `(assert (not a))` published
//! `(assume t1.n.c0 (= a (< x 3)))`, which carcara reads as
//! `(= (< x 3) (< x 3))` and rejects ("could not match term to any of the
//! original problem premises"), in a strict certificate stamped
//! `trust_free=yes`. MEASURED on the CLI with that authority: the `not`, BV
//! `not`, `and` and nested-label shapes below published carcara-`invalid`
//! documents under the default admission and under `--strict-proofs`.
//!
//! Every shape is UNSAT (z3 4.16.0). None may answer `sat`, no document may
//! assume a label's equation, a strict `unsat` needs a carcara-`valid`
//! certificate, and a default document may be holey but never `invalid`.
//! The `define-fun` twin keeps its definition-premise bridge.

use super::{
    carcara_verdict_without_allowances, parse, require_carcara_or_skip, CarcaraVerdict, Executor,
};
use ntest::timeout;

/// Declarations and assertions of each UNSAT shape that uses a label as a term.
const LABEL_USES: &[(&str, &str)] = &[
    (
        "label_not",
        "(declare-const x Int)\n(assert (! (< x 3) :named a))\n(assert (not a))",
    ),
    (
        "label_not_or",
        "(declare-const x Int)\n(declare-const p Bool)\n\
         (assert (! (or p (< x 3)) :named a))\n(assert (not a))",
    ),
    (
        "label_not_bv",
        "(declare-const x (_ BitVec 4))\n(assert (! (bvult x #x3) :named lo))\n(assert (not lo))",
    ),
    (
        "label_in_and",
        "(declare-const x Int)\n(assert (! (< x 3) :named a))\n(assert (and a (> x 5)))",
    ),
    (
        "label_nested",
        "(declare-const x Int)\n(assert (! (and (! (< x 3) :named a) (> x 0)) :named b))\n\
         (assert (not a))",
    ),
    (
        "label_bare_row",
        "(declare-const x Int)\n(declare-const p Bool)\n\
         (assert (! (and p (< x 3)) :named a))\n(assert a)\n(assert (> x 5))",
    ),
    (
        "label_implication",
        "(declare-const x Int)\n(declare-const y Int)\n(assert (! (= x y) :named e))\n\
         (assert (=> e (> x y)))",
    ),
    (
        "label_bare_bv",
        "(declare-const x (_ BitVec 8))\n(assert (! (bvslt x #x00) :named neg))\n\
         (assert neg)\n(assert (bvsge x #x00))",
    ),
];

/// The problem as carcara reads it.
fn problem_text(problem: &str) -> String {
    format!("(set-logic ALL)\n{problem}\n(check-sat)\n")
}

fn script(problem: &str, strict: bool) -> String {
    let strict = if strict {
        "(set-option :check-proofs-strict true)\n"
    } else {
        ""
    };
    format!(
        "(set-option :produce-proofs true)\n{strict}{}",
        problem_text(problem)
    )
}

/// How the commands reach the executor.
#[derive(Clone, Copy, Debug)]
enum Route {
    /// `execute_all`, the generic library boundary.
    Generic,
    /// One `execute_authored` per command, as `crates/ay/src/run.rs` drives a
    /// script: the route the CLI measurement above published on.
    Authored,
}

fn run(exec: &mut Executor, text: &str, route: Route, label: &str) -> Vec<String> {
    let commands = parse(text).expect("parse");
    match route {
        Route::Generic => exec
            .execute_all(&commands)
            .unwrap_or_else(|err| panic!("{label}: execute: {err:?}")),
        Route::Authored => commands
            .iter()
            .filter_map(|command| {
                exec.execute_authored(command)
                    .unwrap_or_else(|err| panic!("{label}: execute: {err:?}"))
            })
            .collect(),
    }
}

/// The verdict, and the Alethe document `(get-proof)` returns after `unsat`
/// (`None` when the proof is refused or unavailable).
fn solve(problem: &str, strict: bool, route: Route, label: &str) -> (String, Option<String>) {
    let mut exec = Executor::new();
    let outputs = run(&mut exec, &script(problem, strict), route, label);
    let verdict = outputs.last().cloned().unwrap_or_default();
    if verdict != "unsat" {
        return (verdict, None);
    }
    let proof = exec
        .execute_all(&parse("(get-proof)").expect("parse get-proof"))
        .ok()
        .and_then(|outputs| outputs.last().cloned())
        .filter(|proof| proof.contains("(assume "));
    (verdict, proof)
}

/// The names the problem's `:named` labels bind.
fn label_names(problem: &str) -> Vec<&str> {
    problem
        .split(":named ")
        .skip(1)
        .filter_map(|rest| rest.split(|c: char| c == ')' || c.is_whitespace()).next())
        .collect()
}

/// Top-level `assume` terms of `proof`, whitespace-collapsed.
fn assumes(proof: &str) -> Vec<String> {
    proof
        .lines()
        .filter_map(|line| line.trim().strip_prefix("(assume "))
        .filter_map(|rest| rest.split_once(' '))
        .filter_map(|(_, term)| term.trim_end().strip_suffix(')'))
        .map(|term| term.split_whitespace().collect::<Vec<_>>().join(" "))
        .collect()
}

#[test]
#[timeout(600_000)]
fn a_label_used_as_a_term_never_publishes_a_definition_premise() {
    let carcara = require_carcara_or_skip();
    for &(name, problem) in LABEL_USES {
        let labels = label_names(problem);
        assert!(!labels.is_empty(), "{name}: the shape names a label");
        for (strict, route) in [false, true]
            .into_iter()
            .flat_map(|strict| [Route::Generic, Route::Authored].map(|route| (strict, route)))
        {
            let mode = if strict { "strict" } else { "default" };
            let label = format!("{name}_{route:?}_{mode}");
            let (verdict, proof) = solve(problem, strict, route, &label);
            assert!(
                verdict == "unsat" || verdict == "unknown",
                "{label}: z3 answers unsat; got {verdict:?}"
            );
            let Some(proof) = proof else {
                continue;
            };
            for assume in assumes(&proof) {
                for label_name in &labels {
                    assert!(
                        !(assume.starts_with(&format!("(= {label_name} "))
                            || (assume.starts_with("(= ")
                                && assume.ends_with(&format!(" {label_name})")))),
                        "{label}: `{assume}` is no premise carcara holds for the label \
                         `{label_name}`:\n{proof}"
                    );
                }
            }
            if let Some(carcara) = &carcara {
                let checked = carcara_verdict_without_allowances(
                    carcara,
                    &label,
                    &problem_text(problem),
                    &proof,
                );
                if strict {
                    assert_eq!(
                        checked,
                        CarcaraVerdict::Valid,
                        "{label}: a strict unsat needs a certificate carcara re-derives:\n{proof}"
                    );
                } else {
                    assert_ne!(
                        checked,
                        CarcaraVerdict::Invalid,
                        "{label}: a published document carcara rejects:\n{proof}"
                    );
                }
            }
        }
    }
}

#[test]
#[timeout(120_000)]
fn the_define_fun_twin_keeps_its_definition_premise() {
    let problem =
        "(declare-const x Int)\n(define-fun a () Bool (< x 3))\n(assert a)\n(assert (not a))";
    let carcara = require_carcara_or_skip();
    for (strict, route) in [false, true]
        .into_iter()
        .flat_map(|strict| [Route::Generic, Route::Authored].map(|route| (strict, route)))
    {
        let mode = if strict { "strict" } else { "default" };
        let label = format!("define_fun_twin_{route:?}_{mode}");
        let (verdict, proof) = solve(problem, strict, route, &label);
        assert_eq!(verdict, "unsat", "{label}");
        let proof = proof.unwrap_or_else(|| panic!("{label}: the bridged document is published"));
        assert!(
            assumes(&proof)
                .iter()
                .any(|assume| assume == "(= a (< x 3))"),
            "{label}: a `define-fun` reads through its definition premise:\n{proof}"
        );
        if let Some(carcara) = &carcara {
            assert_eq!(
                carcara_verdict_without_allowances(carcara, &label, &problem_text(problem), &proof),
                CarcaraVerdict::Valid,
                "{label}:\n{proof}"
            );
        }
    }
}
