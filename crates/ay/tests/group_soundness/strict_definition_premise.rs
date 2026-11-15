// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A nullary `define-fun`'s own equation is a premise a strict certificate may
//! assume; the expanded body substituted into an assertion never is.
//!
//! Pinned carcara 1.1.0, run without `--apply-function-defs`, reads
//! `(define-fun NAME () SORT BODY)` as a declaration of NAME plus the premise
//! `(= NAME BODY)`. `unsat_memory_aliasing.smt2` asserts
//! `(not (= (select mem1 #x..0100) #xAA))` over the nullary array macro `mem1`.
//! Until the printer bridged a negated macro root through that premise, its
//! certificate assumed the expanded assertion and `--strict-proofs` withheld
//! `unsat` (it was a fixture of
//! `a_certificate_that_assumes_a_rewritten_premise_is_not_a_strict_certificate`).
//! MEASURED since: the certificate assumes the assertion as written plus
//! `(= mem1 (store mem #x0000000000000100 #xAA))`, carcara `valid`.

use super::strict_admission_routes::{
    authored_assertions, collapse, premise_assumes, run_route, StrictRoute,
};
use ntest::timeout;
use std::path::PathBuf;

#[path = "strict_definition_premise/ite_guard.rs"]
mod ite_guard;
#[path = "strict_definition_premise/shared_body.rs"]
mod shared_body;

/// The first s-expression (or atom) of `text`, after leading whitespace. An
/// atom ends at whitespace or at the `)` closing its enclosing form, so the
/// atom body of `(define-fun k () (_ BitVec 4) #x3)` is `#x3`.
fn first_sexp(text: &str) -> &str {
    let text = text.trim_start();
    if !text.starts_with('(') {
        let end = text
            .find(|c: char| c.is_whitespace() || c == ')')
            .unwrap_or(text.len());
        return &text[..end];
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

/// `(= NAME BODY)`, whitespace-collapsed, for every nullary
/// `(define-fun NAME () SORT BODY)` of the input.
fn nullary_definition_premises(script: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut rest = script;
    while let Some(start) = rest.find("(define-fun ") {
        let text = rest[start + "(define-fun ".len()..].trim_start();
        let name = first_sexp(text);
        let after_name = text[name.len()..].trim_start();
        let params = first_sexp(after_name);
        let after_params = after_name[params.len()..].trim_start();
        let sort = first_sexp(after_params);
        let body = first_sexp(&after_params[sort.len()..]);
        if collapse(params) == "()" {
            out.push(collapse(&format!("(= {name} {body})")));
        }
        rest = after_name;
    }
    out
}

#[test]
#[timeout(600_000)]
fn a_nullary_definition_premise_is_a_strict_premise() {
    let relative = "benchmarks/conformance/QF_ABV/unsat_memory_aliasing.smt2";
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(relative);
    let script =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    let authored = authored_assertions(&script);
    let definitions = nullary_definition_premises(&script);
    assert_eq!(
        definitions,
        ["(= mem1 (store mem #x0000000000000100 #xAA))"],
        "{relative}"
    );

    let outcome = run_route(StrictRoute::File, &script);
    let context = format!("{relative}: {}", outcome.context);
    assert_eq!(outcome.verdicts, ["unsat"], "{context}");
    let assumes = premise_assumes(&outcome.document);
    for assume in &assumes {
        assert!(
            authored.contains(assume) || definitions.contains(assume),
            "strict published a certificate assuming `{assume}`, neither an assertion nor a \
             nullary definition's equation: {context}"
        );
    }
    assert!(
        assumes.iter().any(|assume| definitions.contains(assume)),
        "the certificate reads its macro through the definition premise: {context}"
    );
}
