// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The problem is read by AY's own SMT-LIB front end (its lexer and its
//! elaborator), and the proof's definitions in document order.
//!
//! REGRESSION (measured 2026-10-07 on a4b66eeff, the r16 verifier's
//! reproducers): every problem in [`SATISFIABLE`] is satisfiable (z3 and AY
//! answer `sat`), and the mirror's hand-rolled reader counted a refutation of
//! it as checked step by step. A string literal closed its command and
//! injected `(assert false)` (`string_paren`, and `string_semicolon`, whose
//! `;` then commented the literal's rest out); the quoted symbol `|#b1|` was
//! read as the literal `#b1`; a user function named `bvf` was given its
//! argument's one-bit width; and a declaration popped with its scope kept its
//! one-bit sort for the later two-bit `x`. `correct_width` is the same
//! truncation proof against a problem whose `x` is declared two bits: it was
//! refused at `t1` then too, which pins the width cases on the sort alone.
//!
//! The [`MISREAD_PROOFS`] were also counted as checked: a `define-fun`'s
//! parameters were dropped and its body expanded over the whole document, so
//! a macro used without its argument, or before its definition, was read as
//! its body. Carcara reads neither so.
//!
//! The consumer: with `CLEAN_PATH` its verdict on each is printed.

use super::super::consumer_rules::{mirror_certificate, step_verdict};
use super::clean_accepts;

const REFUTE_FALSE: &str = "(assume a0 false)\n(step t1 (cl (not false)) :rule false)\n\
     (step t2 (cl) :rule resolution :premises (a0 t1))\n";

const QUOTED_LITERAL_REFUTATION: &str = "(assume a0 (= |#b1| #b0))\n\
     (step t1 (cl (= (= |#b1| #b0) false)) :rule evaluate)\n\
     (step t2 (cl (not (= (= |#b1| #b0) false)) (not (= |#b1| #b0)) false) :rule equiv_pos2)\n\
     (step t3 (cl (not false)) :rule false)\n\
     (step t4 (cl) :rule resolution :premises (t2 t1 a0 t3))\n";

/// A refutation of `(not (= x c))` and `(= ((_ extract 0 0) x) ((_ extract
/// 0 0) c))` that is sound only when `x` and `c` are one bit wide.
fn truncation_refutation(x: &str, c: &str) -> String {
    let (e1, e2) = (
        format!("((_ extract 0 0) {x})"),
        format!("((_ extract 0 0) {c})"),
    );
    let (bx, bc) = (
        format!("((_ @bit_of 0) {x})"),
        format!("((_ @bit_of 0) {c})"),
    );
    let (q, bq, e) = (
        format!("(= {x} {c})"),
        format!("(= {bx} {bc})"),
        format!("(= {e1} {e2})"),
    );
    let bb = format!("(= (@bbterm {bx}) (@bbterm {bc}))");
    format!(
        "(assume a0 (not {q}))\n(assume a1 {e})\n\
         (step t1 (cl (= {q} {bq})) :rule bitblast_equal)\n\
         (step t2 (cl (= {e1} (@bbterm {bx}))) :rule bitblast_extract)\n\
         (step t3 (cl (= {e2} (@bbterm {bc}))) :rule bitblast_extract)\n\
         (step t4 (cl (= {e} {bb})) :rule cong :premises (t2 t3))\n\
         (step t5 (cl (= {bb} {bq})) :rule bitblast_equal)\n\
         (step t6 (cl (= {e} {bq})) :rule trans :premises (t4 t5))\n\
         (step t7 (cl (not (= {e} {bq})) (not {e}) {bq}) :rule equiv_pos2)\n\
         (step t8 (cl {bq}) :rule resolution :premises (t7 t6 a1))\n\
         (step t9 (cl (not (= {q} {bq})) {q} (not {bq})) :rule equiv_pos1)\n\
         (step t10 (cl) :rule resolution :premises (t9 t1 t8 a0))\n"
    )
}

/// The assertions [`truncation_refutation`] refutes.
fn truncated(x: &str) -> String {
    format!(
        "(assert (not (= {x} c)))\n(assert (= ((_ extract 0 0) {x}) ((_ extract 0 0) c)))\n\
         (check-sat)\n"
    )
}

/// `(name, problem, proof)`: every problem is satisfiable.
fn satisfiable() -> Vec<(&'static str, String, String)> {
    let bv_function = "(set-logic QF_UFBV)\n(declare-fun bvf ((_ BitVec 1)) (_ BitVec 2))\n\
        (declare-const a (_ BitVec 1))\n(declare-const c (_ BitVec 2))\n";
    vec![
        (
            "string_paren",
            "(set-logic ALL)\n(set-info :source \"a) (assert false) (b\")\n\
             (declare-const p Bool)\n(assert p)\n(check-sat)\n"
                .to_string(),
            REFUTE_FALSE.to_string(),
        ),
        (
            "string_semicolon",
            "(set-logic ALL)\n(set-info :source \"a) (assert false) ;\")\n\
             (declare-const p Bool)\n(assert p)\n(check-sat)\n"
                .to_string(),
            REFUTE_FALSE.to_string(),
        ),
        (
            "quoted_symbol",
            "(set-logic QF_BV)\n(declare-const |#b1| (_ BitVec 1))\n\
             (assert (= |#b1| #b0))\n(check-sat)\n"
                .to_string(),
            QUOTED_LITERAL_REFUTATION.to_string(),
        ),
        (
            "bv_named_function",
            format!("{bv_function}{}", truncated("(bvf a)")),
            truncation_refutation("(bvf a)", "c"),
        ),
        (
            "popped_declaration",
            "(set-logic QF_BV)\n(push 1)\n(declare-const x (_ BitVec 1))\n(pop 1)\n\
             (declare-const d (_ BitVec 2))\n(declare-const c (_ BitVec 2))\n\
             (define-fun x () (_ BitVec 2) d)\n"
                .to_string()
                + &truncated("x"),
            truncation_refutation("x", "c"),
        ),
        (
            "correct_width",
            "(set-logic QF_BV)\n(declare-const x (_ BitVec 2))\n(declare-const c (_ BitVec 2))\n"
                .to_string()
                + &truncated("x"),
            truncation_refutation("x", "c"),
        ),
    ]
}

/// `(name, proof)` against `(assert false)`: proofs Carcara does not read as
/// the hand-rolled reader did, refused as a document.
const MISREAD_PROOFS: &[(&str, &str)] = &[
    (
        "macro_without_its_argument",
        "(define-fun f ((y Bool)) Bool false)\n(assume a0 false)\n\
         (step t1 (cl (not f)) :rule false)\n(step t2 (cl) :rule resolution :premises (a0 t1))\n",
    ),
    (
        "macro_before_its_definition",
        "(assume a0 false)\n(step t1 (cl (not m)) :rule false)\n\
         (define-fun m () Bool false)\n(step t2 (cl) :rule resolution :premises (a0 t1))\n",
    ),
];

#[test]
#[ntest::timeout(600_000)]
fn the_problem_is_read_by_the_front_end_and_the_proof_in_order() {
    let mut failures = Vec::new();
    for (name, problem, proof) in satisfiable() {
        let (verdict, _) = super::one_shot(&problem, &[]);
        if verdict != "sat" {
            failures.push(format!("{name}: ay answers {verdict:?}"));
        }
        let coverage = mirror_certificate(&problem, &proof);
        if coverage.checked() || coverage.refutation.is_some() {
            failures.push(format!(
                "{name}: a refutation of a satisfiable problem is checked"
            ));
        }
        if name == "correct_width" {
            let t1 = step_verdict(&problem, &proof, "t1").unwrap_or_default();
            if !t1.starts_with("refused") {
                failures.push(format!("{name}: t1 is {t1}"));
            }
        }
        if let Some(accepts) = clean_accepts(&problem, &proof) {
            eprintln!("{name}: CLEAN_PATH accepts it: {accepts}");
        }
    }
    let problem = "(set-logic ALL)\n(assert false)\n(check-sat)\n";
    for &(name, proof) in MISREAD_PROOFS {
        let coverage = mirror_certificate(problem, proof);
        if coverage.checked() {
            failures.push(format!("{name}: checked"));
        }
        if !coverage
            .refused
            .iter()
            .any(|refusal| refusal.contains("the proof is not read as the consumer reads it"))
        {
            failures.push(format!("{name}: the definition is not refused"));
        }
        if let Some(accepts) = clean_accepts(problem, proof) {
            eprintln!("{name}: CLEAN_PATH accepts it: {accepts}");
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
