// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn refuses(input: &str) {
    match QuantifiedChcProblem::parse_smtlib(input) {
        Err(ChcError::Parse(_)) => {}
        result => {
            panic!("expected syntax/admission refusal, not a missing query: {input}: {result:?}")
        }
    }
}

#[test]
fn unsupported_mixed_incremental_and_post_query_commands_refuse() {
    for input in [
        "(declare-const x Bool)(assert x)(check-sat)",
        "(declare-fun f ((_ BitVec 8)) Int)(check-sat)",
        "(define-fun f () Bool true)(check-sat)",
        "(set-option :produce-models true)(check-sat)",
        "(set-logic QF_BV)(check-sat)",
        "(declare-rel P ())(assert P)(check-sat)",
        "(declare-fun P () Bool)(rule P)(query P)",
        "(declare-rel P ())(check-sat)",
        "(declare-rel P ())(rule P)(declare-var x Bool)(query P)",
        "(declare-rel P ())(rule P)",
        "(declare-rel P ())(query P)(query P)",
        "(check-sat)(check-sat)",
        "(check-sat)(push 1)",
        "(check-sat)(exit)(exit)",
        "(declare-rel error ())(query error)(declare-const cover Bool)(assert cover)",
    ] {
        refuses(input);
    }
}

#[test]
fn unsupported_theory_arity_and_sort_metadata_refuse() {
    for declaration in [
        "(declare-var x Int)",
        "(declare-var x (_ BitVec 0))",
        "(declare-var x (_ BitVec 1048577))",
        "(declare-var x (Array Bool Bool))",
        "(declare-var x (Array (_ BitVec 2) (Array (_ BitVec 2) (Array (_ BitVec 2) Bool))))",
        "(declare-var bvult Bool)",
        "(declare-var x Bool)(declare-var x Bool)",
    ] {
        refuses(&format!("{declaration}(declare-rel error ())(query error)"));
    }
    for formula in [
        "(= #b0 #b00)",
        "(and true #b0)",
        "(bvult #b0 true)",
        "(select #b0 #b0)",
        "((_ extract 2 0) #b0)",
        "(_ bv4 2)",
        "(and)",
        "(unknown true)",
        "(! true :named x)",
    ] {
        refuses(&format!(
            "(declare-rel error ())(rule (=> {formula} error))(query error)"
        ));
    }
}

#[test]
fn unsupported_quantifier_positions_and_lexical_capture_near_misses_refuse() {
    for formula in [
        "(=> (exists ((i (_ BitVec 2))) true) P)",
        "(=> (forall ((i Bool)) i) P)",
        "(=> (forall ((i (_ BitVec 2))) (forall ((j (_ BitVec 2))) (= i j))) P)",
        "(=> (or true (forall ((i (_ BitVec 2))) true)) P)",
        "(=> (forall ((i (_ BitVec 2))) P) P)",
        "(=> (= P true) false)",
        "(let ((x true) (x false)) (=> x P))",
        "(let ((x true) (saved x)) (=> saved P))",
        "(let ((P true)) (=> (P #b0) false))",
        "(let ((unused (and true #b0))) P)",
        "(let ((unused (=> true #b0))) P)",
        "(let ((unused (forall ((i (_ BitVec 2))) #b0))) P)",
    ] {
        refuses(&format!(
            "(declare-fun P () Bool)(assert {formula})(check-sat)"
        ));
    }
}

#[test]
fn expansion_refusal_is_atomic_and_fresh_parse_still_succeeds() {
    let mut body = "(=> x20 P)".to_owned();
    for index in (1..=20).rev() {
        body = format!(
            "(let ((x{index} (and x{} x{}))) {body})",
            index - 1,
            index - 1
        );
    }
    body = format!("(let ((x0 true)) {body})");
    let input = format!("(declare-fun P () Bool)(assert {body})(assert (=> P false))(check-sat)");
    assert!(matches!(
        QuantifiedChcProblem::parse_smtlib(&input),
        Err(ChcError::Parse(message)) if message.contains("parse work/copy limit")
    ));
    // Lexical and expanded-depth admissions are independently fail-closed.
    let deep = format!("{}true{}", "(not ".repeat(65), ")".repeat(65));
    refuses(&format!("(assert {deep})(check-sat)"));
    assert_eq!(
        parsed("(declare-fun P () Bool)(assert P)(assert (=> P false))(check-sat)")
            .source_problem()
            .clauses()
            .len(),
        2
    );
}
