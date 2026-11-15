// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Two published certificates pinned carcara refuted, and their SAT twins.
//!
//! * `a7_int_neg_unsat`: the authored `(= (g (- 5)) 0)` rides its canonical
//!   root `(= 0 (g (- 5)))` document-wide. The ground-pin orientation bridge
//!   then printed the checked `eq_symmetric` over that root with two
//!   IDENTICAL sides, the certificate line claimed `ay_self_checkable=yes
//!   carcara_surface=supported`, and carcara answered `invalid` at that step
//!   ("expected terms to be equal"). The printer now judges the printed text:
//!   identical sides are a `refl` instance.
//! * `b6_nullary_define_unsat`: `(assert (= v0 one))` over
//!   `(define-fun one () (_ BitVec 1) #b1)`. The BV guarded-collapse lane
//!   raw-interns the macro-EXPANDED assertion and published
//!   `(assume t0 (= v0 #b1))`, which is no premise of the problem, so carcara
//!   answered `invalid` at `t0`. The authored spelling is now restored and
//!   bridged through the definition premise `(= one #b1)` carcara holds.
//!
//! Every UNSAT document must be literally `valid` with no allowance.

use super::{
    carcara_verdict_without_allowances, parse, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict, Executor,
};
use ntest::timeout;

const A7_INT_NEG_UNSAT: &str = r#"
(set-logic ALL)
(declare-fun g (Int) Int)
(assert (forall ((i Int)) (=> (< i 0) (= (g i) 1))))
(assert (= (g (- 5)) 0))
(check-sat)
"#;

const A7_INT_NEG_SAT: &str = r#"
(set-logic ALL)
(declare-fun g (Int) Int)
(assert (forall ((i Int)) (=> (< i (- 5)) (= (g i) 1))))
(assert (= (g (- 5)) 0))
(check-sat)
"#;

const B6_NULLARY_DEFINE_UNSAT: &str = r#"
(set-logic ALL)
(define-fun one () (_ BitVec 1) #b1)
(declare-fun summary (Bool (_ BitVec 64)) (_ BitVec 1))
(declare-const v0 (_ BitVec 1))
(declare-const v1 (_ BitVec 1))
(assert (forall ((i (_ BitVec 64))) (=> (bvult i (_ bv65 64)) (= (summary false i) (_ bv1 1)))))
(assert (= v0 one))
(assert (= v1 v0))
(assert (= v1 #b0))
(check-sat)
"#;

const B6_NULLARY_DEFINE_GROUND_UNSAT: &str = r#"
(set-logic ALL)
(define-fun one () (_ BitVec 1) #b1)
(declare-const v0 (_ BitVec 1))
(declare-const v1 (_ BitVec 1))
(assert (= v0 one))
(assert (= v1 v0))
(assert (= v1 #b0))
(check-sat)
"#;

const B6_NULLARY_DEFINE_SAT: &str = r#"
(set-logic ALL)
(define-fun one () (_ BitVec 1) #b1)
(declare-fun summary (Bool (_ BitVec 64)) (_ BitVec 1))
(declare-const v0 (_ BitVec 1))
(declare-const v1 (_ BitVec 1))
(assert (forall ((i (_ BitVec 64))) (=> (bvult i (_ bv65 64)) (= (summary false i) (_ bv1 1)))))
(assert (= v0 one))
(assert (= v1 v0))
(assert (= v1 #b1))
(check-sat)
"#;

/// The source-bound frame case whose `frame` macro the same lane expanded.
const POSITIVE_STACK_FRAME: &str =
    include_str!("../../fixtures/source_bound_stack_frame/positive-stack.smt2");

fn assert_carcara_valid(label: &str, problem: &str) -> String {
    let proof = solve_unsat_and_get_proof(problem, label);
    for forbidden in [":rule hole", ":rule trust"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must re-derive every step:\n{proof}"
        );
    }
    proof
}

fn assert_sat(label: &str, problem: &str) {
    let script = format!("(set-option :produce-proofs true)\n{problem}\n");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(&script).expect("parse"))
        .expect("execute");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "{label}: the satisfiable twin must stay SAT, got {outputs:?}"
    );
}

fn assumed_terms(proof: &str) -> Vec<&str> {
    proof
        .lines()
        .filter_map(|line| line.strip_prefix("(assume "))
        .filter_map(|rest| rest.split_once(' '))
        .filter_map(|(_, term)| term.trim_end().strip_suffix(')'))
        .collect()
}

#[test]
#[timeout(60_000)]
fn a_collapsed_eq_symmetric_publishes_as_refl() {
    let proof = assert_carcara_valid("published_spelling_a7", A7_INT_NEG_UNSAT);
    assert!(
        proof.contains("(cl (= (= (g (- 5)) 0) (= (g (- 5)) 0))) :rule refl)"),
        "the identity the override printed is a refl instance:\n{proof}"
    );
    assert_sat("published_spelling_a7_sat", A7_INT_NEG_SAT);
}

#[test]
#[timeout(60_000)]
fn a_macro_expanded_assume_publishes_its_authored_spelling() {
    for (label, problem) in [
        ("published_spelling_b6", B6_NULLARY_DEFINE_UNSAT),
        (
            "published_spelling_b6_ground",
            B6_NULLARY_DEFINE_GROUND_UNSAT,
        ),
    ] {
        let proof = assert_carcara_valid(label, problem);
        let assumed = assumed_terms(&proof);
        assert!(
            assumed.contains(&"(= v0 one)") && assumed.contains(&"(= one #b1)"),
            "{label}: the authored assertion and the definition premise:\n{proof}"
        );
        assert!(
            !assumed.contains(&"(= v0 #b1)"),
            "{label}: the expanded assertion is no premise of the problem:\n{proof}"
        );
    }
    assert_sat("published_spelling_b6_sat", B6_NULLARY_DEFINE_SAT);
}

#[test]
#[timeout(120_000)]
fn the_stack_frame_macro_assume_publishes_its_authored_spelling() {
    let proof = assert_carcara_valid("published_spelling_positive_stack", POSITIVE_STACK_FRAME);
    assert!(
        assumed_terms(&proof).contains(&"(= frame (bvsub sp (_ bv16 64)))"),
        "the `frame` definition premise bridges the authored assertion:\n{proof}"
    );
}
