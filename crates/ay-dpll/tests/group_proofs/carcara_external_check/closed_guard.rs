// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A guarded quantifier instance decided by its CLOSED signed guard.
//!
//! The model-checker-consumer `signed_range64_*` corpus rows refute
//! `(forall ((i ..)) (=> (and (bvsge i lo) (bvslt i hi)) (= (select a i) v)))`
//! at a negative index. AY's strict checker validates the ground lemma
//! `(cl (= v (select a k)) (not (=> guard(k) (= (select a k) v))))` by
//! bit-blasting, and it used to print as `hole`: pinned carcara 1.1.0 has no
//! `bitblast_*` rule for `bvsge`, and its `evaluate` reads a negative signed
//! operand as its magnitude, so it would call the TRUE guard false. The
//! closed-atom lowering (`ay-proof` `alethe_printer/closed_guard.rs`) proves
//! each guard atom with `pbblast_bv*` plus `la_generic` and re-derives the
//! lemma from its Tseitin clauses.
//!
//! The second fixture names the array through a nullary `define-fun`: AY
//! checks the EXPANDED store, the printed instance names `a`, and the bridge
//! is the problem's own premise `(= a (store ..))`, which pinned carcara holds
//! without `--apply-function-defs`.
//!
//! Both are 16-bit versions of the corpus rows (at 8 bits proof mode answers
//! `unknown` before any document exists). Each must be `valid`
//! with no allowance and carry no `evaluate`, `hole` or `trust` step.

use super::{
    carcara_verdict_without_allowances, require_carcara_or_skip, solve_unsat_and_get_proof,
    CarcaraVerdict,
};
use ntest::timeout;

const SIGNED_GUARD_FILL: &str = r#"
(set-logic ALL)
(declare-const a (Array (_ BitVec 16) (_ BitVec 8)))
(assert (forall ((i (_ BitVec 16)))
  (=> (and (bvsge i #xfffe) (bvslt i #x0002))
      (= (select a i) #x07))))
(assert (distinct (select a #xffff) #x07))
(check-sat)
"#;

const MACRO_MISSING_NEGATIVE: &str = r#"
(set-logic ALL)
(define-fun a () (Array (_ BitVec 16) (_ BitVec 8))
  (store ((as const (Array (_ BitVec 16) (_ BitVec 8))) #x07) #xffff #x00))
(assert (forall ((i (_ BitVec 16)))
  (=> (and (bvsge i #xfffe) (bvslt i #x0002))
      (= (select a i) #x07))))
(check-sat)
"#;

fn assert_valid_without_signed_evaluate(label: &str, problem: &str) -> String {
    let proof = solve_unsat_and_get_proof(problem, label);
    for forbidden in [":rule hole", ":rule trust", ":rule evaluate"] {
        assert!(!proof.contains(forbidden), "{label}: {forbidden}:\n{proof}");
    }
    assert!(
        proof.contains(":rule pbblast_bvsge") || proof.contains(":rule pbblast_bvslt"),
        "{label}: the signed guard must be pseudo-Boolean blasted:\n{proof}"
    );
    if let Some(carcara) = require_carcara_or_skip() {
        assert_eq!(
            carcara_verdict_without_allowances(&carcara, label, problem, &proof),
            CarcaraVerdict::Valid,
            "{label}: pinned carcara must re-derive every step"
        );
    }
    proof
}

#[test]
#[timeout(60_000)]
fn true_signed_guard_lowers_the_guarded_instance() {
    assert_valid_without_signed_evaluate("closed_guard_signed_fill", SIGNED_GUARD_FILL);
}

#[test]
#[timeout(60_000)]
fn nullary_macro_is_read_through_its_definition_premise() {
    let proof =
        assert_valid_without_signed_evaluate("closed_guard_macro_read", MACRO_MISSING_NEGATIVE);
    assert!(
        proof.lines().any(|line| line.starts_with("(assume ")
            && line.contains(
                " (= a (store ((as const (Array (_ BitVec 16) (_ BitVec 8))) #x07) #xffff #x00)))"
            )),
        "the definition premise bridges the printed `a` to the checked store:\n{proof}"
    );
}

/// The strict gate and the certificate disclosure judge each premise `assume`
/// against `Executor::authored_premise_surfaces`. The definition premise
/// `(= a body)` is a premise pinned carcara holds, so it must be one there too:
/// without it the carcara-`valid` macro document was disclosed as
/// `foreign_assumes=yes trust_free=no`, and `--rigor strict` answered
/// `unknown` for it.
#[test]
#[timeout(60_000)]
fn the_definition_premise_is_a_premise_for_the_strict_gate() {
    let script =
        format!("(set-option :produce-proofs true)\n{MACRO_MISSING_NEGATIVE}\n(get-proof)\n");
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec
        .execute_all(&ay_frontend::parse(&script).expect("parse"))
        .expect("execute");
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let proof = outputs.last().expect("proof output");
    let surfaces = exec
        .authored_premise_surfaces()
        .expect("every assertion kept its authored syntax");
    let assumed: Vec<&str> = proof
        .lines()
        .filter_map(|line| line.strip_prefix("(assume "))
        .filter_map(|rest| rest.split_once(' '))
        .filter_map(|(_, term)| term.trim_end().strip_suffix(')'))
        .collect();
    assert_eq!(
        assumed.len(),
        2,
        "the quantifier and the definition:\n{proof}"
    );
    for term in assumed {
        assert!(
            surfaces.contains(&ay_dpll::normalize_premise_surface(term)),
            "a premise pinned carcara holds is judged foreign: {term}"
        );
    }
    // Negative twin: another body for `a` is not the definition premise.
    assert!(!surfaces.contains(&ay_dpll::normalize_premise_surface(
        "(= a ((as const (Array (_ BitVec 16) (_ BitVec 8))) #x07))"
    )));
}

/// The two file-backed exports (the String export behind
/// `export_last_unsat_artifact`, and the streaming export the CLI `--proof`
/// file and the strict gate's scan use) hand the printer the same authored
/// surfaces as `(get-proof)`: each must emit the same hole-free document,
/// definition premise included. Passing only the `not`-shell channel at
/// either call site keeps the macro read as `hole` there.
#[test]
#[timeout(60_000)]
fn the_file_exports_carry_the_definition_premise() {
    let script =
        format!("(set-option :produce-proofs true)\n{MACRO_MISSING_NEGATIVE}\n(get-proof)\n");
    let mut exec = ay_dpll::Executor::new();
    let outputs = exec
        .execute_all(&ay_frontend::parse(&script).expect("parse"))
        .expect("execute");
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    let get_proof = outputs.last().expect("proof output").trim_end();
    let file = exec
        .try_export_last_proof_alethe_for_problem_scope()
        .expect("a retained proof")
        .expect("the String export renders it");
    let mut streamed = Vec::new();
    exec.try_export_last_proof_alethe_for_problem_scope_to(&mut streamed)
        .expect("a retained proof")
        .expect("the streaming export renders it");
    let streamed = String::from_utf8(streamed).expect("UTF-8");
    let premise =
        " (= a (store ((as const (Array (_ BitVec 16) (_ BitVec 8))) #x07) #xffff #x00)))";
    for (exit, document) in [("String", file.trim_end()), ("stream", streamed.trim_end())] {
        assert!(
            !document.contains(":rule hole"),
            "{exit} export keeps a hole:\n{document}"
        );
        assert!(
            document
                .lines()
                .any(|line| line.starts_with("(assume ") && line.contains(premise)),
            "{exit} export lacks the definition premise:\n{document}"
        );
        assert_eq!(document, get_proof, "{exit} export and (get-proof) differ");
    }
}
