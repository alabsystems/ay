// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! REACHABILITY for the bit-blast fold-to-`false` rescue
//! (`authored_bv_bitblast_refutation`): the production `execute_all` path under
//! `(set-option :produce-proofs true)`.
//!
//! Term construction rewrites `(bvudiv x 2^k)` to `(bvlshr x k)`, so an authored
//! disequality between the two spellings folds to `false` and, before this
//! rescue, the whole proof was erased to `(step t0 (cl) :rule hole)` — 56 of
//! external-codegen's strict-gate obligations, measured 2026-09-28 on build 11390. The
//! rescue records the fold as a `BvBitBlast` lemma over the author's own
//! assertion, which the strict checker re-derives by bit-blasting.

use ay_dpll::Executor;
use ay_frontend::parse;

fn run_with_proofs(body: &str) -> (Vec<String>, Option<String>) {
    let script = format!("(set-option :produce-proofs true)\n{body}");
    let commands = parse(&script).expect("fixture script must parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture script must run");
    let proof = if outputs.last().map(String::as_str) == Some("unsat") {
        let get_proof = parse("(get-proof)").expect("(get-proof) must parse");
        exec.execute_all(&get_proof)
            .ok()
            .and_then(|out| out.last().cloned())
    } else {
        None
    };
    (outputs, proof)
}

#[test]
fn a_division_by_a_power_of_two_folded_to_a_shift_keeps_its_proof() {
    for (width, divisor, shift) in [(8, "#x02", "#x01"), (32, "#x00000004", "#x00000002")] {
        let (outputs, proof) = run_with_proofs(&format!(
            "(set-logic QF_BV)\n\
             (declare-const base (_ BitVec {width}))\n\
             (declare-const src (_ BitVec {width}))\n\
             (assert (not (= (bvadd base (bvudiv src {divisor})) (bvadd base (bvlshr src {shift})))))\n\
             (check-sat)"
        ));
        assert_eq!(
            outputs.last().map(String::as_str),
            Some("unsat"),
            "{width}-bit"
        );
        let proof = proof.expect("an unsat verdict under :produce-proofs has a proof");
        // RECORDED at every width: the authored root is assumed and refuted,
        // never erased to the bare `(step t0 (cl) :rule hole)`.
        assert!(
            proof.starts_with("(assume ") && proof.contains("bvudiv"),
            "{width}-bit fold must be recorded over the AUTHORED root:\n{proof}"
        );
        // PRINTED hole-free at every width: the checker's divider circuit
        // against a shift is swept into local lemmas (`complete_blast/sweep`),
        // where its monolithic refutation transported past the text budget.
        assert!(
            !proof.contains(":rule hole") && !proof.contains(":rule trust"),
            "{width}-bit fold must print hole-free:\n{proof}"
        );
    }
}

#[test]
fn a_satisfiable_root_is_never_rescued() {
    // `x / 2 == x >> 2` is false for x = 4: the query is SAT and must stay so;
    // nothing about the rescue may turn it into an UNSAT.
    let (outputs, _) = run_with_proofs(
        "(set-logic QF_BV)\n\
         (declare-const src (_ BitVec 8))\n\
         (assert (not (= (bvudiv src #x02) (bvlshr src #x02))))\n\
         (check-sat)",
    );
    assert_eq!(outputs.last().map(String::as_str), Some("sat"));
}

/// external-codegen's `SDIV Xn, #-1 == NEG Xn` spelled by `bvsdiv`'s SMT-LIB
/// definition: term construction folds the constant sign tests, so the
/// internal root no longer prints as authored. The refutation over the RAW
/// authored root prints hole-free.
#[test]
fn a_definitional_signed_division_by_minus_one_prints_hole_free() {
    let (outputs, proof) = run_with_proofs(
        "(set-logic QF_BV)\n\
         (declare-const xn (_ BitVec 8))\n\
         (assert (not (= (ite (and (= ((_ extract 7 7) xn) #b0) (= ((_ extract 7 7) #xff) #b0)) \
         (bvudiv xn #xff) (ite (and (= ((_ extract 7 7) xn) #b1) (= ((_ extract 7 7) #xff) #b0)) \
         (bvneg (bvudiv (bvneg xn) #xff)) (ite (and (= ((_ extract 7 7) xn) #b0) \
         (= ((_ extract 7 7) #xff) #b1)) (bvneg (bvudiv xn (bvneg #xff))) \
         (bvudiv (bvneg xn) (bvneg #xff))))) (bvsub #x00 xn))))\n\
         (check-sat)",
    );
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"));
    let proof = proof.expect("an unsat verdict under :produce-proofs has a proof");
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "the definitional signed division must print hole-free:\n{proof}"
    );
}
