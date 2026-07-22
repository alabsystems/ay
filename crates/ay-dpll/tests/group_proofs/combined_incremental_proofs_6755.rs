// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_core::{ProofStep, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof, check_proof_with_quality, ProofQuality};
use ntest::timeout;

fn run_unsat_proof(input: &str) -> (String, ProofQuality, Vec<TheoryLemmaKind>) {
    let commands = parse(input).expect("proof-enabled SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("proof-enabled SMT-LIB script should execute");

    assert_eq!(outputs.len(), 2, "expected check-sat + get-proof output");
    assert_eq!(outputs[0].trim(), "unsat", "expected UNSAT result");

    let proof_text = outputs[1].clone();
    assert!(
        proof_text.contains("(cl)"),
        "expected empty-clause derivation in proof:\n{proof_text}"
    );
    assert!(
        !proof_text.contains(":rule hole"),
        "combined incremental proof should not contain :rule hole:\n{proof_text}"
    );

    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof(proof, exec.terms()).expect("internal proof checker rejected proof");
    let quality = check_proof_with_quality(proof, exec.terms())
        .expect("proof quality checker rejected proof");
    let theory_kinds = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, .. } => Some(*kind),
            _ => None,
        })
        .collect();

    (proof_text, quality, theory_kinds)
}

#[test]
#[timeout(5_000)]
fn test_uflra_incremental_push_pop_produces_valid_proof_6755() {
    let input = r#"
        (set-logic QF_UFLRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (declare-fun f (Real) Real)
        (push 1)
        (assert (= x 0.0))
        (assert (= (f x) 1.0))
        (assert (= (f 0.0) 2.0))
        (check-sat)
        (get-proof)
    "#;

    let (proof_text, quality, _theory_kinds) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "UFLRA combined proof should not contain hole steps: {quality:?}"
    );
    assert!(
        quality.th_resolution_count > 0,
        "UFLRA combined proof should contain at least one th_resolution step: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "UFLRA push/pop proof should not contain :rule trust after #6756:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "UFLRA push/pop proof should contain :rule eq_congruent:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "UFLRA push/pop proof should contain :rule la_generic:\n{proof_text}"
    );
}

#[test]
#[timeout(5_000)]
fn test_auflia_incremental_push_pop_produces_valid_proof_6755() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (push 1)
        (assert (= (select a 0) 1))
        (assert (= (select a 0) 2))
        (check-sat)
        (get-proof)
    "#;

    let (proof_text, quality, theory_kinds) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "AUFLIA push/pop proof should not contain hole steps: {quality:?}"
    );
    assert!(
        quality.th_resolution_count > 0,
        "AUFLIA push/pop proof should contain at least one th_resolution step: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "AUFLIA push/pop proof should not contain :rule trust after #6756 Packet 1:\n{proof_text}"
    );
    // Accept either LIA-generic or LRA-Farkas: both are valid arithmetic
    // proof rules for this integer-equality conflict. The rule chosen depends
    // on theory-atom routing (#6869) which may change over time.
    assert!(
        theory_kinds.contains(&TheoryLemmaKind::LiaGeneric)
            || theory_kinds.contains(&TheoryLemmaKind::LraFarkas),
        "AUFLIA push/pop proof should retain an arithmetic theory lemma: {theory_kinds:?}\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule lia_generic") || proof_text.contains(":rule la_generic"),
        "AUFLIA push/pop proof should contain an arithmetic proof rule:\n{proof_text}"
    );
}

#[test]
#[timeout(5_000)]
fn test_auflia_check_sat_assuming_retains_lia_generic_6755() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (declare-const x Int)
        (assert (= (select a 0) x))
        (check-sat-assuming ((> x 0) (<= (select a 0) 0)))
        (get-proof)
    "#;

    let (proof_text, quality, theory_kinds) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "AUFLIA assumption proof should not contain hole steps: {quality:?}"
    );
    assert!(
        quality.th_resolution_count > 0,
        "AUFLIA assumption proof should contain at least one th_resolution step: {quality:?}"
    );
    // Accept either LIA-generic or LRA-Farkas: both are structured arithmetic
    // lemmas for this integer conflict, and the latter exports as `la_generic`
    // with explicit Farkas coefficients.
    assert!(
        theory_kinds.contains(&TheoryLemmaKind::LiaGeneric)
            || theory_kinds.contains(&TheoryLemmaKind::LraFarkas),
        "AUFLIA assumption proof should retain an arithmetic theory lemma: {theory_kinds:?}\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule lia_generic") || proof_text.contains(":rule la_generic"),
        "AUFLIA assumption proof should contain an arithmetic proof rule (#6757):\n{proof_text}"
    );
    // The combined theory lemma must use a structured arithmetic rule, not
    // trust. Unit trust steps for check-sat-assuming input literals are
    // acceptable (#6757).
    let multi_lit_trust = proof_text.lines().any(|line| {
        line.contains(":rule trust") && line.contains("(cl ") && line.matches("(not ").count() >= 2
    });
    assert!(
        !multi_lit_trust,
        "AUFLIA assumption proof should not contain multi-literal :rule trust (#6757):\n{proof_text}"
    );
}

#[test]
#[timeout(5_000)]
fn test_auflra_store_axiom_push_pop_produces_structured_proof_6761() {
    // Use a variable index so the store/select simplification can't pre-reduce
    // to false at the term level. The eager ROW axiom must generate disjunctive
    // array axioms for the SAT solver to resolve through.
    let input = r#"
        (set-logic QF_AUFLRA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Real))
        (declare-const i Int)
        (push 1)
        (assert (= i 0))
        (assert (= (select (store a i 1.5) 0) 2.5))
        (check-sat)
        (get-proof)
    "#;

    let (proof_text, quality, _theory_kinds) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "AUFLRA eager-array proof should not contain hole steps: {quality:?}"
    );
    // The AUFLRA eager-array closure was refined from a single coarse
    // th_resolution step to fine-grained standard-rule resolution (explicit
    // read_over_write_pos + la_generic theory lemmas closed by plain boolean
    // resolution + or_pos to the empty clause). That is structurally BETTER,
    // not worse: verdict unchanged (unsat, z3-confirmed), hole_count == 0
    // (asserted above), and `ay solve --verify-proof` still re-checks the
    // emitted Alethe to unsat. Accept EITHER the coarse th_resolution closer OR
    // the fine-grained (resolution + theory-lemma) shape; both are valid,
    // hole-free Alethe. Pinning only `th_resolution_count > 0` would have
    // demanded the coarser proof and rejected the improvement.
    assert!(
        quality.th_resolution_count > 0
            || (quality.resolution_count > 0 && quality.theory_lemma_count > 0),
        "AUFLRA eager-array proof should close via th_resolution OR fine-grained \
         resolution+theory-lemma steps (hole-free either way): {quality:?}\n{proof_text}"
    );
    let line_count = proof_text.lines().filter(|l| !l.trim().is_empty()).count();
    assert!(
        line_count > 1,
        "AUFLRA eager-array proof should have more than a single trust step:\n{proof_text}"
    );
}
