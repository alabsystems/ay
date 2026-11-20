// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const PRELUDE: &str = "(set-logic ALL)
    (declare-const a (Seq Int)) (declare-const x Int) (declare-const v Int)";

fn loaded(assertion: &str) -> Executor {
    let mut executor = Executor::new();
    executor
        .execute_all(&ay_frontend::parse(&format!("{PRELUDE} (assert {assertion})")).unwrap())
        .unwrap();
    executor
}

#[test]
fn seq_word_presolve_installs_only_complete_original_scope_refutations() {
    for theorem in [
        "(= (seq.++ (as seq.empty (Seq Int)) a) a)",
        "(= (seq.len (seq.++ a (seq.unit x))) (+ (seq.len a) 1))",
        "(= (seq.contains (seq.++ a (seq.unit v)) (seq.unit x))
            (or (seq.contains a (seq.unit x)) (= x v)))",
    ] {
        let mut exec = loaded(&format!("(not {theorem})"));
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        assert_eq!(
            exec.try_presolve_seq_word_refutation(),
            Some(SolveResult::unsat())
        );
        let proof = exec.last_proof.as_ref().unwrap();
        assert_eq!(proof.steps.len(), 3);
        assert!(ay_proof::terminal_trust_report(proof).is_trust_free());
        assert!(exec
            .check_proof_strict_with_datatypes(proof)
            .unwrap()
            .is_complete());
        assert!(
            ay_proof::validate_reachable_assumes_in_problem_scope(proof, &exec.ctx.assertions)
                .is_ok()
        );
    }
}

#[test]
fn seq_word_presolve_declines_wrong_membership_and_strict_positive_length() {
    for assertion in [
        "(not (< 0 (seq.len a)))",
        "(not (= (seq.contains (seq.++ a (seq.unit v)) (seq.unit x))
            (or (seq.contains a (seq.unit x)) (= x 0))))",
    ] {
        let mut exec = loaded(assertion);
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        assert!(exec.try_presolve_seq_word_refutation().is_none());
        assert!(exec.last_proof.is_none());
    }
}

#[test]
fn seq_word_presolve_does_not_reuse_a_candidate_after_source_mutation() {
    let mut exec = loaded("(not (= (seq.++ (as seq.empty (Seq Int)) a) a))");
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let (candidate, _memory) = exec.propose_authored_seq_word_refutation().unwrap();
    exec.execute_all(&ay_frontend::parse("(reset-assertions) (assert true)").unwrap())
        .unwrap();
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(!exec.install_consequence_replay_candidate(Some(candidate)));
    assert!(exec.last_proof.is_none());
}

#[test]
fn seq_word_presolve_rejects_an_ordinary_owner_of_a_native_spelling() {
    let mut exec = loaded("(not (<= 0 (seq.len a)))");
    let forged = exec.ctx.terms.mk_fresh_named_var("seq.len", Sort::Int);
    exec.ctx
        .register_symbol("seq.len".to_string(), forged, Sort::Int);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(exec.try_presolve_seq_word_refutation().is_none());
    assert!(exec.last_proof.is_none());
}

#[test]
fn seq_word_presolve_refuses_raw_declared_uf_metadata_without_context_symbol_info() {
    let mut exec = loaded("(not (<= 0 (seq.len a)))");
    assert!(exec.ctx.symbol_info_by_identity("seq.len").is_none());
    exec.context_mut()
        .terms
        .register_declared_function("seq.len");
    assert!(exec.ctx.symbol_info_by_identity("seq.len").is_none());
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(exec.try_presolve_seq_word_refutation().is_none());
    assert!(exec.last_proof.is_none());
}

#[test]
fn seq_word_presolve_checks_internal_ground_source_without_projection_authority() {
    let mut exec = loaded("(not (<= 0 (seq.len a)))");
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    let result = exec.check_sat().unwrap();
    assert!(result.is_unsat());
    assert!(!exec.last_check_saw_authored_query_authority());
    let proof = exec.last_proof.as_ref().unwrap();
    assert!(exec
        .check_proof_strict_with_datatypes(proof)
        .unwrap()
        .is_complete());
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(proof, &exec.ctx.assertions).is_ok()
    );
}

#[test]
fn seq_word_presolve_never_takes_a_soft_constraint_as_a_hard_premise() {
    let mut exec = loaded("true");
    exec.execute_all(&ay_frontend::parse("(assert-soft (not (<= 0 (seq.len a))))").unwrap())
        .unwrap();
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(exec.try_presolve_seq_word_refutation().is_none());
    assert!(exec.last_proof.is_none());
}
