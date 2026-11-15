// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end authored scopes from the scalar UF/array certificate rejection.

use std::time::Duration;

use ay_core::TermId;

use crate::{Executor, VerificationLevel};

// These are the rendered authored roots, not pre-certified planner inputs.
// QF3 and full4 differ only by the retained forall at its original position.
const DECLARATIONS: &str = r#"
(set-logic ALL)
(declare-fun f (Bool (_ BitVec 8)) (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun fill () (_ BitVec 8))
(declare-fun length () (_ BitVec 64))
(declare-fun a () (Array (_ BitVec 64) (_ BitVec 8)))
(declare-fun __gpc1 () (_ BitVec 64))
"#;
const ASSIGNMENT: &str = "(assert (and (= fill (f true x)) (= length #x0000000000000041)))";
const QUANTIFIED: &str = "(assert (forall ((ay!source!0_8 (_ BitVec 64)) (ay!source!1_9 (_ BitVec 64))) (or (= (f true x) (select a ay!source!0_8)) (not (bvult ay!source!0_8 length)))))";
const GUARDED_READ: &str =
    "(assert (or (= (f true x) (select a __gpc1)) (not (bvult __gpc1 length))))";
const COUNTEREXAMPLE: &str = "(assert (or (and (bvult __gpc1 length) (bvule #x0000000000000020 __gpc1) (not (= fill (select a __gpc1)))) (= length #x0000000000000000)))";

fn input(roots: &[&str]) -> String {
    format!("{DECLARATIONS}\n{}\n", roots.join("\n"))
}

fn prepared(source: &str, expected_roots: usize) -> (Executor, Vec<TermId>) {
    let commands = ay_frontend::parse(source).expect("captured source parses");
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    executor.set_verification_level(VerificationLevel::ProofChecked);
    executor.set_timeout(Some(Duration::from_secs(30)));
    executor.set_term_memory_limit(Some(128 * 1024 * 1024));
    let outputs = executor
        .execute_all(&commands)
        .expect("ordinary authored declarations and assertions execute");
    assert!(outputs.is_empty());
    let authored = executor.context().assertions.clone();
    assert_eq!(authored.len(), expected_roots);
    (executor, authored)
}

fn assert_strict_complete(source: &str, expected_roots: usize) {
    let (mut executor, authored) = prepared(source, expected_roots);
    let result = executor
        .execute(&ay_frontend::Command::CheckSat)
        .expect("captured check-sat executes");
    assert_eq!(
        result.as_deref(),
        Some("unsat"),
        "exact source must publish a checked refutation: origin={:?}, reason={:?}",
        executor.unknown_origin(),
        executor.unknown_reason()
    );
    let proof = executor
        .last_proof()
        .expect("proof-requested UNSAT retains the complete refutation");
    // A rewritten guard or flattened child is not an additional assumption.
    // This checks the original captured roots, independently of the executor's
    // own expanded strict-check scope or any deferred-trust rescue.
    ay_proof::validate_reachable_assumes_in_problem_scope(proof, &authored)
        .expect("every reachable assumption belongs to the exact authored scope");
    let quality = executor
        .check_proof_strict_with_datatypes(proof)
        .expect("the actual strict checker accepts without deferred-trust rescue");
    assert!(quality.is_complete(), "strict proof quality: {quality:?}");
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
}

fn assert_sat(source: &str, expected_roots: usize) {
    let (mut executor, _) = prepared(source, expected_roots);
    let result = executor
        .execute(&ay_frontend::Command::CheckSat)
        .expect("mutated check-sat executes");
    assert_eq!(
        result.as_deref(),
        Some("sat"),
        "satisfiable mutation cannot borrow the old refutation: origin={:?}, reason={:?}",
        executor.unknown_origin(),
        executor.unknown_reason()
    );
    assert!(executor.was_model_validated());
    assert!(executor.last_proof().is_none());
}

#[test]
fn captured_qf3_has_strict_complete_exact_scope_refutation() {
    assert_strict_complete(&input(&[ASSIGNMENT, GUARDED_READ, COUNTEREXAMPLE]), 3);
}

#[test]
fn captured_full4_has_strict_complete_exact_scope_refutation() {
    assert_strict_complete(
        &input(&[ASSIGNMENT, QUANTIFIED, GUARDED_READ, COUNTEREXAMPLE]),
        4,
    );
}

#[test]
fn captured_qf3_wrong_value_mutation_is_validated_sat() {
    let matching = COUNTEREXAMPLE.replace(
        "(not (= fill (select a __gpc1)))",
        "(= fill (select a __gpc1))",
    );
    assert_ne!(matching, COUNTEREXAMPLE);
    // length=65, index=32, fill=f(true,x)=a[index]=0 is a model.
    assert_sat(&input(&[ASSIGNMENT, GUARDED_READ, &matching]), 3);
}

#[test]
fn captured_full4_wrong_value_mutation_never_borrows_a_refutation() {
    let matching = COUNTEREXAMPLE.replace(
        "(not (= fill (select a __gpc1)))",
        "(= fill (select a __gpc1))",
    );
    assert_ne!(matching, COUNTEREXAMPLE);
    // Constant-zero f and a satisfy the entire two-binder forall as well.
    // The measured pre-change public standalone returns QuantifierUnhandled
    // for this SAT case. Deciding that quantified SAT fragment is a separate
    // open capability; this control only forbids an unsound reused refutation.
    // The standalone diagnostic retains its stronger validated-SAT requirement.
    let (mut executor, _) = prepared(
        &input(&[ASSIGNMENT, QUANTIFIED, GUARDED_READ, &matching]),
        4,
    );
    let result = executor
        .execute(&ay_frontend::Command::CheckSat)
        .expect("quantified mutation executes");
    assert!(matches!(result.as_deref(), Some("sat" | "unknown")));
    if result.as_deref() == Some("sat") {
        assert!(executor.was_model_validated());
    }
    assert!(executor.last_proof().is_none());
}

#[test]
fn captured_qf3_absent_guard_is_validated_sat() {
    // With the middle root absent, a constant-one array and constant-zero f
    // satisfy the original disagreement at index32. No missing guard is an axiom.
    assert_sat(&input(&[ASSIGNMENT, COUNTEREXAMPLE]), 2);
}
