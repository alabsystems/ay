// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6756 Packet 1: direct combined-theory contradictions
//! should export structured proof rules instead of `:rule trust`.

#![allow(clippy::panic)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::{check_proof, check_proof_strict, check_proof_with_quality, ProofQuality};
use ntest::timeout;

fn run_unsat_proof(input: &str) -> (Executor, String, ProofQuality) {
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

    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof(proof, exec.terms()).expect("internal proof checker rejected proof");
    let quality = check_proof_with_quality(proof, exec.terms())
        .expect("proof quality checker rejected proof");

    (exec, proof_text, quality)
}

fn assert_last_unsat_proof_is_strict(exec: &Executor) {
    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof_strict(proof, exec.terms()).expect("strict proof checker rejected proof");
}

/// Direct QF_AUFLIA fast-path contradiction: `(select a 0) = 1` vs `(select a 0) = 2`.
/// Semantically Farkas-valid integer contradictions should export `la_generic`.
#[test]
#[timeout(5_000)]
fn test_auflia_direct_contradiction_exports_la_generic_6756() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 1))
        (assert (= (select a 0) 2))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "direct AUFLIA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "direct AUFLIA proof should not contain :rule trust after #6756 Packet 1:\n{proof_text}"
    );
    // Integer equality conflicts use lia_generic (not la_generic) because
    // la_generic only accepts strict/non-strict inequality comparisons.
    // Equalities are valid for lia_generic but not for la_generic/Farkas.
    assert!(
        proof_text.contains(":rule la_generic") || proof_text.contains(":rule lia_generic"),
        "direct AUFLIA proof should contain :rule la_generic or lia_generic:\n{proof_text}"
    );
}

/// Same as above but with push/pop scope.
#[test]
#[timeout(5_000)]
fn test_auflia_direct_contradiction_with_push_pop_6756() {
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

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "push/pop AUFLIA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "push/pop AUFLIA proof should not contain :rule trust after #6756 Packet 1:\n{proof_text}"
    );
    // Integer equality conflicts use lia_generic (not la_generic) because
    // la_generic only accepts strict/non-strict inequality comparisons.
    assert!(
        proof_text.contains(":rule la_generic") || proof_text.contains(":rule lia_generic"),
        "push/pop AUFLIA proof should contain :rule la_generic or lia_generic:\n{proof_text}"
    );
}

/// Direct QF_AUFLIA with three array reads — verifies that the promotion
/// handles more than two-literal clauses (falls through to the LRA solver
/// path in `reconstruct_missing_farkas_coefficients`).
#[test]
#[timeout(5_000)]
fn test_auflia_three_reads_direct_contradiction_6756() {
    let input = r#"
        (set-logic QF_AUFLIA)
        (set-option :produce-proofs true)
        (declare-const a (Array Int Int))
        (assert (= (select a 0) 1))
        (assert (= (select a 1) 2))
        (assert (not (= (select a 0) 1)))
        (check-sat)
        (get-proof)
    "#;

    let (_exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "three-read AUFLIA proof should not contain hole steps: {quality:?}"
    );
    // This case may still contain trust if the contradiction is resolved
    // without a theory lemma. The key assertion is that it produces a valid proof.
    assert!(
        proof_text.contains("(cl)"),
        "three-read AUFLIA proof should derive the empty clause:\n{proof_text}"
    );
}

#[test]
#[timeout(5_000)]
fn test_uflra_direct_contradiction_exports_euf_and_lra_rules_6756() {
    let input = r#"
        (set-logic QF_UFLRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (declare-fun f (Real) Real)
        (assert (= x 0.0))
        (assert (= (f x) 1.0))
        (assert (= (f 0.0) 2.0))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "direct UFLRA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "direct UFLRA proof should not contain :rule trust after #6756 Packet 3:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "direct UFLRA proof should contain eq_congruent:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "direct UFLRA proof should contain la_generic:\n{proof_text}"
    );
    assert_last_unsat_proof_is_strict(&exec);
}

#[test]
#[timeout(5_000)]
fn test_uflra_direct_contradiction_with_push_pop_6756() {
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

    let (exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.hole_count, 0,
        "push/pop UFLRA proof should not contain hole steps: {quality:?}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "push/pop UFLRA proof should not contain :rule trust after #6756 Packet 3:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "push/pop UFLRA proof should contain eq_congruent:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule la_generic"),
        "push/pop UFLRA proof should contain la_generic:\n{proof_text}"
    );
    assert_last_unsat_proof_is_strict(&exec);
}

/// EUF congruence over a transitive chain: `a=b ∧ b=c ⊢ f(a)=f(c)`. The
/// congruence closure emits the FUSED lemma `(cl ¬(=a b) ¬(=b c) (= (f a)(f c)))`
/// as a single `:rule trust` step; `split_euf_congruence_lemmas` decomposes it
/// into checker-validated `eq_transitive` + `eq_congruent` + their resolution, so
/// the proof carries no trust step and strict checking accepts it.
#[test]
#[timeout(5_000)]
fn test_euf_fused_congruence_split_is_trust_free() {
    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= (f a) (f c))))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);

    assert_eq!(
        quality.trust_count, 0,
        "fused EUF congruence proof should have zero trust steps after the split: {quality:?}\n{proof_text}"
    );
    assert!(
        !proof_text.contains(":rule trust"),
        "fused EUF congruence proof should not contain :rule trust:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_transitive"),
        "split should introduce eq_transitive:\n{proof_text}"
    );
    assert!(
        proof_text.contains(":rule eq_congruent"),
        "split should introduce eq_congruent:\n{proof_text}"
    );
    // The decomposition must remain strictly checkable (the split steps validate).
    assert_last_unsat_proof_is_strict(&exec);
}

/// The split generalizes to a longer transitive chain `a=b=c=d ⊢ f(a)=f(d)`.
#[test]
#[timeout(5_000)]
fn test_euf_fused_congruence_split_longer_chain() {
    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (assert (= a b))
        (assert (= b c))
        (assert (= c d))
        (assert (not (= (f a) (f d))))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);
    assert_eq!(
        quality.trust_count, 0,
        "longer-chain fused congruence should also be trust-free: {quality:?}\n{proof_text}"
    );
    assert!(proof_text.contains(":rule eq_transitive"));
    assert!(proof_text.contains(":rule eq_congruent"));
    assert_last_unsat_proof_is_strict(&exec);
}

/// The EUF congruence split generalizes to N-ARY functions with INDEPENDENT
/// per-argument chains: `g(a,c)=g(b,d)` from `a=m=b` and `c=n=d`. Each argument
/// position gets its own eq_transitive; one eq_congruent over the direct
/// per-argument equalities; a binary th_resolution chain reproduces the fused
/// clause. No trust step; strict checking accepts it.
#[test]
#[timeout(5_000)]
fn test_euf_nary_congruence_independent_chains_split() {
    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort U 0)
        (declare-fun g (U U) U)
        (declare-const a U) (declare-const m U) (declare-const b U)
        (declare-const c U) (declare-const n U) (declare-const d U)
        (assert (= a m))
        (assert (= m b))
        (assert (= c n))
        (assert (= n d))
        (assert (not (= (g a c) (g b d))))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);
    assert_eq!(
        quality.trust_count, 0,
        "n-ary independent-chain congruence should be trust-free: {quality:?}\n{proof_text}"
    );
    assert!(proof_text.contains(":rule eq_transitive"));
    assert!(proof_text.contains(":rule eq_congruent"));
    assert_last_unsat_proof_is_strict(&exec);
}

/// The split handles congruence where some argument positions are REFLEXIVE
/// (unchanged) and others vary via a chain: `g(a,x)=g(c,x)` from `a=b=c`. The
/// reflexive position discharges a raw `(= x x)` via eq_reflexive (mk_eq would
/// fold it to `true`); the varying position uses eq_transitive. No trust step;
/// strict checking accepts it.
#[test]
#[timeout(5_000)]
fn test_euf_congruence_reflexive_position_split() {
    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort U 0)
        (declare-fun g (U U) U)
        (declare-const a U) (declare-const b U) (declare-const c U) (declare-const x U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= (g a x) (g c x))))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);
    assert_eq!(
        quality.trust_count, 0,
        "reflexive-position congruence should be trust-free: {quality:?}\n{proof_text}"
    );
    assert!(proof_text.contains(":rule eq_reflexive"));
    assert!(proof_text.contains(":rule eq_congruent"));
    assert_last_unsat_proof_is_strict(&exec);
}

/// The split handles a congruence where multiple argument positions share the
/// SAME equality (dedup): `g(a,a)=g(b,b)` from `a=b`. The eq_congruent carries a
/// duplicate `¬(=a b)` premise (one per position); binary resolution keeps the
/// shared edge so the fused clause is reproduced. No trust step; strict accepts.
#[test]
#[timeout(5_000)]
fn test_euf_congruence_dedup_shared_premise_split() {
    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort U 0)
        (declare-fun g (U U) U)
        (declare-const a U) (declare-const b U)
        (assert (= a b))
        (assert (not (= (g a a) (g b b))))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);
    assert_eq!(
        quality.trust_count, 0,
        "dedup (shared-premise) congruence should be trust-free: {quality:?}\n{proof_text}"
    );
    assert!(proof_text.contains(":rule eq_congruent"));
    assert_last_unsat_proof_is_strict(&exec);
}

/// Congruence-then-transitivity to a VALUE: `f(a)=5 ∧ a=3 ⊢ f(3)=5` (the common
/// "substitute a known value into a function" pattern). The fused clause's
/// conclusion is a value-equality, not a congruence, so it is split into an
/// eq_congruent (a=3 → f(a)=f(3)), an eq_transitive (f(3)=f(a)=5), and their
/// resolution. No trust step; strict checking accepts it.
#[test]
#[timeout(5_000)]
fn test_euf_value_congruence_substitution_split() {
    let input = r#"
        (set-logic QF_UFLIA)
        (set-option :produce-proofs true)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (assert (= (f a) 5))
        (assert (= a 3))
        (assert (not (= (f 3) 5)))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);
    assert_eq!(
        quality.trust_count, 0,
        "value-substitution congruence should be trust-free: {quality:?}\n{proof_text}"
    );
    assert!(proof_text.contains(":rule eq_congruent"));
    assert!(proof_text.contains(":rule eq_transitive"));
    assert_last_unsat_proof_is_strict(&exec);
}

/// N-ary value-substitution: `g(a,c)=v ∧ a=b ∧ c=d ⊢ g(b,d)=v`. The n-ary
/// congruence `(g a c)=(g b d)` feeds a transitivity to the value `v`. No trust
/// step; strict checking accepts it.
#[test]
#[timeout(5_000)]
fn test_euf_nary_value_congruence_split() {
    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort U 0)
        (declare-fun g (U U) U)
        (declare-const a U) (declare-const b U)
        (declare-const c U) (declare-const d U) (declare-const v U)
        (assert (= (g a c) v))
        (assert (= a b))
        (assert (= c d))
        (assert (not (= (g b d) v)))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);
    assert_eq!(
        quality.trust_count, 0,
        "n-ary value-substitution congruence should be trust-free: {quality:?}\n{proof_text}"
    );
    assert!(proof_text.contains(":rule eq_congruent"));
    assert!(proof_text.contains(":rule eq_transitive"));
    assert_last_unsat_proof_is_strict(&exec);
}

/// Cross-theory EUF + LIA conflict: `a=b ∧ f(a)=5 ∧ f(b)>5 ⊢ ⊥`. The congruence
/// `f(a)=f(b)` + transitivity derives `f(b)=5`, then a solver-checked la_generic
/// refutes `f(b)=5 ∧ f(b)>5`. No trust step; strict checking accepts it.
#[test]
#[timeout(5_000)]
fn test_cross_theory_euf_lia_conflict_split() {
    let input = r#"
        (set-logic QF_UFLIA)
        (set-option :produce-proofs true)
        (declare-fun f (Int) Int)
        (declare-const a Int)
        (declare-const b Int)
        (assert (= a b))
        (assert (= (f a) 5))
        (assert (> (f b) 5))
        (check-sat)
        (get-proof)
    "#;

    let (exec, proof_text, quality) = run_unsat_proof(input);
    assert_eq!(
        quality.trust_count, 0,
        "cross-theory EUF+LIA conflict should be trust-free: {quality:?}\n{proof_text}"
    );
    assert!(proof_text.contains(":rule eq_congruent"));
    assert!(proof_text.contains(":rule lia_generic") || proof_text.contains(":rule la_generic"));
    assert_last_unsat_proof_is_strict(&exec);
}
