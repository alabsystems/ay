// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{FarkasAnnotation, Sort, Symbol, TheoryLemmaKind};

#[path = "quality_tests/typed_context.rs"]
mod typed_context;

#[test]
fn test_check_proof_with_quality_resolution_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![], x, p0, p1);

    let quality = check_proof_with_quality(&proof, &terms).expect("valid proof should pass");

    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.assume_count, 2);
    assert_eq!(quality.resolution_count, 1);
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
    assert!(quality.is_complete());
    assert_eq!(quality.verified_count(), 1);
    assert_eq!(quality.axiom_count(), 2);
    assert_eq!(quality.fallback_count(), 0);
}

#[test]
fn test_check_proof_with_quality_trust_step() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    proof.add_rule_step(AletheRule::Trust, vec![not_x], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Drup, vec![], vec![], vec![]);

    let quality =
        check_proof_with_quality(&proof, &terms).expect("trust in non-strict should pass");

    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.assume_count, 1);
    assert_eq!(quality.trust_count, 1);
    assert_eq!(quality.trust_fallback_count, 0);
    assert_eq!(quality.drup_count, 1);
    assert!(!quality.is_complete());
    assert_eq!(quality.fallback_count(), 1);
}

#[test]
fn test_check_proof_with_quality_trust_fallback_with_premises() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);
    let not_y = terms.mk_not(y);

    let mut proof = Proof::new();
    let hx = proof.add_assume(x, None);
    let hy = proof.add_assume(y, None);
    let trust = proof.add_rule_step(
        AletheRule::Trust,
        vec![not_x, not_y],
        vec![hx, hy],
        Vec::new(),
    );
    let r0 = proof.add_resolution(vec![not_y], x, trust, hx);
    proof.add_resolution(vec![], y, r0, hy);

    let quality = check_proof_with_quality(&proof, &terms).expect("quality check succeeds");
    assert_eq!(quality.trust_count, 1);
    assert_eq!(
        quality.trust_fallback_count, 1,
        "trust steps with premises should be counted as hint fallbacks"
    );
}

#[test]
fn test_check_proof_strict_rejects_trust() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    proof.add_assume(x, None);
    proof.add_rule_step(AletheRule::Trust, vec![not_x], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Drup, vec![], vec![], vec![]);

    let err = check_proof_strict(&proof, &terms).expect_err("strict mode must reject trust steps");
    assert!(
        matches!(err, ProofCheckError::TrustStep { .. }),
        "expected TrustStep error, got: {err:?}"
    );
}

#[test]
fn test_check_proof_strict_accepts_complete_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![], x, p0, p1);

    let quality = check_proof_strict(&proof, &terms).expect("complete proof should pass strict");

    assert!(quality.is_complete());
    assert_eq!(quality.resolution_count, 1);
}

#[test]
fn test_premise_authentication_accepts_authored_non_refutation() {
    let mut terms = TermStore::new();
    let authored = terms.mk_var("authored_fragment_premise", Sort::Bool);
    let mut proof = Proof::new();
    let authored_step = proof.add_assume(authored, None);

    let authenticated =
        authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[authored])
            .expect("an exact authored premise should authenticate");

    assert_eq!(authenticated.step_count(), 1);
    assert_eq!(
        authenticated.clause(authored_step),
        Some([authored].as_slice())
    );
    assert_eq!(authenticated.clause(ProofId(1)), None);
    assert!(matches!(
        check_proof_strict_with_context(&proof, &terms, None, None, Some(&[authored])),
        Err(ProofCheckError::FinalClauseNotEmpty { .. })
    ));
}

#[test]
fn test_premise_authentication_accepts_supported_clausification() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("fragment_clausification_a", Sort::Bool);
    let b = terms.mk_var("fragment_clausification_b", Sort::Bool);
    let authored_or = terms.mk_app(Symbol::named("or"), vec![a, b], Sort::Bool);
    let mut proof = Proof::new();
    let assume = proof.add_assume(authored_or, None);
    let clause = proof.add_rule_step(AletheRule::Or, vec![a, b], vec![assume], Vec::new());

    let authenticated = authenticate_premise_clauses_strict_with_context(
        &proof,
        &terms,
        None,
        None,
        &[authored_or],
    )
    .expect("supported clausification should authenticate");

    assert_eq!(authenticated.clause(assume), Some([authored_or].as_slice()));
    assert_eq!(authenticated.clause(clause), Some([a, b].as_slice()));
}

#[test]
fn test_premise_authentication_accepts_supported_theory_lemma() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("fragment_bool_tautology_p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let mut proof = Proof::new();
    let lemma =
        proof.add_theory_lemma_with_kind("bool", vec![p, not_p], TheoryLemmaKind::BoolTautology);

    let authenticated =
        authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[])
            .expect("a strictly checked Boolean tautology should authenticate");

    assert_eq!(authenticated.clause(lemma), Some([p, not_p].as_slice()));
}

#[test]
fn test_premise_authentication_separates_generic_theory_obligation() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("fragment_deferred_generic_p", Sort::Bool);
    let mut proof = Proof::new();
    let generic = proof.add_theory_lemma_with_kind("theory", vec![p], TheoryLemmaKind::Generic);

    assert!(
        authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[],).is_err()
    );

    let deferred = authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |_, _| true,
    )
    .expect("only the exact Generic theory premise should be deferred");

    assert_eq!(deferred.step_count(), 1);
    assert_eq!(deferred.strictly_authenticated_clause(generic), None);
    assert_eq!(
        deferred.deferred_generic_clause(generic),
        Some([p].as_slice())
    );
    assert_eq!(
        deferred.deferred_generic_clauses().collect::<Vec<_>>(),
        vec![(generic, [p].as_slice())]
    );
}

#[test]
fn test_deferred_generic_premise_authentication_still_rejects_explicit_trust() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("fragment_explicit_trust_p", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p], Vec::new(), Vec::new());

    let error = authenticate_premise_clauses_with_deferred_generic_theory_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |_, _| true,
    )
    .expect_err("explicit trust must not enter the narrow Generic-theory lane");

    assert!(matches!(error, ProofCheckError::TrustStep { .. }));
}

#[path = "quality_tests/metering_dynamic.rs"]
mod metering_dynamic;

#[path = "quality_tests/metering_semantic.rs"]
mod metering_semantic;

#[path = "quality_tests/metering_tightening.rs"]
mod metering_tightening;

#[test]
fn test_premise_authentication_rejects_unauthorized_assume() {
    let mut terms = TermStore::new();
    let authored = terms.mk_var("fragment_authored", Sort::Bool);
    let foreign = terms.mk_var("fragment_foreign", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(foreign, None);

    let err =
        authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[authored])
            .expect_err("a foreign assumption must not authenticate");

    assert_eq!(
        err,
        ProofCheckError::UnauthorizedAssumption {
            step: ProofId(0),
            term: foreign,
        }
    );
}

#[test]
fn test_premise_authentication_rejects_trust_and_hole() {
    for rule in [AletheRule::Trust, AletheRule::Hole] {
        let mut terms = TermStore::new();
        let p = terms.mk_var("fragment_unverified", Sort::Bool);
        let mut proof = Proof::new();
        proof.add_rule_step(rule.clone(), vec![p], Vec::new(), Vec::new());

        let err = authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[])
            .expect_err("unverified steps must not authenticate");

        assert!(
            matches!(
                (rule, err),
                (AletheRule::Trust, ProofCheckError::TrustStep { .. })
                    | (AletheRule::Hole, ProofCheckError::HoleStep { .. })
            ),
            "unexpected strict rejection"
        );
    }
}

#[test]
fn test_premise_authentication_rejects_invalid_rule() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("fragment_unvalidated_rule", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::AllSimplify, vec![p], Vec::new(), Vec::new());

    let err = authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[])
        .expect_err("an unvalidated rule must not authenticate");

    assert!(matches!(err, ProofCheckError::UnvalidatedRule { .. }));
}

#[test]
fn test_premise_authentication_rejects_future_and_missing_premises() {
    for premise in [ProofId(1), ProofId(99)] {
        let mut terms = TermStore::new();
        let p = terms.mk_var("fragment_bad_premise", Sort::Bool);
        let not_p = terms.mk_not_raw(p);
        let proof = Proof::from_steps(vec![
            ProofStep::Step {
                rule: AletheRule::Resolution,
                clause: Vec::new(),
                premises: vec![premise, premise],
                args: vec![p],
            },
            ProofStep::Assume(not_p),
        ]);

        let err =
            authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[not_p])
                .expect_err("future and missing premise identities must not authenticate");

        assert_eq!(
            err,
            ProofCheckError::MissingPremise {
                step: ProofId(0),
                premise,
            }
        );
    }
}

#[test]
fn test_premise_authentication_rejects_reused_skolem_witness() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("fragment_sko_x", Sort::Int);
    let p_x = terms.mk_app(Symbol::named("fragment_sko_p"), [x], Sort::Bool);
    let forall_p = terms.mk_forall(vec![("fragment_sko_x".to_string(), Sort::Int)], p_x);

    let witness = terms.mk_var("sk!fragment_reused", Sort::Int);
    terms.mark_skolem_symbol("sk!fragment_reused");
    let p_witness = terms.mk_app(Symbol::named("fragment_sko_p"), [witness], Sort::Bool);
    let first_binding = terms.mk_eq(forall_p, p_witness);

    let y = terms.mk_var("fragment_sko_y", Sort::Int);
    let q_y = terms.mk_app(Symbol::named("fragment_sko_q"), [y], Sort::Bool);
    let forall_q = terms.mk_forall(vec![("fragment_sko_y".to_string(), Sort::Int)], q_y);
    let q_witness = terms.mk_app(Symbol::named("fragment_sko_q"), [witness], Sort::Bool);
    let second_binding = terms.mk_eq(forall_q, q_witness);

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::Skolem,
        vec![first_binding],
        Vec::new(),
        vec![witness],
    );
    proof.add_rule_step(
        AletheRule::Skolem,
        vec![second_binding],
        Vec::new(),
        vec![witness],
    );

    let error = authenticate_premise_clauses_strict_with_context(&proof, &terms, None, None, &[])
        .expect_err("one witness must not authenticate two incompatible forall sources");
    assert!(
        matches!(error, ProofCheckError::InvalidBooleanRule { .. }),
        "unexpected strict rejection: {error:?}"
    );
}

#[path = "quality_tests/quality_summary.rs"]
mod quality_summary;
