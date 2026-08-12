// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{FarkasAnnotation, Sort, Symbol, TheoryLemmaKind};

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

#[test]
fn test_metered_premise_authentication_reports_dynamic_edges_and_bytes() {
    let mut terms = TermStore::new();
    let leaves: Vec<TermId> = (0..128)
        .map(|index| terms.mk_var(format!("metered_leaf_{index}"), Sort::Bool))
        .collect();
    let authored = terms.mk_app(Symbol::named("and"), leaves.clone(), Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(leaves[127], None);

    let mut reported_work = 0_usize;
    let mut reported_bytes = 0_usize;
    let authenticated = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[authored],
        &mut |work, bytes| {
            reported_work += work;
            reported_bytes += bytes;
            true
        },
    )
    .expect("a nested authored conjunct should authenticate within an unbounded envelope");

    assert_eq!(authenticated.step_count(), 1);
    assert!(reported_work >= leaves.len());
    assert!(reported_bytes >= leaves.len() * size_of::<TermId>());
}

#[test]
fn test_metered_premise_authentication_can_stop_on_dynamic_edge_payload() {
    let mut terms = TermStore::new();
    let leaves: Vec<TermId> = (0..256)
        .map(|index| terms.mk_var(format!("metered_cutoff_leaf_{index}"), Sort::Bool))
        .collect();
    let authored = terms.mk_app(Symbol::named("and"), leaves.clone(), Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(leaves[255], None);

    let edge_payload = leaves.len() * size_of::<TermId>();
    let mut saw_edge_payload = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[authored],
        &mut |_, bytes| {
            if bytes >= edge_payload {
                saw_edge_payload = true;
                false
            } else {
                true
            }
        },
    )
    .expect_err("the caller must be able to stop before accepting a large edge payload");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(saw_edge_payload);
}

#[test]
fn test_metered_premise_authentication_debits_private_bv_replay_budget() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("metered_bv16", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), vec![value, value], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let clause = vec![equality, negated];
    assert!(crate::bv_bitblast_requires_proof_producer(&terms, &clause));

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", clause, TheoryLemmaKind::BvBitBlast);
    let mut saw_private_budget = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if work
                == usize::try_from(crate::MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA)
                    .expect("published work fits usize")
                && bytes == crate::MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
            {
                saw_private_budget = true;
                false
            } else {
                true
            }
        },
    )
    .expect_err("the aggregate envelope must be debited before private BV replay");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(saw_private_budget);
}

#[test]
fn test_bv_classifier_meter_is_debited_before_budget_classification() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("metered_bv_classifier", Sort::bitvec(16));
    let equality = terms.mk_app(Symbol::named("="), vec![value, value], Sort::Bool);
    let negated = terms.mk_not_raw(equality);
    let clause = vec![equality, negated];

    // Nine proof-producing lemmas exceed the private replay aggregate cap. A
    // callback that rejects the classifier debit must therefore observe
    // ResourceLimit before that unmetered classification can report the cap.
    let mut proof = Proof::new();
    for _ in 0..9 {
        proof.add_theory_lemma_with_kind("BV", clause.clone(), TheoryLemmaKind::BvBitBlast);
    }
    let authentication_stats =
        meter_authentication_payload(&proof, &terms, None, None, Some(&[]), &mut |_, _| true)
            .expect("small payload census should fit usize");
    let classifier_charge =
        proof_producing_bv_classifier_charge(&proof, authentication_stats.aggregate)
            .expect("small classifier charge should fit usize");
    assert!(classifier_charge.0 > 0);
    assert!(classifier_charge.1 > 0);

    let mut saw_classifier_charge = false;
    let error = authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        &mut |work, bytes| {
            if (work, bytes) == classifier_charge {
                saw_classifier_charge = true;
                false
            } else {
                true
            }
        },
    )
    .expect_err("classification must not run before its caller-owned debit");

    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(saw_classifier_charge);
}

#[test]
fn test_semantic_meter_charges_repeated_edge_matching_quadratically() {
    let step = ProofStep::Step {
        rule: AletheRule::AndNeg,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    let payload = PayloadStats {
        work: 257,
        bytes: 4096,
        unfolded_work: 257,
    };
    let (work, bytes) = semantic_validator_charge(&step, payload, SemanticChargeClass::General)
        .expect("small checked products should fit usize");
    assert!(work >= 257 * 257);
    assert!(bytes >= payload.bytes);
}

#[test]
fn test_datatype_registry_meter_covers_all_declaration_backed_kinds() {
    let payload = PayloadStats {
        work: 11,
        bytes: 128,
        unfolded_work: 7,
    };
    let datatype_registry = RegistryPayloadStats {
        work: 37,
        bytes: 512,
    };
    let selector_registry = RegistryPayloadStats {
        work: 19,
        bytes: 256,
    };

    for kind in [
        TheoryLemmaKind::DatatypeDistinct,
        TheoryLemmaKind::DatatypeSelectorProject,
        TheoryLemmaKind::DatatypeTesterEval,
    ] {
        let step = ProofStep::TheoryLemma {
            theory: "DT".to_string(),
            clause: Vec::new(),
            farkas: None,
            kind,
            lia: None,
        };
        let (work, bytes) =
            datatype_registry_charge(&step, payload, datatype_registry, selector_registry)
                .expect("small registry products should fit usize");
        assert_eq!(work, (37 + 19) * payload.work);
        assert_eq!(bytes, payload.bytes * 8);
    }
}

#[test]
fn test_string_ground_meter_covers_decoding_clones_and_tables() {
    let step = ProofStep::TheoryLemma {
        theory: "Strings".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::StringGroundEval,
        lia: None,
    };
    let payload = PayloadStats {
        work: 23,
        bytes: 4096,
        unfolded_work: 23,
    };
    let (work, bytes) = semantic_validator_charge(&step, payload, SemanticChargeClass::General)
        .expect("small string payload products should fit usize");
    let table_overhead = crate::checker::STRING_EVAL_WORK_LIMIT * 96;
    let char_allocation = crate::checker::STRING_CHAR_ALLOCATION_LIMIT * size_of::<char>();
    let numeric_allocation = crate::checker::STRING_NUMERIC_BIT_ALLOCATION_LIMIT.div_ceil(8);
    let private_work = crate::checker::STRING_EVAL_WORK_LIMIT
        + crate::checker::STRING_CHAR_ALLOCATION_LIMIT
        + crate::checker::STRING_NUMERIC_WORK_LIMIT;

    assert!(work >= private_work);
    assert!(bytes >= table_overhead + char_allocation + numeric_allocation + payload.bytes * 16);
    assert!(bytes >= table_overhead + char_allocation + numeric_allocation + payload.bytes * 12);
}

#[test]
fn test_order_ite_meter_uses_complete_preorder_enumeration_factor() {
    let step = ProofStep::TheoryLemma {
        theory: "Order".to_string(),
        clause: Vec::new(),
        farkas: None,
        kind: TheoryLemmaKind::OrderIteTautology,
        lia: None,
    };
    let payload = PayloadStats {
        work: 17,
        bytes: 31,
        unfolded_work: 13,
    };
    let base_work =
        (payload.work * payload.unfolded_work).max(payload.unfolded_work * payload.unfolded_work);
    let (work, bytes) = semantic_validator_charge(&step, payload, SemanticChargeClass::General)
        .expect("small order-ITE products should fit usize");

    assert_eq!(work, base_work * 46_656);
    assert_eq!(bytes, payload.bytes * 46_656);
}

#[test]
fn test_ext_diff_meter_multiplies_reachable_payload_per_binding() {
    let mut terms = TermStore::new();
    let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Bool)));
    let witness = terms.mk_var("metered_ext_witness", Sort::Int);
    let left = terms.mk_var("metered_ext_left", array_sort.clone());
    let right = terms.mk_var("metered_ext_right", array_sort);
    let proof = Proof::from_steps(vec![ProofStep::Step {
        rule: AletheRule::ArrayExtDiffIntro,
        clause: Vec::new(),
        premises: Vec::new(),
        args: vec![witness, left, right],
    }]);
    let payload = PayloadStats {
        work: 100,
        bytes: 200,
        unfolded_work: 100,
    };

    let (work, bytes) = ext_diff_registry_charge(&proof, &terms, payload)
        .expect("small checked products should fit usize");
    assert!(work > 2 * payload.work);
    assert!(bytes >= 2 * payload.bytes);
}

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

#[test]
fn test_check_proof_with_quality_theory_lemma_verified() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    // Use LraFarkas — a verified theory lemma kind (exports as la_generic, not trust)
    let tl = proof.add_theory_lemma_with_farkas_and_kind(
        "LRA",
        vec![not_x],
        FarkasAnnotation::from_ints(&[1]),
        TheoryLemmaKind::LraFarkas,
    );
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, tl], vec![]);

    let quality =
        check_proof_with_quality(&proof, &terms).expect("th_resolution proof should pass");

    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.assume_count, 1);
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.th_resolution_count, 1);
    assert!(quality.is_complete());
}

#[test]
fn test_check_proof_with_quality_theory_lemma_trust_kind() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    // Generic theory lemma exports as trust — should be counted (#5657)
    let tl = proof.add_theory_lemma("BV", vec![not_x]);
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, tl], vec![]);

    let quality =
        check_proof_with_quality(&proof, &terms).expect("th_resolution proof should pass");

    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.theory_lemma_count, 1);
    assert_eq!(
        quality.trust_count, 1,
        "Generic theory lemma should count as trust (#5657)"
    );
    assert!(
        !quality.is_complete(),
        "proof with trust-exported theory lemma is not complete"
    );
}

#[test]
fn test_has_trust_steps_true_for_generic_theory_lemma() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    // Generic theory lemma exports as trust
    let tl = proof.add_theory_lemma("BV", vec![not_x]);
    proof.add_rule_step(AletheRule::ThResolution, vec![], vec![h0, tl], vec![]);

    let quality = check_proof_with_quality(&proof, &terms).expect("quality check should pass");
    assert!(
        quality.has_trust_steps(),
        "has_trust_steps should be true when Generic theory lemma present"
    );
    assert_eq!(quality.trust_theory_kinds.len(), 1);
    assert_eq!(quality.trust_theory_kinds[0], TheoryLemmaKind::Generic);
}

#[test]
fn test_has_trust_steps_false_for_verified_proof() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let p0 = proof.add_assume(x, None);
    let p1 = proof.add_assume(not_x, None);
    proof.add_resolution(vec![], x, p0, p1);

    let quality = check_proof_with_quality(&proof, &terms).expect("valid proof should pass");
    assert!(
        !quality.has_trust_steps(),
        "has_trust_steps should be false for fully verified proof"
    );
    assert!(quality.trust_theory_kinds.is_empty());
}

#[test]
fn test_strict_proof_mode_rejects_trust() {
    let quality = ProofQuality {
        trust_count: 2,
        trust_theory_kinds: vec![TheoryLemmaKind::Generic, TheoryLemmaKind::Generic],
        ..ProofQuality::default()
    };

    let err = quality
        .check_strict_proof_mode(true)
        .expect_err("strict mode should reject trust steps");
    let msg = format!("{err}");
    assert!(
        msg.contains("strict proof mode"),
        "error should mention strict proof mode: {msg}"
    );
    assert!(
        msg.contains("Generic"),
        "error should identify the theory lemma kind: {msg}"
    );
    assert!(
        msg.contains("2 trust step(s)"),
        "error should count trust steps: {msg}"
    );
}

#[test]
fn test_strict_proof_mode_passes_when_disabled() {
    let quality = ProofQuality {
        trust_count: 5,
        trust_theory_kinds: vec![TheoryLemmaKind::Generic],
        ..ProofQuality::default()
    };

    quality
        .check_strict_proof_mode(false)
        .expect("strict mode disabled should pass even with trust steps");
}

#[test]
fn test_strict_proof_mode_passes_with_no_trust() {
    let quality = ProofQuality {
        resolution_count: 10,
        assume_count: 5,
        total_steps: 15,
        ..ProofQuality::default()
    };

    quality
        .check_strict_proof_mode(true)
        .expect("strict mode should pass when no trust steps");
}

#[test]
fn test_strict_proof_mode_identifies_sat_trust_steps() {
    // Trust steps from SAT proof reconstruction (not theory lemmas)
    let quality = ProofQuality {
        trust_count: 3,
        trust_theory_kinds: vec![TheoryLemmaKind::Generic],
        ..ProofQuality::default()
    };

    let err = quality
        .check_strict_proof_mode(true)
        .expect_err("strict mode should reject");
    let msg = format!("{err}");
    assert!(
        msg.contains("SAT proof reconstruction"),
        "error should note additional SAT trust steps: {msg}"
    );
}

#[test]
fn test_proof_quality_display() {
    let quality = ProofQuality {
        assume_count: 2,
        resolution_count: 3,
        th_resolution_count: 1,
        theory_lemma_count: 1,
        trust_count: 0,
        trust_fallback_count: 0,
        hole_count: 0,
        drup_count: 0,
        other_rule_count: 0,
        total_steps: 7,
        trust_theory_kinds: vec![],
    };

    let display = format!("{quality}");
    assert!(display.contains("steps=7"));
    assert!(display.contains("verified=4"));
    assert!(display.contains("axiom=3"));
    assert!(display.contains("fallback=0"));
}
