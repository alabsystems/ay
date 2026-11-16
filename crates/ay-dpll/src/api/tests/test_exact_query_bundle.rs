// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-parse binding tests for portable strict proof bundles.

use crate::api::*;
use ay_core::{ProofStep, TheoryLemmaKind};

const FOLDED_FALSE: &str = r#"
    (define-fun Inv ((__p0_a0 Int)) Bool
      (and (>= __p0_a0 0) (not (> __p0_a0 10))))
    (declare-const x Int)
    (assert (and (>= x 0) (not (> x 10)) (> x 10)))
    (check-sat)
    (exit)
"#;

const SIMPLE_UNSAT: &str = r#"
    (declare-const x Int)
    (assert (> x 5))
    (assert (< x 3))
    (check-sat)
"#;

/// `ubv_to_int`, not `bv2nat`: the two elaborate to one term, and only the
/// first is in pinned Carcara's grammar, which strict proofs require.
const PINNED_U16_BV_LIA: &str = r#"
    (declare-const result (_ BitVec 16))
    (declare-const x (_ BitVec 16))
    (assert (= x #x9c40))
    (assert (= x result))
    (assert (<= (* (ubv_to_int x) 2) 65535))
"#;

fn proof_solver() -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict proof option");
    solver
}

#[test]
fn source_folded_false_bundle_is_bound_through_exact_parse_provenance() {
    let mut solver = proof_solver();
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(FOLDED_FALSE)
        .expect("exact folded-false parse");
    assert_eq!(binding.assertions().len(), 1);
    assert!(solver.check_sat().is_unsat());

    let bundle = solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .expect("source-rebuilt Assume must remain bound to its exact folded root");
    let checked = re_check_bundle_strict(&bundle).expect("bound bundle recheck");
    assert!(checked.quality.is_complete());
    assert_ne!(checked.assume_terms, [] as [TermId; 0]);
    assert_eq!(checked.assume_terms, bundle.obligation_assertions);
    assert_ne!(
        bundle.obligation_assertions,
        binding
            .assertions()
            .iter()
            .map(|term| term.id())
            .collect::<Vec<_>>(),
        "fixture must exercise an authenticated source-rebuild id distinct from the folded root"
    );

    let mut missing_authority = bundle.clone();
    missing_authority.obligation_assertions.clear();
    assert!(re_check_bundle_strict(&missing_authority).is_err());
    let mut mutated_proof = bundle;
    mutated_proof.steps.pop().expect("non-empty proof");
    assert!(re_check_bundle_strict(&mutated_proof).is_err());
}

#[test]
fn exact_query_binding_rejects_foreign_stale_or_mutated_tokens() {
    let mut solver = proof_solver();
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("exact parse");
    assert!(solver.check_sat().is_unsat());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_some());

    let mut sibling = proof_solver();
    let sibling_binding = sibling
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("sibling exact parse");
    assert!(sibling.check_sat().is_unsat());
    assert!(sibling
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&sibling_binding)
        .is_none());

    let mut missing = binding.clone();
    missing.assertions.clear();
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&missing)
        .is_none());
    let mut duplicated = binding.clone();
    duplicated.assertions.push(duplicated.assertions[0]);
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&duplicated)
        .is_none());

    solver.try_reset().expect("full reset");
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
}

#[test]
fn exact_query_binding_rejects_post_parse_assertion_or_declaration() {
    let mut assertion_mutated = proof_solver();
    let assertion_binding = assertion_mutated
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("exact parse");
    assertion_mutated
        .parse_smtlib2("(assert true)")
        .expect("post-parse assertion");
    assert!(assertion_mutated.check_sat().is_unsat());
    assert!(assertion_mutated
        .export_last_unsat_bundle_for_exact_query(&assertion_binding)
        .is_none());

    let mut declaration_mutated = proof_solver();
    let declaration_binding = declaration_mutated
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .expect("exact parse");
    declaration_mutated
        .try_declare_const("late", Sort::Int)
        .expect("post-parse declaration");
    assert!(declaration_mutated.check_sat().is_unsat());
    assert!(declaration_mutated
        .export_last_unsat_bundle_for_exact_query(&declaration_binding)
        .is_none());
}

#[test]
fn exact_query_binding_requires_an_initially_empty_plain_formula_state() {
    let mut solver = proof_solver();
    solver
        .parse_smtlib2("(assert true)")
        .expect("pre-existing assertion");
    assert!(solver
        .parse_smtlib2_with_exact_query_binding(SIMPLE_UNSAT)
        .is_err());
}

#[test]
fn exact_qf_ufbvlia_native_bundle_roundtrips_with_honest_alethe_hole() {
    let mut solver = Solver::try_new(Logic::QfUfbvlia).expect("QF_UFBVLIA solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict native proof option");
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(PINNED_U16_BV_LIA)
        .expect("exact pinned u16 parse");

    assert!(solver.check_sat().is_unsat());
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("native BV/LIA artifact");
    assert!(matches!(
        &artifact.strict_verdict,
        StrictProofVerdict::Verified(quality) if quality.is_complete()
    ));
    assert_eq!(artifact.alethe.matches(":rule hole").count(), 1);
    assert!(!artifact.alethe.contains(":rule trust"));
    assert!(!artifact.alethe.contains(":rule bv_lia_tautology"));
    assert!(!artifact.restricted_rule_subset);
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
        Ok(())
    );
    assert_eq!(
        artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
        Err(ProofAcceptanceError::NotRestrictedRuleSubset)
    );

    let bundle = solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .expect("exact source-bound native bundle");
    let json = serde_json::to_string(&bundle).expect("serialize native bundle");
    let restored: SerializableProofBundle =
        serde_json::from_str(&json).expect("deserialize native bundle");
    let checked = re_check_bundle_strict(&restored).expect("offline native bundle replay");
    assert!(checked.quality.is_complete());
    assert_eq!(checked.assume_terms, restored.obligation_assertions);
    assert_ne!(checked.assume_terms, [] as [TermId; 0]);

    let root_count = restored.obligation_assertions.len();
    assert_eq!(restored.steps.len(), root_count * 2 + 1);
    for (&root, step) in restored
        .obligation_assertions
        .iter()
        .zip(&restored.steps[..root_count])
    {
        assert!(matches!(step, ProofStep::Assume(actual) if *actual == root));
    }
    assert!(matches!(
        &restored.steps[root_count],
        ProofStep::TheoryLemma {
            theory,
            clause,
            farkas: None,
            kind: TheoryLemmaKind::BvLiaTautology,
            lia: None,
        } if theory == "BV_LIA" && clause.len() == root_count
    ));
    assert!(restored.steps[root_count + 1..]
        .iter()
        .all(|step| matches!(step, ProofStep::Resolution { .. })));
    assert!(matches!(
        restored.steps.last(),
        Some(ProofStep::Resolution { clause, .. }) if clause.is_empty()
    ));

    let mut missing_obligation = restored.clone();
    missing_obligation.obligation_assertions.clear();
    assert!(re_check_bundle_strict(&missing_obligation).is_err());
    let mut wrong_theorem = restored.clone();
    let ProofStep::TheoryLemma { kind, .. } = &mut wrong_theorem.steps[root_count] else {
        panic!("canonical BV/LIA theorem step");
    };
    *kind = TheoryLemmaKind::Generic;
    assert!(re_check_bundle_strict(&wrong_theorem).is_err());
    let mut missing_terminal = restored;
    missing_terminal.steps.pop();
    assert!(re_check_bundle_strict(&missing_terminal).is_err());

    solver
        .parse_smtlib2("(assert true)")
        .expect("late assertion mutation");
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
}

#[test]
fn exact_native_bv_lia_bundle_depends_on_source_not_logic_label_or_query_origin() {
    for logic in [Logic::QfUfbvlia, Logic::Uflia, Logic::All] {
        for internal in [false, true] {
            let mut solver = Solver::try_new(logic).expect("mixed BV/LIA solver");
            solver.set_produce_proofs(true);
            solver
                .try_set_option(":check-proofs-strict", "true")
                .expect("strict native proof option");
            let binding = solver
                .parse_smtlib2_with_exact_query_binding(PINNED_U16_BV_LIA)
                .expect("exact pinned u16 parse");

            let result = if internal {
                solver.check_sat_internal_query()
            } else {
                solver.check_sat()
            };
            assert!(result.is_unsat(), "logic {logic:?}, internal {internal}");
            assert_eq!(
                solver.executor.last_check_saw_authored_query_authority(),
                !internal,
                "native bundle certification must preserve the query-origin boundary"
            );
            assert!(solver.executor.has_strict_native_bv_lia_bundle_state());
            let bundle = solver
                .export_last_unsat_bundle_for_exact_query(&binding)
                .expect("exact-source native bundle for each origin and label");
            let checked = re_check_bundle_strict(&bundle).expect("independent native replay");
            assert!(checked.quality.is_complete());
            assert_eq!(checked.assume_terms, bundle.obligation_assertions);
        }
    }
}

#[test]
fn native_bv_lia_assumption_bundle_binds_the_complete_public_query() {
    let mut solver = Solver::try_new(Logic::QfUfbvlia).expect("QF_UFBVLIA solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict native proof option");
    let b = solver.declare_const("b", Sort::bitvec(2));
    let i = solver.declare_const("i", Sort::Int);
    let bv_one = solver.try_bv_const_u64(1, 2).expect("BV one");
    let int_one = solver.int_const(1);
    let b_is_one = solver.try_eq(b, bv_one).expect("BV pin");
    let i_is_one = solver.try_eq(i, int_one).expect("Int pin");
    solver.try_assert_term(b_is_one).expect("assert BV pin");
    solver.try_assert_term(i_is_one).expect("assert Int pin");
    let bv_zero = solver.try_bv_const_u64(0, 2).expect("BV zero");
    let int_zero = solver.int_const(0);
    let b_is_zero = solver.try_eq(b, bv_zero).expect("BV alternative");
    let i_is_zero = solver.try_eq(i, int_zero).expect("Int alternative");
    let assumption = solver
        .try_or(b_is_zero, i_is_zero)
        .expect("mixed Boolean assumption");

    assert!(solver.check_sat_assuming(&[assumption]).is_unsat());
    assert!(!solver.executor.last_check_saw_authored_query_authority());
    assert!(solver.executor.has_strict_native_bv_lia_bundle_state());
    let bundle = solver
        .export_last_unsat_bundle()
        .expect("native assertion-plus-assumption bundle");
    assert_eq!(
        bundle.obligation_assertions,
        vec![b_is_one.id(), i_is_one.id(), assumption.id()]
    );
    let checked = re_check_bundle_strict(&bundle).expect("independent assumption replay");
    assert!(checked.quality.is_complete());
    assert_eq!(checked.assume_terms, bundle.obligation_assertions);

    // The base pins alone are satisfiable. Removing the temporary assumption
    // must not retain a valid refutation of the exported obligation.
    let mut missing_assumption = bundle;
    missing_assumption.obligation_assertions.pop();
    assert!(re_check_bundle_strict(&missing_assumption).is_err());
}

#[test]
fn exact_qf_ufbvlia_stale_native_state_cannot_fall_back_to_generic_bundle_export() {
    let mut solver = Solver::try_new(Logic::QfUfbvlia).expect("QF_UFBVLIA solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("strict native proof option");
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(PINNED_U16_BV_LIA)
        .expect("exact pinned u16 parse");

    assert!(solver.check_sat().is_unsat());
    assert!(solver.export_last_unsat_bundle().is_some());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_some());

    // Append an unasserted term without changing the public result/query. The
    // sealed W7 snapshot is stale, and the generic exporter must not replace
    // it with a newly snapshotted bundle.
    let _late = solver.fresh_var("post_w7_bundle", Sort::Bool);
    assert!(solver.export_last_unsat_bundle().is_none());
    assert!(solver
        .export_last_unsat_bundle_for_exact_query(&binding)
        .is_none());
}

#[test]
fn native_sos_bundle_replays_exact_source_and_refuses_stale_generic_export() {
    for source in [
        "(declare-const x Int) (assert (< (* x x) 0))",
        "(declare-const x Real) (assert (< (* x x) 0.0))",
    ] {
        let mut solver = proof_solver();
        let binding = solver
            .parse_smtlib2_with_exact_query_binding(source)
            .expect("exact polynomial source");
        // Inject only the provisional decision, not a certificate. Ordinary
        // search may prefer a valid wire-clean proof, which would not exercise
        // this exporter's distinct native SOS state at all.
        let result = solver.executor.certify_native_sos_provisional_for_test();
        let SolveResult::Unsat(proof) = result else {
            panic!("independent exact-source certification must succeed")
        };
        let certificate = solver.executor.take_unsat_certificate().unwrap();
        assert!(VerifiedSolveResult::certified_unsat(proof, certificate).is_unsat());
        assert!(solver.executor.has_strict_native_nra_sos_bundle_state());
        let bundle = solver
            .export_last_unsat_bundle_for_exact_query(&binding)
            .expect("native SOS exact-query artifact");
        assert!(bundle
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::NraSos { .. })));
        let checked = re_check_bundle_strict(&bundle).expect("independent native SOS replay");
        assert!(checked.quality.is_complete());
        assert_eq!(checked.assume_terms, bundle.obligation_assertions);
        assert_eq!(checked.quality.hole_count, 0);

        let artifact = solver
            .export_last_unsat_artifact()
            .expect("checked Alethe artifact");
        assert!(!artifact.restricted_rule_subset);
        assert!(!artifact.alethe.contains(":rule hole"));
        assert!(artifact.alethe.contains(":rule la_mult_neg"));

        // This does not change the source assertions or final UNSAT result.
        // A generic snapshot rebuild would still replay, but cannot renew the
        // sealed exact-source authority of the native SOS publication.
        let _late = solver.fresh_var("post_sos_bundle", Sort::Bool);
        assert!(solver.executor.has_strict_native_nra_sos_bundle_state());
        assert!(solver.export_last_unsat_bundle().is_none());
        assert!(solver
            .export_last_unsat_bundle_for_exact_query(&binding)
            .is_none());
    }
}
