// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::{Logic, Solver, VerifiedSolveResult};
use ay_core::{Proof, ProofId, Sort, TermId, TermStore, TheoryLemmaKind};

#[test]
fn native_sos_artifact_is_strict_but_not_in_the_restricted_rule_subset() {
    for source in [
        "(declare-const x Int) (assert (< (* x x) 0))",
        "(declare-const x Real) (assert (< (* x x) 0.0))",
    ] {
        let mut solver = Solver::try_new(Logic::All).unwrap();
        solver.set_produce_proofs(true);
        solver
            .try_set_option(":check-proofs-strict", "true")
            .unwrap();
        let binding = solver
            .parse_smtlib2_with_exact_query_binding(source)
            .unwrap();
        // Only propose the decision; the ordinary source checker constructs,
        // replays, and binds the real native SOS certificate.
        let result = solver.executor.certify_native_sos_provisional_for_test();
        let crate::api::SolveResult::Unsat(proof) = result else {
            panic!("exact polynomial source must acquire a native certificate")
        };
        let certificate = solver.executor.take_unsat_certificate().unwrap();
        assert!(VerifiedSolveResult::certified_unsat(proof, certificate).is_unsat());
        assert!(solver.executor.has_strict_native_nra_sos_bundle_state());
        let bundle = solver
            .export_last_unsat_bundle_for_exact_query(&binding)
            .unwrap();
        let checked = ay_proof::re_check_bundle_strict(&bundle).unwrap();
        assert!(checked.quality.is_complete());
        assert_eq!(checked.quality.hole_count, 0);
        let retained = solver.executor.last_proof().unwrap();
        assert!(retained
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::NraSos { .. })));
        assert!(!check_restricted_rule_subset(&checked.quality, retained));

        let artifact = solver.export_last_unsat_artifact().unwrap();
        // The checked lowering leaves no hole, but a native certificate is
        // still outside the consumer's clean rule subset.
        assert_eq!(artifact.alethe.matches(":rule hole").count(), 0);
        assert!(artifact.alethe.contains(":rule la_mult_neg"));
        assert_eq!(artifact.quality.hole_count, 0);
        assert!(matches!(
            artifact.strict_verdict,
            StrictProofVerdict::Verified(_)
        ));
        assert!(!artifact.restricted_rule_subset);
        assert_eq!(
            artifact.accept_for_consumer(ProofAcceptanceMode::Strict),
            Ok(())
        );
        assert_eq!(
            artifact.accept_for_consumer(ProofAcceptanceMode::RestrictedRuleSubset),
            Err(ProofAcceptanceError::NotRestrictedRuleSubset),
        );
    }
}

#[test]
fn checked_boolean_refutation_keeps_its_clean_classification() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    let mut proof = Proof::new();
    let positive = proof.add_assume(p, None);
    let negative = proof.add_assume(not_p, None);
    proof.add_resolution(Vec::new(), p, positive, negative);
    let quality = ay_proof::check_proof_strict(&proof, &terms).unwrap();
    assert!(quality.is_complete());
    assert!(check_restricted_rule_subset(&quality, &proof));

    let mut trust = quality.clone();
    trust.trust_count = 1;
    assert!(!check_restricted_rule_subset(&trust, &proof));
    let mut hole = quality;
    hole.hole_count = 1;
    assert!(!check_restricted_rule_subset(&hole, &proof));
}

#[test]
fn existing_structural_and_euf_rule_inventory_is_explicit() {
    // This tests only the capability classifier, not proof validity. Actual
    // artifact admission additionally requires the independent strict verdict.
    let quality = ProofQuality::default();
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(1),
        variables: Vec::new(),
    });
    for kind in [
        TheoryLemmaKind::EufTransitive,
        TheoryLemmaKind::EufCongruent,
        TheoryLemmaKind::EufCongruentPred,
    ] {
        proof.add_theory_lemma_with_kind("EUF", Vec::new(), kind);
    }
    for rule in [
        AletheRule::AndPos(0),
        AletheRule::EqTransitive,
        AletheRule::Resolution,
    ] {
        proof.add_rule_step(rule, Vec::new(), Vec::new(), Vec::new());
    }
    assert!(check_restricted_rule_subset(&quality, &proof));
    for kind in [
        TheoryLemmaKind::DatatypeDistinct,
        TheoryLemmaKind::BvLiaTautology,
    ] {
        let mut outside = proof.clone();
        outside.add_theory_lemma_with_kind("native", vec![TermId(0)], kind);
        assert!(!check_restricted_rule_subset(&quality, &outside));
    }
    for rule in [AletheRule::Hole, AletheRule::Trust] {
        let mut outside = proof.clone();
        outside.add_rule_step(rule, Vec::new(), Vec::new(), Vec::new());
        assert!(!check_restricted_rule_subset(&quality, &outside));
    }
}
