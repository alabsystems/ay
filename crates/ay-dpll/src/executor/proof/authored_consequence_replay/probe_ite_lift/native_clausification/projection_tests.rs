// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn closed() -> (Fixture, Proof, Vec<TermId>) {
    let mut f = fixture();
    let (proof, negated) = closed_trust(&mut f.exec, f.targets[0]);
    let roots = vec![f.source, negated, f.source];
    begin(&mut f.exec, &roots, true);
    (f, proof, roots)
}

#[test]
fn native_ite_clausification_projection_does_not_clone_unused_large_owned_payload() {
    let _diagnostics = diagnostic_flags();
    for coefficients in [false, true] {
        let (mut f, mut proof, roots) = closed();
        let truth = f.exec.ctx.terms.true_term();
        if coefficients {
            proof.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_owned(),
                clause: vec![truth],
                kind: TheoryLemmaKind::LraFarkas,
                farkas: Some(ay_core::FarkasAnnotation {
                    coefficients: vec![
                        num_rational::Rational64::from_integer(0);
                        MAX_NATIVE_PAYLOAD * 2
                    ],
                }),
                lia: None,
            });
        } else {
            proof.add_rule_step(
                AletheRule::Custom("x".repeat(MAX_NATIVE_PAYLOAD * 2)),
                vec![truth],
                vec![],
                vec![],
            );
        }
        assert!(
            admit_proof_copy(&proof).is_none(),
            "the old full-copy admission refuses"
        );
        assert!(f.exec.try_rebuild_native_ite_clausification(&mut proof));
        assert!(f
            .exec
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete()));
        assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &roots).is_ok());
        assert_eq!(f.exec.proof_original_problem_assertions_slice(), roots);
        assert!(admit_proof_copy(&proof).is_some());
    }
}

#[test]
fn native_ite_clausification_projection_checks_unused_assumes_anchors_and_proof_ids() {
    for mutation in 0..4 {
        let (mut f, mut proof, _) = closed();
        let truth = f.exec.ctx.terms.true_term();
        match mutation {
            0 => {
                let foreign = f.exec.ctx.terms.mk_var("unused_foreign", Sort::Bool);
                proof.add_assume(foreign, None);
            }
            1 => {
                proof.add_step(ProofStep::Anchor {
                    end_step: ay_core::ProofId(0),
                    variables: Vec::new(),
                });
            }
            2 => {
                proof.add_rule_step(
                    AletheRule::Reordering,
                    vec![truth],
                    vec![ay_core::ProofId(u32::MAX)],
                    Vec::new(),
                );
            }
            _ => {
                let next = ay_core::ProofId(u32::try_from(proof.steps.len()).unwrap());
                proof.add_rule_step(AletheRule::Reordering, vec![truth], vec![next], Vec::new());
            }
        }
        let original = proof.clone();
        assert!(
            !f.exec.try_rebuild_native_ite_clausification(&mut proof),
            "mutation {mutation}"
        );
        assert_eq!(proof, original);
    }
}

#[test]
fn native_ite_clausification_projection_retains_global_metadata_owners() {
    let (f, mut proof, roots) = closed();
    let marker = proof.add_rule_step(
        AletheRule::FreshDefEq,
        vec![f.exec.ctx.terms.true_term()],
        vec![],
        vec![],
    );
    let budget = RepairBudget::new(&f.exec);
    let projected = super::super::projection::copy(&f.exec, &proof, &roots, &budget).unwrap();
    assert_eq!(projected.steps.len(), proof.steps.len() + 1);
    assert_eq!(
        projected.steps[marker.0 as usize],
        proof.steps[marker.0 as usize]
    );
}

#[test]
fn native_ite_clausification_projection_preserves_selected_assumption_names_and_births() {
    let (f, mut proof, roots) = closed();
    proof
        .named_steps
        .insert("exact-negative".to_owned(), ay_core::ProofId(1));
    let prefix = f.exec.ctx.terms.snapshot_stamp();
    let generation = f.exec.ctx.terms.checker_visible_metadata_generation();
    let budget = RepairBudget::new(&f.exec);
    let projected = super::super::projection::copy(&f.exec, &proof, &roots, &budget).unwrap();
    assert_eq!(projected.named_steps["exact-negative"], ay_core::ProofId(1));
    assert_eq!(prefix, f.exec.ctx.terms.snapshot_stamp());
    assert_eq!(
        generation,
        f.exec.ctx.terms.checker_visible_metadata_generation()
    );
}

#[test]
fn native_ite_clausification_projection_and_later_stages_share_sticky_storage_and_stop() {
    let (mut f, proof, roots) = closed();
    let budget = RepairBudget::new(&f.exec);
    budget.set_remaining(1_048_576, 1);
    assert!(super::super::projection::copy(&f.exec, &proof, &roots, &budget).is_none());
    assert!(
        !budget.clone().pay(0, 0),
        "a clone cannot replenish the owner"
    );
    let mut original = proof.clone();
    assert!(f
        .exec
        .stage_checked_integer_and_euf_leaves(&mut original, &budget)
        .is_none());
    assert_eq!(
        original, proof,
        "refusal precedes moving retained proof data"
    );

    f.exec
        .set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
            true,
        )));
    let budget = RepairBudget::new(&f.exec);
    assert!(super::super::projection::copy(&f.exec, &proof, &roots, &budget).is_none());
    f.exec
        .set_interrupt(std::sync::Arc::new(std::sync::atomic::AtomicBool::new(
            false,
        )));
    assert!(!budget.pay(0, 0));
}
