// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, CuttingPlaneAnnotation};
use num_rational::Rational64;

fn fixture() -> (SerializableProofBundle, Proof) {
    let terms = TermStore::new();
    let proof = Proof::from_steps(vec![
        ProofStep::Assume(TermId::SENTINEL),
        ProofStep::Step {
            rule: AletheRule::Custom("unused-rule".repeat(4096)),
            clause: vec![TermId::SENTINEL],
            premises: vec![ProofId(99)],
            args: vec![TermId(98)],
        },
        ProofStep::Anchor {
            end_step: ProofId(0),
            variables: vec![(
                "unused-binder".repeat(128),
                Sort::Seq(Box::new(Sort::Uninterpreted("S".repeat(128)))),
            )],
        },
    ]);
    (
        SerializableProofBundle::from_proof(&proof, &terms, vec![]),
        proof,
    )
}

fn trace(bundle: &SerializableProofBundle, proof: &Proof) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    assert!(bundle
        .proof_steps_match_with_progress(proof, &mut |w, b| {
            charges.push((w, b));
            true
        })
        .unwrap());
    charges
}

#[test]
fn comparison_preserves_all_raw_step_fields_without_validating_them() {
    let (bundle, proof) = fixture();
    assert_ne!(trace(&bundle, &proof), []);
    assert!(re_check_bundle_strict(&bundle).is_err());
    for index in 0..proof.steps.len() {
        let mut changed = proof.clone();
        changed.steps[index] = ProofStep::Assume(TermId(index as u32));
        assert!(!bundle
            .proof_steps_match_with_progress(&changed, &mut |_, _| true)
            .unwrap());
    }
    let mut shortened = proof.clone();
    shortened.steps.pop();
    assert!(!bundle
        .proof_steps_match_with_progress(&shortened, &mut |_, _| true)
        .unwrap());
    let mut named = proof;
    named
        .named_steps
        .insert("outside-step-comparison".into(), ProofId(0));
    assert!(bundle
        .proof_steps_match_with_progress(&named, &mut |_, _| true)
        .unwrap());
}

#[test]
fn byte_scans_on_both_operands_are_work_priced_under_one_allowance() {
    let (bundle, proof) = fixture();
    let charges = trace(&bundle, &proof);
    assert!(charges.iter().all(|(_, bytes)| *bytes == 0));
    let work: usize = charges.iter().map(|(w, _)| *w).sum();
    assert!(work > 2 * "unused-rule".len() * 4096);
    for cap in [work, work - 1] {
        let mut used = 0;
        let mut progress = |w, _| {
            used += w;
            used <= cap
        };
        assert_eq!(
            bundle
                .proof_steps_match_with_progress(&proof, &mut progress)
                .is_ok(),
            cap == work
        );
        assert_eq!(
            bundle.proof_steps_match_with_progress(&proof, &mut progress),
            Err(ProofCheckError::ResourceLimit)
        );
    }
    for stop in 1..=charges.len() {
        let mut calls = 0;
        assert_eq!(
            bundle.proof_steps_match_with_progress(&proof, &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert_eq!(calls, stop);
    }
}

#[test]
fn malformed_deep_supplied_binder_refuses_before_equality() {
    let (bundle, mut proof) = fixture();
    let mut deep = Sort::Bool;
    for _ in 0..258 {
        deep = Sort::Seq(Box::new(deep));
    }
    proof.steps[2] = ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![("deep".into(), deep)],
    };
    assert_eq!(
        bundle.proof_steps_match_with_progress(&proof, &mut |_, _| true),
        Err(ProofCheckError::ResourceLimit)
    );
}

#[test]
fn every_rational_coefficient_lane_compares_raw_pairs_without_arithmetic() {
    for cutting in [false, true] {
        for (left, right, matches) in [
            ((1, 2), (1, 2), true),
            ((1, 2), (2, 4), false),
            ((1, -2), (-1, 2), false),
            ((1, 0), (1, 0), true),
            ((1, 0), (2, 3), false),
            ((2, 3), (1, 0), false),
        ] {
            let step = |(numerator, denominator)| {
                let annotation =
                    FarkasAnnotation::new(vec![Rational64::new_raw(numerator, denominator)]);
                let (farkas, lia) = if cutting {
                    (
                        None,
                        Some(LiaAnnotation::CuttingPlane(CuttingPlaneAnnotation {
                            farkas: annotation,
                            divisor: 2,
                        })),
                    )
                } else {
                    (Some(annotation), None)
                };
                ProofStep::TheoryLemma {
                    theory: "LIA".into(),
                    clause: vec![],
                    farkas,
                    kind: TheoryLemmaKind::LiaGeneric,
                    lia,
                }
            };
            let terms = TermStore::new();
            let original = Proof::from_steps(vec![step(left)]);
            let supplied = Proof::from_steps(vec![step(right)]);
            let bundle = SerializableProofBundle::from_proof(&original, &terms, vec![]);
            assert_eq!(
                bundle
                    .proof_steps_match_with_progress(&supplied, &mut |_, b| {
                        assert_eq!(b, 0);
                        true
                    })
                    .unwrap(),
                matches
            );
        }
    }
}
