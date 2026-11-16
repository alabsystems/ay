// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{AletheRule, ProofStep, Sort};
use ay_frontend::parse;

fn sealed() -> Executor {
    let mut executor = Executor::new();
    executor
        .execute_all(
            &parse(
                "(set-option :produce-proofs true)
        (set-option :check-proofs-strict true) (set-logic ALL)
        (declare-const x Real) (assert (< (* x x) 0.0))",
            )
            .unwrap(),
        )
        .unwrap();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    executor.last_assumptions = Some(vec![]);
    let prepared = executor
        .prepare_strict_native_nra_sos_bundle(&[])
        .unwrap()
        .unwrap();
    let scope = executor.authenticate_unsat_query_scope(&[], true).unwrap();
    assert!(prepared.bind(scope, &mut executor).is_some());
    assert!(executor.has_strict_native_nra_sos_bundle_state());
    executor
}

fn exported(
    executor: &Executor,
    progress: Progress<'_>,
) -> Result<Option<SerializableProofBundle>, ProofCheckError> {
    executor.export_strict_native_nra_sos_bundle_for_proof_with_progress(
        executor.last_proof.as_ref().unwrap(),
        progress,
    )
}

fn trace(executor: &Executor) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    assert!(exported(executor, &mut |w, b| {
        charges.push((w, b));
        true
    })
    .unwrap()
    .is_some());
    charges
}

#[test]
fn controlled_sos_copy_matches_existing_seal_and_strict_replay() {
    let executor = sealed();
    let proof = executor.last_proof.as_ref().unwrap();
    let old = executor
        .strict_native_nra_sos_bundle_for_proof(proof)
        .unwrap();
    let copied = exported(&executor, &mut |_, _| true).unwrap().unwrap();
    assert_eq!(
        serde_json::to_vec(old).unwrap(),
        serde_json::to_vec(&copied).unwrap()
    );
    assert!(ay_proof::re_check_bundle_strict(&copied)
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn controlled_sos_export_debits_one_allowance_and_never_resumes_after_refusal() {
    let executor = sealed();
    let charges = trace(&executor);
    let work: usize = charges.iter().map(|(w, _)| *w).sum();
    let bytes: usize = charges.iter().map(|(_, b)| *b).sum();
    assert!(work > 0 && bytes > 0);
    for (work_cap, bytes_cap, admitted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let mut progress = |dw, db| {
            w += dw;
            b += db;
            w <= work_cap && b <= bytes_cap
        };
        assert_eq!(exported(&executor, &mut progress).is_ok(), admitted);
        assert!(matches!(
            exported(&executor, &mut progress),
            Err(ProofCheckError::ResourceLimit)
        ));
    }
    for stop in 1..=charges.len() {
        let mut calls = 0;
        assert!(matches!(
            exported(&executor, &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        ));
        assert_eq!(calls, stop);
    }
    assert_eq!(trace(&executor), charges);
}

#[test]
fn selected_sos_state_still_rejects_epoch_snapshot_assumption_and_proof_changes() {
    for mutation in 0..4 {
        let mut executor = sealed();
        match mutation {
            0 => {
                let _ = executor.ctx.terms.mk_var("later-unused", Sort::Bool);
            }
            1 => {
                executor.last_assumptions = Some(vec![executor.ctx.terms.true_term()]);
            }
            2 => {
                executor
                    .proof_problem_assertion_provenance
                    .as_mut()
                    .unwrap()
                    .original_problem_assertions
                    .clear();
            }
            _ => {
                executor.last_proof.as_mut().unwrap().steps.pop();
            }
        }
        let proof = executor.last_proof.as_ref().unwrap();
        assert!(executor.has_strict_native_nra_sos_bundle_state());
        assert!(executor
            .strict_native_nra_sos_bundle_for_proof(proof)
            .is_none());
        assert!(exported(&executor, &mut |_, _| true).unwrap().is_none());
    }
}

#[test]
fn changed_proof_owned_payload_is_priced_before_full_structural_mismatch() {
    let executor = sealed();
    let mut proof = executor.last_proof.as_ref().unwrap().clone();
    proof.steps[0] = ProofStep::Step {
        rule: AletheRule::Custom("large-unreachable-rule".repeat(4096)),
        clause: vec![],
        premises: vec![],
        args: vec![],
    };
    let mut work = 0;
    assert!(matches!(
        executor.export_strict_native_nra_sos_bundle_for_proof_with_progress(
            &proof,
            &mut |w, _| {
                work += w;
                work <= 4096
            }
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(executor
        .export_strict_native_nra_sos_bundle_for_proof_with_progress(&proof, &mut |_, _| true)
        .unwrap()
        .is_none());
    assert!(exported(&executor, &mut |_, _| true).unwrap().is_some());
}
