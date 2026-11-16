// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_frontend::parse;

fn sealed() -> Executor {
    let source = "(set-option :produce-proofs true) (set-option :check-proofs-strict true)
        (set-logic QF_UFBVLIA) (declare-const result (_ BitVec 16))
        (declare-const x (_ BitVec 16)) (assert (= x #x9c40))
        (assert (= x result)) (assert (<= (* (ubv_to_int x) 2) 65535))";
    let mut executor = Executor::new();
    executor.execute_all(&parse(source).unwrap()).unwrap();
    executor.begin_public_solve(false);
    executor.bind_unsat_query_assumptions(&[]);
    let proposed = executor.solve_authored_plain_hard_query(&[]).unwrap();
    assert!(proposed.is_unsat());
    assert!(executor
        .certify_unsat_for_publication(proposed, &[])
        .is_unsat());
    assert!(executor.has_strict_native_bv_lia_bundle_state());
    executor
}

fn exported(
    executor: &Executor,
    progress: Progress<'_>,
) -> Result<Option<SerializableProofBundle>, ProofCheckError> {
    executor.export_strict_native_bv_lia_bundle_for_proof_with_progress(
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
fn controlled_bv_lia_copy_preserves_existing_seal_and_independent_replay() {
    let executor = sealed();
    let proof = executor.last_proof.as_ref().unwrap();
    let expected = executor
        .strict_native_bv_lia_bundle_for_proof(proof)
        .unwrap();
    let copied = exported(&executor, &mut |_, _| true).unwrap().unwrap();
    assert_eq!(
        serde_json::to_vec(expected).unwrap(),
        serde_json::to_vec(&copied).unwrap()
    );
    assert!(re_check_bundle_strict(&copied)
        .unwrap()
        .quality
        .is_complete());
}

#[test]
fn controlled_bv_lia_export_has_exact_shared_budget_and_checkpoint_refusals() {
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
fn stale_snapshot_proof_assumptions_and_unused_bundle_rows_remain_terminal() {
    for mutation in 0..4 {
        let mut executor = sealed();
        let proof = executor.last_proof.as_ref().unwrap().clone();
        match mutation {
            0 => {
                let _ = executor.ctx.terms.mk_var("later-unused", Sort::Bool);
            }
            1 => {
                executor.last_proof.as_mut().unwrap().steps.pop();
            }
            2 => {
                executor.last_assumptions = Some(vec![executor.ctx.terms.true_term()]);
            }
            _ => {
                executor
                    .last_strict_native_bv_lia_bundle
                    .as_mut()
                    .unwrap()
                    .bundle
                    .term_entries[0]
                    .1 = Sort::Int;
            }
        }
        assert!(executor.has_strict_native_bv_lia_bundle_state());
        assert!(executor
            .strict_native_bv_lia_bundle_for_proof(&proof)
            .is_none());
        assert!(executor
            .export_strict_native_bv_lia_bundle_for_proof_with_progress(&proof, &mut |_, _| true)
            .unwrap()
            .is_none());
    }
}

#[test]
fn normalization_matches_legacy_true_duplicate_order_and_bad_root_rules() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_bool = terms.mk_var("i", Sort::Int);
    let exact = [terms.true_term(), p, p, q, terms.true_term(), q];
    let expected =
        crate::executor::proof_original_rebuild::collect_bounded_bv_lia_roots(&terms, &exact)
            .unwrap();
    assert_eq!(expected, [p, q]);
    assert!(normalized_roots_match(&terms, &exact, &expected, &mut |_, _| true).unwrap());
    assert!(!normalized_roots_match(&terms, &exact, &[q, p], &mut |_, _| true).unwrap());
    for invalid in [not_bool, TermId::SENTINEL] {
        assert!(!normalized_roots_match(&terms, &[p, invalid], &[p], &mut |_, _| true).unwrap());
    }
    assert!(
        normalized_roots_match(&terms, &[terms.true_term(); 3], &[], &mut |_, _| true).unwrap()
    );
}
