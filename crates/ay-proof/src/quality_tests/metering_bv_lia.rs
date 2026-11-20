// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One bounded source replay reservation, without a second generic product.

use super::*;

const PRODUCTION_WORK: usize = 350_000_000;
const PRODUCTION_BYTES: usize =
    512 * 1024 * 1024 + crate::checker::MAX_EXPENSIVE_BV_BYTES_PER_LEMMA;

/// Original Bool/Int source plus every projection blocker, with one genuine
/// source-semantic lemma and an ordinary resolution spine. Dropping a blocker
/// makes this same proposed refutation invalid.
fn projection_refutation(omit_mask: Option<u16>) -> (TermStore, Proof, Vec<TermId>) {
    let mut terms = TermStore::new();
    let variables: Vec<_> = (0..10)
        .map(|index| terms.mk_var(format!("projected_{index}"), Sort::Bool))
        .collect();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let indicators = variables
        .iter()
        .map(|&variable| terms.mk_ite(variable, one, zero))
        .collect();
    let sum = terms.mk_add(indicators);
    let four = terms.mk_int(4.into());
    let mut roots = vec![terms.mk_ge(sum, four)];
    for mask in 0_u16..1024 {
        if mask.count_ones() < 4 || omit_mask == Some(mask) {
            continue;
        }
        let clause = variables
            .iter()
            .enumerate()
            .map(|(index, &variable)| {
                if mask & (1 << index) == 0 {
                    variable
                } else {
                    terms.mk_not_raw(variable)
                }
            })
            .collect();
        roots.push(terms.mk_or(clause));
    }
    let mut proof = Proof::new();
    let assumptions: Vec<_> = roots
        .iter()
        .map(|&root| proof.add_assume(root, None))
        .collect();
    let negatives: Vec<_> = roots.iter().map(|&root| terms.mk_not_raw(root)).collect();
    let mut previous = proof.add_theory_lemma_with_kind(
        "BV/LIA",
        negatives.clone(),
        TheoryLemmaKind::BvLiaTautology,
    );
    for (index, (&root, &assumption)) in roots.iter().zip(&assumptions).enumerate() {
        previous =
            proof.add_resolution(negatives[index + 1..].to_vec(), root, previous, assumption);
    }
    (terms, proof, roots)
}

fn under_production_envelope(
    proof: &Proof,
    terms: &TermStore,
    roots: &[TermId],
) -> (Result<ProofQuality, ProofCheckError>, usize, usize) {
    let (mut work, mut bytes) = (0_usize, 0_usize);
    let result = check_proof_strict_with_typed_context_and_progress(
        proof,
        terms,
        None,
        None,
        &[],
        Some(roots),
        &mut |work_delta, byte_delta| {
            work = work.saturating_add(work_delta);
            bytes = bytes.saturating_add(byte_delta);
            work <= PRODUCTION_WORK && bytes <= PRODUCTION_BYTES
        },
    );
    (result, work, bytes)
}

#[test]
fn bv_lia_projection_refutation_fits_unchanged_strict_envelope() {
    let (terms, proof, roots) = projection_refutation(None);
    assert_eq!(roots.len(), 849);
    assert_eq!(proof.steps.len(), 1699);
    let (result, work, bytes) = under_production_envelope(&proof, &terms, &roots);
    assert!(result.expect("strict source refutation").is_complete());
    assert!(work >= crate::checker::MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA as usize);
    assert!(work <= PRODUCTION_WORK, "work={work}");
    assert!(bytes <= PRODUCTION_BYTES, "bytes={bytes}");
}

#[test]
fn bv_lia_projection_missing_blocker_is_rejected_by_source_replay() {
    let (terms, proof, roots) = projection_refutation(Some(15));
    let (result, work, _) = under_production_envelope(&proof, &terms, &roots);
    let error = result.expect_err("the omitted four-true assignment satisfies the source");
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { .. }),
        "source replay must reject the false lemma: {error:?}; work={work}"
    );
}

#[test]
fn bv_lia_repeated_source_replays_still_exhaust_one_aggregate_owner() {
    let mut terms = TermStore::new();
    let variable = terms.mk_var("repeated_bv_lia", Sort::Bool);
    let negative = terms.mk_not_raw(variable);
    let not_negative = terms.mk_not_raw(negative);
    let mut proof = Proof::new();
    for _ in 0..4 {
        proof.add_theory_lemma_with_kind(
            "BV/LIA",
            vec![negative, not_negative],
            TheoryLemmaKind::BvLiaTautology,
        );
    }
    let (result, work, _) = under_production_envelope(&proof, &terms, &[]);
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert!(work >= 400_000_000, "aggregate reservation={work}");
}

#[test]
fn bv_lia_original_owner_can_refuse_before_source_replay() {
    let (terms, proof, roots) = projection_refutation(None);
    let result = check_proof_strict_with_typed_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        &[],
        Some(&roots),
        &mut |_, _| false,
    );
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
}
