// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod mutations;
mod normalization;
mod oracle;
mod progress;
mod resources;
mod usage;

fn fixture(op: BvOp, width: u32) -> BvBlastProof {
    export_bv_blast_proof(SliceObligation::identical_at(op, width))
        .expect("constructive identity needs no SAT solver")
}

fn limits(proof: &BvBlastProof) -> BvBlastValidateLimits {
    BvBlastValidateLimits {
        deadline: None,
        max_vars: proof.vars.len(),
        max_bit_lemmas: proof.bit_lemmas.len(),
        max_clauses: proof.clauses.len(),
        max_clause_literals: proof
            .clauses
            .iter()
            .map(|clause| clause.lits.len())
            .max()
            .unwrap_or(0),
        max_original_literals: proof.clauses.iter().map(|clause| clause.lits.len()).sum(),
        max_resolution_steps: proof.refutation.steps.len(),
        max_derived_literals: proof
            .refutation
            .steps
            .iter()
            .map(|step| step.clause.len())
            .sum(),
        max_work: u64::MAX,
    }
}

fn compare(
    proof: &BvBlastProof,
    limits: &BvBlastValidateLimits,
) -> Result<(), BvBlastValidateError> {
    let expected = oracle::validate(proof, limits);
    assert_eq!(proof.validate_with_limits(limits), expected);
    assert_eq!(
        proof.validate_with_limits_and_cancellation(limits, &mut || true),
        expected
    );
    expected
}

#[test]
fn every_constructive_operation_replays_with_unchanged_authority_and_payload() {
    for op in [
        BvOp::Add,
        BvOp::Sub,
        BvOp::Xor,
        BvOp::And,
        BvOp::Or,
        BvOp::Shl,
        BvOp::Lshr,
        BvOp::Ashr,
    ] {
        for width in [1, 2, 4] {
            let proof = fixture(op, width);
            let before = proof.clone();
            assert_eq!(compare(&proof, &limits(&proof)), Ok(()));
            assert_eq!(proof.validate(), Ok(()));
            assert_eq!(proof, before);
        }
    }
}

#[test]
fn descriptive_source_text_does_not_gain_authentication_authority() {
    let mut proof = fixture(BvOp::Xor, 1);
    proof.asserted_smt = "not the producer's source query".to_owned();
    proof.obligation.op = BvOp::Sub;
    proof.obligation.lhs_args = [OperandRef::B, OperandRef::B];
    // Replay has always checked the graph, not these lineage fields. Actual
    // source-bound callers must freshly construct or independently bind it.
    assert_eq!(compare(&proof, &limits(&proof)), Ok(()));
}

#[test]
fn resolution_and_clause_sets_keep_exact_duplicate_polarity_and_output_order_rules() {
    let proof = fixture(BvOp::Xor, 1);
    let limits = limits(&proof);
    let p = Lit::pos(0);
    let n = Lit::neg(0);
    let a = Lit::pos(1);
    let b = Lit::neg(2);
    for (left, right, expected) in [
        (vec![a, p, a, b], vec![n, b], Some(vec![a, b])),
        (vec![b, p, a], vec![a, n], Some(vec![b, a])),
        (vec![p, n], vec![n], None),
        (vec![p, a], vec![n, a.negated()], None),
        (vec![a], vec![n], None),
        (vec![p], vec![n], Some(vec![])),
    ] {
        let mut keep_going = || true;
        let mut budget = ReplayBudget::new(&limits, &mut keep_going);
        assert_eq!(sets::resolve(&left, &right, 0, &mut budget), Ok(expected));
    }
    let mut keep_going = || true;
    let mut budget = ReplayBudget::new(&limits, &mut keep_going);
    assert_eq!(sets::clause_eq(&[a, b, a], &[b, a], &mut budget), Ok(true));
    assert_eq!(
        sets::clause_eq(&[a, b], &[a, b.negated()], &mut budget),
        Ok(false)
    );
}
