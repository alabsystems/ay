// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual whole strict passes, not a replacement for public sealed v4 tests.

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;
use crate::checker::bv_bitblast::MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA;
use std::time::Duration;

fn fixture(constant: u32) -> (TermStore, Proof, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("four_walk_original", Sort::bitvec(9));
    let value = terms.mk_bitvec(constant.into(), 9);
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, value], Sort::bitvec(9));
    let root = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let negated = terms.mk_not(root);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negated, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![root], TheoryLemmaKind::BvBitBlast);
    proof.add_theory_lemma_with_kind("BV", vec![root], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], root, lemma, assumption);
    (terms, proof, negated)
}

fn run(
    terms: &TermStore,
    proof: &Proof,
    assertion: TermId,
    operation: RetainedOperation<'_>,
    end: Instant,
    progress: Progress<'_>,
) -> Result<(ProofQuality, Output), ProofCheckError> {
    check(
        proof,
        Context {
            terms,
            dt_decls: None,
            ctor_selectors: None,
            datatype_member_signatures: &[],
            problem_assertions: &[assertion],
        },
        Request {
            operation,
            deadline: end,
            wire_limits: None,
        },
        progress,
    )
}

struct Owner {
    work: u64,
    bytes: u64,
    refused: bool,
}

impl Owner {
    fn debit(&mut self, work: usize, bytes: usize) -> bool {
        if self.refused {
            return false;
        }
        self.refused = true;
        let Some(work) = u64::try_from(work)
            .ok()
            .and_then(|work| self.work.checked_add(work))
            .filter(|&work| work <= 8 * MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA)
        else {
            return false;
        };
        let Some(bytes) = u64::try_from(bytes)
            .ok()
            .and_then(|bytes| self.bytes.checked_add(bytes))
            .filter(|&bytes| bytes <= 6 * 1024 * 1024 * 1024)
        else {
            return false;
        };
        self.work = work;
        self.bytes = bytes;
        self.refused = false;
        true
    }
}

#[test]
fn two_ordinary_lemmas_and_all_four_strict_walks_fit_one_original_owner_without_refunds() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut owner = Owner {
        work: 0,
        bytes: 0,
        refused: false,
    };
    let before = producer_test_counter::count();
    let payloads = {
        let (terms, proof, assertion) = fixture(0);
        run(
            &terms,
            &proof,
            assertion,
            RetainedOperation::Capture,
            deadline,
            &mut |work, bytes| owner.debit(work, bytes),
        )
        .unwrap()
        .1
    };
    assert_eq!(payloads.len(), 2);
    assert_eq!(producer_test_counter::count(), before + 2);
    let captured = (owner.work, owner.bytes);
    for _ in 0..3 {
        let (terms, proof, assertion) = fixture(0);
        let source = terms.entries_snapshot();
        let old = (owner.work, owner.bytes);
        let (quality, output) = run(
            &terms,
            &proof,
            assertion,
            RetainedOperation::Replay(&payloads),
            deadline,
            &mut |work, bytes| owner.debit(work, bytes),
        )
        .unwrap();
        assert_eq!(quality.total_steps, 4);
        assert_eq!(quality.hole_count, 0);
        assert!(output.is_empty());
        assert!(owner.work > old.0 && owner.bytes > old.1);
        assert_eq!(terms.entries_snapshot(), source);
    }
    assert!(!owner.refused);
    assert!(owner.work > captured.0);
    assert!(owner.work < 8 * MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA);
    assert!(owner.bytes < 6 * 1024 * 1024 * 1024);
    assert_eq!(producer_test_counter::count(), before + 2);
}

#[test]
fn false_original_neighbor_missing_assumption_and_terminal_are_not_cheap_acceptance() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let (terms, proof, assertion) = fixture(0);
    let payloads = run(
        &terms,
        &proof,
        assertion,
        RetainedOperation::Capture,
        deadline,
        &mut |_, _| true,
    )
    .unwrap()
    .1;
    let before = producer_test_counter::count();
    let (wrong, wrong_proof, wrong_assertion) = fixture(1);
    assert!(run(
        &wrong,
        &wrong_proof,
        wrong_assertion,
        RetainedOperation::Replay(&payloads),
        deadline,
        &mut |_, _| true
    )
    .is_err());
    assert!(run(
        &terms,
        &proof,
        terms.true_term(),
        RetainedOperation::Replay(&payloads),
        deadline,
        &mut |_, _| true
    )
    .is_err());
    let missing = Proof::from_steps(proof.steps[..3].to_vec());
    assert!(run(
        &terms,
        &missing,
        assertion,
        RetainedOperation::Replay(&payloads),
        deadline,
        &mut |_, _| true
    )
    .is_err());
    assert_eq!(producer_test_counter::count(), before);
}
