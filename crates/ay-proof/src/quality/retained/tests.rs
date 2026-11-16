// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::producer_test_counter;
use crate::checker::bv_bitblast::{
    MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA, MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA,
};
use std::time::Duration;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn fixture(constant: u32) -> (TermStore, Proof, TermId) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("whole-proof-retained", Sort::bitvec(9));
    let zero = terms.mk_bitvec(constant.into(), 9);
    let sum = terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::bitvec(9));
    let identity = terms.mk_app(Symbol::named("="), [sum, x], Sort::Bool);
    let negated = terms.mk_not(identity);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(negated, None);
    let lemma = proof.add_theory_lemma_with_kind("BV", vec![identity], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], identity, lemma, assumption);
    (terms, proof, negated)
}

fn run(
    terms: &TermStore,
    proof: &Proof,
    assertions: &[TermId],
    operation: RetainedOperation<'_>,
    deadline: Instant,
    progress: Progress<'_>,
) -> Result<(ProofQuality, Output), ProofCheckError> {
    check(
        proof,
        Context {
            terms,
            dt_decls: None,
            ctor_selectors: None,
            datatype_member_signatures: &[],
            problem_assertions: assertions,
        },
        Request {
            operation,
            deadline,
            wire_limits: None,
        },
        progress,
    )
}

fn capture() -> Output {
    let (terms, proof, assertion) = fixture(0);
    run(
        &terms,
        &proof,
        &[assertion],
        RetainedOperation::Capture,
        end(),
        &mut |_, _| true,
    )
    .unwrap()
    .1
}

#[test]
fn full_refutation_captures_once_and_fresh_reader_never_searches() {
    let before = producer_test_counter::count();
    let mut prepayments = 0;
    let (quality, payloads) = {
        let (terms, proof, assertion) = fixture(0);
        run(
            &terms,
            &proof,
            &[assertion],
            RetainedOperation::Capture,
            end(),
            &mut |work, bytes| {
                if (work, bytes)
                    == (
                        MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize,
                        MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
                    )
                {
                    prepayments += 1;
                }
                true
            },
        )
        .unwrap()
    }; // All producer term/proof owners are gone.
    assert_eq!(prepayments, 1);
    assert_eq!(producer_test_counter::count(), before + 1);
    assert_eq!(quality.total_steps, 3);
    assert_eq!(quality.hole_count, 0);
    assert_eq!(payloads.len(), 1);
    assert_eq!(payloads[0].step, 1);
    assert_ne!(payloads[0].payload.as_slice(), &[] as &[u8]);
    let before_replay = producer_test_counter::count();
    let (terms, proof, assertion) = fixture(0);
    let (replayed, fresh_payloads) = run(
        &terms,
        &proof,
        &[assertion],
        RetainedOperation::Replay(&payloads),
        end(),
        &mut |_, _| true,
    )
    .unwrap();
    assert_eq!(replayed, quality);
    assert_eq!(fresh_payloads, []);
    assert_eq!(producer_test_counter::count(), before_replay);
}

#[test]
fn replay_is_bound_to_actual_terms_not_reused_numeric_step_and_term_ids() {
    let payloads = capture();
    let (terms, proof, assertion) = fixture(1);
    let before = producer_test_counter::count();
    assert!(run(
        &terms,
        &proof,
        &[assertion],
        RetainedOperation::Replay(&payloads),
        end(),
        &mut |_, _| true,
    )
    .is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn retained_evidence_does_not_bypass_assumption_or_terminal_validation() {
    let payloads = capture();
    let (terms, proof, assertion) = fixture(0);
    let before = producer_test_counter::count();
    assert!(run(
        &terms,
        &proof,
        &[],
        RetainedOperation::Replay(&payloads),
        end(),
        &mut |_, _| true,
    )
    .is_err());
    let incomplete = Proof::from_steps(proof.steps[..2].to_vec());
    assert!(run(
        &terms,
        &incomplete,
        &[assertion],
        RetainedOperation::Replay(&payloads),
        end(),
        &mut |_, _| true,
    )
    .is_err());
    assert_eq!(producer_test_counter::count(), before);
    // Even a successfully captured lemma is not returned from a non-refutation.
    assert!(run(
        &terms,
        &incomplete,
        &[assertion],
        RetainedOperation::Capture,
        end(),
        &mut |_, _| true,
    )
    .is_err());
}

#[test]
fn exact_aggregate_refusal_precedes_any_capture() {
    let (terms, proof, assertion) = fixture(0);
    let before = producer_test_counter::count();
    let mut refusals = 0;
    let result = run(
        &terms,
        &proof,
        &[assertion],
        RetainedOperation::Capture,
        end(),
        &mut |work, bytes| {
            if (work, bytes)
                == (
                    MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize,
                    MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
                )
            {
                refusals += 1;
                false
            } else {
                true
            }
        },
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(refusals, 1);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn expired_original_deadline_refuses_before_first_callback_or_prepass() {
    let (terms, proof, assertion) = fixture(0);
    let before = producer_test_counter::count();
    let mut callbacks = 0;
    let result = run(
        &terms,
        &proof,
        &[assertion],
        RetainedOperation::Capture,
        Instant::now(),
        &mut |_, _| {
            callbacks += 1;
            true
        },
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(callbacks, 0);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn late_control_refusal_drops_result_and_callback_panics_stay_poisoned() {
    use std::{cell::Cell, panic::AssertUnwindSafe, rc::Rc};
    struct Owner(Rc<Cell<bool>>);
    impl Drop for Owner {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    let dropped = Rc::new(Cell::new(false));
    let mut calls = 0;
    let mut callback = |_, _| {
        calls += 1;
        calls == 1
    };
    let mut control = Control {
        deadline: end(),
        progress: &mut callback,
        refused: false,
    };
    assert!(matches!(
        control.run(|_| Ok(Owner(dropped.clone()))),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert!(dropped.get());
    assert!(!control.charge(0, 0));
    assert_eq!(calls, 2);
    let mut callback = |_, _| -> bool { panic!("test progress panic") };
    let mut control = Control {
        deadline: end(),
        progress: &mut callback,
        refused: false,
    };
    assert!(std::panic::catch_unwind(AssertUnwindSafe(|| control.charge(1, 0))).is_err());
    assert!(!control.charge(0, 0));
}
