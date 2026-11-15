// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn sparse_fixture() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let array = terms.mk_var("sparse-credit", sort.clone());
    let at = terms.mk_var("write", Sort::bitvec(64));
    let key = terms.mk_var("read", Sort::bitvec(64));
    let value = terms.mk_var("cell", Sort::bitvec(8));
    let stored = terms.mk_app(Symbol::named("store"), [array, at, value], sort);
    let read = terms.mk_app(Symbol::named("select"), [stored, key], Sort::bitvec(8));
    let root = terms.mk_app(Symbol::named("="), [read, read], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("BV", vec![root], TheoryLemmaKind::BvBitBlast);
    (terms, proof)
}

#[test]
fn sparse_aggregate_includes_native_u_but_expression_allowance_cannot_borrow_it() {
    let (terms, proof) = sparse_fixture();
    let payloads = capture(&terms, &proof);
    let before = producer_test_counter::count();
    let end = end();
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end, None, &mut |_, _| true)
        .unwrap();
    let price = refined
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .unwrap();
    let expression = price.expression_work().unwrap();
    assert!(price.work > expression);
    assert_eq!(refined.aggregate_charge().work, price.work);
    let mut paid = Vec::new();
    let mut credits = refined
        .prepay(end, &mut |w, b| {
            paid.push((w, b));
            true
        })
        .unwrap();
    assert_eq!(paid, [(price.work, price.bytes), (0, 0)]);
    let allowance = credits
        .take(ProofId(0), &mut |_, _| true)
        .unwrap()
        .into_allowance();
    assert_eq!(allowance.work_limit(), expression as u64);
    assert!(allowance.work_limit() < price.work as u64);
    assert_eq!(allowance.deadline(), end);
    drop(allowance);
    credits.finish().unwrap();
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn sparse_credit_reuse_bad_ids_and_refusal_poison_the_same_original_owner() {
    let (terms, proof) = sparse_fixture();
    let payloads = capture(&terms, &proof);
    for mode in 0..3 {
        let refined = plan(&terms, &proof)
            .refine_replay(&payloads, end(), None, &mut |_, _| true)
            .unwrap();
        let mut paid = refined.prepay(end(), &mut |_, _| true).unwrap();
        match mode {
            0 => assert!(matches!(
                paid.take(ProofId(99), &mut |_, _| true),
                Err(BvCreditError::UnknownStep(ProofId(99)))
            )),
            1 => {
                drop(paid.take(ProofId(0), &mut |_, _| true).unwrap());
                assert!(matches!(
                    paid.take(ProofId(0), &mut |_, _| true),
                    Err(BvCreditError::AlreadyTaken(ProofId(0)))
                ));
            }
            _ => assert!(matches!(
                paid.take(ProofId(0), &mut |_, _| false),
                Err(BvCreditError::Refused)
            )),
        }
        let mut callbacks = 0;
        assert!(matches!(
            paid.take(ProofId(0), &mut |_, _| {
                callbacks += 1;
                true
            }),
            Err(BvCreditError::Refused)
        ));
        assert_eq!(callbacks, 0);
    }
}

#[test]
fn sparse_native_planner_and_native_fee_refusal_are_terminal_before_any_reader() {
    let (terms, proof) = sparse_fixture();
    let payloads = capture(&terms, &proof);
    let mut calls = Vec::new();
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |w, b| {
            calls.push((w, b));
            true
        })
        .unwrap();
    assert!(refined
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .is_some());
    for stop in 1..=calls.len() {
        let mut actual = 0;
        assert!(plan(&terms, &proof)
            .refine_replay(&payloads, end(), None, &mut |_, _| {
                actual += 1;
                actual != stop
            })
            .is_err());
        assert_eq!(actual, stop);
    }
}

#[test]
fn sparse_native_malformed_wire_preserves_exact_legacy_strict_error_class() {
    let (terms, proof) = sparse_fixture();
    let mut payloads = capture(&terms, &proof);
    for bytes in [b"null".as_slice(), b"{}", b"not JSON"] {
        payloads[0].payload = bytes.to_vec();
        let old = legacy_replay_error(&terms, &proof, &payloads);
        let new = plan(&terms, &proof)
            .refine_replay(&payloads, end(), None, &mut |_, _| true)
            .err()
            .unwrap();
        assert_eq!(invalid_step_and_reason(new), invalid_step_and_reason(old));
    }
}

#[test]
fn sparse_singleton_not_source_borrow_and_refinement_remain_search_free() {
    let (mut terms, mut proof) = sparse_fixture();
    let ProofStep::TheoryLemma { clause, .. } = &mut proof.steps[0] else {
        panic!("fixture");
    };
    let inner = terms.mk_not_raw(clause[0]);
    clause[0] = terms.mk_not_raw(inner);
    let snapshot = terms.entries_snapshot();
    let payloads = capture(&terms, &proof);
    let before = producer_test_counter::count();
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    assert!(refined
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .is_some());
    assert_eq!(terms.entries_snapshot(), snapshot);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn sparse_native_large_upper_bound_is_never_truncated_into_legacy_grant() {
    let (terms, proof) = sparse_fixture();
    let payloads = capture(&terms, &proof);
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    let price = refined
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .unwrap();
    assert!(price.with_native_work(usize::MAX).is_none());
    let inflated = price
        .with_native_work(MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize)
        .unwrap();
    let mut original = plan(&terms, &proof);
    let before = original.aggregate_charge();
    let entry = original.entries.iter_mut().flatten().next().unwrap();
    apply_price(entry, inflated);
    assert!(entry.replay_price.is_none());
    assert_eq!(entry.charge.work, before.work);
    assert_eq!(entry.charge.bytes, before.bytes);
    assert_eq!(original.aggregate_charge(), before);
}

#[test]
fn unchanged_expression_and_capture_api_keep_native_reserve_zero() {
    let (terms, proof) = fixture();
    let payloads = capture(&terms, &proof);
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    let price = refined
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .unwrap();
    assert_eq!(price.expression_work(), Some(price.work));
    let mut capture_credits = plan(&terms, &proof)
        .prepay(end(), &mut |_, _| true)
        .unwrap();
    let credit = capture_credits.take(ProofId(0), &mut |_, _| true).unwrap();
    assert!(credit.replay_price().is_none());
    assert_eq!(
        credit.into_allowance().work_limit(),
        MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA
    );
    capture_credits.finish().unwrap();
    let (terms, mut proof) = sparse_fixture();
    let payloads = capture(&terms, &proof);
    let ProofStep::TheoryLemma { lia, .. } = &mut proof.steps[0] else {
        panic!("fixture");
    };
    *lia = Some(ay_core::LiaAnnotation::BoundsGap);
    let old = plan(&terms, &proof).aggregate_charge();
    let kept = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    assert_eq!(kept.aggregate_charge(), old);
    assert!(kept
        .entries
        .iter()
        .flatten()
        .next()
        .unwrap()
        .replay_price
        .is_none());
}

#[test]
fn sparse_original_earlier_wire_deadline_and_low_resource_owners_are_not_renewed() {
    let (terms, proof) = sparse_fixture();
    let payloads = capture(&terms, &proof);
    let mut wire = transport_wire_limits(end());
    wire.deadline = Instant::now() - Duration::from_secs(1);
    let mut callbacks = 0;
    assert!(plan(&terms, &proof)
        .refine_replay(&payloads, end(), Some(wire), &mut |_, _| {
            callbacks += 1;
            true
        })
        .is_err());
    assert_eq!(callbacks, 0);
    let refined = plan(&terms, &proof)
        .refine_replay(&payloads, end(), None, &mut |_, _| true)
        .unwrap();
    let charge = refined.aggregate_charge();
    assert!(refined
        .prepay(end(), &mut |w, b| w < charge.work && b < charge.bytes)
        .is_err());
}

mod ge;
