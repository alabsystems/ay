// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod controls;
mod fixtures;
use fixtures::{deadline, mixed, ordinary, plan, prepaid};

#[test]
fn mixed_families_share_the_exact_legacy_census_and_single_aggregate_debit() {
    let (proof, terms) = mixed();
    let mut legacy_polls = Vec::new();
    let legacy = validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |w, b| {
        legacy_polls.push((w, b));
        true
    })
    .unwrap();
    let mut plan_polls = Vec::new();
    let plan = plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |w, b| {
        plan_polls.push((w, b));
        true
    })
    .unwrap();
    assert_eq!(legacy_polls, plan_polls);
    assert_eq!(plan.aggregate_charge(), legacy);
    assert_eq!(
        legacy,
        ExpensiveBvAggregateCharge {
            work: 2 * MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize
                + 5 * MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA as usize
                + closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA as usize,
            bytes: 2 * MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
                + 5 * MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA
                + closed_bv_evaluate::MAX_CLOSED_BV_EVALUATE_BYTES_PER_LEMMA,
        }
    );
    let end = deadline();
    let mut debits = Vec::new();
    let mut credits = plan
        .prepay(end, &mut |w, b| {
            debits.push((w, b));
            true
        })
        .unwrap();
    assert_eq!(debits, [(legacy.work, legacy.bytes), (0, 0)]);
    assert_eq!(credits.ordinary_count(), 2);
    assert_eq!(
        credits.ordinary_ids().collect::<Vec<_>>(),
        [ProofId(1), ProofId(2)]
    );
    assert!(std::ptr::eq(credits.terms(), &raw const terms));
    assert_eq!(credits.deadline(), end);
    for id in [ProofId(2), ProofId(1)] {
        let credit = credits
            .take(id, &mut |w, b| {
                assert_eq!((w, b), (0, 0));
                true
            })
            .unwrap();
        assert_eq!(credit.id(), id);
        assert!(std::ptr::eq(
            credit.step(),
            &raw const proof.steps[id.0 as usize]
        ));
        assert!(std::ptr::eq(credit.terms(), &raw const terms));
        let ProofStep::TheoryLemma { clause, .. } = credit.step() else {
            panic!("fixture")
        };
        assert!(std::ptr::eq(credit.clause(), clause.as_slice()));
        assert_eq!(
            credit.charge(),
            ExpensiveBvAggregateCharge {
                work: MAX_PROOF_PRODUCING_BV_WORK_PER_LEMMA as usize,
                bytes: MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA,
            }
        );
        assert_eq!(credit.into_allowance().deadline(), end);
    }
    assert_eq!(credits.ordinary_count(), 2); // Inventory does not shrink on use.
    assert_eq!(credits.finish(), Ok(())); // Other families were paid, not issued.
}

#[test]
fn ninth_mixed_entry_refuses_with_legacy_error_and_poll_sequence() {
    let (mut proof, terms) = mixed();
    proof.add_step(proof.steps[1].clone());
    let mut old_polls = Vec::new();
    let old = validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |w, b| {
        old_polls.push((w, b));
        true
    });
    let mut new_polls = Vec::new();
    let new = plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |w, b| {
        new_polls.push((w, b));
        true
    })
    .map(|plan| plan.aggregate_charge());
    assert_eq!(new, old);
    assert_eq!(new_polls, old_polls);
    assert!(matches!(
        new,
        Err(ProofCheckError::InvalidTheoryLemma {
            step: ProofId(9),
            ..
        })
    ));
}

#[test]
fn source_positions_not_names_or_equal_clauses_define_one_use_credits() {
    let (mut proof, terms) = ordinary(2);
    proof.named_steps.insert("0".to_owned(), ProofId(1));
    let mut credits = prepaid(&proof, &terms);
    assert_eq!(
        credits.ordinary_ids().collect::<Vec<_>>(),
        [ProofId(0), ProofId(1)]
    );
    assert!(std::ptr::eq(
        credits.source_step(ProofId(0)).unwrap(),
        &raw const proof.steps[0]
    ));
    assert!(credits.source_step(ProofId(2)).is_none());
    for id in [ProofId(0), ProofId(1)] {
        let _credit = credits.take(id, &mut |_, _| true).unwrap();
    }
    assert!(matches!(
        credits.take(ProofId(0), &mut |_, _| true),
        Err(BvCreditError::AlreadyTaken(ProofId(0)))
    ));
    assert!(matches!(
        credits.take(ProofId(1), &mut |_, _| panic!("poisoned")),
        Err(BvCreditError::Refused)
    ));
    assert_eq!(credits.finish(), Err(BvCreditError::Refused));
}

#[test]
fn cheap_nonordinary_wrong_and_unconsumed_ids_cannot_issue_or_complete() {
    let (proof, terms) = mixed();
    for (id, expected) in [
        (ProofId(0), BvCreditError::UnknownStep(ProofId(0))),
        (ProofId(3), BvCreditError::NonOrdinary(ProofId(3))),
        (ProofId(5), BvCreditError::NonOrdinary(ProofId(5))),
        (
            ProofId(u32::MAX),
            BvCreditError::UnknownStep(ProofId(u32::MAX)),
        ),
    ] {
        let mut credits = prepaid(&proof, &terms);
        assert!(credits.source_step(id).is_none());
        assert_eq!(credits.take(id, &mut |_, _| true).err(), Some(expected));
        assert!(matches!(
            credits.take(ProofId(1), &mut |_, _| panic!("poisoned")),
            Err(BvCreditError::Refused)
        ));
        assert_eq!(credits.finish(), Err(BvCreditError::Refused));
    }
    let mut credits = prepaid(&proof, &terms);
    {
        let _credit = credits.take(ProofId(1), &mut |_, _| true).unwrap();
    }
    assert_eq!(credits.finish(), Err(BvCreditError::Unconsumed(ProofId(2))));
}

#[test]
fn empty_and_nonordinary_only_plans_need_no_ordinary_consumption() {
    let (mut proof, mut terms) = mixed();
    proof.steps.retain(|step| {
        !matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. },
                ..
            }
        )
    });
    let narrow = terms.mk_var("cheap", Sort::bitvec(1));
    let equality = terms.mk_app(Symbol::named("="), [narrow, narrow], Sort::Bool);
    let cheap_id = proof.add_step(fixtures::tagged(equality, TheoryLemmaKind::BvBitBlast));
    let mut credits = prepaid(&proof, &terms);
    assert!(credits.source_step(cheap_id).is_none());
    assert_eq!(
        credits.take(cheap_id, &mut |_, _| true).err(),
        Some(BvCreditError::UnknownStep(cheap_id))
    );
    assert_eq!(credits.finish(), Err(BvCreditError::Refused));
    for proof in [&Proof::new(), &proof] {
        let credits = prepaid(proof, &terms);
        assert_eq!(credits.ordinary_count(), 0);
        assert!(credits.ordinary_ids().next().is_none());
        assert_eq!(credits.finish(), Ok(()));
    }
}

#[test]
fn credit_is_source_accounting_not_semantic_or_gate_authority() {
    let (mut proof, mut terms) = ordinary(1);
    let var = terms.mk_var("false-claim", Sort::bitvec(16));
    let zero = terms.mk_bitvec(num_bigint::BigInt::from(0), 16);
    let false_claim = terms.mk_app(Symbol::named("="), [var, zero], Sort::Bool);
    proof.steps[0] = fixtures::tagged(
        false_claim,
        TheoryLemmaKind::BvBitBlastGate {
            gate_type: BvGateType::And,
            width: 3,
        },
    );
    let mut credits = prepaid(&proof, &terms);
    {
        let credit = credits.take(ProofId(0), &mut |_, _| true).unwrap();
        assert_eq!(credit.clause(), [false_claim]);
        assert!(matches!(
            credit.step(),
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::BvBitBlastGate {
                    gate_type: BvGateType::And,
                    width: 3
                },
                ..
            }
        ));
    }
    // Only the separate gate/source/semantic validator may reject this claim.
    assert_eq!(credits.finish(), Ok(()));
}
