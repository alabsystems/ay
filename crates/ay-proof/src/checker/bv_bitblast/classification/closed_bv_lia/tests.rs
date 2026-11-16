// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::credits::BvCreditError;
use super::*;
use ay_core::time::Instant;
use std::time::Duration;

fn chain(value: bool, negations: usize) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let mut root = if value {
        terms.true_term()
    } else {
        terms.false_term()
    };
    for _ in 0..negations {
        root = terms.mk_not_raw(root);
    }
    (terms, root)
}

fn tagged(root: TermId) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "BV_LIA".into(),
        clause: vec![root],
        farkas: None,
        kind: TheoryLemmaKind::BvLiaTautology,
        lia: None,
    }
}

fn charge(terms: &TermStore, step: ProofStep) -> ExpensiveBvAggregateCharge {
    validate_expensive_bv_budget_with_progress(
        &Proof::from_steps(vec![step]),
        terms,
        &mut |_, _| true,
    )
    .unwrap()
}

fn old() -> ExpensiveBvAggregateCharge {
    ExpensiveBvAggregateCharge {
        work: MAX_BV_LIA_TAUTOLOGY_WORK_PER_LEMMA as usize,
        bytes: MAX_BV_LIA_TAUTOLOGY_BYTES_PER_LEMMA,
    }
}

#[test]
fn closed_const_chain_fee_is_not_a_truth_decision_or_native_rule_shortcut() {
    for value in [false, true] {
        let (terms, root) = chain(value, 2);
        let source = terms.entries_snapshot();
        let priced = charge(&terms, tagged(root));
        assert_eq!((priced.work, priced.bytes), CHARGE);
        let result = crate::checker::bv_lia_query::validate_bv_lia_tautology(
            &terms,
            ProofId(0),
            &[root],
            false,
            false,
        );
        assert_eq!(result.is_ok(), value);
        if !value {
            assert!(matches!(
                result,
                Err(ProofCheckError::InvalidTheoryLemma {
                    step: ProofId(0),
                    ..
                })
            ));
        }
        assert_eq!(terms.entries_snapshot(), source);
    }
}

#[test]
fn exact_thirty_two_term_chain_fits_but_next_term_retains_original_fee() {
    let (mut terms, root) = chain(true, MAX_CHAIN_TERMS - 1);
    let priced = charge(&terms, tagged(root));
    assert_eq!((priced.work, priced.bytes), CHARGE);
    let deeper = terms.mk_not_raw(root);
    assert_eq!(charge(&terms, tagged(deeper)), old());
}

#[test]
fn dangling_cycle_and_ill_sorted_sources_keep_exact_old_fee_without_panicking() {
    for entries in [
        vec![(TermData::Not(TermId(0)), Sort::Bool)],
        vec![(TermData::Not(TermId(1)), Sort::Bool)],
        vec![
            (TermData::Not(TermId(1)), Sort::Bool),
            (TermData::Const(Constant::Bool(false)), Sort::bitvec(1)),
        ],
        vec![
            (TermData::Not(TermId(1)), Sort::bitvec(1)),
            (TermData::Const(Constant::Bool(false)), Sort::Bool),
        ],
    ] {
        let terms = TermStore::from_entries(entries, None, None, 0);
        assert_eq!(charge(&terms, tagged(TermId(0))), old());
    }
    let terms = TermStore::new();
    assert_eq!(charge(&terms, tagged(TermId(u32::MAX))), old());
}

#[test]
fn variables_apps_ite_bv_and_indexed_syntax_are_not_discounted() {
    let mut terms = TermStore::new();
    let boolean = terms.mk_var("unknown-boolean", Sort::Bool);
    let constant = terms.true_term();
    let app = terms.mk_app(Symbol::named("or"), [constant], Sort::Bool);
    let indexed = terms.mk_app(Symbol::indexed("unknown", vec![0]), [], Sort::Bool);
    let choice = terms.mk_ite_raw(boolean, constant, constant);
    let bv = terms.mk_bitvec(0.into(), 1);
    for body in [boolean, app, indexed, choice] {
        let literal = terms.mk_not_raw(body);
        assert_eq!(charge(&terms, tagged(literal)), old());
    }
    // The checked Bool constructor correctly refuses Not(BV). Import the
    // malformed native entries directly to test the checker's own boundary.
    let malformed = TermStore::from_entries(
        vec![
            (TermData::Not(TermId(1)), Sort::Bool),
            (terms.get(bv).clone(), terms.sort(bv).clone()),
        ],
        None,
        None,
        0,
    );
    assert_eq!(charge(&malformed, tagged(TermId(0))), old());
}

#[test]
fn annotations_non_singletons_and_other_families_keep_original_fees() {
    let (terms, root) = chain(true, 2);
    let mut annotated = tagged(root);
    let ProofStep::TheoryLemma { farkas, .. } = &mut annotated else {
        panic!("fixture");
    };
    *farkas = Some(ay_core::FarkasAnnotation::new(vec![]));
    assert_eq!(charge(&terms, annotated), old());
    let mut annotated = tagged(root);
    let ProofStep::TheoryLemma { lia, .. } = &mut annotated else {
        panic!("fixture");
    };
    *lia = Some(ay_core::LiaAnnotation::BoundsGap);
    assert_eq!(charge(&terms, annotated), old());
    for clause in [vec![], vec![root, root], vec![terms.true_term()]] {
        let mut step = tagged(root);
        let ProofStep::TheoryLemma { clause: target, .. } = &mut step else {
            panic!("fixture");
        };
        *target = clause;
        assert_eq!(charge(&terms, step), old());
    }
    let mut companion = tagged(root);
    let ProofStep::TheoryLemma { kind, .. } = &mut companion else {
        panic!("fixture");
    };
    *kind = TheoryLemmaKind::SeqExtensionalCompanionContradiction;
    assert_eq!(charge(&terms, companion), old());
}

#[test]
fn every_census_checkpoint_stop_is_sticky_and_never_retried_after_refusal() {
    let (terms, root) = chain(true, MAX_CHAIN_TERMS - 1);
    let proof = Proof::from_steps(vec![tagged(root)]);
    let mut total = 0;
    validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |w, b| {
        assert_eq!((w, b), (0, 0));
        total += 1;
        true
    })
    .unwrap();
    for stop in 1..=total {
        let mut calls = 0;
        let result = validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop);
    }
}

#[test]
fn repeated_cheap_lemmas_still_consume_each_original_shared_count_slot() {
    let (terms, root) = chain(true, 2);
    let mut proof = Proof::new();
    for _ in 0..MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF {
        proof.add_step(tagged(root));
    }
    let total =
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| true).unwrap();
    assert_eq!(total.work, CHARGE.0 * MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF);
    assert_eq!(total.bytes, CHARGE.1 * MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF);
    proof.add_step(tagged(root));
    assert!(matches!(
        validate_expensive_bv_budget_with_progress(&proof, &terms, &mut |_, _| true),
        Err(ProofCheckError::InvalidTheoryLemma {
            step: ProofId(8),
            ..
        })
    ));
}

#[test]
fn reduced_aggregate_low_work_or_bytes_refuses_without_an_inner_grant() {
    let (terms, root) = chain(true, 2);
    let proof = Proof::from_steps(vec![tagged(root)]);
    for work_owner in [true, false] {
        let plan =
            plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| true).unwrap();
        let mut calls = 0;
        let result = plan.prepay(Instant::now() + Duration::from_secs(60), &mut |w, b| {
            calls += 1;
            if work_owner {
                w < CHARGE.0
            } else {
                b < CHARGE.1
            }
        });
        assert!(matches!(result, Err(BvCreditError::Refused)));
        assert_eq!(calls, 1);
    }
}

#[test]
fn closed_bv_lia_credit_is_nonordinary_single_owner_and_deadline_bound() {
    let (terms, root) = chain(true, 2);
    let proof = Proof::from_steps(vec![tagged(root)]);
    let plan = plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| true).unwrap();
    let deadline = Instant::now() + Duration::from_secs(60);
    let mut paid = Vec::new();
    let mut credit = plan
        .prepay(deadline, &mut |w, b| {
            paid.push((w, b));
            true
        })
        .unwrap();
    assert_eq!(paid, [CHARGE, (0, 0)]);
    assert_eq!(credit.ordinary_count(), 0);
    assert_eq!(credit.deadline(), deadline);
    assert!(matches!(
        credit.take(ProofId(0), &mut |_, _| true),
        Err(BvCreditError::NonOrdinary(ProofId(0)))
    ));
    let mut calls = 0;
    assert!(matches!(
        credit.take(ProofId(0), &mut |_, _| {
            calls += 1;
            true
        }),
        Err(BvCreditError::Refused)
    ));
    assert_eq!(calls, 0);
    let plan = plan_expensive_bv_credits_with_progress(&proof, &terms, &mut |_, _| true).unwrap();
    assert!(matches!(
        plan.prepay(Instant::now(), &mut |_, _| {
            calls += 1;
            true
        }),
        Err(BvCreditError::Deadline)
    ));
    assert_eq!(calls, 0);
}
