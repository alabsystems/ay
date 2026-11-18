// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::counted_storage::test_owner;
use admitted::Counted;
use ay_core::original_query::{
    CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant, OriginalAdmissionError,
};
use std::sync::{
    atomic::{AtomicUsize, Ordering},
    Arc,
};

fn pos(v: u32) -> Literal {
    Literal::positive(Variable(v))
}
fn neg(v: u32) -> Literal {
    pos(v).negated()
}

/// The immutable source requires x0=x1, x2=!x1 and (x1 or x3).
pub(crate) fn original_clauses() -> Vec<Vec<Literal>> {
    vec![
        vec![neg(0), pos(1)],
        vec![pos(0), neg(1)],
        vec![neg(2), neg(1)],
        vec![pos(2), pos(1)],
        vec![pos(1), pos(3)],
    ]
}

/// Direct construction is essential: push_sweep now emits Witness entries.
pub(crate) fn legacy_stack() -> ReconstructionStack {
    ReconstructionStack {
        steps: vec![
            ReconstructionStep::Sweep {
                num_vars: 4,
                lit_map: vec![
                    pos(1),
                    neg(1),
                    pos(1),
                    neg(1),
                    neg(1),
                    pos(1),
                    pos(3),
                    neg(3),
                ],
            },
            ReconstructionStep::Witness(WitnessClause {
                witness: vec![pos(1)],
                clause: vec![pos(1), pos(3)],
            }),
        ],
        ever_pushed: true,
    }
}

pub(crate) fn wrong_sign_stack() -> ReconstructionStack {
    let mut stack = legacy_stack();
    let ReconstructionStep::Sweep { lit_map, .. } = &mut stack.steps[0] else {
        panic!("direct legacy Sweep fixture");
    };
    lit_map[0] = neg(1);
    lit_map[1] = pos(1);
    stack
}

fn satisfies_original(model: &[bool]) -> bool {
    original_clauses().iter().all(|clause| {
        clause.iter().any(|lit| {
            model
                .get(lit.variable().index())
                .is_some_and(|value| *value == lit.is_positive())
        })
    })
}

#[test]
fn legacy_sweep_requires_reverse_chronology_and_preserves_both_polarities() {
    let mut satisfying = 0;
    for bits in 0..16 {
        let model: Vec<bool> = (0..4).map(|v| bits & (1 << v) != 0).collect();
        let relation = model[0] == model[1] && model[2] != model[1] && (model[1] || model[3]);
        assert_eq!(satisfies_original(&model), relation);
        satisfying += usize::from(relation);
    }
    assert_eq!(satisfying, 3, "the five original clauses are not vacuous");
    let stack = legacy_stack();
    assert!(matches!(stack.steps[0], ReconstructionStep::Sweep { .. }));
    assert!(matches!(stack.steps[1], ReconstructionStep::Witness(_)));
    let mut ordinary = vec![false; 4];
    assert!(!satisfies_original(&ordinary));
    stack.reconstruct(&mut ordinary);
    assert_eq!(ordinary, vec![true, true, false, false]);
    assert!(satisfies_original(&ordinary));
    let owner = test_owner(1_000_000, 1_000_000);
    let mut actual = vec![false; 4];
    stack
        .reconstruct_admitted(&mut actual, &Counted(&owner))
        .unwrap();
    assert_eq!(actual, ordinary);
    assert!(owner.usage().unwrap().refusal.is_none());
    assert!(owner.usage().unwrap().work_admitted > 4);
    // A forward walk sees the old representative, then changes x1 too late.
    let mut wrong_order = stack.clone();
    wrong_order.steps.reverse();
    let mut counterexample = vec![false; 4];
    wrong_order.reconstruct(&mut counterexample);
    assert_eq!(counterexample, vec![false, true, true, false]);
    assert!(!satisfies_original(&counterexample));
}

#[test]
fn legacy_sweep_growth_exact_and_every_short_grant_preserve_original_owner() {
    let stack = legacy_stack();
    let mut ordinary = vec![false];
    stack.reconstruct(&mut ordinary);
    assert_eq!(ordinary, vec![true, true, false, false]);
    let owner = test_owner(1_000_000, 1_000_000);
    let mut actual = vec![false];
    stack
        .reconstruct_admitted(&mut actual, &Counted(&owner))
        .unwrap();
    assert_eq!(actual, ordinary);
    assert_eq!(actual.capacity(), ordinary.capacity());
    let used = owner.usage().unwrap();
    assert!(used.storage_admitted >= actual.capacity());
    let exact = test_owner(used.work_admitted + 7, used.storage_admitted + 5);
    exact.admit(7, 5).unwrap();
    stack
        .reconstruct_admitted(&mut vec![false], &Counted(&exact))
        .unwrap();
    assert_eq!(exact.usage().unwrap().work_remaining, 0);
    assert_eq!(exact.usage().unwrap().storage_remaining, 0);
    for limit in 0..used.work_admitted {
        assert_short(
            &stack,
            test_owner(limit, used.storage_admitted),
            CountedAdmissionError::WorkExhausted,
        );
    }
    for limit in 0..used.storage_admitted {
        assert_short(
            &stack,
            test_owner(used.work_admitted, limit),
            CountedAdmissionError::StorageExhausted,
        );
    }
}

fn assert_short(
    stack: &ReconstructionStack,
    owner: CountedAdmission,
    error: CountedAdmissionError,
) {
    let mut partial = vec![false];
    assert_eq!(
        stack.reconstruct_admitted(&mut partial, &Counted(&owner)),
        Err(error)
    );
    let stopped = owner.usage().unwrap();
    let before_retry = partial.clone();
    assert_eq!(
        stack.reconstruct_admitted(&mut partial, &Counted(&owner)),
        Err(error)
    );
    assert_eq!(partial, before_retry);
    assert_eq!(owner.usage().unwrap(), stopped);
}

fn observing(cut: usize, calls: &Arc<AtomicUsize>) -> CountedAdmission {
    let seen = Arc::clone(calls);
    CountedAdmission::new(
        FiniteAdmissionGrant::new(1_000_000, 1_000_000),
        None,
        Arc::new(move || seen.fetch_add(1, Ordering::SeqCst) == cut),
    )
    .unwrap()
}

#[test]
fn every_legacy_sweep_growth_observer_cut_stops_without_replaying_partial_state() {
    let stack = legacy_stack();
    let calls = Arc::new(AtomicUsize::new(0));
    let owner = observing(usize::MAX, &calls);
    let mut complete = vec![false];
    stack
        .reconstruct_admitted(&mut complete, &Counted(&owner))
        .unwrap();
    assert_eq!(complete, vec![true, true, false, false]);
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 4);
    for cut in 0..total {
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing(cut, &calls);
        assert_short(
            &stack,
            owner,
            CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped),
        );
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1, "{cut}/{total}");
    }
}
