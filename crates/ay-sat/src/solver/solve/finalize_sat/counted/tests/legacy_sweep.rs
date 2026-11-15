// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use crate::reconstruct::legacy_sweep_tests::{legacy_stack, original_clauses, wrong_sign_stack};

fn fixture() -> Solver {
    let mut s = Solver::new(4);
    s.enable_clause_trace();
    s.set_unsat_certificate_enabled(false);
    for clause in original_clauses() {
        assert!(s.add_clause(clause));
    }
    let indices: Vec<_> = s.arena.indices().collect();
    for index in indices {
        s.arena.mark_garbage_keep_data(index);
    }
    for var in 0..3 {
        s.var_lifecycle.mark_eliminated(var);
    }
    s.inproc.reconstruction = legacy_stack();
    assert!(matches!(
        s.inproc.reconstruction.steps_ref()[0],
        crate::reconstruct::ReconstructionStep::Sweep { .. }
    ));
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    s.decide(neg(3));
    assert!(s.propagate().is_none());
    assert_eq!(s.get_model(), vec![false; 4]);
    assert_eq!(s.trail, vec![neg(3)]);
    s
}

fn baseline() -> ay_core::original_query::AdmissionUsage {
    let mut s = fixture();
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(SatResult::Sat(vec![true, true, false, false]))
    );
    admission.usage().unwrap()
}

#[test]
fn reached_legacy_sweep_publishes_ordinary_model_only_after_original_replay() {
    let mut ordinary = fixture();
    assert!(!ordinary.verify_external_model(&ordinary.get_model()));
    let expected = ordinary.declare_sat_from_current_assignment();
    assert_eq!(expected, SatResult::Sat(vec![true, true, false, false]));
    let mut s = fixture();
    let before_vals = s.vals.clone();
    let admission = owner();
    attach(&mut s, &admission);
    let actual = s.declare_counted_complete_assignment_sat(&admission);
    assert_eq!(actual, Ok(expected));
    let Ok(SatResult::Sat(model)) = actual else {
        panic!("legacy Sweep SAT model");
    };
    assert!(s.verify_external_model(&model));
    assert_eq!(
        s.vals, before_vals,
        "only private external model is reconstructed"
    );
    assert_eq!(s.vals, ordinary.vals);
    assert_eq!(s.trail, ordinary.trail);
    let ledger = |s: &Solver| {
        s.cold
            .original_ledger
            .iter_clauses()
            .map(<[Literal]>::to_vec)
            .collect::<Vec<_>>()
    };
    // `add_clause` registers each original in its normalized (sorted,
    // duplicate-free) literal order; publication leaves exactly those rows.
    let normalized: Vec<_> = original_clauses()
        .into_iter()
        .map(|mut clause| {
            clause.sort_by_key(|l| l.0);
            clause.dedup();
            clause
        })
        .collect();
    assert_eq!(ledger(&s), normalized);
    assert_eq!(ledger(&s), ledger(&ordinary));
    assert!(admission.usage().unwrap().refusal.is_none());
    assert!(!s.clause_trace().unwrap().proof_work_exhausted());
}

#[test]
fn legacy_sweep_wrong_polarity_cannot_replace_original_ledger_authority() {
    let mut s = fixture();
    s.inproc.reconstruction = wrong_sign_stack();
    let mut counterfeit = s.get_model();
    s.inproc.reconstruction.reconstruct(&mut counterfeit);
    assert_eq!(counterfeit, vec![false, true, false, false]);
    assert!(!s.verify_external_model(&counterfeit));
    assert!(
        s.verify_model(&counterfeit),
        "deleted arena alone is vacuously satisfied"
    );
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Err(SatUnknownReason::InvalidSatModel)
    );
    assert_eq!(s.cold.finalize_sat_fail_count, 1);
    refused(&s, &admission);
}

#[test]
fn legacy_sweep_terminal_exact_and_every_short_budget_never_publish_after_stop() {
    let used = baseline();
    assert!(used.work_admitted > 64 && used.storage_admitted >= 12);
    let mut s = fixture();
    let exact = test_owner(used.work_admitted + 7, used.storage_admitted + 5);
    exact.admit(7, 5).unwrap();
    attach(&mut s, &exact);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&exact),
        Ok(SatResult::Sat(vec![true, true, false, false]))
    );
    assert_eq!(exact.usage().unwrap().work_remaining, 0);
    assert_eq!(exact.usage().unwrap().storage_remaining, 0);
    assert!(exact.shares_ledger_with(s.cold.counted_admission.as_ref().unwrap()));
    for limit in 0..used.work_admitted {
        let mut s = fixture();
        let admission = test_owner(limit, used.storage_admitted);
        attach(&mut s, &admission);
        assert!(s
            .declare_counted_complete_assignment_sat(&admission)
            .is_err());
        assert_eq!(admission.check(), Err(CountedAdmissionError::WorkExhausted));
        refused(&s, &admission);
    }
    for limit in 0..used.storage_admitted {
        let mut s = fixture();
        let admission = test_owner(used.work_admitted, limit);
        attach(&mut s, &admission);
        assert!(s
            .declare_counted_complete_assignment_sat(&admission)
            .is_err());
        assert_eq!(
            admission.check(),
            Err(CountedAdmissionError::StorageExhausted)
        );
        refused(&s, &admission);
    }
}

#[test]
fn every_legacy_sweep_terminal_observer_cut_keeps_partial_model_private() {
    let mut s = fixture();
    let calls = Arc::new(AtomicUsize::new(0));
    let admission = observed(usize::MAX, &calls);
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(SatResult::Sat(vec![true, true, false, false]))
    );
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 50);
    for cut in 0..total {
        let mut s = fixture();
        let vals = s.vals.clone();
        let calls = Arc::new(AtomicUsize::new(0));
        let admission = observed(cut, &calls);
        attach(&mut s, &admission);
        assert!(
            s.declare_counted_complete_assignment_sat(&admission)
                .is_err(),
            "{cut}/{total}"
        );
        let stopped = admission.usage().unwrap();
        assert!(s
            .declare_counted_complete_assignment_sat(&admission)
            .is_err());
        assert_eq!(admission.usage().unwrap(), stopped);
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(s.vals, vals);
        assert_eq!(
            admission.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverStopped
            ))
        );
        refused(&s, &admission);
    }
}
