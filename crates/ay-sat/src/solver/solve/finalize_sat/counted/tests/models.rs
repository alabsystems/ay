// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn ordinary_and_counted_reconstruct_actual_removed_variable_identically() {
    let mut expected = reconstructed();
    let ordinary = expected.declare_sat_from_current_assignment();
    assert_eq!(ordinary, SatResult::Sat(vec![true, false, true]));
    let mut s = reconstructed();
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(ordinary)
    );
    assert_eq!(
        s.vals, expected.vals,
        "reconstruction must not rewrite CDCL assignment"
    );
    assert!(s.var_lifecycle.is_removed(0));
    assert_eq!(s.inproc.reconstruction.len(), 2);
    assert!(admission.usage().unwrap().refusal.is_none());
    assert!(!s.clause_trace().unwrap().proof_work_exhausted());
}

#[test]
fn saved_compacted_external_assignment_is_preserved_and_rechecked() {
    let make = || {
        let mut s = Solver::new(2);
        s.enable_clause_trace();
        s.set_unsat_certificate_enabled(false);
        assert!(s.add_clause(vec![pos(0), pos(1)]));
        s.initialize_watches();
        assert!(s.process_initial_clauses().is_none());
        s.decide(pos(0));
        assert!(s.propagate().is_none());
        s.decide(neg(1));
        assert!(s.propagate().is_none());
        // Exact compacted shape: two internal variables, three external ones.
        // The third variable survives only in saved external state and ledger.
        s.cold.e2i.push(compact::UNMAPPED);
        s.user_num_vars = 3;
        s.cold.eliminated_ext_vals = vec![false, false, true];
        s.cold.original_ledger.push_clause(&[pos(2)]);
        s
    };
    let mut ordinary = make();
    let expected = ordinary.declare_sat_from_current_assignment();
    assert_eq!(expected, SatResult::Sat(vec![true, false, true]));
    let mut s = make();
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Ok(expected)
    );
}

#[test]
fn supplied_phase_model_remains_authoritative_in_shared_ordinary_mapping() {
    let s = assigned();
    let candidate = vec![false, true, false];
    assert_ne!(candidate, s.get_model());
    assert_eq!(s.finalize_sat_model(candidate.clone()), Ok(candidate));
}

#[test]
fn immutable_original_clause_lost_from_arena_still_rejects_model() {
    let mut s = assigned();
    s.cold.original_ledger.push_clause(&[neg(0), pos(1)]);
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Err(SatUnknownReason::InvalidSatModel)
    );
    assert_eq!(s.cold.finalize_sat_fail_count, 1);
    assert_eq!(
        s.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel)
    );
    refused(&s, &admission);
}

#[test]
fn original_unit_violation_refuses_before_any_reconstruction_repair() {
    let mut s = assigned();
    s.cold.original_ledger.push_clause(&[neg(0)]);
    s.inproc
        .reconstruction
        .push_witness_clause(vec![neg(0)], vec![neg(0)]);
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
fn post_truncation_original_gate_is_not_replaced_by_pretruncate_validation() {
    let mut s = assigned();
    s.cold.original_ledger.push_clause(&[pos(2)]);
    s.user_num_vars = 2;
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
fn invalid_reconstruction_cannot_publish_model_or_repair_corrupt_originals() {
    let mut s = reconstructed();
    // Reverse order first forces x2=false. The remaining witness cannot
    // satisfy both immutable original clauses under that assignment.
    s.inproc
        .reconstruction
        .push_witness_clause(vec![neg(2)], vec![neg(2)]);
    let admission = owner();
    attach(&mut s, &admission);
    assert_eq!(
        s.declare_counted_complete_assignment_sat(&admission),
        Err(SatUnknownReason::InvalidSatModel)
    );
    refused(&s, &admission);
}

#[test]
fn configured_scope_and_domain_are_refused_without_mutating_selection() {
    for domain in [false, true] {
        let mut s = assigned();
        if domain {
            s.active_domain = Some(vec![false; 3]);
        } else {
            s.cold.scope_selectors.push(Variable(2));
        }
        let scope_before = s.cold.scope_selectors.clone();
        let domain_before = s.active_domain.clone();
        let admission = owner();
        attach(&mut s, &admission);
        assert!(s
            .declare_counted_complete_assignment_sat(&admission)
            .is_err());
        assert_eq!(s.cold.scope_selectors, scope_before);
        assert_eq!(s.active_domain, domain_before);
        refused(&s, &admission);
    }
}

#[test]
fn foreign_owner_cannot_publish_or_spend_attached_original_credit() {
    let mut s = assigned();
    let attached = owner();
    let foreign = owner();
    attach(&mut s, &attached);
    let before = attached.usage().unwrap();
    assert!(s.declare_counted_complete_assignment_sat(&foreign).is_err());
    assert_eq!(attached.usage().unwrap(), before);
    assert!(foreign.usage().unwrap().refusal.is_some());
    assert!(s.clause_trace().unwrap().proof_work_exhausted());
}

#[test]
fn shared_original_and_arena_validators_match_truth_tables_for_all_assignments() {
    use crate::solver::preprocess_verify::admitted::{ArenaMode, OriginalDomain};
    let clauses = vec![vec![pos(0), neg(1)], vec![pos(1), pos(2)]];
    let mut s = Solver::new(3);
    for clause in &clauses {
        assert!(s.add_clause(clause.clone()));
    }
    for bits in 0..8 {
        let model: Vec<bool> = (0..3).map(|v| bits & (1 << v) != 0).collect();
        let expected = clauses.iter().position(|clause| {
            !clause
                .iter()
                .any(|lit| model[lit.variable().index()] == lit.is_positive())
        });
        let admission = owner();
        let policy = Counted(&admission);
        assert_eq!(
            s.first_original_violation_admitted(&model, OriginalDomain::Full, &policy)
                .unwrap(),
            expected
        );
        assert_eq!(
            s.first_arena_violation_admitted(&model, ArenaMode::Full, &policy)
                .unwrap()
                .is_some(),
            expected.is_some()
        );
        assert_eq!(s.verify_external_model(&model), expected.is_none());
        assert_eq!(
            s.first_model_violation(&model, false).is_some(),
            expected.is_some()
        );
        assert!(admission.usage().unwrap().work_admitted > 0);
    }
}

#[test]
fn shared_replay_growth_is_fallible_and_preserves_ordinary_capacity_and_order() {
    let mut stack = crate::reconstruct::ReconstructionStack::new();
    stack.push_witness_clause(vec![pos(2)], vec![pos(2), pos(0)]);
    stack.push_witness_clause(vec![neg(0)], vec![neg(0)]);
    let initial = vec![true];
    let mut expected = initial.clone();
    stack.reconstruct(&mut expected);
    assert_eq!(expected, vec![false, false, true]);
    let admission = owner();
    let mut actual = initial.clone();
    stack
        .reconstruct_admitted(&mut actual, &Counted(&admission))
        .unwrap();
    assert_eq!(actual, expected);
    assert_eq!(actual.capacity(), expected.capacity());
    let used = admission.usage().unwrap();
    assert!(used.storage_admitted >= actual.capacity());
    for limit in 0..used.storage_admitted {
        let admission = test_owner(used.work_admitted, limit);
        let mut candidate = initial.clone();
        assert!(stack
            .reconstruct_admitted(&mut candidate, &Counted(&admission))
            .is_err());
        assert_eq!(
            admission.check(),
            Err(CountedAdmissionError::StorageExhausted)
        );
    }
}
