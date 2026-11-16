// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
use super::*;

#[test]
fn actual_main_driver_decides_learns_repropagates_and_finishes_source_bound_unsat() {
    let mut expected = unsat();
    assert!(matches!(drive(&mut expected), SatResult::Unsat(_)));
    let mut s = unsat();
    let source_ids = s.cold.original_clause_id_bits.clone();
    let owner = generous();
    attach(&mut s, &owner);
    assert!(matches!(drive(&mut s), SatResult::Unsat(_)));
    assert!(s.num_decisions > 0 && s.num_conflicts > 0);
    assert!(s.cold.search_decisions > 0);
    assert!(rows(&s).iter().any(|r| !r.2 && !r.1.is_empty()));
    assert!(rows(&s).iter().any(|r| !r.2 && r.1.is_empty()));
    assert_eq!(s.cold.original_clause_id_bits, source_ids);
    assert_eq!(rows(&s), rows(&expected));
    assert_eq!(s.trail, expected.trail);
    assert_eq!(s.vals, expected.vals);
    // Ordinary analysis clears its SEEN marks lazily (at the next analysis or
    // reset), so its last analysis leaves them set, every one still tracked
    // for that clear. The counted scopes retire them at once (`clean`).
    for (var, data) in expected.var_data.iter().enumerate() {
        assert_eq!(
            data.is_seen(),
            expected.conflict.analyzed_vars().contains(&var)
        );
    }
    assert_eq!(assignments(&s), assignments(&expected));
    assert_eq!(s.num_decisions, expected.num_decisions);
    assert_eq!(s.num_conflicts, expected.num_conflicts);
    assert_eq!(s.conflicts_since_restart, expected.conflicts_since_restart);
    assert_eq!(s.stats.stable_conflicts, expected.stats.stable_conflicts);
    assert_eq!(s.cold.search_decisions, expected.cold.search_decisions);
    assert_eq!(
        s.counted_admission_usage().unwrap().unwrap(),
        owner.usage().unwrap()
    );
    assert!(!s.clause_trace().unwrap().proof_work_exhausted());
    assert!(owner.usage().unwrap().work_admitted > 0);
    clean(&s);
}

#[test]
fn complete_assignment_publishes_the_same_fully_validated_original_model() {
    let mut expected = sat();
    let ordinary = drive(&mut expected);
    assert!(matches!(ordinary, SatResult::Sat(_)));
    let mut s = sat();
    let owner = generous();
    attach(&mut s, &owner);
    let actual = drive(&mut s);
    assert_eq!(actual, ordinary);
    let SatResult::Sat(model) = actual else {
        panic!("counted SAT publication");
    };
    assert!(s.verify_external_model(&model));
    assert!(s.num_decisions > 0 && s.trail.len() == s.num_vars);
    assert_eq!(s.trail, expected.trail);
    assert_eq!(s.vals, expected.vals);
    assert_eq!(s.num_decisions, expected.num_decisions);
    assert!(owner.usage().unwrap().refusal.is_none());
    assert!(owner.usage().unwrap().storage_admitted >= 3 * s.num_vars);
    assert!(!s.clause_trace().unwrap().proof_work_exhausted());
    clean(&s);
}

#[test]
fn main_selection_preserves_main_route_even_with_domain_configuration() {
    for heuristic in [
        BranchHeuristic::Evsids,
        BranchHeuristic::Chb,
        BranchHeuristic::Vmtf,
    ] {
        let make = || {
            let mut s = sat();
            s.active_branch_heuristic = heuristic;
            s.active_domain = Some(vec![false; 3]);
            s.decision_domain = Some(vec![false; 3]);
            s
        };
        let mut expected = make();
        let chosen = expected
            .pick_next_decision_variable_main()
            .map(|v| expected.pick_phase(v));
        assert!(
            chosen.is_some(),
            "empty domain must not replace MAIN candidate selection"
        );
        let mut s = make();
        let owner = generous();
        attach(&mut s, &owner);
        assert_eq!(s.pick_main_decision_literal_counted(), Ok(chosen));
        assert_eq!(format!("{:?}", s.vsids), format!("{:?}", expected.vsids));
        assert_eq!(s.active_domain, expected.active_domain);
        assert_eq!(s.decision_domain, expected.decision_domain);
        assert_eq!(s.trail.len(), 0);
    }
}

#[test]
fn original_ordinary_complete_assignment_route_still_returns_a_checked_model() {
    let mut s = sat();
    let SatResult::Sat(model) = drive(&mut s) else {
        panic!("ordinary satisfiable source")
    };
    assert_eq!(model.len(), 3);
    assert!(model[0] || model[1]);
    assert!(s.cold.counted_admission.is_none());
}

#[test]
fn inherited_original_work_consumption_is_not_renewed_by_driver_entry() {
    let mut baseline = unsat();
    let owner = generous();
    attach(&mut baseline, &owner);
    assert!(matches!(drive(&mut baseline), SatResult::Unsat(_)));
    let used = owner.usage().unwrap();
    let mut s = unsat();
    let exact = test_owner(used.work_admitted + 7, used.storage_admitted);
    exact.admit(7, 0).unwrap();
    attach(&mut s, &exact);
    assert!(matches!(drive(&mut s), SatResult::Unsat(_)));
    let done = exact.usage().unwrap();
    assert_eq!(done.work_remaining, 0);
    assert_eq!(done.storage_remaining, 0);
    assert_eq!(done.work_admitted, used.work_admitted + 7);
}

#[test]
fn one_clause_sat_unsat_neighbors_use_the_same_real_ordinary_driver() {
    for omit_last in [false, true] {
        let make = || {
            let mut s = Solver::new(2);
            s.enable_clause_trace();
            s.set_unsat_certificate_enabled(false);
            let clauses = [
                vec![pos(0), pos(1)],
                vec![pos(0), neg(1)],
                vec![neg(0), pos(1)],
                vec![neg(0), neg(1)],
            ];
            for clause in clauses.iter().take(if omit_last { 3 } else { 4 }) {
                assert!(s.add_clause(clause.clone()));
            }
            s.initialize_watches();
            assert!(s.process_initial_clauses().is_none());
            s
        };
        let mut expected = make();
        let ordinary = drive(&mut expected);
        let mut s = make();
        let owner = generous();
        attach(&mut s, &owner);
        let result = drive(&mut s);
        assert_eq!(result, ordinary);
        assert!(s.num_decisions > 0);
        match result {
            SatResult::Sat(model) => {
                assert!(omit_last && s.verify_external_model(&model));
            }
            SatResult::Unsat(_) => assert!(!omit_last),
            SatResult::Unknown => panic!("neighbor escaped the admitted ordinary route"),
        }
        assert!(owner.usage().unwrap().refusal.is_none());
        assert_eq!(s.num_conflicts, expected.num_conflicts);
        assert_eq!(rows(&s), rows(&expected));
    }
}

#[test]
fn every_sat_driver_observer_cut_includes_the_outer_post_model_fence() {
    let calls = Arc::new(AtomicUsize::new(0));
    let mut baseline = sat();
    attach(&mut baseline, &observing(usize::MAX, &calls));
    assert!(matches!(drive(&mut baseline), SatResult::Sat(_)));
    let total = calls.load(Ordering::SeqCst);
    assert!(total > 50);
    for cut in 0..total {
        let mut s = sat();
        let calls = Arc::new(AtomicUsize::new(0));
        let owner = observing(cut, &calls);
        attach(&mut s, &owner);
        assert_eq!(drive(&mut s), SatResult::Unknown, "{cut}/{total}");
        assert_eq!(calls.load(Ordering::SeqCst), cut + 1);
        assert_eq!(
            owner.check(),
            Err(CountedAdmissionError::Original(
                OriginalAdmissionError::ObserverStopped
            ))
        );
        refused(&s, &owner);
    }
}
