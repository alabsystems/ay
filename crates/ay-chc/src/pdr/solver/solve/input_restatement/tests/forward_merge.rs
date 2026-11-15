// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The incoming recorded clause maps and retained original owner compose.

use super::*;
use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
use crate::pdr::CounterexampleStep;

fn split_expansion() -> (PdrSolver, Counterexample) {
    let (mut solver, _) = prepared(PdrConfig::default());
    let duplicate = solver.problem.clauses()[0].clone();
    solver.problem.add_clause(duplicate);
    assert_eq!(solver.problem.clauses().len(), 3);
    solver.problem.clauses_mut().rotate_right(1);
    solver.case_split_origins = Some(vec![0, 0, 1]);
    let p = solver.problem.lookup_predicate("P").unwrap();
    let mut cex = candidate();
    let ground = cex.ground_derivation.as_mut().unwrap();
    ground.steps[0].clause_index = 1;
    ground.steps[1].clause_index = 2;
    assert_eq!(validate_ground_derivation(&solver.problem, ground), Ok(()));
    cex.witness = Some(DerivationWitness {
        root: 0,
        query_clause: Some(2),
        entries: vec![DerivationWitnessEntry {
            predicate: p,
            level: 0,
            state: ChcExpr::Bool(true),
            incoming_clause: Some(1),
            premises: vec![],
            instances: FxHashMap::default(),
        }],
    });
    let mut step = CounterexampleStep::new(p, FxHashMap::default());
    step.clause_index = Some(1);
    cex.steps = vec![step];
    (solver, cex)
}

#[test]
fn recorded_case_map_precedes_nullary_map_and_replays_original() {
    let (solver, cex) = split_expansion();
    let owner = solver.input_restatement_owner();
    let cex = solver.restate_cex_for_input(cex, &owner).unwrap();
    let ground = cex.ground_derivation.as_ref().unwrap();
    assert_eq!(validate_ground_derivation(&input(), ground), Ok(()));
    assert_eq!(
        ground
            .steps
            .iter()
            .map(|s| s.clause_index)
            .collect::<Vec<_>>(),
        vec![0, 1, 2]
    );
    let witness = cex.witness.as_ref().unwrap();
    assert_eq!(witness.entries[0].incoming_clause, Some(0));
    assert_eq!(witness.entries[witness.root].incoming_clause, Some(1));
    assert_eq!(witness.entries[witness.root].premises, vec![0]);
    assert_eq!(witness.query_clause, Some(2));
    assert_eq!(cex.steps[0].clause_index, Some(0));
    assert!(owner.open());
}

fn observations(refusal: Option<usize>) -> usize {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let (solver, cex) = split_expansion();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        let at = observed.fetch_add(1, Ordering::Relaxed) + 1;
        refusal == Some(at)
    }));
    let owner = solver.input_restatement_owner();
    let result = solver.restate_cex_for_input(cex, &owner);
    if let Some(at) = refusal {
        assert!(
            result.is_err(),
            "one-shot refusal {at} must not drop into fallback"
        );
        assert!(!owner.open(), "refusal must remain terminal");
        assert_eq!(calls.load(Ordering::Relaxed), at);
    } else {
        let cex = result.unwrap();
        assert!(cex.ground_derivation.is_some());
        assert!(cex.witness.is_some());
    }
    calls.load(Ordering::Relaxed)
}

#[test]
fn every_split_nullary_and_witness_mapping_poll_keeps_first_refusal() {
    let total = observations(None);
    assert!(total > 10);
    for refusal in 1..=total {
        observations(Some(refusal));
    }
}

#[test]
fn fail_routing_level_overflow_drops_witness_not_original_ground() {
    let (solver, mut cex) = split_expansion();
    cex.witness.as_mut().unwrap().entries[0].level = usize::MAX;
    let owner = solver.input_restatement_owner();
    let cex = solver.restate_cex_for_input(cex, &owner).unwrap();
    assert!(cex.witness.is_none());
    assert_eq!(
        validate_ground_derivation(&input(), cex.ground_derivation.as_ref().unwrap()),
        Ok(())
    );
}
