// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Delete a real, unrelated original arena row with no live assignments.
/// This selects the existing ledger/arena-count rebuild path without setting
/// a synthetic reset flag or pretending that the diagnostic observed a GC.
fn lose_unrelated_original(solver: &mut Solver, offset: usize) {
    assert_eq!(solver.current_decision_level(), 0);
    assert_eq!(solver.trail_len(), 0);
    assert!(!solver.arena.is_learned(offset));
    assert!(solver.arena.is_active(offset));
    solver.arena.delete(offset);
    solver.reset_search_state();
}

fn rebuild_fixture(retain: bool) -> (Solver, u64) {
    let mut solver = Solver::new(5);
    solver.set_preprocess_enabled(false);
    solver.enable_clause_trace();
    solver.add_clause(vec![
        Literal::positive(Variable(2)),
        Literal::positive(Variable(3)),
        Literal::positive(Variable(4)),
    ]);
    let unrelated = solver.arena.active_indices().next().expect("real original");
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    let before = solver.issued_original_clause_id_max();
    let conflict = vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ];
    if retain {
        assert!(solver.add_retained_theory_conflict_clause(conflict));
    } else {
        assert!(solver.add_theory_conflict_lemma(conflict).is_some());
    }
    let id = solver.issued_original_clause_id_max();
    assert_eq!(
        id,
        before + 1,
        "one exact clause receives one fresh identity"
    );
    assert!(solver.is_issued_original_clause_id(id));
    lose_unrelated_original(&mut solver, unrelated);
    (solver, id)
}

#[test]
fn retained_conflict_survives_rebuild_with_original_identity_and_retracts_on_pop() {
    let (mut solver, id) = rebuild_fixture(true);
    assert!(solver.cold.original_ledger.clause_ids().contains(&id));
    let restored = solver
        .arena
        .active_indices()
        .find(|&offset| solver.clause_id(ClauseRef(offset as u32)) == id)
        .expect("rebuild must restore the retained clause with the same identity");
    assert!(!solver.arena.is_learned(restored));
    assert!(solver.solve().into_inner().is_unsat());
    assert!(solver.pop());
    assert!(!solver.cold.original_ledger.clause_ids().contains(&id));
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "a retained clause must not escape its popped assertion scope"
    );
}

#[test]
fn immediate_conflict_keeps_its_existing_deletable_rebuild_contract() {
    let (mut solver, id) = rebuild_fixture(false);
    assert!(!solver.cold.original_ledger.clause_ids().contains(&id));
    assert!(!solver
        .arena
        .active_indices()
        .any(|offset| { solver.clause_id(ClauseRef(offset as u32)) == id }));
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
}

#[test]
fn retained_conflict_blocks_cached_model_and_preserves_nested_scope() {
    let mut solver = Solver::new(2);
    solver.set_preprocess_enabled(false);
    solver.push();
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.add_clause(vec![Literal::positive(Variable(1))]);
    assert!(matches!(solver.solve().into_inner(), SatResult::Sat(_)));
    solver.push();
    assert!(solver.add_retained_theory_conflict_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]));
    assert!(solver.solve().into_inner().is_unsat());
    assert!(solver.pop());
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Sat(_)),
        "popping the child restores the still-active outer p/q model"
    );
    assert!(solver.pop());
}

#[test]
fn retained_conflict_cannot_be_exported_as_a_standalone_lrat_input() {
    let proof = ProofOutput::lrat_text(Vec::new(), 0);
    let mut solver = Solver::with_proof_output(2, proof);
    solver.push();
    let before = solver.issued_original_clause_id_max();
    assert!(solver.add_retained_theory_conflict_clause(vec![
        Literal::negative(Variable(0)),
        Literal::negative(Variable(1)),
    ]));
    assert!(solver
        .proof_manager
        .as_ref()
        .expect("proof manager")
        .lrat_blocked_by_theory_lemmas());
    let ids = solver.cold.original_ledger.clause_ids();
    assert_eq!(ids.len(), 1);
    assert!(ids[0] > before);
    let id = ids[0];
    assert!(solver.is_issued_original_clause_id(id));
    assert!(solver.pop());
    assert!(!solver.cold.original_ledger.clause_ids().contains(&id));
}
