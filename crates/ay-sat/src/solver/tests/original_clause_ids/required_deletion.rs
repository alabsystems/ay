// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Required proof deletion is not optional satisfied-arena collection.

use super::*;

fn unknown(solver: &Solver) {
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ProofFinalizationFailure),
    );
    assert!(solver.original_ledger_replay_failed());
    let manager = solver.proof_manager.as_ref().expect("attached manager");
    assert!(
        manager.has_io_error(),
        "the structural refusal is unbypassable"
    );
    assert!(
        !manager.has_lrat_authority_fail_closed(),
        "no Fmla replay exception"
    );
    assert!(!solver.cold.empty_clause_in_proof);
}

#[test]
fn required_input_delete_revokes_visibility_and_serializes_the_exact_id() {
    let mut s = solver(Format::Text, 1);
    let clause = vec![p(0), p(1)];
    assert!(s.add_clause(clause.clone()));
    let input = originals(&s);
    let id = input[0].0;
    s.proof_emit_delete(&clause, id).expect("required delete");
    assert!(!s.lrat_hint_id_visible(id));
    assert_eq!(
        s.proof_manager.as_ref().expect("manager").deleted_count(),
        1
    );
    s.proof_emit_delete_optional_gc(&clause, id)
        .expect("later optional request");
    assert!(
        !s.lrat_hint_id_visible(id),
        "optional retention cannot revive a delete"
    );
    assert_eq!(
        s.proof_manager.as_ref().expect("manager").deleted_count(),
        1
    );
    check(&mut s, Format::Text, &input, false);
}

#[test]
fn optional_collection_deletes_derived_rows_instead_of_retaining_them() {
    let mut s = solver(Format::Text, 1);
    let clause = vec![p(0), p(1)];
    assert!(s.add_clause(clause.clone()));
    let input = originals(&s);
    let derived = s
        .proof_emit_add(&clause, &[input[0].0], ProofAddKind::Derived)
        .expect("RUP duplicate");
    s.proof_emit_delete_optional_gc(&clause, derived)
        .expect("derived collect");
    assert!(!s.lrat_hint_id_visible(derived));
    assert!(s.lrat_hint_id_visible(input[0].0));
    assert_eq!(
        s.proof_manager.as_ref().expect("manager").deleted_count(),
        1
    );
    check(&mut s, Format::Text, &input, false);
}

#[test]
fn satisfied_l0_collection_retains_live_input_proof_authority_for_rebuild() {
    let mut s = solver(Format::Text, 2);
    assert!(s.add_clause(vec![p(0), p(1)]));
    let binary = s.arena.live_indices().next().expect("binary input");
    assert!(s.add_clause(vec![p(0)]));
    let input = originals(&s);
    s.initialize_watches();
    assert!(s.process_initial_clauses().is_none());
    s.cold.last_collect_fixed = 0;
    assert!(!s.collect_level0_garbage());
    assert!(
        !s.arena.is_active(binary),
        "satisfied arena row is actually collected"
    );
    assert!(s.lrat_hint_id_visible(input[0].0));
    assert_eq!(
        s.proof_manager.as_ref().expect("manager").deleted_count(),
        0
    );
    s.reset_search_state();
    assert!(!s.original_ledger_replay_failed());
    assert!(s.solve().is_sat());
    assert_eq!(originals(&s), input);
    check(&mut s, Format::Text, &input, false);
}

fn deleted_rebuild(format: Format) {
    let mut s = solver(format, 3);
    let clause = vec![p(0), p(1)];
    assert!(s.add_clause(clause.clone()));
    let input = originals(&s);
    s.proof_emit_delete(&clause, input[0].0)
        .expect("required input delete");
    let index = s.arena.live_indices().next().expect("arena input");
    s.arena.delete(index);
    s.cold.inprocessing_modified_clause_db = true;
    assert!(
        s.solve().is_unknown(),
        "dead input cannot become a replay axiom"
    );
    unknown(&s);
    assert!(!s.lrat_hint_id_visible(input[0].0));
    assert_eq!(originals(&s), input, "durable identity is not reminted");
    assert!(
        s.arena.live_indices().next().is_none(),
        "refusal precedes replay"
    );
    assert!(s.solve_with_assumptions(&[n(0), n(1)]).is_unknown());
    unknown(&s);
    assert!(s.solve_interruptible(|| false).is_unknown());
    unknown(&s);
    check(&mut s, format, &input, false);
}

#[test]
fn full_text_rebuild_refuses_deleted_inputs_without_emitting_hints() {
    deleted_rebuild(Format::Text);
}

#[test]
fn full_binary_rebuild_refuses_deleted_inputs_without_emitting_hints() {
    deleted_rebuild(Format::Binary);
}

fn deferred_attach(format: Format) {
    let mut s = solver(format, 2);
    assert!(s.add_clause(vec![p(0), p(1)]));
    assert!(s.solve_with_assumptions(&[p(0)]).is_sat());
    s.cold.inc_engine_reset_mode = true;
    assert!(s.add_clause(vec![n(0)]));
    assert!(s.cold.ic3_new_clauses_pending);
    let input = originals(&s);
    let (id, clause) = input.last().expect("new deferred input");
    s.proof_emit_delete(clause, *id)
        .expect("required deferred input delete");
    let boundary = s.cold.incremental_original_boundary;
    assert!(s.solve_with_assumptions(&[n(1)]).is_unknown());
    unknown(&s);
    assert_eq!(
        s.cold.incremental_original_boundary, boundary,
        "refused input not consumed"
    );
    assert!(!s.lrat_hint_id_visible(*id));
    assert_eq!(originals(&s), input);
    assert!(
        s.solve().is_unknown(),
        "same attached proof owner remains refused"
    );
    unknown(&s);
    check(&mut s, format, &input, false);
}

#[test]
fn incremental_text_attachment_refuses_deleted_deferred_input_before_propagation() {
    deferred_attach(Format::Text);
}

#[test]
fn incremental_binary_attachment_refuses_deleted_deferred_input_before_propagation() {
    deferred_attach(Format::Binary);
}

#[test]
fn zero_and_missing_replay_identity_are_sticky_structural_refusals() {
    let mut s = solver(Format::Text, 0);
    let manager = s.proof_manager.as_mut().expect("manager");
    assert!(!manager.preflight_ledger_replay(Some(&[0])));
    assert!(manager.ledger_replay_failed());
    assert!(
        !manager.preflight_ledger_replay(Some(&[])),
        "no reset of refusal"
    );
    assert!(!manager.preflight_ledger_replay(None), "no invented range");
    assert!(s.solve().is_unknown());
    unknown(&s);
    check(&mut s, Format::Text, &[], false);
}

#[test]
fn original_check_stop_refuses_between_bounded_replay_chunks() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    let mut s = solver(Format::Text, 130);
    s.ensure_num_vars(131);
    for variable in 1..131 {
        assert!(s.add_clause(vec![p(0), p(variable)]));
    }
    let input = originals(&s);
    assert_eq!(input.len(), 130);
    let polls = Arc::new(AtomicUsize::new(0));
    let original = polls.clone();
    let scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        original.fetch_add(1, Ordering::SeqCst) >= 2
    }));
    assert!(!s.preflight_original_ledger_replay(0));
    assert_eq!(polls.load(Ordering::SeqCst), 3);
    drop(scope);
    assert!(
        s.solve().is_unknown(),
        "dropping the scope does not renew replay authority"
    );
    unknown(&s);
    assert_eq!(originals(&s), input);
    check(&mut s, Format::Text, &input, false);
}

#[test]
fn raw_interrupt_refuses_ledger_replay_without_resetting_the_original_flag() {
    use std::sync::atomic::{AtomicBool, Ordering};
    let mut s = solver(Format::Text, 1);
    assert!(s.add_clause(vec![p(0), p(1)]));
    let input = originals(&s);
    let flag = Arc::new(AtomicBool::new(true));
    s.set_interrupt_handle(Some(flag.clone()));
    assert!(!s.preflight_original_ledger_replay(0));
    assert!(flag.load(Ordering::SeqCst));
    s.set_interrupt_handle(None);
    assert!(s.solve().is_unknown());
    unknown(&s);
    check(&mut s, Format::Text, &input, false);
}

#[test]
fn original_absolute_deadline_refuses_ledger_replay_without_refresh() {
    let mut s = solver(Format::Text, 1);
    assert!(s.add_clause(vec![p(0), p(1)]));
    let input = originals(&s);
    s.set_solve_deadline(Some(ay_core::time::Instant::now()));
    assert!(!s.preflight_original_ledger_replay(0));
    s.set_solve_deadline(None);
    assert!(s.solve().is_unknown());
    unknown(&s);
    check(&mut s, Format::Text, &input, false);
}

#[test]
fn replay_debits_existing_proof_bookkeeping_and_exhaustion_stays_refused() {
    let mut s = solver(Format::Text, 1);
    assert!(s.add_clause(vec![p(0), p(1)]));
    let input = originals(&s);
    s.cold.proof_bookkeeping_budget = Some(3);
    assert!(s.preflight_original_ledger_replay(0));
    assert_eq!(s.cold.proof_bookkeeping_budget, Some(2));
    s.cold.proof_bookkeeping_budget = Some(1);
    assert!(!s.preflight_original_ledger_replay(0));
    assert_eq!(s.cold.proof_bookkeeping_budget, Some(0));
    assert!(s.solve().is_unknown());
    unknown(&s);
    check(&mut s, Format::Text, &input, false);
}
