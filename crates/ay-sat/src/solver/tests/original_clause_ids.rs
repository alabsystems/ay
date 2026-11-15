// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Original IDs survive deferral/rebuild without becoming derived authority.

use super::*;
use crate::proof_manager::ProofAddKind;
use crate::ProofOutput;
use ay_lrat_check::checker::{ConcludeResult, LratChecker};
use ay_lrat_check::lrat_parser::LratStep;

#[derive(Clone, Copy)]
enum Format {
    Text,
    Binary,
}

fn p(var: u32) -> Literal {
    Literal::positive(Variable::new(var))
}
fn n(var: u32) -> Literal {
    Literal::negative(Variable::new(var))
}

fn solver(format: Format, reserved: u64) -> Solver {
    let output = match format {
        Format::Text => ProofOutput::lrat_text(Vec::<u8>::new(), reserved),
        Format::Binary => ProofOutput::lrat_binary(Vec::<u8>::new(), reserved),
    };
    let mut solver = Solver::with_proof_output(3, output);
    solver.disable_all_inprocessing();
    solver.set_preprocess_enabled(false);
    solver
}

fn originals(solver: &Solver) -> Vec<(u64, Vec<Literal>)> {
    solver
        .cold
        .original_ledger
        .iter_clauses()
        .enumerate()
        .map(|(index, clause)| {
            (
                solver.cold.original_ledger.clause_id(index),
                clause.to_vec(),
            )
        })
        .collect()
}

fn add_late_units(solver: &mut Solver) {
    solver.add_clause(vec![n(0)]);
    solver.add_clause(vec![n(1)]);
    for (id, _) in originals(solver) {
        assert_ne!(id, 0);
        assert!(
            solver.lrat_hint_id_visible(id),
            "input registered before attachment"
        );
    }
}

fn conditional_then_sat(solver: &mut Solver) {
    let conditional = solver.solve_with_assumptions(&[n(0), n(1)]);
    assert!(conditional.is_unsat());
    assert!(conditional.proof_certificate().is_none());
    assert!(!solver.has_empty_clause);
    assert!(!solver.cold.empty_clause_in_proof);
    assert!(solver.solve().is_sat());
}

fn check(solver: &mut Solver, format: Format, input: &[(u64, Vec<Literal>)], unsat: bool) {
    let bytes = solver
        .take_proof_writer()
        .expect("attached writer")
        .into_vec()
        .expect("flush");
    let steps = match format {
        Format::Text => {
            ay_lrat_check::lrat_parser::parse_text_lrat(std::str::from_utf8(&bytes).expect("UTF-8"))
        }
        Format::Binary => ay_lrat_check::lrat_parser::parse_binary_lrat(&bytes),
    }
    .expect("LRAT parses");
    let mut checker = LratChecker::new(solver.num_vars);
    for (index, (id, clause)) in input.iter().enumerate() {
        assert_ne!(*id, 0);
        assert!(!input[..index].iter().any(|(previous, _)| previous == id));
        let literals: Vec<_> = clause
            .iter()
            .map(|lit| ay_proof_common::literal::Literal::from_index(lit.index()))
            .collect();
        assert!(checker.add_original(*id, &literals), "original ID {id}");
    }
    for step in steps {
        match step {
            LratStep::Add { id, clause, hints } => {
                if !unsat {
                    assert!(
                        !clause.is_empty(),
                        "conditional prefix has no base terminal"
                    );
                }
                assert!(checker.add_derived(id, &clause, &hints), "derived ID {id}");
            }
            LratStep::Delete { ids } => {
                for id in ids {
                    assert!(checker.delete(id), "deleted ID {id}");
                }
            }
        }
    }
    assert_eq!(checker.conclude_unsat() == ConcludeResult::Verified, unsat);
}

fn later_base(format: Format, incremental: bool) {
    let mut solver = solver(format, 3);
    solver.add_clause(vec![p(0), p(1)]);
    conditional_then_sat(&mut solver);
    solver.cold.inc_engine_reset_mode = incremental;
    add_late_units(&mut solver);
    let input = originals(&solver);
    let result = if incremental {
        solver.solve_with_assumptions(&[]).into_inner().is_unsat()
    } else {
        solver.solve().is_unsat()
    };
    assert!(result, "genuine later base refutation must be accepted");
    assert!(solver.has_empty_clause);
    assert!(solver.cold.empty_clause_in_proof);
    assert_eq!(originals(&solver), input);
    check(&mut solver, format, &input, true);
}

#[test]
fn later_base_refutation_text_is_independently_checked() {
    later_base(Format::Text, false);
}
#[test]
fn later_base_refutation_binary_is_independently_checked() {
    later_base(Format::Binary, false);
}
#[test]
fn forced_incremental_text_registers_inputs_before_propagation() {
    later_base(Format::Text, true);
}
#[test]
fn forced_incremental_binary_registers_inputs_before_propagation() {
    later_base(Format::Binary, true);
}

fn beyond_reservation(format: Format) {
    let mut solver = solver(format, 1);
    let clause = vec![p(0), p(1)];
    solver.add_clause(clause.clone());
    let first = originals(&solver)[0].0;
    let derived = solver
        .proof_emit_add(&clause, &[first], ProofAddKind::Derived)
        .expect("RUP duplicate");
    assert!(derived > first);
    assert!(solver.solve_with_assumptions(&[p(0)]).is_sat());
    add_late_units(&mut solver);
    let input = originals(&solver);
    assert!(input[1].0 > derived && input[2].0 > input[1].0);
    assert!(!solver.is_original_clause_id(derived));
    assert!(solver.solve().is_unsat());
    assert_eq!(originals(&solver), input);
    check(&mut solver, format, &input, true);
}

#[test]
fn late_text_inputs_beyond_reservation_do_not_alias_derived_ids() {
    beyond_reservation(Format::Text);
}
#[test]
fn late_binary_inputs_beyond_reservation_do_not_alias_derived_ids() {
    beyond_reservation(Format::Binary);
}

fn rebuild(format: Format) {
    let mut solver = solver(format, 3);
    solver.add_clause(vec![p(0), p(1)]);
    conditional_then_sat(&mut solver);
    add_late_units(&mut solver);
    let input = originals(&solver);
    solver.cold.inprocessing_modified_clause_db = true;
    solver.reset_search_state();
    for (id, clause) in &input {
        assert!(solver.arena.live_indices().any(|index| {
            solver.cold.clause_ids.get(index) == Some(id)
                && solver.arena.literals(index) == clause.as_slice()
        }));
    }
    assert!(solver.solve().is_unsat());
    assert_eq!(originals(&solver), input);
    check(&mut solver, format, &input, true);
}

#[test]
fn full_text_rebuild_reuses_exact_original_identities() {
    rebuild(Format::Text);
}
#[test]
fn full_binary_rebuild_reuses_exact_original_identities() {
    rebuild(Format::Binary);
}

fn globals(format: Format) {
    let mut solver = solver(format, 1);
    solver.add_clause(vec![p(0), p(1)]);
    conditional_then_sat(&mut solver);
    solver.push();
    solver.add_clause_global(vec![n(0)]);
    solver.push();
    solver.add_clause_global(vec![n(1)]);
    let input = originals(&solver);
    assert!(solver.pop());
    assert_eq!(originals(&solver), input);
    assert!(solver.pop());
    assert_eq!(originals(&solver), input);
    assert!(solver.solve().is_unsat());
    check(&mut solver, format, &input, true);
}

#[test]
fn nested_global_text_replay_preserves_issued_ids() {
    globals(Format::Text);
}
#[test]
fn nested_global_binary_replay_preserves_issued_ids() {
    globals(Format::Binary);
}

#[test]
fn ancestor_replay_and_expiration_preserve_only_the_same_input() {
    let mut solver = solver(Format::Text, 1);
    solver.add_clause(vec![p(0), p(1)]);
    solver.push();
    solver.push();
    solver.add_clause_at_scope_depth(vec![n(0)], 1);
    let input = originals(&solver);
    let ancestor = input[1].clone();
    assert!(solver.pop());
    assert_eq!(originals(&solver), input);
    assert!(solver.solve().is_sat());
    assert!(solver.pop());
    assert_eq!(originals(&solver), input[..1]);
    add_late_units(&mut solver);
    let final_input = originals(&solver);
    assert!(final_input[1].0 > ancestor.0);
    assert!(solver.solve().is_unsat());
    let all_input = vec![
        input[0].clone(),
        ancestor,
        final_input[1].clone(),
        final_input[2].clone(),
    ];
    check(&mut solver, Format::Text, &all_input, true);
}

#[test]
fn normalized_duplicate_events_keep_distinct_durable_ids() {
    let mut solver = solver(Format::Text, 1);
    solver.add_clause(vec![p(0), p(1)]);
    assert!(solver.solve_with_assumptions(&[p(0)]).is_sat());
    solver.add_clause(vec![p(1), p(0), p(0)]);
    let input = originals(&solver);
    assert_eq!(input[0].1, input[1].1);
    assert_ne!(input[0].0, input[1].0);
    solver.cold.inprocessing_modified_clause_db = true;
    solver.reset_search_state();
    assert_eq!(originals(&solver), input);
    assert!(solver.solve().is_sat());
    check(&mut solver, Format::Text, &input, false);
}

#[test]
fn discarded_tautology_reservation_is_not_reused_by_rebuild() {
    let mut solver = solver(Format::Text, 4);
    solver.add_clause(vec![p(0), p(1)]);
    solver.add_clause(vec![p(0), n(0)]);
    add_late_units(&mut solver);
    let input = originals(&solver);
    assert_eq!(
        input.iter().map(|(id, _)| *id).collect::<Vec<_>>(),
        vec![1, 3, 4]
    );
    solver.cold.inprocessing_modified_clause_db = true;
    solver.reset_search_state();
    assert_eq!(originals(&solver), input);
    assert!(solver.solve().is_unsat());
    check(&mut solver, Format::Text, &input, true);
}

#[test]
fn clone_keeps_ledger_ids_without_cloning_proof_authority() {
    let mut solver = solver(Format::Text, 1);
    solver.add_clause(vec![p(0), p(1)]);
    assert!(solver.solve_with_assumptions(&[p(0)]).is_sat());
    add_late_units(&mut solver);
    let input = originals(&solver);
    let mut cloned = solver.clone_for_incremental();
    assert_eq!(originals(&cloned), input);
    assert!(cloned.proof_manager.is_none());
    assert!(cloned.cold.registered_original_clause_id.is_none());
    assert!(cloned.solve().is_unsat());
    assert!(solver.solve().is_unsat());
    check(&mut solver, Format::Text, &input, true);
}

#[test]
fn live_input_proof_deletion_is_optional_until_rebuild() {
    let mut solver = solver(Format::Text, 3);
    solver.add_clause(vec![p(0), p(1)]);
    let (id, clause) = originals(&solver)[0].clone();
    solver
        .proof_emit_delete_optional_gc(&clause, id)
        .expect("optional input delete");
    assert!(
        solver.lrat_hint_id_visible(id),
        "live input cannot be resurrected later"
    );
    let index = solver.arena.live_indices().next().expect("original row");
    solver.arena.delete(index);
    solver.cold.inprocessing_modified_clause_db = true;
    solver.reset_search_state();
    assert_eq!(originals(&solver)[0].0, id);
    add_late_units(&mut solver);
    let input = originals(&solver);
    assert!(solver.solve().is_unsat());
    check(&mut solver, Format::Text, &input, true);
}

#[test]
fn retention_cannot_revive_an_actually_deleted_derived_id() {
    let mut solver = solver(Format::Text, 1);
    let clause = vec![p(0), p(1)];
    solver.add_clause(clause.clone());
    let first = originals(&solver)[0].0;
    let derived = solver
        .proof_emit_add(&clause, &[first], ProofAddKind::Derived)
        .expect("RUP duplicate");
    solver
        .proof_emit_delete(&clause, derived)
        .expect("derived delete");
    assert!(!solver.lrat_hint_id_visible(derived));
    solver
        .proof_manager
        .as_mut()
        .expect("manager")
        .retain_ledger_original_id(derived);
    assert!(!solver.lrat_hint_id_visible(derived));
    let input = originals(&solver);
    check(&mut solver, Format::Text, &input, false);
}

#[test]
fn unbound_private_ledger_entries_cannot_mint_base_proof_ids() {
    let mut solver = solver(Format::Text, 2);
    solver.cold.original_ledger.push_clause(&[p(0)]);
    solver.cold.original_ledger.push_clause(&[n(0)]);
    solver.reset_search_state();
    assert!(solver
        .cold
        .original_ledger
        .clause_ids()
        .iter()
        .all(|&id| id == 0));
    assert!(solver
        .arena
        .live_indices()
        .all(|index| solver.cold.clause_ids[index] == 0));
    assert!(!solver.solve().is_unsat());
    assert!(!solver.cold.empty_clause_in_proof);
    let bytes = solver
        .take_proof_writer()
        .expect("writer")
        .into_vec()
        .expect("flush");
    assert!(
        bytes.is_empty(),
        "missing authority cannot invent ordinal IDs or a terminal"
    );
}

#[test]
fn repeated_scoped_prefix_checks_without_selector_axioms_or_base_empty() {
    let mut solver = solver(Format::Text, 0);
    let mut input = Vec::new();
    for _ in 0..2 {
        solver.push();
        solver.add_clause(vec![p(0)]);
        solver.add_clause(vec![n(0)]);
        let guarded = originals(&solver);
        assert_eq!(guarded.len(), 2);
        for (id, clause) in &guarded {
            assert_eq!(
                clause.len(),
                2,
                "actual guarded originals, not helper axioms"
            );
            #[cfg(debug_assertions)]
            assert!(!solver.cold.scope_selector_axiom_ids.contains(id));
        }
        input.extend(guarded);
        let result = solver.solve_with_assumptions(&[]);
        assert!(result.is_unsat());
        assert!(result.proof_certificate().is_none());
        assert!(!solver.has_empty_clause);
        assert!(!solver.cold.empty_clause_in_proof);
        assert!(solver.cold.empty_clause_lrat_id.is_none());
        assert!(solver.pop());
        assert!(solver.solve().is_sat());
    }
    // Only the real guarded inputs are admitted to this independent checker.
    // Debug-only negative selector axioms are deliberately absent.
    check(&mut solver, Format::Text, &input, false);
}

#[path = "original_clause_ids/required_deletion.rs"]
mod required_deletion;
