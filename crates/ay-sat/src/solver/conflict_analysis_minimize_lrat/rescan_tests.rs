// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual root-trail visits, not the eliminated legacy suffix, spend scan credit.

use super::*;
use crate::{ClauseTrace, Variable};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

#[derive(Clone, Copy, Debug)]
enum Pass {
    Minimize,
    Root,
}

impl Pass {
    fn run(self, solver: &mut Solver) {
        match self {
            Self::Minimize => solver.materialize_level0_minimize_unit_proofs(),
            Self::Root => solver.materialize_level0_unit_proofs(),
        }
    }

    fn visited(self, solver: &Solver) -> u64 {
        match self {
            Self::Minimize => solver.stats.lrat_materialize_minimize_root_trail_entries,
            Self::Root => solver.stats.lrat_materialize_root_trail_entries,
        }
    }
}

fn pinned_fixture() -> Solver {
    let mut solver = Solver::new(8);
    solver.enable_clause_trace();
    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));
    let reason = solver.add_clause_db(&[target, support.negated()], false);
    solver.trail = (0..8).map(|var| Literal::positive(Variable(var))).collect();
    for position in 0..solver.trail.len() {
        let lit = solver.trail[position];
        let var = lit.variable().index();
        solver.var_data[var].level = 0;
        solver.var_data[var].trail_pos = position as u32;
        solver.var_data[var].reason = NO_REASON;
        solver.vals[lit.index()] = 1;
        solver.vals[lit.negated().index()] = -1;
        if position >= 2 {
            let offset = solver.add_clause_db(&[lit], false);
            let id = solver.clause_id(ClauseRef(offset as u32));
            solver.record_unit_proof_id_for_lit(lit, id);
        }
    }
    // As in the existing depinning fixture, support deliberately has no unit
    // provenance. The pending target must not acquire an invented derivation.
    solver.var_data[1].reason = reason as u32;
    solver.cold.lrat_level0_unit_materialize_cursor = solver.trail.len();
    solver.cold.lrat_level0_unit_materialize_pinned = vec![1];
    solver.cold.lrat_materialize_hints_buf = Vec::with_capacity(16);
    solver
}

type TraceRows = Vec<(u64, Vec<Literal>, bool, Vec<u64>)>;

fn trace_rows(trace: &ClauseTrace) -> TraceRows {
    trace
        .entries()
        .iter()
        .map(|entry| {
            (
                entry.id,
                entry.clause.to_vec(),
                entry.is_original,
                entry.resolution_hints.to_vec(),
            )
        })
        .collect()
}

fn entries(solver: &Solver) -> TraceRows {
    trace_rows(solver.cold.clause_trace.as_ref().unwrap())
}

#[test]
fn one_pin_pays_one_visit_not_the_materialized_suffix_in_both_passes() {
    for pass in [Pass::Minimize, Pass::Root] {
        let mut solver = pinned_fixture();
        let before = entries(&solver);
        solver.set_proof_bookkeeping_budget(Some(4));
        for remaining in [3, 2, 1] {
            let visited = pass.visited(&solver);
            pass.run(&mut solver);
            assert_eq!(pass.visited(&solver) - visited, 1, "{pass:?}");
            assert_eq!(solver.cold.proof_bookkeeping_budget, Some(remaining));
            assert!(solver.has_live_clause_trace());
            assert_eq!(entries(&solver), before);
            assert_eq!(solver.cold.lrat_level0_unit_materialize_pinned, [1]);
            assert_eq!(solver.cold.lrat_level0_unit_materialize_cursor, 8);
        }
    }
}

#[test]
fn fresh_entries_are_charged_even_when_the_pass_does_not_leave_a_pin() {
    for pass in [Pass::Minimize, Pass::Root] {
        let mut solver = pinned_fixture();
        solver.var_data[1].reason = NO_REASON;
        solver.cold.lrat_level0_unit_materialize_cursor = 0;
        solver.cold.lrat_level0_unit_materialize_pinned.clear();
        solver.set_proof_bookkeeping_budget(Some(9));
        pass.run(&mut solver);
        assert_eq!(pass.visited(&solver), 8);
        assert_eq!(solver.cold.proof_bookkeeping_budget, Some(1));
        assert!(solver.cold.lrat_level0_unit_materialize_pinned.is_empty());
        pass.run(&mut solver);
        assert_eq!(pass.visited(&solver), 8, "empty retry does no work");
        assert_eq!(solver.cold.proof_bookkeeping_budget, Some(1));
    }
}

#[test]
fn literal_and_hint_copy_charges_remain_separate_from_actual_scan_work() {
    for pass in [Pass::Minimize, Pass::Root] {
        let mut solver = pinned_fixture();
        solver.set_proof_bookkeeping_budget(Some(29));
        let unit = Literal::positive(Variable(2));
        let original = solver.unit_proof_id[2];
        assert_ne!(original, 0);
        // One copied literal, one original-unit hint and the original entry
        // metadata: 4 + 8 + 16 units. This is independent of trail visits.
        solver.trace_materialized_level0_unit(10_000, unit, &[original]);
        assert_eq!(solver.cold.proof_bookkeeping_budget, Some(1));
        assert!(solver.has_live_clause_trace());
        pass.run(&mut solver);
        assert_eq!(pass.visited(&solver), 1);
        assert_eq!(solver.cold.proof_bookkeeping_budget, Some(0));
        assert!(!solver.has_live_clause_trace());
    }
}

#[test]
fn actual_visit_exhaustion_restores_scratch_and_cannot_revive_the_trace() {
    for pass in [Pass::Minimize, Pass::Root] {
        let mut solver = pinned_fixture();
        let capacity = solver.cold.lrat_materialize_hints_buf.capacity();
        solver.set_proof_bookkeeping_budget(Some(1));
        pass.run(&mut solver);
        assert_eq!(pass.visited(&solver), 1);
        // Preserve the existing strict boundary: remaining == charge refuses.
        assert_eq!(solver.cold.proof_bookkeeping_budget, Some(0));
        assert!(!solver.has_live_clause_trace());
        assert_eq!(solver.cold.lrat_level0_unit_materialize_pinned, [1]);
        assert_eq!(solver.cold.lrat_level0_unit_materialize_cursor, 8);
        assert!(solver.cold.lrat_materialize_hints_buf.is_empty());
        assert_eq!(solver.cold.lrat_materialize_hints_buf.capacity(), capacity);
        pass.run(&mut solver);
        assert_eq!(pass.visited(&solver), 1);
        solver.materialize_level0_unit_proofs();
        solver.set_proof_bookkeeping_budget(None);
        pass.run(&mut solver);
        assert!(!solver.cold.lrat_enabled);
        assert!(!solver.has_live_clause_trace());
        assert!(solver
            .cold
            .clause_trace
            .as_ref()
            .unwrap()
            .proof_work_exhausted());
    }
}

fn assert_stopped_prefix_preserved(mut solver: Solver) {
    let before = entries(&solver);
    let capacity = solver.cold.lrat_materialize_hints_buf.capacity();
    solver.set_proof_bookkeeping_budget(Some(3));
    for _ in 0..2 {
        assert!(!solver.materialize_level0_unit_proofs_interruptible());
        assert_eq!(solver.stats.lrat_materialize_root_trail_entries, 0);
        assert_eq!(solver.cold.proof_bookkeeping_budget, Some(3));
        assert_eq!(solver.cold.lrat_level0_unit_materialize_pinned, [1]);
        assert_eq!(solver.cold.lrat_level0_unit_materialize_cursor, 8);
        assert_eq!(entries(&solver), before);
        assert!(solver.cold.lrat_materialize_hints_buf.is_empty());
        assert_eq!(solver.cold.lrat_materialize_hints_buf.capacity(), capacity);
    }
}

#[test]
fn cancellation_before_a_retry_preserves_pins_without_charging_unvisited_work() {
    let mut solver = pinned_fixture();
    solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert_stopped_prefix_preserved(solver);
}

#[test]
fn expired_original_deadline_preserves_pins_without_charging_unvisited_work() {
    let mut solver = pinned_fixture();
    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));
    assert_stopped_prefix_preserved(solver);
}

fn solved_trace(budget: Option<u64>) -> ClauseTrace {
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();
    solver.set_proof_bookkeeping_budget(budget);
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    for clause in [
        [a, b],
        [a.negated(), b],
        [a, b.negated()],
        [a.negated(), b.negated()],
    ] {
        solver.add_clause(clause.to_vec());
    }
    assert!(matches!(solver.solve().into_inner(), SatResult::Unsat(_)));
    let trace = solver.take_clause_trace().unwrap();
    crate::validate_clause_trace_resolution(
        &trace,
        2,
        &crate::ResolutionValidationLimits::unbounded(),
    )
    .expect("complete original CNF refutation must pass independent positive-RUP replay");
    trace
}

#[test]
fn sufficient_original_credit_preserves_exact_clause_ids_hints_and_checked_result() {
    let unbudgeted = solved_trace(None);
    let budgeted = solved_trace(Some(100_000));
    assert_eq!(trace_rows(&budgeted), trace_rows(&unbudgeted));
    assert!(!budgeted.proof_work_exhausted());
}
