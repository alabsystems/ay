// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::extension::{ExtPropagateResult, Extension, PreparedExtension, SolverContext};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;

struct NoopExtension;

impl Extension for NoopExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }
}

#[test]
fn preprocessing_extension_stop_preserves_consumed_clauses_for_retry() {
    let x0 = Variable(0);
    let x1 = Variable(1);
    let mut solver = Solver::new(2);

    // Together these clauses imply x0. Removing either makes ~x0 satisfiable.
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);
    solver.add_clause(vec![Literal::positive(x0), Literal::negative(x1)]);

    let active_before = solver.arena.active_clause_count();
    let builder_ran = std::cell::Cell::new(false);
    let polls_after_builder = std::cell::Cell::new(0usize);

    let stopped = solver
        .solve_interruptible_with_preprocessing_extension::<NoopExtension, _, _>(
            |clauses| {
                assert_eq!(clauses.len(), active_before);
                builder_ran.set(true);
                Some(PreparedExtension::new(NoopExtension, vec![0], vec![x0, x1]))
            },
            || {
                if !builder_ran.get() {
                    return false;
                }
                let polls = polls_after_builder.get() + 1;
                polls_after_builder.set(polls);
                polls == 2
            },
        )
        .into_inner();

    assert!(matches!(stopped, SatResult::Unknown));
    assert_eq!(polls_after_builder.get(), 2);
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
    assert_eq!(solver.arena.active_clause_count(), active_before);
    assert!(!solver.is_frozen(x0));
    assert!(!solver.is_frozen(x1));
    assert!(!solver.cold.extension_trusted_lemmas);
    assert!(solver.cold.preprocess_deadline.is_none());
    assert!(!solver.is_preprocess_enabled());
    assert_eq!(solver.qhead, solver.trail.len());

    let retried = solver
        .solve_with_assumptions(&[Literal::negative(x0)])
        .into_inner();
    assert!(matches!(retried, AssumeResult::Unsat(..)));
}

#[test]
fn preprocessing_extension_rejects_incomplete_frozen_interface() {
    let x0 = Variable(0);
    let x1 = Variable(1);
    let mut solver = Solver::new(2);
    solver.add_clause(vec![Literal::positive(x0), Literal::positive(x1)]);

    let pending = solver.prepare_preprocessing_extension::<NoopExtension, _>(&mut |_| {
        Some(PreparedExtension::new(NoopExtension, vec![0], vec![x0]))
    });

    assert!(pending.is_none());
    assert!(!solver.is_frozen(x0));
    assert!(!solver.is_frozen(x1));
}

#[test]
fn expired_solve_deadline_at_assumption_entry_is_typed_and_reusable() {
    let mut solver = Solver::new(2);
    solver.add_clause(vec![
        Literal::positive(Variable(0)),
        Literal::positive(Variable(1)),
    ]);
    let assumptions = [Literal::negative(Variable(0))];

    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));
    let stopped = solver.solve_with_assumptions(&assumptions).into_inner();

    assert!(matches!(stopped, AssumeResult::Unknown));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );
    assert!(solver.cold.preprocess_deadline.is_none());
    assert!(
        solver.is_preprocess_enabled(),
        "an entry stop must not start or disarm preprocessing"
    );
    assert_eq!(solver.qhead, solver.trail.len());

    solver.set_solve_deadline(None);
    let retried = solver.solve_with_assumptions(&assumptions).into_inner();
    assert!(matches!(retried, AssumeResult::Sat(_)));
}

#[test]
fn stopped_extension_assumption_entry_clears_one_shot_constraint() {
    let mut solver = Solver::new(1);
    solver.constrain(&[]);
    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));

    let stopped = solver
        .solve_with_extension_and_assumptions(&mut NoopExtension, &[])
        .into_inner();
    assert!(matches!(stopped, SatResult::Unknown));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );

    solver.set_solve_deadline(None);
    let retried = solver
        .solve_with_extension_and_assumptions(&mut NoopExtension, &[])
        .into_inner();
    assert!(matches!(retried, SatResult::Sat(_)));
}

#[test]
fn scoped_empty_extension_assumption_exit_clears_one_shot_constraint() {
    let mut solver = Solver::new(1);
    solver.push();
    assert!(!solver.add_clause(Vec::new()));
    solver.constrain(&[]);

    let unsat = solver
        .solve_with_extension_and_assumptions(&mut NoopExtension, &[])
        .into_inner();
    assert!(matches!(unsat, SatResult::Unsat(_)));

    assert!(solver.pop());
    let retried = solver
        .solve_with_extension_and_assumptions(&mut NoopExtension, &[])
        .into_inner();
    assert!(matches!(retried, SatResult::Sat(_)));
}

#[test]
fn preprocess_finish_disarms_without_bcp_after_empty_clause() {
    let mut solver = Solver::new(1);
    solver.add_clause(vec![Literal::positive(Variable(0))]);
    solver.has_empty_clause = true;

    assert!(solver.finish_initial_preprocessing());
    assert!(!solver.is_preprocess_enabled());
    assert_eq!(solver.qhead, solver.trail.len());
}

#[test]
fn stopped_lrat_preprocess_cleanup_deletes_removed_var_reason_clause() {
    let proof = ProofOutput::lrat_text(Vec::new(), 2);
    let mut solver = Solver::with_proof_output(2, proof);
    let support = Literal::positive(Variable(0));
    let target = Literal::positive(Variable(1));

    let support_idx = solver.add_clause_db(&[support], false);
    let support_ref = ClauseRef(support_idx as u32);
    let support_id = solver.clause_id(support_ref);
    let reason_idx = solver.add_clause_db(&[target, support.negated()], false);
    let reason_ref = ClauseRef(reason_idx as u32);

    for (trail_pos, (lit, reason)) in [(support, support_ref), (target, reason_ref)]
        .into_iter()
        .enumerate()
    {
        let var_idx = lit.variable().index();
        solver.vals[lit.index()] = 1;
        solver.vals[lit.negated().index()] = -1;
        solver.var_data[var_idx].level = 0;
        solver.var_data[var_idx].trail_pos = trail_pos as u32;
        solver.var_data[var_idx].reason = reason.0;
        solver.trail.push(lit);
    }
    solver.record_unit_proof_id_for_lit(support, support_id);
    solver.refresh_reason_clause_marks();
    solver
        .var_lifecycle
        .mark_eliminated(target.variable().index());
    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));

    assert_eq!(
        solver.delete_clause_checked(reason_idx, mutate::ReasonPolicy::ClearLevel0),
        mutate::DeleteResult::Skipped,
        "the ordinary deletion path must remain interruptible"
    );
    assert!(solver.arena.is_active(reason_idx));

    assert!(!solver.finish_initial_preprocessing());
    assert!(!solver.arena.is_active(reason_idx));
    for clause_idx in solver.arena.active_indices() {
        assert!(solver
            .arena
            .literals(clause_idx)
            .iter()
            .all(|lit| { !solver.var_lifecycle.is_removed(lit.variable().index()) }));
    }
    assert!(!solver.is_preprocess_enabled());
    assert_eq!(solver.qhead, solver.trail.len());
}

#[test]
fn expired_deadline_preempts_trivial_entry_verdicts() {
    let mut empty_formula = Solver::new(1);
    empty_formula.set_solve_deadline(Some(ay_core::time::Instant::now()));
    assert!(matches!(
        empty_formula.solve().into_inner(),
        SatResult::Unknown
    ));
    assert_eq!(
        empty_formula.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );

    let mut empty_clause = Solver::new(1);
    empty_clause.add_clause(Vec::new());
    empty_clause.set_solve_deadline(Some(ay_core::time::Instant::now()));
    assert!(matches!(
        empty_clause.solve().into_inner(),
        SatResult::Unknown
    ));
    assert_eq!(
        empty_clause.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );

    let mut assumptions = Solver::new(1);
    assumptions.set_solve_deadline(Some(ay_core::time::Instant::now()));
    assert!(matches!(
        assumptions
            .solve_with_assumptions(&[Literal::positive(Variable(0))])
            .into_inner(),
        AssumeResult::Unknown
    ));
    assert_eq!(
        assumptions.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );

    let mut extension = Solver::new(1);
    extension.set_solve_deadline(Some(ay_core::time::Instant::now()));
    assert!(matches!(
        extension
            .solve_with_extension(&mut NoopExtension)
            .into_inner(),
        SatResult::Unknown
    ));
    assert_eq!(
        extension.last_unknown_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );
}

#[test]
fn preset_callback_preempts_empty_formula_verdict() {
    let mut solver = Solver::new(1);
    assert!(matches!(
        solver.solve_interruptible(|| true).into_inner(),
        SatResult::Unknown
    ));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::Interrupted)
    );
}

#[test]
fn active_interrupt_preserves_expired_deadline_provenance() {
    let mut solver = Solver::new(1);
    solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    solver.set_solve_deadline(Some(ay_core::time::Instant::now()));

    assert_eq!(
        solver.active_interrupt_reason(),
        Some(SatUnknownReason::DeadlineExceeded)
    );
}
