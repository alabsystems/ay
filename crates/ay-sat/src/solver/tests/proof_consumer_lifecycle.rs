// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[derive(Debug, PartialEq, Eq)]
struct LifecycleState {
    ic3: bool,
    preprocess: bool,
    chrono: bool,
    stable: bool,
    sweep: bool,
    output_lrat: Option<bool>,
    lrat: bool,
    internal_lrat: bool,
    trace: bool,
    trace_exhausted: bool,
    budget: Option<u64>,
    backward_limits: bool,
    backward_failure: bool,
    saved_controls: bool,
}

fn lifecycle_state(solver: &Solver) -> LifecycleState {
    LifecycleState {
        ic3: solver.cold.ic3_mode,
        preprocess: solver.cold.preprocess_enabled,
        chrono: solver.chrono_enabled,
        stable: solver.stable_mode,
        sweep: solver.is_sweep_enabled(),
        output_lrat: solver.proof_writer().map(ProofOutput::is_lrat),
        lrat: solver.cold.lrat_enabled,
        internal_lrat: solver.cold.internal_lrat_enabled,
        trace: solver.cold.clause_trace.is_some(),
        trace_exhausted: solver
            .cold
            .clause_trace
            .as_ref()
            .is_some_and(ClauseTrace::proof_work_exhausted),
        budget: solver.cold.proof_bookkeeping_budget,
        backward_limits: solver.cold.backward_proof_limits.is_some(),
        backward_failure: solver.cold.backward_proof_failure.is_some(),
        saved_controls: solver.inproc_ctrl_pre_proof.is_some(),
    }
}

fn assert_ic3_rejected_without_mutation(mut solver: Solver) {
    let before = lifecycle_state(&solver);
    let rejected = catch_unwind(AssertUnwindSafe(|| solver.set_ic3_mode()));
    assert!(rejected.is_err());
    assert_eq!(lifecycle_state(&solver), before);
}

#[test]
fn ic3_rejects_drat_lrat_and_trace_before_mutation() {
    assert_ic3_rejected_without_mutation(Solver::with_proof(2, Vec::<u8>::new()));
    assert_ic3_rejected_without_mutation(Solver::with_proof_output(
        2,
        ProofOutput::lrat_text(Vec::<u8>::new(), 0),
    ));

    let mut trace_solver = Solver::new(2);
    trace_solver.enable_clause_trace();
    assert_ic3_rejected_without_mutation(trace_solver);
}

#[test]
fn ic3_rejects_internal_lrat_and_exhausted_trace_tombstone() {
    let mut internal = Solver::new(2);
    internal.enable_lrat();
    assert_ic3_rejected_without_mutation(internal);

    let mut tombstone = Solver::new(2);
    tombstone.enable_clause_trace();
    tombstone.set_proof_bookkeeping_budget(Some(0));
    if let Some(trace) = tombstone.cold.clause_trace.as_mut() {
        trace.mark_proof_work_exhausted();
    }
    tombstone.degrade_proof_bookkeeping_after_exhaustion();
    tombstone.set_proof_bookkeeping_budget(None);
    assert!(!tombstone.cold.lrat_enabled);
    assert_ic3_rejected_without_mutation(tombstone);

    let mut retained_limit = Solver::new(2);
    retained_limit.set_backward_proof_limits(backward_proof::BackwardProofLimits {
        deadline: None,
        max_steps: 1,
        max_literals: 1,
        max_hints: 1,
        max_bytes: 1,
    });
    retained_limit.cold.backward_proof_failure =
        Some(backward_proof::BackwardProofFailure::Deadline);
    assert_ic3_rejected_without_mutation(retained_limit);
}

#[test]
fn public_drat_writer_detach_keeps_conservative_controls() {
    let mut solver = Solver::with_proof(2, Vec::<u8>::new());
    solver.cold.ambient_artifacts_enabled = false;
    solver.set_sweep_enabled(true);
    assert!(!solver.is_sweep_enabled());
    assert!(solver.inproc_ctrl_pre_proof.is_some());

    let detached = solver.take_proof_writer();
    assert!(detached.is_some());
    assert!(solver.proof_writer().is_none());
    assert!(!solver.cold.lrat_enabled);
    assert!(solver.inproc_ctrl_pre_proof.is_none());
    assert!(!solver.is_sweep_enabled());
}

#[test]
fn artifact_free_lrat_writer_detach_preserves_live_trace() {
    let mut solver = Solver::with_proof_output(2, ProofOutput::lrat_text(Vec::<u8>::new(), 0));
    solver.enable_clause_trace();

    let detached = solver.take_proof_writer_without_artifact();
    assert!(detached.is_some());
    assert!(solver.proof_writer().is_none());
    assert!(solver.clause_trace_enabled());
    assert!(solver.cold.lrat_enabled);
    assert!(!solver.cold.internal_lrat_enabled);
    assert!(solver.inproc_ctrl_pre_proof.is_some());
}

#[test]
fn writer_detach_preserves_explicit_internal_lrat() {
    let mut solver = Solver::with_proof(2, Vec::<u8>::new());
    solver.enable_lrat();

    assert!(solver.take_proof_writer_without_artifact().is_some());
    assert!(solver.proof_writer().is_none());
    assert!(solver.cold.internal_lrat_enabled);
    assert!(solver.cold.lrat_enabled);
}

#[test]
fn writer_detach_clears_backward_limits_and_allows_ic3() {
    let mut solver = Solver::with_proof_output(2, ProofOutput::lrat_text(Vec::<u8>::new(), 0));
    solver.set_backward_proof_limits(backward_proof::BackwardProofLimits {
        deadline: None,
        max_steps: 1,
        max_literals: 1,
        max_hints: 1,
        max_bytes: 1,
    });
    solver.cold.backward_proof_failure = Some(backward_proof::BackwardProofFailure::Deadline);

    assert!(solver.take_proof_writer_without_artifact().is_some());
    assert!(solver.cold.backward_proof_limits.is_none());
    assert!(solver.cold.backward_proof_failure.is_none());
    solver.set_ic3_mode();
    assert!(solver.is_ic3_mode());
}

#[test]
fn trace_detach_normalizes_budget_and_stamps_provenance() {
    let mut solver = Solver::new(3);
    solver.enable_clause_trace();
    solver.set_proof_bookkeeping_budget(Some(7));
    solver.set_sweep_enabled(true);
    assert!(!solver.is_sweep_enabled());

    let trace = solver.take_clause_trace();
    assert!(trace
        .as_ref()
        .is_some_and(|trace| trace.solver_num_vars() == Some(3)));
    assert!(!solver.clause_trace_enabled());
    assert!(!solver.cold.lrat_enabled);
    assert_eq!(solver.cold.proof_bookkeeping_budget, None);
    assert!(solver.inproc_ctrl_pre_proof.is_none());
    assert!(!solver.is_sweep_enabled());
}

#[test]
fn trace_detach_preserves_writer_and_internal_lrat_owners() {
    let mut output_owner =
        Solver::with_proof_output(2, ProofOutput::lrat_text(Vec::<u8>::new(), 0));
    output_owner.enable_clause_trace();
    assert!(output_owner.take_clause_trace().is_some());
    assert!(output_owner.proof_writer().is_some());
    assert!(output_owner.cold.lrat_enabled);

    let mut internal_owner = Solver::new(2);
    internal_owner.enable_lrat();
    internal_owner.enable_clause_trace();
    assert!(internal_owner.take_clause_trace().is_some());
    assert!(internal_owner.cold.internal_lrat_enabled);
    assert!(internal_owner.cold.lrat_enabled);
}

#[test]
fn exhausted_trace_does_not_reactivate_when_writer_detach_is_empty() {
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();
    solver.set_proof_bookkeeping_budget(Some(0));
    if let Some(trace) = solver.cold.clause_trace.as_mut() {
        trace.mark_proof_work_exhausted();
    }
    solver.degrade_proof_bookkeeping_after_exhaustion();
    assert!(!solver.cold.lrat_enabled);

    assert!(solver.take_proof_writer_without_artifact().is_none());
    assert!(!solver.clause_trace_enabled());
    assert!(solver.clause_trace().is_some());
    assert!(!solver.cold.lrat_enabled);
    assert_eq!(solver.cold.proof_bookkeeping_budget, None);
}

#[test]
fn exhausted_trace_does_not_reactivate_after_lrat_writer_detach() {
    let mut solver = Solver::with_proof_output(2, ProofOutput::lrat_text(Vec::<u8>::new(), 0));
    solver.enable_clause_trace();
    if let Some(trace) = solver.cold.clause_trace.as_mut() {
        trace.mark_proof_work_exhausted();
    }
    assert!(solver.cold.lrat_enabled);

    assert!(solver.take_proof_writer_without_artifact().is_some());
    assert!(solver.clause_trace().is_some());
    assert!(!solver.clause_trace_enabled());
    assert!(!solver.cold.lrat_enabled);
}

#[test]
fn exhausted_trace_stays_inert_through_later_root_unsat() {
    let mut solver = Solver::new(1);
    solver.enable_clause_trace();
    solver.set_proof_bookkeeping_budget(Some(0));
    if let Some(trace) = solver.cold.clause_trace.as_mut() {
        trace.mark_proof_work_exhausted();
    }
    solver.degrade_proof_bookkeeping_after_exhaustion();
    let x = Literal::positive(Variable(0));
    assert!(solver.add_clause(vec![x]));
    assert!(solver.add_clause(vec![x.negated()]));
    assert!(matches!(solver.solve().into_inner(), SatResult::Unsat(_)));

    let trace = solver.clause_trace();
    assert!(trace.is_some_and(|trace| {
        trace.proof_work_exhausted() && trace.is_empty() && !trace.has_empty_clause()
    }));
    assert!(!solver.clause_trace_enabled());
    assert!(solver.take_proof_writer_without_artifact().is_none());
    assert!(!solver.cold.lrat_enabled);
}

#[test]
fn mixed_budget_ownership_is_rejected_in_both_orders() {
    let mut budget_first = Solver::new(2);
    budget_first.enable_clause_trace();
    budget_first.set_proof_bookkeeping_budget(Some(5));
    let before = lifecycle_state(&budget_first);
    let rejected = catch_unwind(AssertUnwindSafe(|| budget_first.enable_lrat()));
    assert!(rejected.is_err());
    assert_eq!(lifecycle_state(&budget_first), before);

    let mut owner_first = Solver::new(2);
    owner_first.enable_lrat();
    owner_first.enable_clause_trace();
    let before = lifecycle_state(&owner_first);
    let rejected = catch_unwind(AssertUnwindSafe(|| {
        owner_first.set_proof_bookkeeping_budget(Some(5));
    }));
    assert!(rejected.is_err());
    assert_eq!(lifecycle_state(&owner_first), before);
    owner_first.set_proof_bookkeeping_budget(None);
}

#[test]
fn clearing_budget_normalizes_exhausted_but_preserves_live_trace() {
    let mut exhausted = Solver::new(2);
    exhausted.enable_clause_trace();
    exhausted.set_proof_bookkeeping_budget(Some(1));
    assert!(!exhausted.charge_proof_bookkeeping(1));
    assert!(exhausted.cold.lrat_enabled);
    exhausted.set_proof_bookkeeping_budget(None);
    assert!(exhausted.clause_trace().is_some());
    assert!(!exhausted.clause_trace_enabled());
    assert!(!exhausted.cold.lrat_enabled);

    let mut live = Solver::new(2);
    live.enable_clause_trace();
    live.set_proof_bookkeeping_budget(Some(2));
    live.set_proof_bookkeeping_budget(None);
    assert!(live.clause_trace_enabled());
    assert!(live.cold.lrat_enabled);
}

#[test]
fn late_enable_rejects_base_empty_clause_authority() {
    let mut lrat = Solver::new(1);
    assert!(!lrat.add_clause(Vec::new()));
    let rejected = catch_unwind(AssertUnwindSafe(|| lrat.enable_lrat()));
    assert!(rejected.is_err());
    assert!(!lrat.cold.lrat_enabled);
    assert!(!lrat.cold.internal_lrat_enabled);

    let mut trace = Solver::new(1);
    assert!(!trace.add_clause(Vec::new()));
    let rejected = catch_unwind(AssertUnwindSafe(|| trace.enable_clause_trace()));
    assert!(rejected.is_err());
    assert!(!trace.clause_trace_enabled());
    assert!(!trace.cold.lrat_enabled);
}

#[test]
fn flush_does_not_expose_or_change_manager_format_authority() {
    let mut solver = Solver::with_proof_output(2, ProofOutput::lrat_text(Vec::<u8>::new(), 0));
    assert!(matches!(solver.flush_proof_writer(), Ok(true)));
    assert!(solver.proof_writer().is_some_and(ProofOutput::is_lrat));
    assert!(solver
        .proof_manager
        .as_ref()
        .is_some_and(ProofManager::is_lrat));

    let mut no_output = Solver::new(2);
    assert!(matches!(no_output.flush_proof_writer(), Ok(false)));
}

#[test]
fn incremental_clone_strips_every_proof_consumer_and_stale_limit() {
    let mut solver = Solver::with_proof_output(2, ProofOutput::lrat_text(Vec::<u8>::new(), 0));
    solver.enable_lrat();
    solver.enable_clause_trace();
    solver.set_backward_proof_limits(backward_proof::BackwardProofLimits {
        deadline: None,
        max_steps: 1,
        max_literals: 1,
        max_hints: 1,
        max_bytes: 1,
    });

    let mut clone = solver.clone_for_incremental();
    assert!(clone.proof_writer().is_none());
    assert!(!clone.clause_trace_enabled());
    assert!(!clone.cold.lrat_enabled);
    assert!(!clone.cold.internal_lrat_enabled);
    assert_eq!(clone.cold.proof_bookkeeping_budget, None);
    assert!(clone.cold.backward_proof_limits.is_none());
    assert!(clone.inproc_ctrl_pre_proof.is_none());

    let x = Literal::positive(Variable(0));
    assert!(clone.add_clause(vec![x]));
    assert!(clone.add_clause(vec![x.negated()]));
    assert!(matches!(clone.solve().into_inner(), SatResult::Unsat(_)));
}

#[test]
fn incomplete_trace_only_level0_chain_drops_ghost_lrat_owner() {
    let mut solver = Solver::new(3);
    solver.enable_clause_trace();
    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    assert!(solver.add_clause(vec![a]));
    assert!(solver.add_clause(vec![a.negated(), b]));
    assert!(solver.add_clause(vec![a.negated(), c]));
    let conflict_offset = solver.arena.len();
    assert!(solver.add_clause(vec![b.negated(), c.negated()]));
    assert_ne!(solver.cold.clause_ids[conflict_offset], 0);
    solver.cold.clause_ids[conflict_offset] = 0;

    assert!(matches!(solver.solve().into_inner(), SatResult::Unsat(_)));
    assert!(solver
        .clause_trace()
        .is_some_and(ClauseTrace::proof_work_exhausted));
    assert!(!solver.clause_trace_enabled());
    assert!(!solver.cold.lrat_enabled);
}

#[test]
fn clause_trace_snapshots_preserve_persistent_solver_ownership() {
    let mut solver = Solver::new(2);
    solver.enable_clause_trace();

    let first = solver.snapshot_clause_trace();
    let second = solver.snapshot_clause_trace();
    assert!(first.is_some());
    assert!(second.is_some());
    assert!(solver.clause_trace_enabled());
    assert!(solver.cold.lrat_enabled);
}
