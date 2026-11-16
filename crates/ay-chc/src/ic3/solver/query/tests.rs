// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::ic3::cube::Cube;
use crate::ic3::solver::{BlockResult, TryBlockResult};
use crate::ic3::transition_system::BitLevelTransitionSystem;
use ay_core::time::Instant;
use ay_sat::Variable;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

fn safe_solver() -> Ic3Solver {
    let x = Variable::new(0);
    let next = Variable::new(1);
    let ts = BitLevelTransitionSystem::new(
        1,
        0,
        vec![x],
        vec![next],
        vec![],
        vec![vec![Literal::negative(x)]],
        vec![vec![Literal::negative(next)]],
        vec![Literal::positive(x)],
        2,
    );
    Ic3Solver::new(ts, false)
}

fn future() -> Instant {
    Instant::now() + Duration::from_secs(60)
}

fn cube() -> Cube {
    Cube::new(vec![Literal::positive(Variable::new(0))])
}

#[test]
fn expired_original_deadline_reaches_both_retained_sat_solvers() {
    let mut solver = safe_solver().with_deadline(Some(Instant::now()));
    assert!(matches!(
        solver.init_solver.solve_incremental_ic3(&[]).into_inner(),
        AssumeResult::Unknown
    ));
    assert!(matches!(
        solver.solver.solve_incremental_ic3(&[]).into_inner(),
        AssumeResult::Unknown
    ));
    assert!(matches!(solver.solve(), Ic3Result::Unknown));
    assert!(solver.frames.is_empty());
}

#[test]
fn expired_immediate_counterexample_is_unknown_not_unsafe() {
    let mut ts = safe_solver().ts;
    ts.init_clauses = vec![vec![Literal::positive(Variable::new(0))]];
    let mut live = Ic3Solver::new(ts.clone(), false).with_deadline(Some(future()));
    assert!(matches!(live.solve(), Ic3Result::Unsafe { .. }));
    let mut expired = Ic3Solver::new(ts, false).with_deadline(Some(Instant::now()));
    assert!(matches!(expired.solve(), Ic3Result::Unknown));
    assert_eq!(expired.stats.cex_traces, 0);
}

#[test]
fn unknown_init_query_is_not_disjoint_and_cannot_resume() {
    let flag = Arc::new(AtomicBool::new(true));
    let mut solver = safe_solver().with_deadline(Some(future()));
    solver.init_solver.set_interrupt(flag.clone());
    assert!(!solver.cube_is_disjoint_from_init(&cube()));
    assert!(solver.query_stopped.get());
    flag.store(false, Ordering::Relaxed);
    assert!(!solver.cube_is_disjoint_from_init(&cube()));
    assert!(matches!(solver.solve(), Ic3Result::Unknown));
    assert!(solver.frames.is_empty());
    let mut fresh = safe_solver().with_deadline(Some(future()));
    assert!(fresh.cube_is_disjoint_from_init(&cube()));
    assert!(matches!(fresh.solve(), Ic3Result::Safe { .. }));
}

#[test]
fn unknown_bad_state_query_is_not_exhaustion() {
    let flag = Arc::new(AtomicBool::new(true));
    let mut solver = safe_solver().with_deadline(Some(future()));
    solver.new_frame();
    solver.new_frame();
    solver.solver.set_interrupt(flag.clone());
    assert!(solver.get_bad_cube(1).is_err());
    assert!(matches!(solver.block_all_bad(1), BlockResult::Unknown));
    flag.store(false, Ordering::Relaxed);
    assert!(solver.get_bad_cube(1).is_err());
    assert!(matches!(solver.solve(), Ic3Result::Unknown));
    assert!(solver
        .frames
        .iter()
        .all(|frame| frame.blocked_clauses.is_empty()));
}

#[test]
fn interrupted_consecution_cannot_install_a_frame_lemma() {
    let mut solver = safe_solver().with_deadline(Some(future()));
    solver.new_frame();
    solver.new_frame();
    solver.solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert!(matches!(
        solver.try_block_cube(&cube(), 1),
        TryBlockResult::Unknown
    ));
    let mut limit = 1;
    assert!(!solver.trivial_block(&cube(), 1, &mut limit));
    assert!(!solver.is_inductive_relative(&cube(), 1));
    assert!(!solver.is_inductive_relative_capture(&cube(), 1).0);
    assert!(!solver.propagate());
    assert_eq!(solver.stats.cubes_blocked, 0);
    assert!(solver
        .frames
        .iter()
        .all(|frame| frame.blocked_clauses.is_empty()));
}

#[test]
fn propagation_restores_all_unprocessed_clauses_at_first_refusal() {
    let mut solver = safe_solver().with_deadline(Some(future()));
    solver.new_frame();
    solver.new_frame();
    solver.new_frame();
    let x = Literal::positive(Variable::new(0));
    let original = vec![
        vec![x.negated()],
        vec![x.negated(), x.negated()],
        vec![x, x.negated()],
    ];
    for clause in &original {
        solver.add_blocked_clause_to_frames(clause, 1);
    }
    solver.solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert!(!solver.propagate());
    assert_eq!(solver.stats.sat_calls, 1);
    assert_eq!(solver.frames[1].blocked_clauses, original);
    assert_eq!(
        solver.frames[2].blocked_clauses,
        [] as [std::vec::Vec<ay_sat::Literal>; 0]
    );
    assert_eq!(solver.stats.clauses_propagated, 0);
    assert!(matches!(solver.solve(), Ic3Result::Unknown));
    assert_eq!(solver.frames.len(), 3);
}

#[test]
fn unknown_init_during_generalization_keeps_the_original_cube() {
    let mut solver = safe_solver().with_deadline(Some(future()));
    solver.new_frame();
    solver.new_frame();
    solver
        .init_solver
        .set_interrupt(Arc::new(AtomicBool::new(true)));
    let original = cube();
    let result = solver.generalize_cube(&original, 1);
    assert_eq!(result.literals, original.literals);
    assert!(solver.query_stopped.get());
    assert!(solver
        .frames
        .iter()
        .all(|frame| frame.blocked_clauses.is_empty()));
}

#[test]
fn final_admission_rejects_a_genuine_but_late_safe_result() {
    let mut solver = safe_solver().with_deadline(Some(future()));
    let candidate = solver.solve();
    assert!(matches!(candidate, Ic3Result::Safe { .. }));
    // Inject only passage of the outer admission deadline, not solver truth.
    solver.deadline = Some(Instant::now());
    assert!(matches!(solver.admit_result(candidate), Ic3Result::Unknown));
    solver.deadline = Some(future());
    assert!(matches!(solver.solve(), Ic3Result::Unknown));
}

#[test]
fn query_cleanup_is_charged_to_the_original_deadline() {
    let mut solver = safe_solver().with_deadline(Some(future()));
    let result = solver.init_query(&[]);
    assert!(matches!(result, Ok(AssumeResult::Sat(_))));
    // Model an opaque scope/domain teardown crossing the deadline. This is
    // the same post-cleanup seam used by solve_with_domain_and_constraints.
    solver.deadline = Some(Instant::now());
    assert!(solver.after_query_cleanup(result).is_err());
    assert!(solver.query_stopped.get());
}

#[test]
fn none_and_live_deadlines_preserve_small_safe_and_disjoint_results() {
    for deadline in [None, Some(future())] {
        let mut solver = safe_solver().with_deadline(deadline);
        assert!(solver.cube_is_disjoint_from_init(&cube()));
        assert!(matches!(solver.solve(), Ic3Result::Safe { .. }));
        assert!(!solver.query_stopped.get());
    }
}

mod resources;
