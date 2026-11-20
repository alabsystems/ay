// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used, clippy::panic)]

use super::super::SingleExecutorOutcome;
use super::*;
use crate::engine_result::ChcEngineResult;
use crate::{BmcConfig, CancellationToken, ChcExpr, ChcProblem};
use std::sync::atomic::Ordering;
use std::time::Duration;

const SAT: &str = "(set-logic QF_BV) (declare-const x (_ BitVec 8)) \
                  (assert (= x #x07)) (check-sat)";
const UNSAT: &str = "(set-logic QF_BV) (declare-const x (_ BitVec 8)) \
                    (assert (= x #x07)) (assert (= x #x08)) (check-sat)";

fn solver(token: &CancellationToken) -> BmcSolver {
    BmcSolver::new(
        ChcProblem::new(),
        BmcConfig::default()
            .with_cancellation(token.clone())
            .with_memory_budget(64 * 1024 * 1024),
    )
}

fn execute(solver: &BmcSolver, script: &str) -> Option<Vec<String>> {
    let commands = ay_frontend::parse(script).unwrap();
    solver.exec_commands(&mut ay_dpll::Executor::new(), &commands)
}

#[test]
fn native_sat_and_unsat_batches_preserve_verdicts_without_cancelling_parent() {
    let parent = CancellationToken::new();
    let solver = solver(&parent);
    assert_eq!(execute(&solver, SAT).unwrap(), ["sat"]);
    assert_eq!(execute(&solver, UNSAT).unwrap(), ["unsat"]);
    assert!(!parent.is_cancelled());
}

#[test]
fn observed_parent_cancel_cannot_be_reset_between_persistent_batches() {
    let parent = CancellationToken::new();
    let child = parent.child();
    let old = solver(&child);
    let mut executor = ay_dpll::Executor::new();
    let commands = ay_frontend::parse(SAT).unwrap();
    assert_eq!(
        old.exec_commands(&mut executor, &commands).unwrap(),
        ["sat"]
    );
    parent.cancel();
    assert!(old.exec_commands(&mut executor, &commands).is_none());
    parent.reset();
    assert!(!child.is_cancelled());
    assert!(old.exec_commands(&mut executor, &commands).is_none());
    assert_eq!(execute(&solver(&child), UNSAT).unwrap(), ["unsat"]);
}

#[test]
fn installed_observer_reaches_executor_flag_and_reset_does_not_reopen_attempt() {
    let parent = CancellationToken::new();
    let solver = solver(&parent.child());
    let commands = ay_frontend::parse(SAT).unwrap();
    let mut phases = Vec::new();
    let result = solver.execute_controlled_batch(
        &mut ay_dpll::Executor::new(),
        &commands,
        None,
        |phase, interrupt| {
            phases.push(phase);
            if phase == BatchPhase::Installed {
                parent.cancel();
                let flag = interrupt.expect("caller cancellation owns an executor flag");
                let until = Instant::now() + Duration::from_secs(5);
                while !flag.load(Ordering::Relaxed) && Instant::now() < until {
                    std::thread::yield_now();
                }
                assert!(flag.load(Ordering::Relaxed), "observer must sample parent");
                parent.reset();
            }
        },
    );
    assert_eq!(result, Err(BatchFailure::Stopped(AttemptStop::Cancelled)));
    assert_eq!(phases, [BatchPhase::Installed, BatchPhase::Executed]);
    assert!(!parent.is_cancelled());
    assert!(execute(&solver, SAT).is_none());
}

#[test]
fn cancellation_at_landing_discards_native_output_and_latches_refusal() {
    for script in [SAT, UNSAT] {
        let parent = CancellationToken::new();
        let solver = solver(&parent);
        let commands = ay_frontend::parse(script).unwrap();
        let result = solver.execute_controlled_batch(
            &mut ay_dpll::Executor::new(),
            &commands,
            None,
            |phase, _| {
                if phase == BatchPhase::Executed {
                    parent.cancel();
                }
            },
        );
        assert_eq!(result, Err(BatchFailure::Stopped(AttemptStop::Cancelled)));
        parent.reset();
        assert!(execute(&solver, script).is_none());
    }
}

#[test]
fn expired_ambient_wall_is_terminal_after_the_scope_is_removed() {
    let parent = CancellationToken::new();
    let commands = ay_frontend::parse(SAT).unwrap();
    let past = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("fixture instant supports a one-second offset");
    let future = Instant::now() + Duration::from_secs(60);
    for local in [Some(past), None, Some(future)] {
        let old = solver(&parent);
        {
            let _ambient = crate::smt::ScopedSmtDeadline::install_until(past);
            let result = old.execute_controlled_batch(
                &mut ay_dpll::Executor::new(),
                &commands,
                local,
                |_, _| panic!("expired work must not install a batch"),
            );
            assert_eq!(result, Err(BatchFailure::Stopped(AttemptStop::Deadline)));
        }
        assert_eq!(old.execution_stop.get(), Some(AttemptStop::Deadline));
        assert_eq!(
            old.execute_controlled_batch(
                &mut ay_dpll::Executor::new(),
                &commands,
                None,
                |_, _| panic!("removing the ambient wall cannot rearm this attempt"),
            ),
            Err(BatchFailure::Stopped(AttemptStop::Deadline)),
        );
    }
    assert_eq!(execute(&solver(&parent), SAT).unwrap(), ["sat"]);
}

#[test]
fn expired_local_wall_allows_a_fresh_depth_without_rearming_the_attempt() {
    let parent = CancellationToken::new();
    let solver = solver(&parent);
    let commands = ay_frontend::parse(SAT).unwrap();
    let past = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("fixture instant supports a one-second offset");
    let mut executor = ay_dpll::Executor::new();
    assert_eq!(
        solver.execute_controlled_batch(&mut executor, &commands, Some(past), |_, _| panic!(
            "a locally expired batch must not be installed"
        ),),
        // Expired before the executor ran: the caller's build, not a BV
        // encoding cut, so the fresh sweep may still continue deeper.
        Err(BatchFailure::LocalDeadline),
    );
    assert_eq!(solver.execution_stop.get(), None);
    assert!(solver
        .exec_commands_with_deadline(&mut executor, &commands, Some(past))
        .is_none());
    assert_eq!(solver.execution_stop.get(), None);
    assert_eq!(
        solver.exec_commands(&mut executor, &commands).unwrap(),
        ["sat"]
    );
    assert!(!parent.is_cancelled());
}

#[test]
fn equal_global_and_local_deadlines_take_terminal_priority() {
    let parent = CancellationToken::new();
    let solver = solver(&parent);
    let commands = ay_frontend::parse(SAT).unwrap();
    let past = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("fixture instant supports a one-second offset");
    solver.solve_deadline.set(Some(past));
    assert_eq!(
        solver.execute_controlled_batch(
            &mut ay_dpll::Executor::new(),
            &commands,
            Some(past),
            |_, _| panic!("expired work must not install a batch"),
        ),
        Err(BatchFailure::Stopped(AttemptStop::Deadline)),
    );
    solver.solve_deadline.set(None);
    assert_eq!(solver.execution_stop.get(), Some(AttemptStop::Deadline));
    {
        let mut raw = solver.stats.borrow_mut();
        raw.budget_exhausted = false;
        raw.exhausted_search = true;
    }
    let stats = solver.stats();
    assert!(
        stats.budget_exhausted,
        "the captured deadline owns the report"
    );
    assert!(!stats.exhausted_search);
    assert!(execute(&solver, SAT).is_none());
    assert!(!parent.is_cancelled());
}

#[test]
fn setup_batches_honor_solve_wall_and_zero_memory() {
    let parent = CancellationToken::new();
    let solver = solver(&parent);
    solver.solve_deadline.set(Some(Instant::now()));
    assert!(execute(&solver, SAT).is_none());
    assert_eq!(solver.execution_stop.get(), Some(AttemptStop::Deadline));
    solver.solve_deadline.set(None);
    assert!(execute(&solver, SAT).is_none());
    let zero = BmcSolver::new(
        ChcProblem::new(),
        BmcConfig::default().with_memory_budget(0),
    );
    assert!(execute(&zero, SAT).is_none());
    assert_eq!(zero.execution_stop.get(), Some(AttemptStop::Memory));
    assert!(!parent.is_cancelled());
}

#[test]
fn removed_memory_limits_cannot_revive_an_observed_attempt() {
    let parent = CancellationToken::new();
    let commands = ay_frontend::parse(SAT).unwrap();
    let old = solver(&parent);
    {
        let _zero = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(0));
        assert_eq!(
            old.execute_controlled_batch(
                &mut ay_dpll::Executor::new(),
                &commands,
                None,
                |_, _| panic!("a closed memory owner must not install a batch"),
            ),
            Err(BatchFailure::Stopped(AttemptStop::Memory)),
        );
    }
    assert_eq!(old.execution_stop.get(), Some(AttemptStop::Memory));
    {
        // Model a later fallback writing broad legacy flags after refusal.
        let mut raw = old.stats.borrow_mut();
        raw.budget_exhausted = true;
        raw.exhausted_search = true;
    }
    let stats = old.stats();
    assert!(
        !stats.budget_exhausted,
        "memory refusal is not a time budget"
    );
    assert!(!stats.exhausted_search);
    // Use a new executor: refusal must be held by BMC, not its previous cap.
    assert!(execute(&old, SAT).is_none());

    let mut configured = solver(&parent);
    configured.config.memory_budget = Some(0);
    assert_eq!(
        configured.execute_controlled_batch(
            &mut ay_dpll::Executor::new(),
            &commands,
            None,
            |_, _| panic!("a zero configured cap must not install a batch"),
        ),
        Err(BatchFailure::Stopped(AttemptStop::Memory)),
    );
    configured.config.memory_budget = None;
    assert_eq!(configured.execution_stop.get(), Some(AttemptStop::Memory));
    assert!(execute(&configured, SAT).is_none());
    assert_eq!(execute(&solver(&parent), SAT).unwrap(), ["sat"]);
    assert!(!parent.is_cancelled());
}

#[test]
fn an_unavailable_command_allows_the_next_real_batch() {
    let parent = CancellationToken::new();
    let solver = solver(&parent);
    let commands = ay_frontend::parse("(pop 1)").unwrap();
    // This is the real executor's scope-underflow error, not an injected stop.
    assert!(ay_dpll::Executor::new().execute_all(&commands).is_err());
    let mut executor = ay_dpll::Executor::new();
    let mut phases = Vec::new();
    assert_eq!(
        solver.execute_controlled_batch(&mut executor, &commands, None, |phase, _| {
            phases.push(phase);
        }),
        Err(BatchFailure::Unavailable),
    );
    assert_eq!(phases, [BatchPhase::Installed, BatchPhase::Executed]);
    assert_eq!(solver.execution_stop.get(), None);
    let sat = ay_frontend::parse(SAT).unwrap();
    assert_eq!(solver.exec_commands(&mut executor, &sat).unwrap(), ["sat"]);
    assert!(!parent.is_cancelled());
}

#[test]
fn single_batch_failure_preserves_checked_prefix_and_terminal_failures() {
    let parent = CancellationToken::new();
    let local = solver(&parent);
    for (first_unchecked, consecutive, expected_start, expected_consecutive) in
        [(None, 5, 7, 5), (Some(3), 5, 3, 0), (Some(7), 5, 7, 0)]
    {
        let result = local.single_batch_failure(
            BatchFailure::LocalDeadline,
            7,
            first_unchecked,
            consecutive,
        );
        let Some(SingleExecutorOutcome::RetryFresh {
            start_depth,
            consecutive_unsat,
        }) = result
        else {
            panic!("local expiry must retry the actual unchecked prefix: {result:?}");
        };
        assert_eq!(start_depth, expected_start);
        assert_eq!(consecutive_unsat, expected_consecutive);
        assert_eq!(local.execution_stop.get(), None);
    }
    assert!(local
        .single_batch_failure(BatchFailure::Unavailable, 7, Some(3), 5)
        .is_none());
    for stop in [
        AttemptStop::Cancelled,
        AttemptStop::Deadline,
        AttemptStop::Memory,
        AttemptStop::Observer,
    ] {
        // The real controlled caller captures terminal ownership before this
        // bookkeeping helper. Exercise each exact reason without a fake solve.
        let stopped = solver(&parent);
        stopped.execution_stop.set(Some(stop));
        assert!(matches!(
            stopped.single_batch_failure(BatchFailure::Stopped(stop), 7, Some(3), 5),
            Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown))
        ));
        assert_eq!(stopped.execution_stop.get(), Some(stop));
    }
}

#[test]
fn expired_symbolic_wall_never_becomes_a_fresh_thirty_second_query() {
    let parent = CancellationToken::new();
    let solver = solver(&parent);
    let false_formula = ChcExpr::Bool(false);
    assert_eq!(
        solver.check_symbolic_formula(&false_formula, Some(Instant::now())),
        Some(None),
    );
    assert_eq!(
        solver.check_symbolic_formula(&false_formula, None),
        Some(Some(false))
    );
    parent.cancel();
    assert_eq!(
        solver.check_symbolic_formula(&false_formula, None),
        Some(None)
    );
}

/// Only a local deadline whose batch cut a BV encoding and searched nothing
/// is an encoding deadline; a batch that also searched, or cut nothing, keeps
/// `LocalDeadline`, and every other failure passes through.
#[test]
fn only_an_encoding_cut_with_no_search_is_an_encoding_deadline() {
    use super::classify_local_deadline as classify;
    assert_eq!(
        classify(BatchFailure::LocalDeadline, true, false),
        BatchFailure::EncodingDeadline
    );
    assert_eq!(
        classify(BatchFailure::LocalDeadline, true, true),
        BatchFailure::LocalDeadline
    );
    assert_eq!(
        classify(BatchFailure::LocalDeadline, false, false),
        BatchFailure::LocalDeadline
    );
    for failure in [
        BatchFailure::Unavailable,
        BatchFailure::Stopped(AttemptStop::Deadline),
        BatchFailure::Stopped(AttemptStop::Memory),
    ] {
        assert_eq!(classify(failure, true, false), failure);
    }
}
