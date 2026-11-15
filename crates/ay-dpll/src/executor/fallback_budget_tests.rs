// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #defmacro-named-preuse fallback chain: an attempt that spends its narrowed
//! half of the command budget must still leave the next stack its solve.

use super::*;
use ay_core::time::Instant;
use std::time::Duration;

/// The first attempt of a two-stack chain runs on half the command budget.
/// When it spends that half and answers `unknown`, the command still has the
/// other half, so the raw stack is due. Before the fix the question was asked
/// with the attempt's narrowed deadline still installed, read it as an
/// expired command, and published `unknown` at half the budget.
#[test]
fn an_attempt_that_spent_its_half_still_leaves_the_next_stack_due() {
    let exec = Executor::new();
    let command_deadline = Instant::now() + Duration::from_secs(600);
    exec.solve_deadline.set(Some(command_deadline));

    let attempt = exec.reserve_budget_for_fallback_stacks(1);
    assert!(
        attempt.is_some(),
        "a chain with a fallback narrows the attempt"
    );
    let narrowed = exec.solve_deadline.get().expect("narrowed deadline");
    assert!(narrowed < command_deadline, "the attempt runs on a share");

    // The attempt spends its share: its deadline is now in the past.
    exec.solve_deadline.set(Some(Instant::now()));
    assert!(
        !exec.raw_stack_retry_is_due(&SolveResult::Unknown),
        "asked under the spent share, the chain looks finished (the old question)"
    );

    assert!(
        exec.fallback_retry_is_due(attempt, &SolveResult::Unknown),
        "the command still has budget, so the next stack is due"
    );
    assert_eq!(
        exec.solve_deadline.get(),
        Some(command_deadline),
        "the command deadline is back for the retry"
    );
}

/// The fix gives back the share; it does not invent budget. A command whose
/// own deadline has passed, and any decisive verdict, end the chain.
#[test]
fn an_expired_command_or_a_decisive_verdict_ends_the_chain() {
    let exec = Executor::new();
    exec.solve_deadline.set(Some(Instant::now()));
    let attempt = exec.reserve_budget_for_fallback_stacks(1);
    assert!(!exec.fallback_retry_is_due(attempt, &SolveResult::Unknown));

    let exec = Executor::new();
    exec.solve_deadline
        .set(Some(Instant::now() + Duration::from_secs(600)));
    let attempt = exec.reserve_budget_for_fallback_stacks(1);
    assert!(!exec.fallback_retry_is_due(attempt, &SolveResult::Sat));

    // No chain, no share: the question is the ordinary one.
    let exec = Executor::new();
    exec.solve_deadline
        .set(Some(Instant::now() + Duration::from_secs(600)));
    assert!(exec.reserve_budget_for_fallback_stacks(0).is_none());
    assert!(exec.fallback_retry_is_due(None, &SolveResult::Unknown));
}
