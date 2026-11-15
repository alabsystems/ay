// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[test]
#[timeout(180000)]
fn counterexample_recheck_binds_original_source_path_and_exact_replay() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(90);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = fixtures::bodyless(true, false);
    let mut evidence = require_unsafe(&source, deadline, &token);
    let changed = fixtures::bodyless(true, true);
    assert_ne!(source.source_smtlib(), changed.source_smtlib());
    assert!(!evidence.recheck(&changed, remaining(deadline), &token));

    // These are descendant-test fault injections; the public evidence API
    // exposes none of these mutation capabilities or an unchecked constructor.
    let original_source = evidence.source.clone();
    evidence.source = Arc::from(changed.source_smtlib());
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    evidence.source = original_source;
    let original_indices = evidence.clause_indices.clone();
    evidence.clause_indices[0] = usize::MAX;
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    evidence.clause_indices = original_indices;
    let original_replay = evidence.obligation.clone();
    evidence.obligation.push_str("\n(assert false)\n");
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    evidence.obligation = original_replay;
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
fn original_counterexample_entry_refuses_cancellation_time_and_memory_exhaustion() {
    let source = fixtures::bodyless(true, false);
    let token = CancellationToken::new();
    token.cancel();
    assert!(!matches!(
        source.solve(Duration::from_secs(1), Some(TERM_BUDGET), &token),
        QuantifiedChcResult::Unsafe(_)
    ));
    token.reset();
    for duration in [Duration::ZERO, Duration::MAX] {
        assert!(!matches!(
            source.solve(duration, Some(TERM_BUDGET), &token),
            QuantifiedChcResult::Unsafe(_)
        ));
    }
    {
        let _deadline = ScopedSmtDeadline::install_until(Instant::now());
        assert!(!matches!(
            source.solve(Duration::from_secs(60), Some(TERM_BUDGET), &token),
            QuantifiedChcResult::Unsafe(_)
        ));
    }
    assert!(!matches!(
        source.solve(Duration::from_secs(1), Some(0), &token),
        QuantifiedChcResult::Unsafe(_)
    ));
}

#[test]
#[timeout(180000)]
fn original_counterexample_recheck_refuses_stale_controls_and_retains_memory_cap() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(90);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let source = fixtures::bodyless(true, false);
    let token = CancellationToken::new();
    let mut evidence = require_unsafe(&source, deadline, &token);
    token.cancel();
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    token.reset();
    assert!(!evidence.recheck(&source, Duration::ZERO, &token));
    assert!(!evidence.recheck(&source, Duration::MAX, &token));
    {
        let _expired = ScopedSmtDeadline::install_until(Instant::now());
        assert!(!evidence.recheck(&source, remaining(deadline), &token));
    }
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    evidence.memory_budget = Some(0);
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
}
