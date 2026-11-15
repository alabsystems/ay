// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// A panic inside the #quantified-trace-arming retry hands back everything the
/// retry borrowed.
///
/// The retry arms the proof recorder, parsed retention and a reconstruction
/// budget on a shed (competition-mode) executor. `(reset)` carries the
/// recorder and the budget over as host configuration, and no later
/// `begin_public_solve` restores the budget or the retention, so a borrow that
/// outlives its query changes how every later query certifies. The disarm
/// used to run only when the retry RETURNED.
#[test]
fn quantified_trace_retry_hands_back_its_borrow_when_the_retry_panics() {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    load_quantified_mix(&mut exec);
    assert!(
        exec.competition_shedding_active(),
        "the retry only runs on a shed executor"
    );
    let authored = exec.ctx.assertions.clone();
    let before = exec.session_proof_configuration();
    let recorder_before = exec.proof_tracker.is_enabled();
    assert!(
        !recorder_before,
        "a shed executor starts with the recorder off"
    );
    exec.test_panic_in_quantified_trace_retry = true;

    let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        exec.quantified_trace_arming_unknown_retry(
            SolveResult::Unknown,
            &authored,
            super::retry_allowance::RetryAllowance::UNBOUNDED,
        )
    }));

    assert!(
        unwound.is_err(),
        "the fixture must reach the retry and panic inside it"
    );
    assert_eq!(
        exec.session_proof_configuration(),
        before,
        "the retry's borrowed proof configuration must be handed back on unwind"
    );
    assert_eq!(
        exec.proof_tracker.is_enabled(),
        recorder_before,
        "the retry's recorder arming must be undone on unwind"
    );
    assert!(!exec.quantified_trace_retry_armed);
    assert!(!exec.quantified_query_defeats_shedding);
    assert_eq!(exec.ctx.assertions, authored);

    // The same executor retries again on a later query: the one-shot latch did
    // not stay armed.
    exec.test_panic_in_quantified_trace_retry = false;
    let again = exec.quantified_trace_arming_unknown_retry(
        SolveResult::Unknown,
        &authored,
        super::retry_allowance::RetryAllowance::UNBOUNDED,
    );
    assert!(again.is_ok(), "{again:?}");
    assert_eq!(exec.session_proof_configuration(), before);
}
