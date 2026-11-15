// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The response a run owes the query in flight, and how a run that a budget
//! or a signal ends reports it.

use super::*;

/// An incremental script's later query is owed its own `unknown`: the latch
/// is per query. As a once-per-process latch, a hard exit during the second
/// `check-sat` printed nothing for it (stdout `sat` only, exit 0).
#[test]
fn each_query_is_owed_one_unknown_whatever_an_earlier_query_printed() {
    // The first query printed its verdict.
    let printed = AtomicBool::new(true);
    assert!(!claim_owed_unknown_in(&printed), "answered already");

    // A new query starts: `owe_response_for_new_query` clears the latch.
    printed.store(false, Ordering::SeqCst);
    assert!(claim_owed_unknown_in(&printed), "the cut query is answered");
    assert!(!claim_owed_unknown_in(&printed), "and answered once");
}

/// A run SIGTERM ended says so; it said `timeout`, though no deadline fired.
#[test]
fn a_terminated_run_is_not_reported_as_a_timeout() {
    let pairs: [(&[u8], &[u8]); 3] = [
        (
            b"(:reason-unknown \"timeout\")\n",
            b"(:reason-unknown \"canceled\")\n",
        ),
        (b"c timeout\n", b"c terminated\n"),
        (
            b"c timeout after the verdict was published; verdict stands\n",
            b"c terminated after the verdict was published; verdict stands\n",
        ),
    ];
    for (timeout, terminated) in pairs {
        assert_eq!(termination_note(timeout, false), timeout);
        assert_eq!(termination_note(timeout, true), terminated);
    }
}

/// A memory breach never turns a published decisive verdict into a failed
/// run, the same rule a deadline follows.
#[test]
fn a_memout_after_a_decisive_verdict_exits_with_the_verdicts_code() {
    assert_eq!(memout_exit_code(false, false, 124), 124);
    assert_eq!(memout_exit_code(true, false, 124), 0);
    // An abandoned export promised an artifact it did not produce.
    assert_eq!(memout_exit_code(true, true, 124), 124);
}
