// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! P4a: a congruence pass cut by a clock leaves `unknown` with that stop's
//! reason, never `incomplete`; only a count cap leaves `incomplete`.

use ay_frontend::parse;

use super::*;
use crate::executor_types::UnknownReason;

/// Satisfiable only through a model of `f` (one non-BV-return application
/// pair, so the non-BV congruence pass runs).
const UFBV_SAT: &str = r#"
    (set-logic QF_UFBV)
    (declare-sort U 0)
    (declare-fun f ((_ BitVec 8)) U)
    (declare-fun x () (_ BitVec 8))
    (declare-fun y () (_ BitVec 8))
    (assert (distinct (f x) (f y)))
    (check-sat)
"#;

fn solve(script: &str, bail: Option<TestCongruenceBail>) -> (Vec<String>, Executor) {
    let mut exec = Executor::new();
    exec.test_force_non_bv_congruence_bail = bail;
    let output = exec
        .execute_all(&parse(script).expect("fixture parses"))
        .expect("fixture runs");
    (output, exec)
}

#[test]
fn a_count_cap_outranks_a_stop_and_the_first_stop_stands() {
    let timeout = Some(CongruenceBail::Stop(UnknownOrigin::SolveDeadline));
    let interrupt = Some(CongruenceBail::Stop(UnknownOrigin::InterruptFlag));
    let count = Some(CongruenceBail::Count);
    assert_eq!(CongruenceBail::merge(None, None), None);
    assert_eq!(CongruenceBail::merge(None, timeout), timeout);
    assert_eq!(CongruenceBail::merge(timeout, None), timeout);
    assert_eq!(CongruenceBail::merge(timeout, interrupt), timeout);
    assert_eq!(CongruenceBail::merge(timeout, count), count);
    assert_eq!(CongruenceBail::merge(count, interrupt), count);
    assert_eq!(
        CongruenceBail::Count.origin().reason(),
        UnknownReason::Incomplete
    );
    assert_eq!(
        CongruenceBail::Stop(UnknownOrigin::MemoryBudget)
            .origin()
            .reason(),
        UnknownReason::MemoryLimit
    );
}

#[test]
fn a_deadline_that_cuts_the_congruence_pass_is_published_as_timeout() {
    let (baseline, _) = solve(UFBV_SAT, None);
    assert_eq!(baseline, vec!["sat"], "without a bail the fixture is sat");

    // The deadline (share) passes inside the pass and is over by the time the
    // SAT search runs, so the search still finds its model: only the bail can
    // say what made that model untrustworthy.
    let (output, exec) = solve(UFBV_SAT, Some(TestCongruenceBail::DeadlineShareExpires));
    assert_eq!(output, vec!["unknown"]);
    assert_eq!(
        exec.unknown_reason(),
        Some(UnknownReason::Timeout),
        "a clock cut the pass: the stop it was, never incomplete"
    );
    let statistics = exec.statistics();
    assert_eq!(statistics.get_string("unknown.reason"), Some("timeout"));
    assert_eq!(
        statistics.get_string("unknown.phase"),
        Some("non-bv-congruence-bail")
    );
}

#[test]
fn a_count_capped_congruence_pass_stays_incomplete() {
    let (output, exec) = solve(UFBV_SAT, Some(TestCongruenceBail::CountCap));
    assert_eq!(output, vec!["unknown"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::Incomplete));
}

/// An incremental session whose first check-sat runs the non-BV congruence
/// pass; the pass runs again only when a check-sat brings new assertions.
const UFBV_SESSION: &str = r#"
    (set-logic QF_UFBV)
    (declare-sort U 0)
    (declare-fun f ((_ BitVec 8)) U)
    (declare-fun x () (_ BitVec 8))
    (declare-fun y () (_ BitVec 8))
    (push 1)
    (assert (distinct (f x) (f y)))
    (check-sat)
"#;

/// The first check-sat of [`UFBV_SESSION`] under a forced bail, then a second
/// check-sat with no stop of its own.
fn session_after_bail(bail: TestCongruenceBail) -> (Executor, Vec<String>) {
    let mut exec = Executor::new();
    exec.test_force_non_bv_congruence_bail = Some(bail);
    let first = exec
        .execute_all(&parse(UFBV_SESSION).expect("fixture parses"))
        .expect("fixture runs");
    assert_eq!(first, vec!["unknown"]);
    exec.test_force_non_bv_congruence_bail = None;
    let second = exec
        .execute_all(&parse("(check-sat)").expect("parses"))
        .expect("runs");
    (exec, second)
}

#[test]
fn an_incremental_session_re_encodes_after_a_stop_cut_its_congruence_pass() {
    // The first check-sat's deadline cut the pass, and it said so. The
    // second hit no stop: it must neither inherit that stop (`timeout` for a
    // clock that never fired on it, `interrupted` for an interrupt nobody
    // raised) nor relabel it `incomplete`. It re-encodes, the pass runs in
    // full, and the query's own answer stands.
    let (exec, second) = session_after_bail(TestCongruenceBail::DeadlineShareExpires);
    assert_eq!(second, vec!["sat"], "{:?}", exec.unknown_reason());
    let state = exec
        .incremental_bv_state()
        .expect("the session keeps its incremental BV state");
    assert_eq!(state.congruence_partial, None);
    assert_eq!(state.scope_depth, 1, "the rebuild keeps the frontend scope");
}

#[test]
fn an_incremental_session_keeps_a_count_capped_congruence_partial() {
    // A count cap leaves the same partial set on every host: the second
    // check-sat reuses it and says `incomplete`, as the first did.
    let (exec, second) = session_after_bail(TestCongruenceBail::CountCap);
    assert_eq!(second, vec!["unknown"]);
    assert_eq!(exec.unknown_reason(), Some(UnknownReason::Incomplete));
}
