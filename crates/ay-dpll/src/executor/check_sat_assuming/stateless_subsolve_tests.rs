// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! D10(a): a scoped assumption window is never solved on the session's own
//! lanes, in any session, and the session's lanes come back untouched on every
//! exit.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_frontend::{parse, Command};

use super::{Executor, Result, SolveResult};
use crate::incremental_state::{IncrementalBvState, IncrementalTheoryState};

const SESSION_THEORY_MARK: u64 = 7;
const SESSION_BV_MARK: u32 = 99;
const WINDOW_THEORY_MARK: u64 = 1234;
const WINDOW_BV_MARK: u32 = 555;

/// A session with one assertion and a mark on both of its persistent lanes,
/// in incremental mode (after a `push`) or not, proof-producing or not, with
/// its assertion captured as the query's root (as `with_scope_root_depths`
/// does at a query's entry).
fn marked_session(incremental: bool, proofs: bool) -> Executor {
    marked_session_demanding(incremental, proofs, false)
}

/// [`marked_session`], optionally demanding a checked certificate
/// (`--self-check`).
fn marked_session_demanding(incremental: bool, proofs: bool, demanded: bool) -> Executor {
    let commands = parse(
        r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        "#,
    )
    .expect("test SMT should parse");
    let mut exec = Executor::new();
    exec.execute_all(&commands)
        .expect("test SMT setup should execute");
    if incremental {
        exec.execute(&Command::Push(1)).expect("push");
    }
    assert_eq!(exec.incremental_mode, incremental);
    if proofs {
        exec.proof_tracker.enable();
    } else {
        exec.proof_tracker.disable();
    }
    assert_eq!(exec.produce_proofs_enabled(), proofs);
    exec.set_self_check(demanded);
    assert_eq!(exec.checked_certificate_demanded(), demanded);
    let mut theory = IncrementalTheoryState::new();
    theory.theory_conflicts = SESSION_THEORY_MARK;
    exec.incr_theory_state = Some(theory);
    let mut bv = IncrementalBvState::new();
    bv.next_bv_var = SESSION_BV_MARK;
    exec.incr_bv_state = Some(Box::new(bv));
    let roots: HashMap<_, _> = exec.ctx.assertions.iter().map(|&root| (root, 0)).collect();
    exec.scope_root_depths = Some(Arc::new(roots));
    exec
}

fn lane_marks(exec: &Executor) -> (Option<u64>, Option<u32>) {
    (
        exec.incr_theory_state
            .as_ref()
            .map(|state| state.theory_conflicts),
        exec.incr_bv_state.as_ref().map(|state| state.next_bv_var),
    )
}

thread_local! {
    static SEEN: std::cell::RefCell<Vec<(Option<u64>, Option<u32>)>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

fn take_seen() -> Vec<(Option<u64>, Option<u32>)> {
    SEEN.with(|seen| std::mem::take(&mut *seen.borrow_mut()))
}

/// What a window's solve does to the lanes it runs on: it encodes the window
/// (here: marks) into them — at depth 0 as permanent units. Records what it
/// was handed.
fn window_solve(this: &mut Executor) -> Result<SolveResult> {
    SEEN.with(|seen| seen.borrow_mut().push(lane_marks(this)));
    this.incr_theory_state
        .get_or_insert_with(IncrementalTheoryState::new)
        .theory_conflicts = WINDOW_THEORY_MARK;
    let mut bv = IncrementalBvState::new();
    bv.next_bv_var = WINDOW_BV_MARK;
    this.incr_bv_state = Some(Box::new(bv));
    Ok(SolveResult::Unknown)
}

fn panicking_window_solve(this: &mut Executor) -> Result<SolveResult> {
    let _ = window_solve(this);
    panic!("sentinel window panic");
}

fn assert_session_lanes_back(exec: &Executor, what: &str) {
    assert_eq!(
        lane_marks(exec),
        (Some(SESSION_THEORY_MARK), Some(SESSION_BV_MARK)),
        "{what}: the session's lanes never see the window"
    );
}

/// Which lanes the window starts on, per session kind — never the session's:
/// in incremental mode an empty theory lane (origin/main's
/// `solve_without_persistent_encoding`); outside it a COPY of the session's
/// lanes (the marks are copied), also under the default posture's
/// best-effort proof tracker; when a checked certificate is demanded
/// (`--self-check`), no lanes at all (a copy logs no proof). The session's
/// lanes come back on every exit.
#[test]
fn scoped_window_never_runs_on_the_session_lanes() {
    let session_copy = (Some(SESSION_THEORY_MARK), Some(SESSION_BV_MARK));
    let cases = [
        (true, false, false, (Some(0), None)),
        (true, true, false, (Some(0), None)),
        (true, true, true, (Some(0), None)),
        (false, false, false, session_copy),
        (false, true, false, session_copy),
        (false, true, true, (None, None)),
    ];
    for (incremental, proofs, demanded, starts_on) in cases {
        let what = format!("incremental={incremental} proofs={proofs} demanded={demanded}");
        let mut exec = marked_session_demanding(incremental, proofs, demanded);
        let _ = take_seen();
        let result = exec.solve_scoped_window(window_solve);
        assert!(matches!(result, Ok(SolveResult::Unknown)));
        assert_eq!(
            take_seen(),
            [starts_on],
            "{what}: the lanes the window starts on"
        );
        assert_session_lanes_back(&exec, &what);

        let panic = catch_unwind(AssertUnwindSafe(|| {
            let _ = exec.solve_scoped_window(panicking_window_solve);
        }));
        assert!(panic.is_err(), "test panic should propagate");
        assert_session_lanes_back(&exec, &format!("{what}, unwind"));
    }
}

/// Outside incremental mode a later sub-solve of the SAME window in the same
/// query continues the lanes the first one left (origin/main continued the
/// session's); a different window starts over from the session; the query
/// boundary drops them.
#[test]
fn scoped_window_lanes_are_continued_for_the_same_window_only() {
    let mut exec = marked_session(false, false);
    let window = exec.ctx.assertions.clone();
    let _ = take_seen();
    let _ = exec.solve_scoped_window(window_solve);
    let _ = exec.solve_scoped_window(window_solve);
    assert_eq!(
        take_seen(),
        [
            (Some(SESSION_THEORY_MARK), Some(SESSION_BV_MARK)),
            (Some(WINDOW_THEORY_MARK), Some(WINDOW_BV_MARK)),
        ],
        "the second sub-solve of the window continues the first one's lanes"
    );
    assert_session_lanes_back(&exec, "continued window");

    let extra = exec.ctx.terms.mk_bool(true);
    exec.ctx.assertions.push(extra);
    let _ = exec.solve_scoped_window(window_solve);
    assert_eq!(
        take_seen(),
        [(Some(SESSION_THEORY_MARK), Some(SESSION_BV_MARK))],
        "another window starts from a copy of the session again"
    );
    exec.ctx.assertions = window;

    exec.scope_root_depths = None;
    let _ = exec.with_scope_root_depths(|this| {
        let _ = this.solve_scoped_window(window_solve);
    });
    assert_eq!(
        take_seen(),
        [(Some(SESSION_THEORY_MARK), Some(SESSION_BV_MARK))],
        "a new query does not continue the last query's window"
    );
    assert!(
        exec.scoped_window_lanes.is_none(),
        "dropped at the query boundary"
    );
    assert_session_lanes_back(&exec, "new query");
}

/// A window that leaves out one of the query's roots (the unsat-core
/// minimizer's subsets, under a named-core redirect) must not be solved under
/// that root's live activation, so it gets no copy of the session's lanes.
#[test]
fn scoped_window_missing_a_root_gets_no_copy_of_the_session() {
    let mut exec = marked_session(false, false);
    exec.ctx.assertions.clear();
    let _ = take_seen();
    let _ = exec.solve_scoped_window(window_solve);
    assert_eq!(take_seen(), [(None, None)]);
    assert_session_lanes_back(&exec, "subset window");
}

/// The quantified route's helper (origin/main ec28f5b4f8, unchanged here)
/// swaps the lanes only in incremental mode; outside it the solve runs on the
/// session's own lanes. The scoped route does not use it.
#[test]
fn quantified_route_helper_swaps_lanes_only_in_incremental_mode() {
    let mut exec = marked_session(true, false);
    let _ = take_seen();
    let _ = exec.solve_without_persistent_encoding(window_solve);
    assert_eq!(take_seen(), [(Some(0), None)]);
    assert_session_lanes_back(&exec, "incremental");

    let mut exec = marked_session(false, false);
    let _ = exec.solve_without_persistent_encoding(window_solve);
    assert_eq!(
        take_seen(),
        [(Some(SESSION_THEORY_MARK), Some(SESSION_BV_MARK))],
        "outside incremental mode the session's own lanes"
    );
}
