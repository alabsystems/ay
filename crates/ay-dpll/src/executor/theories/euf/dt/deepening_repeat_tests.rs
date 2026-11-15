// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The datatype deepening loop does not solve the same assertions twice.
//!
//! `solve_with_dt_axioms` re-solves at a larger unroll depth after every
//! `Unknown`. Its own stop test compares term-store sizes, and a real solve
//! grows the store (split atoms, model terms), so the loop used to walk to its
//! ceiling whether or not a deeper unroll added an axiom. The stand-in solves
//! below answer `Unknown` and mint terms on every call, like a ground solve
//! whose candidate model is rejected.
//!
//! A deeper round's window is not always larger. The recursive unroll takes
//! its next level from the selector terms the current call MINTS, so a round
//! whose selector terms were all minted by an earlier round stops at the
//! first level: on a recursive datatype the rounds after the first add only
//! the tester axioms of the earlier rounds' constructor terms, and then
//! nothing. The twin below therefore grows the window through the model terms
//! its stand-in solve mints, not through the depth.
//!
//! The repeat exit answers `Unknown`, never a verdict: it runs no round, so
//! nothing it sees could justify a Sat or an Unsat.

use std::cell::{Cell, RefCell};

use ay_core::{Sort, Symbol, TermId};
use ay_frontend::parse;

use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

thread_local! {
    static SOLVES: Cell<usize> = const { Cell::new(0) };
    /// The assertion window each stand-in solve was handed, in order.
    static WINDOWS: RefCell<Vec<Vec<TermId>>> = const { RefCell::new(Vec::new()) };
}

/// A ground solve that cannot decide: it grows the term store, as every real
/// solve does, and answers `Unknown`.
fn undecided_solve(executor: &mut Executor) -> Result<SolveResult> {
    let n = SOLVES.with(|solves| {
        solves.set(solves.get() + 1);
        solves.get()
    });
    WINDOWS.with(|windows| windows.borrow_mut().push(executor.ctx.assertions.clone()));
    let _ = executor
        .ctx
        .terms
        .mk_var(format!("__deepening_test_scratch_{n}"), Sort::Bool);
    executor.last_unknown_reason = Some(UnknownReason::Incomplete);
    Ok(SolveResult::Unknown)
}

/// [`undecided_solve`] that also mints a new `Pair` value, `(mk k k)` for a
/// fresh `k`, as a model term. The next round's tester-evaluation axioms cover
/// every constructor term of the store, so every window is larger than the
/// one before it.
fn undecided_solve_minting_a_value(executor: &mut Executor) -> Result<SolveResult> {
    let n = SOLVES.with(Cell::get) + 1;
    let k = executor
        .ctx
        .terms
        .mk_var(format!("__deepening_test_value_{n}"), Sort::Int);
    let _ = executor.ctx.terms.mk_app(
        Symbol::named("mk"),
        vec![k, k],
        Sort::Uninterpreted("Pair".to_string()),
    );
    undecided_solve(executor)
}

/// A ground solve that answers `Unknown` the first time it is handed a window
/// and `Sat` when it is handed the same window again: a solve whose answer is
/// not a function of its assertions. Only a loop that solves a window twice
/// can see the `Sat`.
fn sat_on_a_repeated_window(executor: &mut Executor) -> Result<SolveResult> {
    let window = executor.ctx.assertions.clone();
    let repeated = WINDOWS.with(|windows| windows.borrow().contains(&window));
    let _ = undecided_solve(executor)?;
    if repeated {
        executor.last_unknown_reason = None;
        return Ok(SolveResult::Sat);
    }
    Ok(SolveResult::Unknown)
}

struct Run {
    result: SolveResult,
    reason: Option<UnknownReason>,
    solves: usize,
    windows: Vec<Vec<TermId>>,
}

/// Run the deepening loop over `script` with `solve`.
fn run(script: &str, solve: fn(&mut Executor) -> Result<SolveResult>) -> Run {
    let commands = parse(script).expect("test script parses");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("test script executes");
    SOLVES.with(|solves| solves.set(0));
    WINDOWS.with(|windows| windows.borrow_mut().clear());
    let result = executor
        .solve_with_dt_axioms(None, solve)
        .expect("the deepening loop returns a verdict");
    Run {
        result,
        reason: executor.last_unknown_reason,
        solves: SOLVES.with(Cell::get),
        windows: WINDOWS.with(|windows| windows.borrow().clone()),
    }
}

/// A pair has no datatype-sorted field: its unroll is complete after a round
/// or two (the first round's own selector terms seed the second), and every
/// deeper one produces the same axioms again.
const FLAT: &str = r#"
    (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)) (end))))
    (declare-const p Pair)
    (declare-const q Pair)
    (assert (= (fst p) (fst q)))
    (assert (not (= p q)))
"#;

/// Solves a complete unroll may still take before the loop notices that the
/// next depth adds nothing. The loop's ceiling is 64 depths.
const SOLVES_TO_A_FIXPOINT: usize = 3;

fn window_sizes(run: &Run) -> Vec<usize> {
    run.windows.iter().map(Vec::len).collect()
}

#[test]
fn a_deeper_unroll_that_adds_nothing_is_not_solved_again() {
    let run = run(FLAT, undecided_solve);
    assert!(
        matches!(run.result, SolveResult::Unknown),
        "an undecided solve must stay undecided, got {:?}",
        run.result
    );
    assert!(
        run.solves <= SOLVES_TO_A_FIXPOINT,
        "{} solves (windows {:?}) of a datatype whose unroll is complete: \
         the same assertions were solved again",
        run.solves,
        window_sizes(&run)
    );
    for pair in run.windows.windows(2) {
        assert_ne!(pair[0], pair[1], "one window was solved twice in a row");
    }
}

/// The twin: the same datatype, and a solve that mints a model value each
/// time, so each round's window has new axioms. Every one is solved, up to
/// the loop's ceiling.
#[test]
fn a_deeper_round_whose_window_gained_axioms_is_still_solved() {
    let run = run(FLAT, undecided_solve_minting_a_value);
    assert!(
        matches!(run.result, SolveResult::Unknown),
        "an undecided solve must stay undecided, got {:?}",
        run.result
    );
    assert!(
        run.solves > 3 * SOLVES_TO_A_FIXPOINT,
        "{} solves (windows {:?}): every round adds axioms, so deepening \
         must go on",
        run.solves,
        window_sizes(&run)
    );
    for pair in run.windows.windows(2) {
        assert!(pair[1].len() > pair[0].len(), "a window did not grow");
    }
}

/// The repeat exit is fail-safe: it answers `Unknown` with the reason the
/// last round that ran recorded, and it does not hand the repeated window to
/// a solve that would answer it otherwise.
#[test]
fn the_repeat_exit_answers_unknown_and_never_a_verdict() {
    let run = run(FLAT, sat_on_a_repeated_window);
    assert!(
        matches!(run.result, SolveResult::Unknown),
        "the repeat exit must answer Unknown, got {:?}",
        run.result
    );
    assert_eq!(run.reason, Some(UnknownReason::Incomplete));
    let mut distinct = run.windows.clone();
    distinct.sort();
    distinct.dedup();
    assert_eq!(
        distinct.len(),
        run.windows.len(),
        "a window was solved twice"
    );
}
