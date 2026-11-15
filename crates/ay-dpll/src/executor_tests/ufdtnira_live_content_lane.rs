// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Routing pins for `#ufdtnira-live-content-lane` (`executor/check_sat.rs`,
//! `executor/quantifier_loop/dispatch.rs`, `logic_detection/transforms.rs`).
//!
//! A declared `UFDTNIRA`/`AUFDTNIRA` maps to `LogicCategory::Ufdtnira`, which
//! used to answer a bare `unknown` in BOTH dispatch tables without running any
//! theory solver — while every SPARK/Why3 VC in those divisions declares
//! `real__ref : Real` and array sorts in its prelude and asserts over neither.
//! The category now takes the `Ufdtnia` lane (`solve_dt_uf_nia`: lazy DT over
//! EUF + NIA) when the LIVE window mentions no Real and no array term, and
//! keeps the fail-closed `unknown` otherwise.
//!
//! Each fail-closed pin is built so that the WRONG lane would answer wrongly:
//! reading a live Real term as Int refutes a satisfiable window, and relaxing a
//! live array to congruence satisfies an unsatisfiable one. A pin that merely
//! checked for `unknown` on a window whose verdict the lane would get RIGHT
//! anyway would not detect the guard being dropped.

use crate::Executor;
use ay_frontend::parse;

fn execute(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    (executor, output)
}

fn verdict(output: &[String]) -> String {
    output
        .iter()
        .rev()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
}

fn category(executor: &Executor) -> Option<String> {
    executor
        .statistics()
        .get_string("solver.logic_category")
        .map(str::to_owned)
}

/// The lane itself: a declared `UFDTNIRA` window over datatypes, an
/// uninterpreted function and a genuine product, with the prelude's `Real`
/// constant DECLARED and never asserted. Before the lane this answered
/// `unknown` from `route_to_solver(Ufdtnira)` with no solver run; z3 answers
/// `unsat` (`fst p = 2`, `fst p * snd p = 6` forces `snd p = 3`).
#[test]
fn declared_ufdtnira_with_real_free_array_free_window_takes_the_dt_uf_nia_lane() {
    let input = r#"
        (set-logic UFDTNIRA)
        (declare-datatypes ((pair 0)) (((mk (fst Int) (snd Int)))))
        (declare-fun f (Int) Int)
        (declare-fun p () pair)
        (declare-fun real__ref () Real)
        (assert (= (fst p) 2))
        (assert (= (* (fst p) (snd p)) 6))
        (assert (= (f (snd p)) 1))
        (assert (not (= (snd p) 3)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    assert_eq!(
        category(&executor).as_deref(),
        Some("Ufdtnira"),
        "the pin must exercise the declared-NIRA category, not a narrowed one"
    );
    assert_eq!(verdict(&output), "unsat");
}

/// The same window declared `AUFDTNIRA` (the SPARK array-bearing token) with
/// no array term asserted: the declaration is an upper bound, the live window
/// decides the lane.
#[test]
fn declared_aufdtnira_without_a_live_array_term_takes_the_lane_too() {
    let input = r#"
        (set-logic AUFDTNIRA)
        (declare-datatypes ((pair 0)) (((mk (fst Int) (snd Int)))))
        (declare-fun f (Int) Int)
        (declare-fun p () pair)
        (declare-fun real__ref () Real)
        (declare-fun unused_map () (Array Int Int))
        (assert (= (fst p) 2))
        (assert (= (* (fst p) (snd p)) 6))
        (assert (= (f (snd p)) 1))
        (assert (not (= (snd p) 3)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    assert_eq!(category(&executor).as_deref(), Some("Ufdtnira"));
    assert_eq!(verdict(&output), "unsat");
}

/// The quantifier-loop mirror table (`solve_for_category`) must route the same
/// way: the refutation here needs the E-matched instance `f(2) = 2 * snd p`,
/// so the ground solve that decides it runs INSIDE the quantifier loop, on the
/// table that used to answer a blanket `unknown` (#5989 shape).
#[test]
fn quantified_ufdtnira_refutation_reaches_the_lane_through_the_mirror_table() {
    let input = r#"
        (set-logic UFDTNIRA)
        (declare-datatypes ((pair 0)) (((mk (fst Int) (snd Int)))))
        (declare-fun f (Int) Int)
        (declare-fun p () pair)
        (declare-fun real__ref () Real)
        (assert (forall ((x Int)) (! (= (f x) (* x (snd p))) :pattern ((f x)))))
        (assert (= (f 2) 6))
        (assert (= (fst p) (snd p)))
        (assert (not (= (fst p) 3)))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    assert_eq!(category(&executor).as_deref(), Some("Ufdtnira"));
    assert_eq!(verdict(&output), "unsat");
}

/// Fail-closed on a LIVE Real term. `2r = 1` is satisfiable over the Reals
/// (z3: `sat`) and unsatisfiable over the Integers, so a lane that read the
/// Real sort as Int would publish a wrong `unsat`. The window must keep the
/// fail-closed `unknown` (or answer `sat` through a lane that interprets
/// Reals) — never `unsat`.
///
/// The quantified `f` axiom is load-bearing: the same window without a binder
/// is narrowed to `QfNira` by the existing quantifier-free rule and would
/// never have reached `Ufdtnira`'s table at all, so a pin written ground would
/// guard nothing here (measured: `solver.logic_category "QfNira"`).
#[test]
fn live_real_term_keeps_the_fail_closed_unknown() {
    let input = r#"
        (set-logic UFDTNIRA)
        (declare-datatypes ((pair 0)) (((mk (fst Int) (snd Int)))))
        (declare-fun f (Int) Int)
        (declare-fun p () pair)
        (declare-fun r () Real)
        (assert (forall ((x Int)) (! (>= (f x) 0) :pattern ((f x)))))
        (assert (= (f (fst p)) 0))
        (assert (= (* (fst p) (snd p)) 6))
        (assert (= (* 2.0 r) 1.0))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    assert_eq!(category(&executor).as_deref(), Some("Ufdtnira"));
    assert_ne!(
        verdict(&output),
        "unsat",
        "a live Real term read as Int would refute a satisfiable window"
    );
}

/// Fail-closed on a LIVE array term. `select(store(a, i, 7), j) = 8` with
/// `i = j` is unsatisfiable under read-over-write (z3: `unsat`) — and the
/// non-syntactic index pair keeps the rewriter from folding it away, so under
/// congruence alone the window is satisfiable. A lane that relaxed the array
/// to an uninterpreted function would publish a wrong `sat`.
#[test]
fn live_array_term_keeps_the_fail_closed_unknown() {
    let input = r#"
        (set-logic AUFDTNIRA)
        (declare-datatypes ((pair 0)) (((mk (fst Int) (snd Int)))))
        (declare-fun a () (Array Int Int))
        (declare-fun p () pair)
        (declare-fun i () Int)
        (declare-fun j () Int)
        (assert (= i j))
        (assert (= (select (store a i 7) j) 8))
        (assert (= (* (fst p) (snd p)) 6))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    assert_eq!(category(&executor).as_deref(), Some("Ufdtnira"));
    assert_ne!(
        verdict(&output),
        "sat",
        "a live array relaxed to congruence would satisfy an unsatisfiable window"
    );
}
