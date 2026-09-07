// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Routing pins for `#qf-aufnia-array-drop` (`executor/logic_detect.rs`).
//!
//! A declared `QF_AUFNIA` maps to the array-LESS `QfUfnia` category
//! (`logic_detection/parse.rs`, the `"QF_UFNIA" | "QF_AUFNIA"` arm), which
//! dispatches to `solve_uf_nia` — EUF + NIA and nothing else. Arrays then
//! survive only as uninterpreted functions under congruence, so a candidate
//! model that needs read-over-write is refused by the strict model-validation
//! oracle and the query answers `unknown`.
//!
//! The re-derivation block gives the window back to the array-aware AUFLIA
//! route (`TheoryCombiner::auf_lia` = EUF + `ArraySolver` + `LiaSolver`) — but
//! ONLY where that lane covers the whole fragment. Each guard below has its own
//! pin: nonlinear arithmetic and symbolic `div`/`mod` divisors are outside
//! AUFLIA's coverage and MUST stay on the fail-closed NIA lane, and the
//! content-detection path must not move at all.

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

fn category(input: &str) -> Option<String> {
    execute(input)
        .0
        .statistics()
        .get_string("solver.logic_category")
        .map(str::to_owned)
}

/// The rank-6 routing hole itself: arrays + UF + LINEAR integer arithmetic
/// under a declared `QF_AUFNIA` must reach the array-aware AUFLIA lane, not the
/// array-less EUF+NIA lane. (`(* x 4294967296)` is a literal multiply, which is
/// linear — exactly the shape of all 17 SMT-LIB QF_AUFNIA benchmarks, whose
/// only products are `(* v 4294967296)`.) The read is at a DIFFERENT index from
/// the store so the rewriter cannot fold the array away: the window really does
/// need the array theory.
#[test]
fn declared_qf_aufnia_with_linear_arithmetic_keeps_the_array_theory() {
    let input = r#"
        (set-logic QF_AUFNIA)
        (declare-fun a () (Array Int Int))
        (declare-fun f (Int) Int)
        (declare-fun i () Int)
        (declare-fun j () Int)
        (declare-fun x () Int)
        (assert (= (select (store a i 7) j) x))
        (assert (= (f x) (* x 4294967296)))
        (assert (> i 0))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    // z3 4.16.0 and 5.1.0 both answer sat on this window.
    assert_eq!(output, vec!["sat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfAuflia")
    );
}

/// The read-over-write refutation the array-less lane could only reach through
/// its `try_ufnia_store_flat_row_refutation` rescue is decided on the array lane
/// — and the verdict must not move.
#[test]
fn declared_qf_aufnia_nested_row_stays_unsat_on_the_array_lane() {
    let input = r#"
        (set-logic QF_AUFNIA)
        (declare-fun m0 () (Array Int (Array Int Int)))
        (declare-fun m1 () (Array Int (Array Int Int)))
        (declare-fun b () Int)
        (declare-fun o () Int)
        (declare-fun x () Int)
        (assert (= m1 (store m0 b (store (select m0 b) o 8448))))
        (assert (<= x (select (select m1 b) o)))
        (assert (>= x 8640))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    assert_eq!(output, vec!["unsat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfAuflia")
    );
}

/// FAIL-CLOSED RESIDUE. AY has no arrays+UF+NIA lane (`TheoryCombiner` carries
/// `lia`/`lra` only; `UfNiaSolver` owns no `ArraySolver`), so a window with a
/// GENUINE nonlinear product must NOT be handed to the linear array lane, which
/// would abstract the product — the wrong-SAT mechanism `with_nonlinear`
/// (#6086) exists to prevent. It stays on the array-less NIA lane.
#[test]
fn declared_qf_aufnia_with_genuine_nonlinearity_stays_on_the_nia_lane() {
    let input = r#"
        (set-logic QF_AUFNIA)
        (declare-fun a () (Array Int Int))
        (assert (= (select a 1) 0))
        (assert (= (* (select a 1) (select a 4)) 1))
        (check-sat)
    "#;
    assert_eq!(category(input).as_deref(), Some("QfUfnia"));
}

/// FAIL-CLOSED RESIDUE. A SYMBOLIC `div`/`mod` divisor is owned by the NIA lane
/// (`eliminate_int_mod_div` with the guarded Euclidean axioms); `solve_auf_lia`
/// refuses an array window with an unsupported divisor outright, so re-routing
/// this shape would trade a search for an instant `unsupported arithmetic`.
#[test]
fn declared_qf_aufnia_with_symbolic_divisor_stays_on_the_nia_lane() {
    let input = r#"
        (set-logic QF_AUFNIA)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (assert (= x (div 7 (select a 0))))
        (assert (= x 99))
        (check-sat)
    "#;
    assert_eq!(category(input).as_deref(), Some("QfUfnia"));
}

/// A CONSTANT divisor is inside AUFLIA's coverage (`eliminate_int_mod_div_by_constant`
/// runs in its preprocessing), so the array window still moves.
#[test]
fn declared_qf_aufnia_with_constant_divisor_keeps_the_array_theory() {
    let input = r#"
        (set-logic QF_AUFNIA)
        (declare-fun a () (Array Int Int))
        (declare-fun i () Int)
        (assert (= (select a i) (mod i 4294967296)))
        (assert (> i 0))
        (check-sat)
    "#;
    assert_eq!(category(input).as_deref(), Some("QfAuflia"));
}

/// An array-FREE declared `QF_AUFNIA` has nothing to recover, so the guard must
/// not fire: the EUF+NIA lane keeps deciding the UF-congruence fragment (#5984).
#[test]
fn declared_qf_aufnia_without_arrays_is_unchanged() {
    let input = r#"
        (set-logic QF_AUFNIA)
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= x y))
        (assert (= (f x) 1))
        (assert (= (f y) 2))
        (check-sat)
    "#;
    let (executor, output) = execute(input);
    assert_eq!(output, vec!["unsat"]);
    assert_eq!(
        executor.statistics().get_string("solver.logic_category"),
        Some("QfUfnia")
    );
}

/// The CONTENT-DETECTION path must not move. `infer_logic` answers
/// `QF_AUFNIA`/`QF_UFNIA` only under a nonlinear flag, which the guard excludes,
/// so an `(set-logic ALL)` window with arrays and a genuine product keeps its
/// array-less category exactly as before.
#[test]
fn content_detected_nonlinear_array_window_is_unchanged() {
    let input = r#"
        (set-logic ALL)
        (declare-fun a () (Array Int Int))
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (select a 1) x))
        (assert (= (* x y) 6))
        (check-sat)
    "#;
    assert_eq!(category(input).as_deref(), Some("QfUfnia"));
}
