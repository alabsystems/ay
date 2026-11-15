// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests of the finite-domain datatype lane: verdicts end to end in
//! both postures, the fragment gate's refusals, deepening at the exact cell
//! bound, and a semantic clause-validity oracle for Theorem 1.

use std::sync::Mutex;

use ay_frontend::parse;
use ntest::timeout;

use super::driver::D_OVERRIDE;
use crate::{Executor, StatValue};

/// Serializes the tests that force the cell count.
static D_LOCK: Mutex<()> = Mutex::new(());

const LIST: &str = "(declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) \
                    ((cons (hd E) (tl L)) (nil))))";

fn stat(exec: &Executor, key: &str) -> Option<String> {
    match exec.get_statistics().extra.get(key) {
        Some(StatValue::String(s)) => Some(s.clone()),
        Some(StatValue::Int(i)) => Some(i.to_string()),
        _ => None,
    }
}

/// Run `body` (declarations + assertions) with `(check-sat)` appended.
fn run(body: &str, z3_mode: bool, d: Option<usize>) -> (String, Executor) {
    let _guard = D_LOCK.lock().unwrap_or_else(|e| e.into_inner());
    D_OVERRIDE.with(|o| o.set(d));
    let commands = parse(&format!("(set-logic QF_DT)\n{body}\n(check-sat)\n")).unwrap();
    let mut exec = Executor::new();
    exec.set_competition_mode(z3_mode);
    let outputs = exec.execute_all(&commands).unwrap();
    D_OVERRIDE.with(|o| o.set(None));
    (outputs.last().cloned().unwrap_or_default(), exec)
}

fn lane(exec: &Executor) -> Option<String> {
    stat(exec, "solver.dt_fd_lane")
}

#[test]
#[timeout(60000)]
fn enum_only_problem_is_left_to_the_enum_lane() {
    let body = "(declare-datatypes ((E 0)) (((A) (B) (C))))\n\
                (declare-const x E) (declare-const y E)\n\
                (assert (distinct x y)) (assert (not (= x A)))";
    let (out, exec) = run(body, true, None);
    assert_eq!(out, "sat");
    assert_eq!(lane(&exec), None, "no list sort: the gate must decline");
}

#[test]
#[timeout(60000)]
fn enum_constraints_over_list_cells() {
    let body = format!(
        "{LIST}\n(declare-const x L) (declare-const e E)\n\
         (assert ((_ is cons) x)) (assert (= (hd x) e)) (assert (distinct e A))\n\
         (assert (not (= e B)))"
    );
    let (out, exec) = run(&body, true, None);
    assert_eq!(out, "sat");
    assert_eq!(lane(&exec).as_deref(), Some("sat"));
    let body = format!("{body}\n(assert (not (= (hd x) C)))");
    for d in [1, 2, 3] {
        let (out, exec) = run(&body, true, Some(d));
        assert_eq!(out, "unsat", "D = {d}");
        assert_eq!(lane(&exec).as_deref(), Some("unsat"), "D = {d}");
    }
}

#[test]
#[timeout(60000)]
fn recursive_list_unsat_at_every_cell_count() {
    // x = [A, B]; tl(x) has head A is false.
    let body = format!(
        "{LIST}\n(declare-const x L) (declare-const y L)\n\
         (assert (= x (cons A y))) (assert (= y (cons B nil)))\n\
         (assert (= (hd (tl x)) A))"
    );
    for d in [1, 2, 3, 5] {
        let (out, exec) = run(&body, true, Some(d));
        assert_eq!(out, "unsat", "D = {d}");
        assert_eq!(lane(&exec).as_deref(), Some("unsat"), "D = {d}");
    }
    // Default posture: the lane never publishes an unevidenced UNSAT.
    let (_, exec) = run(&body, false, None);
    assert_ne!(lane(&exec).as_deref(), Some("unsat"));
}

#[test]
#[timeout(60000)]
fn wrong_constructor_selectors_are_functions() {
    // tl(nil) and hd(nil) are arbitrary but fixed: satisfiable ...
    let body = format!(
        "{LIST}\n(declare-const x L) (declare-const y L)\n\
         (assert ((_ is nil) x)) (assert (= (tl x) (cons A x)))\n\
         (assert (= (tl (tl x)) x)) (assert (= y (tl (tl x))))\n\
         (assert (= (hd (tl y)) A)) (assert (= (hd x) C))"
    );
    for posture in [true, false] {
        let (out, exec) = run(&body, posture, None);
        assert_eq!(out, "sat");
        assert_eq!(lane(&exec).as_deref(), Some("sat"));
    }
    // ... but one value per selector: two nil arguments agree.
    let body = format!(
        "{LIST}\n(declare-const x L) (declare-const y L)\n\
         (assert ((_ is nil) x)) (assert ((_ is nil) y)) (assert ((_ is nil) (tl x)))\n\
         (assert (or (distinct (tl x) (tl y)) (distinct (hd x) (hd y))))"
    );
    for d in [1, 2] {
        let (out, exec) = run(&body, true, Some(d));
        assert_eq!(out, "unsat", "D = {d}");
        assert_eq!(lane(&exec).as_deref(), Some("unsat"));
    }
    // Without the shallow `tl(nil)`, the lane may only over-approximate (a
    // deep/deep list equality is free): it must never answer `sat`, and the
    // verdict comes from the other lanes.
    let body = format!(
        "{LIST}\n(declare-const x L) (declare-const y L)\n\
         (assert ((_ is nil) x)) (assert ((_ is nil) y))\n\
         (assert (distinct (tl x) (tl y)))"
    );
    let (out, exec) = run(&body, true, Some(1));
    assert_ne!(out, "sat");
    assert_ne!(lane(&exec).as_deref(), Some("sat"));
}

#[test]
#[timeout(60000)]
fn record_equality_is_fieldwise() {
    let rec = format!(
        "{LIST}\n(declare-datatypes ((R 0)) (((mk (lf L) (rt L) (flag Bool)))))\n\
         (declare-const r R) (declare-const s R)"
    );
    let sat = format!(
        "{rec}\n(assert (= r s)) (assert (= (lf r) (cons A nil)))\n\
         (assert (= (rt s) (cons B (lf s)))) (assert (flag r))"
    );
    let (out, exec) = run(&sat, true, None);
    assert_eq!(out, "sat");
    assert_eq!(lane(&exec).as_deref(), Some("sat"));
    let unsat = format!(
        "{rec}\n(assert (= (lf r) (lf s))) (assert (= (rt r) (rt s)))\n\
         (assert (= (flag r) (flag s))) (assert (not (= r s)))"
    );
    for d in [1, 2, 4] {
        let (out, exec) = run(&unsat, true, Some(d));
        assert_eq!(out, "unsat", "D = {d}");
        assert_eq!(lane(&exec).as_deref(), Some("unsat"));
    }
}

#[test]
#[timeout(60000)]
fn satisfiable_at_exactly_the_cell_bound() {
    // x has exactly three cells (forced through cons testers: a selector on
    // nil is an arbitrary value, so testers on selector chains alone do not
    // force length).
    let body = format!(
        "{LIST}\n(declare-const x L)\n\
         (assert ((_ is cons) x)) (assert ((_ is cons) (tl x)))\n\
         (assert ((_ is cons) (tl (tl x)))) (assert ((_ is nil) (tl (tl (tl x)))))\n\
         (assert (= (hd (tl (tl x))) B))"
    );
    let (out, exec) = run(&body, true, Some(3));
    assert_eq!(out, "sat");
    assert_eq!(lane(&exec).as_deref(), Some("sat"));
    assert_eq!(stat(&exec, "dt_fd.d").as_deref(), Some("3"));
    assert_eq!(stat(&exec, "dt_fd.rounds").as_deref(), Some("1"));
    // One cell more than the bound: the deep model is spurious, D doubles.
    let body = format!(
        "{LIST}\n(declare-const x L)\n\
         (assert ((_ is cons) x)) (assert ((_ is cons) (tl x)))\n\
         (assert ((_ is cons) (tl (tl x)))) (assert ((_ is cons) (tl (tl (tl x)))))\n\
         (assert ((_ is nil) (tl (tl (tl (tl x))))))"
    );
    let (out, exec) = run(&body, true, Some(3));
    assert_eq!(out, "sat");
    assert_eq!(lane(&exec).as_deref(), Some("sat"));
    assert_eq!(stat(&exec, "dt_fd.d").as_deref(), Some("6"));
    assert_eq!(stat(&exec, "dt_fd.rounds").as_deref(), Some("2"));
}

#[test]
#[timeout(60000)]
fn the_gate_refuses_inputs_outside_the_fragment() {
    let quantified =
        format!("{LIST}\n(declare-const x L) (assert (forall ((y L)) (distinct x (cons A y))))");
    let refused: [&str; 8] = [
        // Int cell field.
        "(declare-datatypes ((L 0)) (((cons (hd Int) (tl L)) (nil))))\n\
         (declare-const x L) (assert ((_ is cons) x))",
        // Declared function with arguments.
        "(declare-datatypes ((L 0)) (((cons (tl L)) (nil))))\n\
         (declare-fun f (L) L) (declare-const x L) (assert (= (f x) x))",
        // Mutual recursion.
        "(declare-datatypes ((T 0) (F 0)) (((node (kids F)) (leaf)) ((fcons (h T) (t F)) (fnil))))\n\
         (declare-const x T) (assert ((_ is node) x))",
        // Two nils (critique F3).
        "(declare-datatypes ((L 0)) (((cons (tl L)) (nil1) (nil2))))\n\
         (declare-const x L) (assert (not ((_ is cons) x)))",
        // Nil with a field (critique F4).
        "(declare-datatypes ((C 0) (L 0)) (((R) (G)) ((cons (tl L)) (nil (tag C)))))\n\
         (declare-const x L) (assert ((_ is cons) x))",
        // Cell field of a sum sort with fields (critique F1/F2).
        "(declare-datatypes ((G 0) (F 0) (L 0)) (((G1) (G2)) ((F1 (g G)) (F2)) \
         ((cons (hd F) (tl L)) (nil))))\n\
         (declare-const x L) (assert ((_ is cons) x)) (assert (= (hd x) F2))",
        // Tree shape.
        "(declare-datatypes ((T 0)) (((node (l T) (r T)) (leaf))))\n\
         (declare-const x T) (assert ((_ is node) x))",
        // Quantifier.
        &quantified,
    ];
    for body in refused {
        let commands = parse(&format!("(set-logic ALL)\n{body}\n")).unwrap();
        let mut exec = Executor::new();
        exec.execute_all(&commands).unwrap();
        assert!(exec.dt_fd_scan().is_err(), "must refuse:\n{body}");
    }
}

#[test]
#[timeout(60000)]
fn assumption_solves_run_the_lane_on_the_merged_window() {
    let body = format!(
        "{LIST}\n(declare-const x L) (declare-const p Bool)\n\
         (assert (=> p ((_ is cons) x)))"
    );
    let commands = parse(&format!(
        "(set-logic QF_DT)\n{body}\n(check-sat-assuming (p))\n"
    ))
    .unwrap();
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs.last().map(String::as_str), Some("sat"));
    // `check-sat-assuming A` is `check-sat (B ∧ A)`: the lane decides the
    // merged window before the direct DT assumption engine (#dt-fd-session).
    assert_eq!(lane(&exec).as_deref(), Some("sat"));
}

#[test]
#[timeout(60000)]
fn rejected_publication_leaves_no_trace_for_the_fallback_lanes() {
    // Fuzz reproducer (rec mode, seed 4, case 1277; z3: sat). The lane's own
    // evaluator accepts its model but the validation pipeline rejects it on
    // the flattened record field `r2!lf`. Before the attempt ran inside the
    // speculative bracket, the minted ground terms stayed in the store,
    // changed the lazy lane's atom set, and the query ended `unknown`; the
    // baseline answers `sat` through the lazy lane.
    let body = "(declare-datatypes ((G 0) (E 0) (F 0) (L 0) (R 0)) \
                (((G1) (G2) (G3)) ((E1) (E2)) ((F1) (F2) (F3)) \
                ((cons (hd F) (tl L)) (nil)) ((mk (lf L) (ff F) (bf Bool)))))\n\
                (declare-const x1 L) (declare-const x2 L) (declare-const x3 L)\n\
                (declare-const f1 F) (declare-const f2 F) (declare-const r1 R)\n\
                (declare-const r2 R) (declare-const b1 Bool) (declare-const b2 Bool)\n\
                (assert (ite (= (cons (hd nil) (tl x3)) (tl (lf r2))) \
                (not (ite b2 ((_ is F1) f1) b2)) (ite (= nil (ite ((_ is F1) f2) x1 x1)) \
                (and (= r1 r1) (distinct x2 x3 x3)) ((_ is F2) (ff r1)))))\n\
                (assert (=> (= (tl x1) (ite (ite (and ((_ is cons) x2) (distinct x2 nil x1)) \
                (= (cons f2 x1) (cons (hd x2) nil)) (ite (and ((_ is cons) nil) ((_ is nil) x1)) \
                (= (ite (= x2 x2) x3 nil) (cons (hd nil) x1)) (= x1 x1))) x3 x3)) \
                (= (mk x3 f1 (ite (and ((_ is cons) x3) ((_ is nil) x3)) \
                (= (cons F1 x2) (cons (hd x3) nil)) ((_ is cons) x1))) r1)))\n\
                (assert (bf (mk x1 F2 (bf (mk nil F2 (= r2 r2))))))\n\
                (assert (or (=> (= x2 x1) (= x3 (cons F2 nil))) \
                (=> (not ((_ is F2) f1)) (distinct nil nil (tl x3)))))\n\
                (assert ((_ is cons) (cons f2 (cons F3 x3))))\n\
                (assert (= (bf r1) (= (lf r1) (tl x1))))";
    let (out, exec) = run(body, true, None);
    assert!(stat(&exec, "dt_fd.rounds").is_some(), "the lane must run");
    assert_eq!(out, "sat");
}

#[path = "tests_oracle.rs"]
mod oracle;
