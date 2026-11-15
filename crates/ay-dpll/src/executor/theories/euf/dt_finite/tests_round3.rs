// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the round-3 verification findings (E13 verify-2 hunt
//! and audit, v2verify): one test per finding, each a minimized reproducer
//! with z3's answers as the expectations.

use ay_frontend::parse;
use ntest::timeout;

use crate::{Executor, StatValue};

fn stat(exec: &Executor, key: &str) -> Option<String> {
    match exec.get_statistics().extra.get(key) {
        Some(StatValue::String(s)) => Some(s.clone()),
        Some(StatValue::Int(i)) => Some(i.to_string()),
        _ => None,
    }
}

/// Run a whole script; every command output, in order.
fn run(src: &str, z3_mode: bool) -> (Vec<String>, Executor) {
    let commands = parse(src).unwrap();
    let mut exec = Executor::new();
    exec.set_competition_mode(z3_mode);
    let outputs = exec.execute_all(&commands).unwrap();
    (outputs, exec)
}

fn verdicts(outputs: &[String]) -> Vec<&str> {
    outputs
        .iter()
        .map(String::as_str)
        .filter(|o| matches!(*o, "sat" | "unsat" | "unknown"))
        .collect()
}

fn expect(src: &str, z3_modes: &[bool], expected: &[&str]) {
    for &z3_mode in z3_modes {
        let (outputs, _) = run(src, z3_mode);
        assert_eq!(verdicts(&outputs), expected, "z3_mode = {z3_mode}\n{src}");
    }
}

/// Lost SAT, single check (#dt-live-scan): the eager axiom scans took every
/// term older than the command for session history, so an authored subterm
/// the term builder dropped (`(or true ..)`, `(=> c true false)`) lost its
/// domain-closure and wrong-constructor axioms, the model gave it a fresh
/// enum element and the cardinality gate (or the independent gate) refused
/// it. verify-2 hunt `lost_dead_subterm_*`, `lost_boolcell_*`,
/// `lost_reccell_*`, `lost_mutual_wrongctor_gate_default`.
#[test]
#[timeout(120000)]
fn authored_subterms_are_never_session_history() {
    let dead_or = "(set-logic QF_DT)\n\
        (declare-datatypes ((E1 0)) (((c2) (c3))))\n\
        (declare-datatypes ((S4 0)) (((s5 (sa6 E1)) (s7) (s8 (sc9 Bool)))))\n\
        (declare-fun k10 () S4) (declare-const k11 S4) (declare-fun k12 () S4)\n\
        (assert (ite (ite (or true ((_ is s5) (s5 c2)) (distinct c3 (sa6 k10))) false true) true \
        (or false ((_ is s8) (ite (distinct (sa6 k12) c2) k12 k11)) (and (sc9 k12) ((_ is s7) k10)))))\n\
        (check-sat)\n";
    expect(dead_or, &[true], &["sat"]);
    let bool_cell = "(set-logic QF_DT)\n\
        (declare-datatypes ((E1 0)) (((c2) (c3) (c4))))\n\
        (declare-datatypes ((X33 0)) (((xc35 (xb36 Bool) (xt34 X33)) (xn37))))\n\
        (declare-const k44 X33) (declare-const k45 X33)\n\
        (assert (=> (xb36 (ite (not (xb36 (xt34 k45))) k45 (xc35 true k44))) true false))\n\
        (check-sat)\n";
    expect(bool_cell, &[true, false], &["sat"]);
    let mutual = "(set-logic QF_DT)\n\
        (declare-datatype E1 ((c2) (c3) (c4)))\n\
        (declare-datatypes ((L7 0)) (((nil13) (cons12 (hd9 E1) (tl11 L7)))))\n\
        (declare-datatypes ((Tr14 0) (Fo15 0)) (((tn16 (tv17 E1) (kids18 Fo15))) \
        ((fnil19) (fcons20 (fh21 Tr14) (ft22 Fo15)))))\n\
        (declare-fun k31 () L7) (declare-fun k32 () L7) (declare-const k34 Tr14)\n\
        (declare-fun k35 () Tr14) (declare-fun k36 () Fo15)\n\
        (assert (distinct (fh21 k36) k34 (tn16 c2 fnil19)))\n\
        (assert (= nil13 (ite (= k35 k35 k34) k31 k31) k31 k32))\n\
        (check-sat)\n";
    expect(mutual, &[true, false], &["sat"]);
}

/// Lost SAT in a later check (#dt-live-scan, v2verify `incr_default_loss`,
/// `incr_loss_a`): only terms an EARLIER decision minted are history.
#[test]
#[timeout(180000)]
fn incremental_checks_keep_their_authored_terms() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((K0) (K1) (K2))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-datatypes ((R 0)) (((mk (rl L) (re E) (rb Bool)))))\n\
        (declare-fun e1 () E) (declare-fun e2 () E) (declare-fun e3 () E)\n\
        (declare-fun x1 () L) (declare-fun x2 () L) (declare-fun x3 () L)\n\
        (declare-fun q1 () R) (declare-fun q2 () R) (declare-fun b1 () Bool) (declare-fun b2 () Bool)\n\
        (assert (ite (not (distinct x2 (rl q2) (tl nil))) (ite (not b1) (= e1 e1) \
        (= q2 (mk (tl nil) K1 (not ((_ is nil) x2))))) (xor b1 (not (= nil x2)))))\n\
        (assert (ite b1 (distinct e2 e2 e1 (re (mk (cons (re q2) x3) (hd nil) (rb q1)))) \
        (not ((_ is cons) x1))))\n\
        (push 1) (assert b2) (check-sat)\n\
        (push 1) (assert (not (distinct (cons (re q2) nil) (rl q1) nil))) (check-sat)\n";
    expect(src, &[true, false], &["sat", "sat"]);
    // The second check needs the axiom chains the first one's lanes left
    // (main: `sat`, `sat` in the default posture); the finite-domain lane
    // decided nothing here, so nothing is history.
    let other_lanes_first = "\
        (set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((K0) (K1) (K2) (K3))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-datatypes ((R 0)) (((mk (rl L) (re E) (rb Bool)))))\n\
        (declare-fun e1 () E)\n\
        (declare-fun e2 () E)\n\
        (declare-fun e3 () E)\n\
        (declare-fun x1 () L)\n\
        (declare-fun x2 () L)\n\
        (declare-fun x3 () L)\n\
        (declare-fun q1 () R)\n\
        (declare-fun q2 () R)\n\
        (declare-fun b1 () Bool)\n\
        (declare-fun b2 () Bool)\n\
        (assert (= q1 (ite (= (cons (hd (cons e3 x3)) (cons (hd nil) (cons e3 nil))) (rl q2)) q1 q1)))\n\
        (assert (and (ite (not (= nil x2)) (= q2 (mk x2 (hd x1) (= e3 K3))) (not ((_ is nil) (tl (cons (re q1) nil))))) (=> (= (re (mk nil e3 (rb q2))) e2) (not (distinct (hd nil) (hd (rl q1)) (hd x3) (hd x1)))) (and b2 (= (rl q1) (cons (re (mk (tl (rl (mk (rl (mk nil e2 b2)) (hd (cons (hd nil) (cons K0 (tl (tl (cons K1 nil)))))) ((_ is cons) (tl (cons e1 x1)))))) e1 (distinct (rl q2) nil x2))) (rl (mk (cons e1 x2) e3 (= (hd nil) e3))))) ((_ is cons) (cons (re q1) (tl (rl (mk nil (re q2) (rb (mk nil K0 (not ((_ is cons) (tl (rl (mk x3 e3 (not (= (cons (hd x2) (rl (mk x2 K2 (not (= q1 q2))))) (cons e2 x1))))))))))))))))))\n\
        (push 1)\n\
        (assert (=> (= q2 (mk x3 K3 (= (mk x1 e1 (= (re q2) (re q1))) (mk (tl (cons K3 x2)) e2 (= (tl (tl x2)) x3))))) (rb (ite (or (distinct x2 (rl (mk x3 (re q1) (= (tl nil) x3))) nil) (not ((_ is cons) nil))) q1 q2))))\n\
        (assert (not ((_ is cons) (tl x1))))\n\
        (assert (= (xor b2 (distinct e2 (re q1))) ((_ is cons) nil)))\n\
        (check-sat)\n\
        (pop 1)\n\
        (push 1)\n\
        (assert (not (= (re (mk x3 K2 (distinct x1 nil (tl (cons (re q1) (tl nil)))))) (hd x2))))\n\
        (assert (not ((_ is cons) (rl (ite ((_ is nil) x3) (mk x1 (hd x2) (not (= x2 nil))) (mk (tl (rl q1)) K1 ((_ is cons) (cons K2 (tl nil)))))))))\n\
        (assert (or (= (cons (hd x2) (cons K0 (tl x2))) (tl (cons (re q1) (rl q2)))) (= e1 (re (mk (tl (tl x1)) e2 (= q2 (mk x1 (re q2) (distinct x3 (tl (cons e3 x1)) (tl x1)))))))))\n\
        (check-sat)\n";
    expect(other_lanes_first, &[false], &["sat", "sat"]);
    let (outputs, _) = run(other_lanes_first, true);
    assert!(!verdicts(&outputs).contains(&"unsat"));
}

/// After a lane `sat`, `(get-value)` of Boolean terms the query does not
/// contain (testers, selector equalities) answers from the lane's model
/// instead of erroring (#dt-fd-ground-model, verify-2 hunt
/// `gv_error_bool_term_lane`).
#[test]
#[timeout(60000)]
fn get_value_reads_the_whole_lane_model() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((A) (B))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const y L)\n\
        (assert ((_ is cons) x)) (assert (= (hd x) A)) (assert (= y (cons B x)))\n\
        (check-sat)\n\
        (get-value (((_ is nil) x) (= (hd x) A) ((_ is nil) (tl (tl y))) (= x y) \
        (hd (tl y)) (= (tl y) x)))\n";
    for z3_mode in [true, false] {
        let (outputs, exec) = run(src, z3_mode);
        assert_eq!(verdicts(&outputs), ["sat"], "z3_mode = {z3_mode}");
        assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("sat"));
        let values = outputs.last().unwrap();
        assert!(!values.contains("error"), "z3_mode = {z3_mode}: {values}");
        for pair in [
            "(((_ is nil) x) false)",
            "((= (hd x) A) true)",
            "((= x y) false)",
            "((hd (tl y)) A)",
            "((= (tl y) x) true)",
        ] {
            assert!(
                values.contains(pair),
                "z3_mode = {z3_mode}: {pair} in {values}"
            );
        }
    }
}

/// A constant the query never mentions has no lane value; terms over it
/// read the value the other printers give it, and constructor terms of sorts
/// the query never uses are values too (verify-2 hunt gv sweep:
/// `(f21 (mk23 (= (hd16 k37) k33)))`, `(f30 (mk44 c26 (distinct c6 c5) ..))`
/// errored).
#[test]
#[timeout(60000)]
fn get_value_over_constants_the_query_never_mentions() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((A) (B))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-datatypes ((R 0)) (((mk (f Bool) (g L)))))\n\
        (declare-datatypes ((F 0)) (((F1) (F2) (F3))))\n\
        (declare-datatypes ((S 0)) (((ms (sf F) (sb Bool)))))\n\
        (declare-const x L) (declare-const k L) (declare-const r R) (declare-const b Bool)\n\
        (declare-const s S)\n\
        (assert ((_ is cons) x)) (check-sat)\n\
        (get-value (k r b (f (mk (= (hd k) A) x)) (hd k) (f r) (= (g r) k) (distinct F1 F2) \
        (sb (ms F3 (= (sf s) F1))) ((_ is F2) (sf (ms F2 b)))))\n";
    for z3_mode in [true, false] {
        let (outputs, exec) = run(src, z3_mode);
        assert_eq!(verdicts(&outputs), ["sat"], "z3_mode = {z3_mode}");
        assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("sat"));
        let values = outputs.last().unwrap();
        assert!(!values.contains("error"), "z3_mode = {z3_mode}: {values}");
    }
}

/// `(get-value)` and the printed selector tables describe ONE model:
/// selectors are functions of their argument's value, also on the wrong
/// constructor (#dt-fd-ground-model, verify-2 hunt `gv_congruence_alias_e13`,
/// `gv_table_vs_getvalue_both`).
#[test]
#[timeout(60000)]
fn get_value_is_congruent_on_the_wrong_constructor() {
    let alias = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((A) (B) (C))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const y L)\n\
        (assert ((_ is nil) (ite (distinct x (tl y)) nil nil))) (assert (= x y))\n\
        (check-sat) (get-value ((tl x) (tl y) (tl nil) (hd x) (hd y)))\n";
    let table = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((A) (B))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L)\n\
        (assert ((_ is nil) x)) (assert ((_ is nil) (ite (= nil (tl x)) x x)))\n\
        (check-sat) (get-model) (get-value ((tl x) (tl nil)))\n";
    for z3_mode in [true, false] {
        for src in [alias, table] {
            let (outputs, _) = run(src, z3_mode);
            assert_eq!(verdicts(&outputs), ["sat"], "z3_mode = {z3_mode}");
            let values = outputs.last().unwrap();
            let value_of = |key: &str| -> String {
                let at = values
                    .find(&format!("({key} "))
                    .unwrap_or_else(|| panic!("{key} in {values}"));
                let rest = &values[at + key.len() + 2..];
                let mut depth = 0i32;
                let end = rest
                    .char_indices()
                    .find(|&(_, c)| {
                        depth += i32::from(c == '(') - i32::from(c == ')');
                        depth < 0
                    })
                    .map_or(rest.len(), |(i, _)| i);
                rest[..end].to_string()
            };
            assert_eq!(value_of("(tl x)"), value_of("(tl nil)"), "{values}");
            if src == alias {
                assert_eq!(value_of("(tl x)"), value_of("(tl y)"), "{values}");
                assert_eq!(value_of("(hd x)"), value_of("(hd y)"), "{values}");
            } else {
                // The printed table's nil arm is that same value.
                let model = &outputs[1];
                let tl_nil = value_of("(tl nil)");
                assert!(
                    model.contains(&format!("(ite (= @p0 nil) {tl_nil} "))
                        || !model.contains("(ite (= @p0 nil)"),
                    "{model}\n{values}"
                );
            }
        }
    }
}

/// Incompleteness (verify-2 audit `s02`): two `rest` applications to
/// arguments that are both nil are equal (functionality), which the window
/// alone cannot show when `rest(nil)` may be deep. The lane now refutes it.
#[test]
#[timeout(60000)]
fn rest_of_two_nils_is_one_value() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const y L) (declare-const z L)\n\
        (assert (or (= z x) (= z y))) (assert ((_ is nil) x)) (assert ((_ is nil) y))\n\
        (assert (not (= (tl x) (tl y)))) (check-sat)\n";
    let (outputs, exec) = run(src, true);
    assert_eq!(verdicts(&outputs), ["unsat"]);
    assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("unsat"));
}
