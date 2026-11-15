// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the round-6 verification findings
//! (`dt-fd/r6/hunt/repro`), each a minimized reproducer with z3's answers as
//! the expectations.

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

/// Run a whole script; every output line, in order.
fn outputs(src: &str, z3_mode: bool) -> (Vec<String>, Executor) {
    let commands = parse(src).unwrap();
    let mut exec = Executor::new();
    exec.set_competition_mode(z3_mode);
    let out = exec.execute_all(&commands).unwrap();
    (out, exec)
}

/// Every check answer of a whole script, in order.
fn verdicts(src: &str, z3_mode: bool) -> Vec<String> {
    outputs(src, z3_mode)
        .0
        .into_iter()
        .filter(|o| matches!(o.as_str(), "sat" | "unsat" | "unknown"))
        .collect()
}

fn both_postures(src: &str, expected: &[&str]) {
    for z3_mode in [true, false] {
        assert_eq!(
            verdicts(src, z3_mode),
            expected,
            "z3_mode = {z3_mode}\n{src}"
        );
    }
}

/// Lost verdict (#dt-fd-session, `e13only_hang_burn_budget_pushpop`): the
/// lane decided the first check and declined every later one because the
/// session had turned incremental, so the eager incremental route met the
/// next query cold and ran until the budget was gone (forever without one).
#[test]
#[timeout(60000)]
fn later_checks_of_a_push_pop_session_stay_decided() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E1 0)) (((c2) (c3) (c4) (c5) (c6) (c7) (c8) (c9) (c10))))\n\
        (declare-datatypes ((E16 0)) (((c17) (c18) (c19))))\n\
        (declare-datatypes ((E21 0)) (((c22))))\n\
        (declare-datatypes ((L25 0)) (((cons28 (hd26 E1) (tl27 L25)) (nil29))))\n\
        (declare-datatype R31 ((mk32 (f20 E16) (f23 E21) (f24 E16) (f30 L25))))\n\
        (declare-const k41 L25) (declare-fun k42 () L25) (declare-const k43 R31)\n\
        (assert (distinct nil29 (ite (= k42 (f30 k43)) k41 k42)))\n\
        (check-sat) (push 1) (pop 1) (check-sat) (check-sat)\n";
    both_postures(src, &["sat", "sat", "sat"]);
}

/// Lost verdict (#dt-fd-session, `e13only_hang_burn_budget_csa`): a
/// `check-sat-assuming` after a lane-decided check ran the direct DT
/// assumption engine first, which spent the whole budget.
#[test]
#[timeout(60000)]
fn assumption_check_after_a_lane_decided_check_stays_decided() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatype E1 ((c2) (c3) (c4)))\n\
        (declare-datatypes ((E5 0)) (((c6) (c7) (c8))))\n\
        (declare-datatypes ((E9 0)) (((c10) (c11) (c12))))\n\
        (declare-datatypes ((L13 0)) (((nil17) (cons16 (tl15 L13) (hd14 E9)))))\n\
        (declare-datatypes ((L18 0)) (((nil23) (cons22 (hd19 E5) (hd20 E1) (tl21 L18)))))\n\
        (declare-datatype R25 ((mk26 (f24 L18))))\n\
        (declare-fun k27 () E1) (declare-fun k28 () E1) (declare-fun k29 () L13)\n\
        (declare-fun k30 () L13) (declare-const k31 L13) (declare-const k32 L18)\n\
        (declare-fun k33 () L18) (declare-fun k34 () L18) (declare-fun k35 () R25)\n\
        (declare-fun k36 () R25) (declare-fun b38 () Bool) (declare-const b39 Bool)\n\
        (assert (= false ((_ is cons22) k32)))\n\
        (assert ((_ is cons22) (tl21 k34)))\n\
        (assert (= c8 (ite (= nil23 (f24 k36)) c8 c7)))\n\
        (assert (or (= k33 nil23) (distinct k29 nil17 (tl15 nil17) (cons16 nil17 c12))))\n\
        (check-sat)\n\
        (push 1)\n\
        (assert (distinct k33 nil23 (ite b38 (f24 k35) nil23) (cons22 (hd19 k33) c3 k33) \
        (cons22 (hd19 k32) k27 (cons22 c7 (hd20 k33) \
        (ite (distinct (hd19 k32) (hd19 k34)) nil23 nil23)))))\n\
        (assert (not (= k31 k29)))\n\
        (check-sat-assuming ((not b39)))\n";
    both_postures(src, &["sat", "sat"]);
}

/// Lost verdict (`e13only_lost_z3mode_csa_after_lane`): the last
/// `check-sat-assuming` reached main's DT model builder, whose model the
/// soundness gate refused (`(not (= k20 (tl16 k19)))`).
#[test]
#[timeout(60000)]
fn assumption_checks_around_a_lane_decided_check_stay_decided() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E1 0)) (((c2) (c3) (c4) (c5) (c6) (c7) (c8) (c9) (c10) \
        (c11) (c12) (c13))))\n\
        (declare-datatypes ((L14 0)) (((nil18) (cons17 (hd15 E1) (tl16 L14)))))\n\
        (declare-fun k19 () L14) (declare-fun k20 () L14) (declare-const k21 L14)\n\
        (declare-fun b24 () Bool) (declare-const b25 Bool) (declare-const b26 Bool)\n\
        (assert (= (hd15 (tl16 k21)) c3))\n\
        (assert (not (= k20 (tl16 k19))))\n\
        (check-sat-assuming (b26))\n\
        (check-sat)\n\
        (check-sat-assuming ((not b24) (not b25)))\n";
    both_postures(src, &["sat", "sat", "sat"]);
}

/// The lane's UNSAT under assumptions (published only in `--z3-mode`)
/// reports every assumption as the core, which `get-unsat-assumptions`
/// prints; the default posture leaves the refutation to the other lanes.
#[test]
#[timeout(60000)]
fn lane_unsat_under_assumptions_reports_every_assumption() {
    let src = "(set-logic QF_DT)\n\
        (set-option :produce-unsat-assumptions true)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const p Bool) (declare-const q Bool)\n\
        (assert (=> p ((_ is cons) x)))\n\
        (assert (=> q (= x nil)))\n\
        (check-sat-assuming (p q))\n\
        (get-unsat-assumptions)\n\
        (check-sat-assuming (p))\n";
    for z3_mode in [true, false] {
        let (out, _) = outputs(src, z3_mode);
        let shown: Vec<&str> = out.iter().map(String::as_str).collect();
        assert_eq!(
            shown.first(),
            Some(&"unsat"),
            "z3_mode = {z3_mode}: {shown:?}"
        );
        assert_eq!(shown.last(), Some(&"sat"), "z3_mode = {z3_mode}: {shown:?}");
        let core = shown.get(1).copied().unwrap_or_default();
        assert!(core.contains('p') && core.contains('q'), "core {core}");
    }
    let (_, exec) = outputs(src, true);
    assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("sat"));
}

/// The value printed for `term` in a `(get-value)` answer.
fn value_of<'a>(answer: &'a str, term: &str) -> &'a str {
    let key = format!("({term} ");
    let start = answer.find(&key).map(|i| i + key.len()).expect(term);
    let mut depth = 0i32;
    for (i, c) in answer[start..].char_indices() {
        match c {
            '(' => depth += 1,
            ')' if depth == 0 => return &answer[start..start + i],
            ')' => depth -= 1,
            _ => {}
        }
    }
    panic!("unterminated value of {term} in {answer}")
}

/// `get-value` after a lane `sat` of every check answer's script, the lane
/// having decided it.
fn lane_get_value(src: &str) -> Vec<String> {
    let mut answers = Vec::new();
    for z3_mode in [true, false] {
        let (out, exec) = outputs(src, z3_mode);
        assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}");
        assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("sat"));
        let answer = out[1..].join(" ");
        assert!(!answer.contains("error"), "z3_mode = {z3_mode}: {answer}");
        answers.push(answer);
    }
    answers
}

/// Missing value (#dt-fd-foreign-get-value, `e13only_gv_foreign_eq_after_lane_sat`):
/// an equality over a record sort with an Int field, which the lane never
/// sees, had no value after a lane `sat`.
#[test]
#[timeout(60000)]
fn get_value_compares_records_with_int_fields_after_a_lane_sat() {
    let src = "(set-logic ALL)\n\
        (declare-datatype E1 ((c2) (c3) (c4)))\n\
        (declare-datatype L9 ((nil13) (cons12 (hd10 E1) (tl11 L9))))\n\
        (declare-datatypes ((RI 0)) (((mki (fi Int) (fe E1)))))\n\
        (declare-fun k20 () L9) (declare-const k29 RI) (declare-const k30 RI)\n\
        (assert ((_ is cons12) k20))\n\
        (check-sat)\n\
        (get-value (k20 k29 k30 (= k29 k30) (= (fi k29) (fi k30))))\n";
    for answer in lane_get_value(src) {
        let same = value_of(&answer, "k29") == value_of(&answer, "k30");
        assert_eq!(
            value_of(&answer, "(= k29 k30)"),
            same.to_string(),
            "{answer}"
        );
        let fields = value_of(&answer, "(= (fi k29) (fi k30))");
        assert!(!same || fields == "true", "{answer}");
    }
}

/// Missing value (`e13only_gv_mixed_arith_after_lane_sat`): a lane term
/// compared with an arithmetic `ite`.
#[test]
#[timeout(60000)]
fn get_value_mixes_lane_terms_and_arithmetic_after_a_lane_sat() {
    let src = "(set-logic ALL)\n\
        (declare-datatypes ((E 0)) (((A) (B) (C))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const n Int)\n\
        (assert ((_ is cons) x))\n\
        (check-sat)\n\
        (get-value (x n (hd x) (> n 0) (ite (> n 0) A B) (= (hd x) (ite (> n 0) A B))))\n";
    for answer in lane_get_value(src) {
        let positive = value_of(&answer, "(> n 0)") == "true";
        let chosen = value_of(&answer, "(ite (> n 0) A B)");
        assert_eq!(chosen, if positive { "A" } else { "B" }, "{answer}");
        let equal = value_of(&answer, "(hd x)") == chosen;
        assert_eq!(
            value_of(&answer, "(= (hd x) (ite (> n 0) A B))"),
            equal.to_string(),
            "{answer}"
        );
    }
}

/// Missing value (`e13only_gv_foreign_sum_dropped_authored_after_lane_sat`):
/// a formula over a sum sort the query does not use, false under every
/// model (each branch has a false conjunct).
#[test]
#[timeout(60000)]
fn get_value_over_a_dropped_sum_sort_after_a_lane_sat() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E1 0)) (((c2) (c3) (c4))))\n\
        (declare-datatype E5 ((c6) (c7) (c8) (c9) (c10)))\n\
        (declare-datatypes ((E11 0)) (((c12) (c13) (c14))))\n\
        (declare-datatypes ((L24 0)) (((cons29 (hd25 E1) (hd26 E5) (hd27 E11) (tl28 L24)) \
        (nil30))))\n\
        (declare-datatype S31 ((s32 (sa33 E11)) (s34 (sl35 L24) (sb36 E11)) (s37)))\n\
        (declare-const k40 L24) (declare-fun k41 () S31)\n\
        (assert (= nil30 k40))\n\
        (check-sat)\n\
        (get-value ((ite (= (hd26 nil30) c8) (and (= (sa33 s37) (sb36 k41)) true \
        (= c10 (ite (not (distinct s37 k41 s37)) c8 c7))) (and false (= s37 k41) false))))\n";
    for answer in lane_get_value(src) {
        assert!(answer.ends_with(" false))"), "{answer}");
    }
}

/// Two printed values of one model (`both_gv_congruence_dropped_sort_lane_sat`):
/// on a list sort preprocessing dropped from the query, `(tl27 nil29)` and
/// `(tl27 (tl27 k37))` with `(tl27 k37) = nil29` printed different values.
#[test]
#[timeout(60000)]
fn wrong_constructor_selectors_on_a_dropped_sort_are_one_function() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E1 0)) (((c2) (c3) (c4) (c5) (c6) (c7) (c8) (c9) (c10))))\n\
        (declare-datatype L11 ((nil17) (cons16 (hd12 E1) (hd13 E1) (hd14 E1) (tl15 L11))))\n\
        (declare-datatypes ((E18 0)) (((c19) (c20) (c21) (c22))))\n\
        (declare-datatypes ((L23 0)) (((cons28 (hd24 E1) (hd25 E1) (hd26 E18) (tl27 L23)) \
        (nil29))))\n\
        (declare-fun k30 () E1) (declare-fun k31 () E1) (declare-const k37 L23)\n\
        (assert (let ((p (= nil29 (tl27 nil29)))) (let ((q p)) \
        (xor p q (distinct nil17 (cons16 k31 c7 k30 nil17))))))\n\
        (check-sat)\n\
        (get-value (k37 (tl27 k37) (tl27 nil29) (tl27 (tl27 k37)) (tl27 (tl27 nil29)) \
        (hd24 (tl27 nil29)) (hd24 nil29)))\n";
    for answer in lane_get_value(src) {
        if value_of(&answer, "(tl27 k37)") == "nil29" {
            assert_eq!(
                value_of(&answer, "(tl27 (tl27 k37))"),
                value_of(&answer, "(tl27 nil29)"),
                "{answer}"
            );
        }
    }
}

/// The `(get-value)` answers of a script, both postures, none an error.
fn get_values(src: &str) -> Vec<String> {
    let mut answers = Vec::new();
    for z3_mode in [true, false] {
        let (out, _) = outputs(src, z3_mode);
        assert_eq!(out.first().map(String::as_str), Some("sat"), "{out:?}");
        for answer in out.iter().filter(|o| o.starts_with("((")) {
            assert!(!answer.contains("error"), "z3_mode = {z3_mode}: {answer}");
            answers.push(answer.clone());
        }
        assert!(
            !out.iter().any(|o| o.contains("error")),
            "z3_mode = {z3_mode}: {out:?}"
        );
    }
    answers
}

/// Two printed values of one model, outside the lane fragment
/// (#get-value-wrong-ctor-congruence, `main_congruence_plain_check_tl_nil`
/// with arithmetic so the lane declines): `k = nil` and `(tl k) = nil`
/// printed `(= k (tl k))` false, and an internal `(tl k)` with `k = nil`
/// printed another value than `(tl nil)`.
#[test]
#[timeout(60000)]
fn wrong_constructor_selectors_are_one_function_outside_the_lane() {
    let arith = "(set-logic ALL)\n\
        (declare-datatypes ((L 0)) (((cons (tl L)) (nil))))\n\
        (declare-fun k () L) (declare-fun n () Int)\n\
        (assert (= (> n 0) ((_ is nil) k))) (assert (> n 3))\n\
        (check-sat)\n\
        (get-value (k (tl nil) (tl (tl nil)) (tl k) (= k (tl k)) (= (tl k) (tl nil))))\n";
    let uf = "(set-logic QF_UFDT)\n\
        (declare-datatypes ((L 0)) (((cons (tl L)) (nil))))\n\
        (declare-sort U 0) (declare-fun f (L) U) (declare-fun k () L) (declare-fun u () U)\n\
        (assert (= (f k) u)) (assert ((_ is nil) k)) (assert (not (= (f (tl k)) u)))\n\
        (check-sat)\n\
        (get-value (k (tl nil) (tl (tl nil)) (tl k) (= k (tl k)) (= (tl k) (tl nil))))\n";
    for src in [arith, uf] {
        for answer in get_values(src) {
            assert_eq!(value_of(&answer, "k"), "nil", "{answer}");
            let tl_k = value_of(&answer, "(tl k)");
            assert_eq!(tl_k, value_of(&answer, "(tl nil)"), "{answer}");
            assert_eq!(
                value_of(&answer, "(= k (tl k))"),
                (tl_k == "nil").to_string(),
                "{answer}"
            );
            assert_eq!(value_of(&answer, "(= (tl k) (tl nil))"), "true", "{answer}");
        }
    }
}

/// A tester had no value after `check-sat-assuming`
/// (#get-value-tester-coherence, `both_gv_tester_error_after_csa`), and a
/// tester disagreed with its argument's printed value
/// (`both_tester_contradicts_value_after_csa`).
#[test]
#[timeout(60000)]
fn testers_answer_for_the_printed_value() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((L 0)) (((cons (tl L)) (nil))))\n\
        (declare-const k L) (declare-const b Bool)\n\
        (assert (= b (= k k)))\n\
        (check-sat-assuming (b))\n\
        (get-value (k ((_ is cons) k) ((_ is nil) k)))\n";
    for answer in get_values(src) {
        let nil = value_of(&answer, "k") == "nil";
        assert_eq!(
            value_of(&answer, "((_ is nil) k)"),
            nil.to_string(),
            "{answer}"
        );
        assert_eq!(
            value_of(&answer, "((_ is cons) k)"),
            (!nil).to_string(),
            "{answer}"
        );
    }
}

/// An equality printed true over two different printed lists under
/// produce-unsat-cores (`both_gv_eq_true_distinct_values_cores`).
#[test]
#[timeout(60000)]
fn datatype_equalities_answer_for_the_printed_values() {
    let src = "(set-logic QF_DT)\n\
        (set-option :produce-unsat-cores true)\n\
        (declare-datatype E7 ((c8) (c9) (c10)))\n\
        (declare-datatypes ((L16 0)) (((cons20 (hd17 E7) (tl19 L16) (hd18 E7)) (nil21))))\n\
        (declare-const k37 L16) (declare-const k38 L16)\n\
        (assert (! (= k37 (tl19 k38)) :named a5))\n\
        (check-sat)\n\
        (get-value (k37 k38 (= k37 k38)))\n";
    for answer in get_values(src) {
        let same = value_of(&answer, "k37") == value_of(&answer, "k38");
        assert_eq!(
            value_of(&answer, "(= k37 k38)"),
            same.to_string(),
            "{answer}"
        );
    }
}

/// An Int selector on the wrong constructor of a sort the lane query never
/// uses had no value after a lane `sat` (`main_unknown_trivial_sat_many_sorts`):
/// it reads the printed table's default arm.
#[test]
#[timeout(60000)]
fn wrong_constructor_int_selector_reads_the_printed_table() {
    let src = "(set-logic ALL)\n\
        (declare-datatypes ((E 0)) (((A) (B) (C))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-datatypes ((LI 0)) (((icons (ih Int) (it LI)) (inil))))\n\
        (declare-const x L) (declare-const li LI)\n\
        (assert ((_ is cons) x))\n\
        (check-sat)\n\
        (get-value (x (ih inil) (it inil) (= (ih inil) (ih (it inil)))))\n";
    for answer in get_values(src) {
        assert!(!value_of(&answer, "(ih inil)").is_empty(), "{answer}");
    }
}

/// An equality over two records whose fields nothing constrains had no
/// value although `(get-value)` printed both records (#get-value-printed-bool,
/// `gvlane_61_0050`).
#[test]
#[timeout(60000)]
fn record_equalities_answer_for_the_printed_records() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E5 0)) (((c6) (c7) (c8))))\n\
        (declare-datatypes ((R18 0)) (((mk19 (fb14 Bool) (fe17 E5)))))\n\
        (declare-const k29 R18) (declare-fun k30 () R18) (declare-const p Bool)\n\
        (assert p)\n\
        (check-sat)\n\
        (get-value (k29 k30 (= k29 k30) (= (fe17 k29) (fe17 k30)) (not (= k29 k30))))\n";
    for answer in get_values(src) {
        let same = value_of(&answer, "k29") == value_of(&answer, "k30");
        assert_eq!(
            value_of(&answer, "(= k29 k30)"),
            same.to_string(),
            "{answer}"
        );
        assert_eq!(
            value_of(&answer, "(not (= k29 k30))"),
            (!same).to_string(),
            "{answer}"
        );
    }
}

/// A wrong-constructor selector application `(get-value)` interned after
/// the check printed a value of its own that the printed selector table did
/// not carry, and a different one when another term was requested first
/// (`incrgv_61_0017`).
#[test]
#[timeout(60000)]
fn get_value_terms_after_the_check_read_the_printed_table() {
    let head = "(set-logic QF_DT)\n\
        (declare-datatype E1 ((c2) (c3)))\n\
        (declare-datatypes ((E4 0)) (((c5) (c6) (c7) (c8) (c9))))\n\
        (declare-datatype L10 ((cons14 (hd11 E4) (tl13 L10) (hd12 E1)) (nil15)))\n\
        (declare-fun b21 () Bool)\n\
        (assert (=> b21 (not (= (hd11 (cons14 c6 nil15 c2)) (hd11 (cons14 c9 nil15 c3))))))\n\
        (check-sat)\n";
    for request in [
        "((tl13 nil15))",
        "((hd11 (cons14 c5 nil15 c2)) (tl13 nil15))",
    ] {
        let src = format!("{head}(get-value {request})\n(get-model)\n");
        for z3_mode in [true, false] {
            let (out, _) = outputs(&src, z3_mode);
            let answer = out.iter().find(|o| o.starts_with("((")).expect("get-value");
            let value = value_of(answer, "(tl13 nil15)");
            let model = out.last().expect("get-model");
            let table = model
                .lines()
                .find(|l| l.contains("(define-fun tl13 "))
                .expect("tl13 table");
            let arm = match table.find("(ite (= @p0 nil15) ") {
                Some(i) => first_sexpr(&table[i + "(ite (= @p0 nil15) ".len()..]).to_string(),
                None => table
                    .trim_end_matches(')')
                    .rsplit(' ')
                    .next()
                    .unwrap()
                    .to_string(),
            };
            assert_eq!(value, arm, "z3_mode = {z3_mode}: {answer}\n{table}");
        }
    }
}

/// The first s-expression of `text`.
fn first_sexpr(text: &str) -> &str {
    let mut depth = 0i32;
    for (i, c) in text.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => {
                depth -= 1;
                if depth == 0 {
                    return &text[..=i];
                }
            }
            ' ' if depth == 0 => return &text[..i],
            _ => {}
        }
    }
    text
}
