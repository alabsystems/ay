// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the round-2 verification findings: one test per
//! finding, each a minimized reproducer from the verifiers' hunt and audit
//! (`dt-fd/verify-1/{hunt,audit}`), with z3's answers as the expectations.

use ay_frontend::parse;
use ntest::timeout;

use super::driver::PUBLICATION_DEADLINE;
use crate::{Executor, StatValue};

fn stat(exec: &Executor, key: &str) -> Option<String> {
    match exec.get_statistics().extra.get(key) {
        Some(StatValue::String(s)) => Some(s.clone()),
        Some(StatValue::Int(i)) => Some(i.to_string()),
        _ => None,
    }
}

/// Run a whole script; every `(check-sat)` answer, in order.
fn script(src: &str, z3_mode: bool) -> (Vec<String>, Executor) {
    let commands = parse(src).unwrap();
    let mut exec = Executor::new();
    exec.set_competition_mode(z3_mode);
    let outputs = exec.execute_all(&commands).unwrap();
    let verdicts = outputs
        .into_iter()
        .filter(|o| matches!(o.as_str(), "sat" | "unsat" | "unknown"))
        .collect();
    (verdicts, exec)
}

fn both_postures(src: &str, expected: &[&str]) {
    for z3_mode in [true, false] {
        let (verdicts, _) = script(src, z3_mode);
        assert_eq!(verdicts, expected, "z3_mode = {z3_mode}\n{src}");
    }
}

/// Wrong UNSAT (pre-existing, #dt-fd-lnh-ctor): the LNH symmetry pass took
/// the constructors of a 5+-constructor enum for interchangeable domain
/// constants and injected ground-false signature roots.
#[test]
#[timeout(60000)]
fn enum_constructors_are_never_symmetry_broken() {
    let pushed = "(set-logic QF_DT)\n\
        (declare-datatype E ((C0) (C1) (C2) (C3) (C4) (C5)))\n\
        (declare-datatype L ((cons (hd E) (tl L)) (nil)))\n\
        (declare-const e E) (declare-const x L)\n\
        (push 1) (assert ((_ is C2) (hd x))) (check-sat) (check-sat)\n";
    let (verdicts, _) = script(pushed, true);
    assert_eq!(verdicts, ["sat", "sat"]);
    let closure = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((A) (B) (C) (D) (E5))))\n\
        (declare-const e0 E)\n\
        (assert (or (= e0 A) (= e0 B) (= e0 C) (= e0 D) (= e0 E5)))\n\
        (assert ((_ is D) e0)) (check-sat)\n";
    both_postures(closure, &["sat"]);
    // The default posture used to publish this one as a corroborated trust
    // closure (the re-solve shared the defect).
    let single = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B) (C) (D) (E5) (E6) (E7) (E8) (E9) (E10)) \
        ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const e0 E) (declare-const x L)\n\
        (assert (or (= A e0) (= B e0) (= C e0) (= D e0) (= E5 e0) (= E6 e0) (= E7 e0) \
        (= E8 e0) (= E9 e0) (= E10 e0)))\n\
        (assert ((_ is E7) e0)) (assert ((_ is cons) x)) (check-sat)\n";
    both_postures(single, &["sat"]);
}

/// Lost SAT (#dt-fd-pin-roots): datatype model construction guessed `x = nil`
/// for a class no collected constructor term forced, falsifying the
/// record disequality the lane's own model satisfies.
#[test]
#[timeout(60000)]
fn record_with_a_formula_field_keeps_the_lane_model() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0)) (((A) (B))))\n\
        (declare-datatypes ((L 0)) (((cons (hd E) (tl L)) (nil))))\n\
        (declare-datatypes ((R 0)) (((mk (f L) (g Bool)))))\n\
        (declare-const x L) (declare-const y L) (declare-const p Bool)\n\
        (assert (distinct (mk x (= nil (cons A y))) (mk nil false)))\n\
        (check-sat)\n";
    for z3_mode in [true, false] {
        let (verdicts, exec) = script(src, z3_mode);
        assert_eq!(verdicts, ["sat"], "z3_mode = {z3_mode}");
        assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("sat"));
    }
}

/// Lost verdicts after `pop` (#dt-live-scan): the eager unroll instantiated
/// axioms over terms earlier commands left in the store, so the third query
/// depended on which lane answered the first one.
#[test]
#[timeout(120000)]
fn later_queries_do_not_depend_on_earlier_lanes() {
    let lane_first = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const y L)\n\
        (assert (= x (cons A y))) (check-sat)\n\
        (push 1) (assert (= (hd x) B)) (check-sat) (pop 1)\n\
        (assert (= (tl x) (cons C nil))) (check-sat)\n";
    both_postures(lane_first, &["sat", "unsat", "sat"]);
    // The same shape with the enum lane answering first. Its third query is
    // `unknown` on main (pre-existing); only the lane's own history is
    // masked (round 3: a wider mask lost other verdicts main decides), so
    // this one is main's answer, never a wrong one.
    let enum_first = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const y L) (declare-const e E) (declare-const f E)\n\
        (assert (distinct e f)) (check-sat)\n\
        (push 1) (assert (= x (cons e y))) (assert (= (hd y) B)) (check-sat) (pop 1)\n\
        (assert (= x (cons A y))) (assert (= (tl x) (cons C nil))) (check-sat)\n";
    for z3_mode in [true, false] {
        let (verdicts, _) = script(enum_first, z3_mode);
        assert_eq!(verdicts[..2], ["sat", "sat"], "z3_mode = {z3_mode}");
        assert_ne!(verdicts[2], "unsat", "z3_mode = {z3_mode}");
    }
}

/// Lane re-entry (#dt-fd-reentry): a certification re-solve runs in a
/// derived-query executor; the SAT-only posture cannot publish the UNSAT it
/// is asked for, so the lane must not run there.
#[test]
#[timeout(60000)]
fn derived_query_executors_skip_the_sat_only_lane() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (assert ((_ is cons) x)) (assert (= (hd x) B))\n";
    let commands = parse(src).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    exec.certification_resolve = true;
    let check = parse("(check-sat)\n").unwrap();
    let out = exec.execute_all(&check).unwrap();
    assert_eq!(out.last().map(String::as_str), Some("sat"));
    assert_eq!(
        stat(&exec, "dt_fd.decline").as_deref(),
        Some("derived-query")
    );
    // `--z3-mode` (the lane may publish UNSAT) is unaffected.
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.execute_all(&commands).unwrap();
    exec.certification_resolve = true;
    let out = exec.execute_all(&check).unwrap();
    assert_eq!(out.last().map(String::as_str), Some("sat"));
    assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("sat"));
}

/// Memory (#dt-fd-memory): past the encoding's share of the memory ceiling
/// the lane declines and the fallback lanes answer, instead of the
/// check-sat ending in `memout`.
#[test]
#[timeout(60000)]
fn memory_pressure_declines_the_lane() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (assert ((_ is cons) x)) (assert (= (hd x) B))\n\
        (assert (= (tl x) (cons C nil))) (check-sat)\n";
    ay_sys::force_process_memory_predictive_exceeded_for_testing(true);
    let (verdicts, exec) = script(src, true);
    ay_sys::force_process_memory_predictive_exceeded_for_testing(false);
    assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("memory"));
    assert_ne!(verdicts, ["unsat"]);
}

/// Publication under the SAT-only cap (#dt-fd-cap-publication): the cap
/// bounds the search only; validation must run against the command's own
/// deadline, or its sticky stop turns a found model into `unknown`.
#[test]
#[timeout(60000)]
fn sat_only_cap_never_covers_publication() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (assert ((_ is cons) x)) (assert (= (hd x) B))\n";
    let commands = parse(src).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap();
    exec.set_timeout(Some(std::time::Duration::from_secs(600)));
    PUBLICATION_DEADLINE.with(|c| c.set(None));
    let out = exec.execute_all(&parse("(check-sat)\n").unwrap()).unwrap();
    assert_eq!(out.last().map(String::as_str), Some("sat"));
    assert_eq!(stat(&exec, "solver.dt_fd_lane").as_deref(), Some("sat"));
    let seen = PUBLICATION_DEADLINE
        .with(std::cell::Cell::get)
        .expect("lane published");
    let remaining = seen
        .expect("the command deadline")
        .saturating_duration_since(ay_core::time::Instant::now());
    // The cap is at most 4 s; the command deadline is ten minutes away.
    assert!(
        remaining > std::time::Duration::from_secs(60),
        "{remaining:?}"
    );
}

/// Memory (#dt-fd-memory): under the default ceiling of this machine class
/// (2764 MiB) the clause cap stops well below the encodings that ran the
/// process into the allocator's hard ceiling (11.0M clauses, `kprobe_3800`)
/// and well above the largest blocksworld encoding (3.3M clauses).
#[test]
fn clause_cap_follows_the_memory_ceiling() {
    use super::memory::budget_for;
    const MIB: usize = 1 << 20;
    let cap = budget_for(2764 * MIB, 100 * MIB, 24_000_000);
    assert!(cap < 9_000_000, "{cap}");
    assert!(cap > 3_300_000, "{cap}");
    // Nothing left under the load share: no clause at all.
    assert_eq!(budget_for(2764 * MIB, 2764 * MIB, 24_000_000), 0);
    // No ceiling: the lane's own cap.
    assert_eq!(budget_for(0, 100 * MIB, 24_000_000), 24_000_000);
}

/// `(get-value)` of a wrong-constructor selector application the query never
/// mentions agrees with the printed selector table (pre-existing,
/// #get-value-wrong-ctor, verify-1 audit `m01_c8_model`).
#[test]
#[timeout(60000)]
fn get_value_of_a_wrong_constructor_selector_reads_the_table() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((E 0) (L 0)) (((A) (B)) ((cons (hd E) (tl L)) (nil))))\n\
        (declare-const x L) (declare-const y L)\n\
        (assert ((_ is nil) x)) (assert (= (tl x) (cons A x)))\n\
        (assert (= (tl (tl x)) x)) (assert (= y (tl (tl x))))\n\
        (assert (= (hd (tl y)) A))\n\
        (check-sat) (get-value ((tl x) (tl nil) (tl (tl nil))))\n";
    for z3_mode in [true, false] {
        let commands = parse(src).unwrap();
        let mut exec = Executor::new();
        exec.set_competition_mode(z3_mode);
        let out = exec.execute_all(&commands).unwrap();
        assert_eq!(
            out.first().map(String::as_str),
            Some("sat"),
            "z3_mode = {z3_mode}"
        );
        let values = out.last().expect("get-value output");
        assert!(
            values.contains("((tl x) (cons A nil))")
                && values.contains("((tl nil) (cons A nil))")
                && values.contains("((tl (tl nil)) nil)"),
            "z3_mode = {z3_mode}: {values}"
        );
    }
}

/// The eager axiom scans' live set includes the axioms this command
/// generated (#dt-live-scan): hash-consing gave the third query's regenerated
/// selector chains the ids the second query had created, the scan called them
/// history, a deepening round skipped them, and validation rejected the model
/// (`unknown`; round-3 incremental accounting, pushpop seed 404 case 41).
#[test]
#[timeout(120000)]
fn regenerated_selector_chains_stay_live() {
    let src = "(set-logic QF_DT)\n\
        (declare-datatypes ((U 0) (L 0)) (((U1)) ((cons (hd U) (tl L)) (nil))))\n\
        (declare-const u0 U) (declare-const u1 U) (declare-const u2 U)\n\
        (declare-const l0 L) (declare-const l1 L) (declare-const l2 L)\n\
        (declare-const b0 Bool) (declare-const b1 Bool)\n\
        (assert (ite (and (and (not ((_ is nil) l0)) ((_ is cons) (tl l0))) ((_ is U1) u1)) \
        (= (tl (tl l0)) l1) (= l0 nil)))\n\
        (check-sat)\n\
        (push 1)\n\
        (assert (= (cons U1 (tl nil)) (cons (ite (=> (not ((_ is nil) l1)) (= (hd l1) U1)) u2 u0) \
        (tl l2))))\n\
        (assert (= (not (= u0 U1)) (= (= u0 u0) ((_ is U1) U1))))\n\
        (check-sat)\n\
        (pop 1)\n\
        (push 1) (assert (and (= (ite b0 l0 l0) l0) (= u1 U1))) (check-sat) (pop 1)\n";
    both_postures(src, &["sat", "unsat", "sat"]);
}
