// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the authored consequence-replay UNSAT translation
//! (#consequence-replay).
//!
//! This file deliberately holds ONE test in its own binary: it mutates the
//! process environment, which must never race sibling tests in a shared
//! process.

#![allow(clippy::panic)]

mod common;

/// The CEGQI range-bound universal the consequence-replay producer translates
/// (its live proof carries a residual `trust` step, and the instance is a
/// guarded implication the flat arithmetic `forall_inst` lane's comparison
/// pre-filter refuses). With `the kill switch off` BOTH the trust-
/// rejected cascade member and the CEGQI certification translation leg are
/// disabled — and the normalized-source provenance recording with them — so
/// the publication gate must restore the exact baseline `unknown`; with the
/// switch back on the same input must decide `unsat`. Deleting the kill-switch
/// guard in `build_authored_consequence_replay_refutation` or the one on the
/// normalized-source record push in `register_ematching_proof_provenance`
/// makes the OFF half fail.
#[test]
fn consequence_replay_is_fully_covered_by_the_kill_switch() {
    let smt = r#"
        (set-logic LIA)
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (<= a b))
        (assert (forall ((x Int))
            (=> (and (<= a x) (<= x b)) (>= x 0))))
        (assert (< a 0))
        (check-sat)
    "#;
    let frame_smt = r#"
        (set-logic ALL)
        (declare-fun s () (Array Int Int))
        (declare-fun snew () (Array Int Int))
        (declare-fun val () Int)
        (assert (= (select s 0) 10))
        (assert (= (select s 1) 20))
        (assert (= (select s 2) 30))
        (assert (>= val 0))
        (assert (forall ((k Int))
            (= (select snew k) (ite (= k 1) val (select s k)))))
        (assert (exists ((j Int))
            (and (<= 0 j) (< j 3) (< (select snew j) 0))))
        (check-sat)
    "#;
    let guarded_frame_smt = r#"
        (set-logic ALL)
        (declare-fun s () (Array Int Int))
        (declare-fun snew () (Array Int Int))
        (declare-fun val () Int)
        (assert (= (select s 0) 10))
        (assert (= (select s 1) 20))
        (assert (= (select s 2) 30))
        (assert (>= val 0))
        (assert (forall ((k Int))
            (= (select snew k) (ite (= k 1) val (select s k)))))
        (assert (exists ((j Int))
            (and (>= j 0) (< j 18446744073709551616) (< j 3)
                 (< (select snew j) 0))))
        (check-sat)
    "#;

    let off_guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_consequence_replay: true,
        ..Default::default()
    });
    let off_results = common::solve_vec(smt);
    let off_frame = common::solve_vec(frame_smt);
    let off_guarded_frame = common::solve_authored_selfcheck_vec(guarded_frame_smt);
    drop(off_guard);
    assert!(
        off_results.iter().any(|r| r == "unknown") && !off_results.iter().any(|r| r == "unsat"),
        "with the kill switch off the translation is disabled and the \
         mandatory certification gate must restore the baseline downgrade; got {off_results:?}"
    );
    assert!(
        !off_guarded_frame.iter().any(|r| r == "unsat"),
        "without consequence-replay provenance the u64-guarded finite-expanded \
         frame obligation may not mint UNSAT; got guarded={off_guarded_frame:?} \
         (the smaller frame may discharge through an independent exact lane: {off_frame:?})"
    );

    let on_results = common::solve_vec(smt);
    let on_frame = common::solve_vec(frame_smt);
    let on_guarded_frame = common::solve_authored_selfcheck_vec(guarded_frame_smt);
    assert!(
        on_results.iter().any(|r| r == "unsat"),
        "with the kill switch on (default) the consequence replay must stitch \
         a strict authored-scope proof and publish unsat; got {on_results:?}"
    );
    assert!(
        on_frame.iter().any(|r| r == "unsat") && on_guarded_frame.iter().any(|r| r == "unsat"),
        "with exact recorded forall/Skolem provenance both frame obligations \
         must publish strict UNSAT; got frame={on_frame:?}, guarded={on_guarded_frame:?}"
    );
}
