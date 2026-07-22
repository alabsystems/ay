// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Symbolic RoundingMode finite-domain regressions (#P0.2).
//!
//! `RoundingMode` is the FIXED 5-element domain {RNE, RNA, RTP, RTN, RTZ}.
//! Before the #P0.2 fix its core representation (an uninterpreted sort, with
//! literals historically Bool-sorted) produced FOUR live wrong-`sat` verdicts
//! (z3: `unsat`) — literal-literal equality, contradictory mode pins,
//! `distinct` pigeonholes over 6 RM consts (plain and via
//! `check-sat-assuming`) — and fail-closed `unknown` where z3 decides a
//! symbolic mode via the finite domain. These tests pin:
//!
//! * Pass B (executor/rm_domain.rs): EUF-lane domain axioms — the wrong sats
//!   become `unsat`, while the 5-element-satisfiable duals STAY `sat`.
//! * Pass C (executor/theories/fp/rm_expand.rs): FP-lane mode enumeration —
//!   a declared RM const used as a rounding-op operand DECIDES like z3, with
//!   the model pinning the forced mode (long spelling, z3-exact).
//! * The strengthened `check_fp_support` backstop: out-of-scope symbolic-RM
//!   shapes return `unknown`, never a guess.

use ntest::timeout;

fn first_result(smt: &str) -> String {
    let outputs = crate::common::solve_vec(smt);
    outputs
        .iter()
        .find_map(|o| crate::common::sat_result(o).map(str::to_string))
        .unwrap_or_else(|| panic!("no sat/unsat/unknown in outputs: {outputs:?}"))
}

const SIX_RM_CONSTS: &str = "
    (declare-const a RoundingMode)
    (declare-const b RoundingMode)
    (declare-const c RoundingMode)
    (declare-const d RoundingMode)
    (declare-const e RoundingMode)
    (declare-const f RoundingMode)
";

// ---- Pass B: pure-RM domain semantics (EUF lane) ----

#[test]
#[timeout(60_000)]
fn rm_literal_equality_is_unsat() {
    // Was a live wrong-sat: EUF merged the two literal constants.
    let r = first_result("(assert (= roundTowardPositive roundTowardZero))(check-sat)");
    assert_eq!(r, "unsat");
}

#[test]
#[timeout(60_000)]
fn rm_contradictory_pins_unsat() {
    let r = first_result(
        "(declare-const rm RoundingMode)
         (assert (= rm roundTowardPositive))
         (assert (= rm roundTowardZero))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

#[test]
#[timeout(60_000)]
fn rm_distinct_six_pigeonhole_unsat() {
    let r = first_result(&format!(
        "{SIX_RM_CONSTS}(assert (distinct a b c d e f))(check-sat)"
    ));
    assert_eq!(r, "unsat");
}

#[test]
#[timeout(60_000)]
fn rm_distinct_five_stays_sat() {
    // Dual wrong-verdict guard: the domain axioms must not over-constrain.
    let r = first_result(&format!(
        "{SIX_RM_CONSTS}(assert (distinct a b c d e))(check-sat)"
    ));
    assert_eq!(r, "sat");
}

#[test]
#[timeout(60_000)]
fn rm_check_sat_assuming_distinct_six_unsat() {
    // The assumption routes bypass check_sat.rs preprocessing entirely; the
    // wrong-sat lived in check_sat_assuming_with_controls (QfUf arm).
    let r = first_result(&format!(
        "{SIX_RM_CONSTS}(check-sat-assuming ((distinct a b c d e f)))"
    ));
    assert_eq!(r, "unsat");
}

#[test]
#[timeout(60_000)]
fn rm_model_prints_long_mode_name() {
    let outputs = crate::common::solve_vec(
        "(declare-const rm RoundingMode)
         (assert (= rm roundTowardPositive))
         (check-sat)
         (get-value (rm))",
    );
    let all = outputs.join("\n");
    assert!(
        all.contains("roundTowardPositive"),
        "RM model value must be the z3-exact long literal, got: {all}"
    );
    assert!(
        !all.contains("@RoundingMode"),
        "no abstract @RoundingMode!n token may leak into the model: {all}"
    );
}

// ---- Pass C: FP-lane symbolic-mode enumeration ----

#[test]
#[timeout(120_000)]
fn rm_symbolic_mode_decides_sat_with_forced_mode() {
    // roundToIntegral(rm, 2.5) = 3.0 AND roundToIntegral(rm, -2.5) = -2.0
    // forces rm = RTP uniquely (z3 agrees sat with roundTowardPositive).
    let outputs = crate::common::solve_vec(
        "(declare-const rm RoundingMode)
         (assert (= (fp.roundToIntegral rm ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 3.0)))
         (assert (= (fp.roundToIntegral rm ((_ to_fp 8 24) RNE (- 2.5))) ((_ to_fp 8 24) RNE (- 2.0))))
         (check-sat)
         (get-value (rm))",
    );
    let all = outputs.join("\n");
    assert!(all.contains("sat"), "must decide sat: {all}");
    assert!(
        all.contains("roundTowardPositive"),
        "forced mode must be RTP: {all}"
    );
}

#[test]
#[timeout(120_000)]
fn rm_symbolic_mode_wrong_pin_unsat() {
    // Twin: same rounding facts + a wrong mode pin must be unsat, not sat and
    // not unknown (Pass C decides every branch).
    let r = first_result(
        "(declare-const rm RoundingMode)
         (assert (= (fp.roundToIntegral rm ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 2.0)))
         (assert (= rm roundTowardPositive))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

#[test]
#[timeout(120_000)]
fn rm_equal_pair_conflicting_modes_unsat() {
    // Adversarial: r1 = r2 while their rounding behaviors conflict.
    let r = first_result(
        "(declare-const r1 RoundingMode)
         (declare-const r2 RoundingMode)
         (assert (= r1 r2))
         (assert (= (fp.roundToIntegral r1 ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 3.0)))
         (assert (= (fp.roundToIntegral r2 ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 2.0)))
         (check-sat)",
    );
    assert_eq!(r, "unsat");
}

// ---- Backstop: out-of-scope shapes fail closed, never guess ----

#[test]
#[timeout(60_000)]
fn rm_ite_of_modes_stays_fail_closed() {
    // An RM-sorted ite is outside the v1 enumeration scope (documented
    // residue): must be `unknown` — z3 decides `unsat` here, and a `sat`
    // would be a wrong verdict.
    let r = first_result(
        "(declare-const b Bool)
         (assert (fp.eq (fp.roundToIntegral (ite b RTP RTZ) ((_ to_fp 8 24) RNE 2.5))
                        ((_ to_fp 8 24) RNE 3.5)))
         (check-sat)",
    );
    assert_eq!(r, "unknown", "out-of-scope RM shape must fail closed");
}
