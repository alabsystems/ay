// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV relational atoms reachable only through a BV/FP value ITE.
//!
//! The FP bit-blaster used to refuse such an atom as an encoding gap (#3586),
//! because the outer Tseitin walk never gave it a variable. Every FP-aware
//! route then answered `unknown` with no search on a query the BV-only route
//! decides. model-checker-consumer's Kani BMC lowering of `i32 as f32` produces exactly this
//! shape: a leading-bit search `(ite (= ((_ extract k k) |x|) #b1) …)` inside
//! the operands of an `fp` constructor. The atom is now encoded as its exact
//! comparator over the operand bits the rest of the encoding shares.
//!
//! `fixtures/model_checker_consumer_fp_all_test6/query-all.smt2` is byte-identical to the
//! query model-checker-consumer exports for Kani `tests/expected/test6/main.rs` (Kani
//! 4c0fce8c3, sha256 `1bb78d18…e68e`): `add2(1, 1) == 2.0` holds and
//! `add2(2, 1) == 2.0` fails, so Kani reports FAILED. At ay ca183f8d4 it was
//! `sat` under `(set-logic QF_AUFBV)` and `unknown` with 0 decisions under
//! `ALL`, `QF_ABVFP`, `QF_BVFP` and `QF_FP`.

use ntest::timeout;

const TEST6: &str = include_str!("../fixtures/model_checker_consumer_fp_all_test6/query-all.smt2");
const TEST6_GOAL: &str = "(assert (or ay_violation_kani_assert_0 ay_violation_kani_assert_1))";
/// The routes that bit-blast floating point.
const FP_LOGICS: [&str; 4] = ["ALL", "QF_ABVFP", "QF_BVFP", "QF_FP"];

fn with_logic(query: &str, logic: &str) -> String {
    let declared = query
        .lines()
        .find(|line| line.starts_with("(set-logic "))
        .unwrap_or_else(|| panic!("query declares no logic:\n{query}"));
    query.replacen(declared, &format!("(set-logic {logic})"), 1)
}

fn test6_with_goal(goal: &str) -> String {
    assert_eq!(TEST6.matches(TEST6_GOAL).count(), 1, "fixture goal moved");
    TEST6.replacen(TEST6_GOAL, goal, 1)
}

fn assert_confirmed_sat(query: &str, context: &str) {
    let (output, gate) = crate::common::solve_authored_vec_with_gate_result(query);
    assert_eq!(output, ["sat"], "{context}");
    assert_eq!(
        gate.as_deref(),
        Some("confirmed-sat"),
        "{context}: the independent model gate must confirm the witness"
    );
}

fn assert_unsat(query: &str, context: &str) {
    assert_eq!(
        crate::common::solve_authored_vec(query),
        ["unsat"],
        "{context}"
    );
}

#[test]
#[timeout(60_000)]
fn model_checker_consumer_test6_is_confirmed_sat_on_every_fp_route() {
    for logic in FP_LOGICS {
        assert_confirmed_sat(&with_logic(TEST6, logic), logic);
    }
    // The BV-only route the consumer used to send keeps its answer.
    assert_confirmed_sat(&with_logic(TEST6, "QF_AUFBV"), "QF_AUFBV");
}

/// The witness is the failing assertion (`2 + 1 != 2`), not the holding one.
#[test]
#[timeout(60_000)]
fn model_checker_consumer_test6_witness_violates_only_the_second_assertion() {
    let query = TEST6.replacen(
        "(check-sat)",
        "(check-sat)\n(get-value (ay_violation_kani_assert_0 ay_violation_kani_assert_1))",
        1,
    );
    let output = crate::common::solve_vec(&query);
    assert_eq!(
        output.first().map(String::as_str),
        Some("sat"),
        "{output:?}"
    );
    let values = output.get(1).map(String::as_str).unwrap_or_default();
    assert!(
        values.contains("(ay_violation_kani_assert_0 false)")
            && values.contains("(ay_violation_kani_assert_1 true)"),
        "unexpected witness: {values}"
    );
}

/// Each assertion alone: `1 + 1 == 2.0` cannot be violated (UNSAT), and
/// `2 + 1 == 2.0` can (SAT), on every FP route. The UNSAT half is what a
/// relaxed (unconstrained) condition literal would get wrong.
#[test]
#[timeout(120_000)]
fn model_checker_consumer_test6_assertions_separately_have_sat_and_unsat_controls() {
    let holds = test6_with_goal("(assert ay_violation_kani_assert_0)");
    let fails = test6_with_goal("(assert ay_violation_kani_assert_1)");
    for logic in FP_LOGICS {
        assert_unsat(&with_logic(&holds, logic), logic);
        assert_confirmed_sat(&with_logic(&fails, logic), logic);
    }
}

/// The test6 shape reduced: `x as f32` for `x < 4` by a two-step leading-bit
/// search inside the `fp` operands, plus `1.0`. Reachable sums are 1, 2, 3.
fn reduced_cast_add(goal_bits: &str) -> String {
    format!(
        "(set-logic ALL)
        (declare-const x (_ BitVec 32))
        (assert (bvult x #x00000004))
        (declare-const r (_ BitVec 32))
        (assert (let ((e (ite (= ((_ extract 1 1) x) #b1) #x40000000
                         (ite (= ((_ extract 0 0) x) #b1) #x3f800000 #x00000000))))
          (= r (fp.to_ieee_bv (fp.add RNE
             (fp ((_ extract 31 31) e) ((_ extract 30 23) e) ((_ extract 22 0) e))
             ((_ to_fp 8 24) #x3f800000))))))
        (assert (= r {goal_bits}))
        (check-sat)"
    )
}

#[test]
#[timeout(60_000)]
fn reduced_cast_add_has_sat_and_unsat_controls_on_every_fp_route() {
    for logic in FP_LOGICS {
        // 3.0 is reachable (x = 2 or 3); 4.0 is not.
        assert_confirmed_sat(&with_logic(&reduced_cast_add("#x40400000"), logic), logic);
        assert_unsat(&with_logic(&reduced_cast_add("#x40800000"), logic), logic);
    }
}

/// Unsigned, signed and arithmetic guards over `x`, which top-level atoms
/// confine to {3, 4} without pinning it to a constant: the hidden guard's
/// circuit and the linked top-level atoms must agree on one set of `x` bits.
fn ordered_guard(guard: &str, result: &str) -> String {
    format!(
        "(set-logic ALL)
        (declare-const x (_ BitVec 8))
        (assert (bvslt x #x05))
        (assert (bvsgt x #x02))
        (assert (= (fp.to_ieee_bv ((_ to_fp 5 11) (ite {guard} #x3c00 #x4000))) {result}))
        (check-sat)"
    )
}

#[test]
#[timeout(60_000)]
fn hidden_ordered_and_arithmetic_guards_have_sat_and_unsat_controls() {
    // x in {3, 4}: each guard is false, so the value is #x4000 (2.0), never
    // #x3c00 (1.0). All ten relational operators appear in a hidden position;
    // `bvslt x 3` and `bvsgt x 4` are false only by the boundary itself.
    for guard in [
        "(bvult x #x02)",
        "(bvugt x #x05)",
        "(bvsle x #x01)",
        "(bvsge x #x05)",
        "(bvuge x #x05)",
        "(bvslt x #x03)",
        "(bvsgt x #x04)",
        "(= (bvadd x #x01) #x02)",
        "(and (bvule x #x04) (= x #x00))",
        "(not (distinct x #x07))",
    ] {
        assert_confirmed_sat(&ordered_guard(guard, "#x4000"), guard);
        assert_unsat(&ordered_guard(guard, "#x3c00"), guard);
    }
}

/// Formerly `test_fp_ite_non_fp_condition_returns_unknown` (#3586): the BV
/// guard is now encoded, so the query is decided (`x <= 5` selects `b < a`).
#[test]
#[timeout(30_000)]
fn fp_ite_bv_guard_is_decided() {
    let open = "(set-logic QF_BVFP)
        (declare-const x (_ BitVec 8))
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (assert (fp.lt (ite (bvugt x #x05) a b) a))
        (check-sat)";
    assert_confirmed_sat(open, "x free");
    // A distinct top-level atom confining x above 5 selects `a`, and `a < a`
    // is false: the hidden guard must read the same x bits.
    let confined = open.replacen("(check-sat)", "(assert (bvuge x #x06))\n(check-sat)", 1);
    assert_unsat(&confined, "x >= 6");
}

/// Formerly `test_fp_ite_mixed_conditions_one_gap_returns_unknown`: an FP
/// guard and a BV guard in one query are both encoded.
#[test]
#[timeout(30_000)]
fn fp_ite_mixed_fp_and_bv_guards_are_decided() {
    let query = "(set-logic QF_BVFP)
        (declare-const x (_ BitVec 8))
        (declare-const a (_ FloatingPoint 8 24))
        (declare-const b (_ FloatingPoint 8 24))
        (declare-const c (_ FloatingPoint 8 24))
        (assert (fp.lt (ite (fp.lt a b) a c) b))
        (assert (fp.eq (ite (bvugt x #x05) a b) c))
        (check-sat)";
    assert_confirmed_sat(query, "mixed guards");
    // x >= 6 makes the BV guard select `a`, so `a == c` (neither is NaN).
    // With `a < b` false the FP guard selects `c`, which must be `< b`; but
    // `c == a` and `a < b` is false.
    let refuted = query.replacen(
        "(check-sat)",
        "(assert (bvuge x #x06))\n(assert (not (fp.lt a b)))\n(check-sat)",
        1,
    );
    assert_unsat(&refuted, "x >= 6 and not a < b");
}

/// A guard the bit-blaster cannot encode (an uninterpreted predicate) keeps
/// the fail-closed refusal: no verdict from an unconstrained proxy.
#[test]
#[timeout(30_000)]
fn hidden_uninterpreted_guard_still_refuses() {
    let query = "(set-logic ALL)
        (declare-const x (_ BitVec 2))
        (declare-fun opaque ((_ BitVec 2)) Bool)
        (assert (= (fp.to_ieee_bv ((_ to_fp 5 11) (ite (opaque x) #x3c00 #x4000))) #x3c00))
        (check-sat)";
    assert_eq!(crate::common::solve_authored_vec(query), ["unknown"]);
}
