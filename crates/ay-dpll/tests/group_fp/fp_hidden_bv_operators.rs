// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV operators around a float that the FP route's value encoder lacked.
//!
//! Under `(set-logic ALL)`, which model-checker-consumer declares for every floating-point
//! BMC query, the FP bit-blaster encodes the bitvector terms around the floats
//! itself. A symbolic `bvashr`, `rotate_left`/`rotate_right`, `repeat` over a
//! symbolic operand and `bvcomp` (which `bvredor` and `bvredand` elaborate
//! into) had no arm in that encoder, so such a query answered `unknown` with
//! no search while the same text declared QF_AUFBV, where the BV engine owns
//! these operators, was `sat`: the class of model-checker-consumer ask
//! 2026-10-14-fp-logic-all-unknown-test6 (DR-47) through a value operator
//! instead of a hidden ITE condition.

use ntest::timeout;

const OPERANDS: [&str; 6] = [
    "(bvashr f k)",
    "((_ rotate_left 1) f)",
    "((_ rotate_right 3) f)",
    "(concat #b0000000000000000000000000000000 (bvredor f))",
    "(concat #b0000000000000000000000000000000 (bvcomp f k))",
    "((_ repeat 2) ((_ extract 31 16) f))",
];

fn query(logic: &str, operand: &str, goal: &str) -> String {
    format!(
        "(set-logic {logic})
         (declare-const f (_ BitVec 32))
         (declare-const k (_ BitVec 32))
         (declare-const s (_ BitVec 32))
         (assert (= f #x3f800000))
         (assert (= k #x00000001))
         (assert (= s (fp.to_ieee_bv (fp.add RNE ((_ to_fp 8 24) {operand})
                                                 ((_ to_fp 8 24) f)))))
         (assert {goal})
         (check-sat)"
    )
}

/// QF_AUFBV decides the `sat` side; ALL must too, with a model the
/// independent gate confirms, and must refute the `unsat` twin: no operand
/// value here added to 1.0 gives +0.0.
#[test]
#[timeout(60_000)]
fn all_logic_fp_query_over_ashr_rotate_bvcomp_is_decided() {
    for operand in OPERANDS {
        let sat_goal = "(not (= s #x00000000))";
        let (narrow, _) = crate::common::solve_authored_vec_with_gate_result(&query(
            "QF_AUFBV", operand, sat_goal,
        ));
        assert_eq!(narrow, vec!["sat"], "QF_AUFBV reference route, {operand}");
        let (outputs, gate) =
            crate::common::solve_authored_vec_with_gate_result(&query("ALL", operand, sat_goal));
        assert_eq!(outputs, vec!["sat"], "ALL, {operand}");
        assert_eq!(
            gate.as_deref(),
            Some("confirmed-sat"),
            "ALL gate, {operand}"
        );
        let twin = crate::common::solve_authored_vec(&query("ALL", operand, "(= s #x00000000)"));
        assert_eq!(twin, vec!["unsat"], "ALL unsat twin, {operand}");
    }
}

/// Negative twin: the same operators over an uninterpreted application, which
/// the FP route cannot encode exactly, still answer `unknown`.
#[test]
#[timeout(60_000)]
fn ashr_rotate_bvcomp_over_uninterpreted_operand_still_refuses() {
    for operand in OPERANDS {
        let opaque = operand.replace(" f", " (g f)");
        let text = query("ALL", &opaque, "(not (= s #x00000000))").replace(
            "(declare-const s",
            "(declare-fun g ((_ BitVec 32)) (_ BitVec 32))\n         (declare-const s",
        );
        assert_eq!(
            crate::common::solve_authored_vec(&text),
            vec!["unknown"],
            "{opaque}"
        );
    }
}

/// The same operators over free operands, so no preprocessing pass can fold
/// them away before the FP route sees them. Each verdict agrees with z3 5.1.0.
const FREE_OPERAND_CASES: [(&str, &str); 6] = [
    // An arithmetic shift keeps the sign of a positive, non-NaN operand.
    (
        "(assert (fp.isNegative (F (bvashr f k))))
         (assert (fp.isPositive (F f)))
         (assert (not (fp.isNaN (F f))))",
        "unsat",
    ),
    // A shift at or past the width fills a negative operand with ones: NaN.
    (
        "(assert (bvuge k #x00000020))
         (assert (= ((_ extract 31 31) f) #b1))
         (assert (not (fp.isNaN (F (bvashr f k)))))",
        "unsat",
    ),
    (
        "(assert (not (fp.eq (F ((_ rotate_right 37) ((_ rotate_left 5) f))) (F f))))
         (assert (not (fp.isNaN (F f))))",
        "unsat",
    ),
    (
        "(assert (= (bvcomp f g) #b1))
         (assert (fp.lt (F f) (F g)))",
        "unsat",
    ),
    // Bits 30..23 of `repeat 2 h` are bits 14..7 of `h`: a NaN needs them set.
    (
        "(assert (fp.isNaN (F ((_ repeat 2) h))))
         (assert (not (= ((_ extract 14 7) h) #xff)))",
        "unsat",
    ),
    (
        "(assert (fp.isNaN (F ((_ repeat 2) h))))
         (assert (= (bvredand f) #b0))
         (assert (fp.isNaN (F (bvor f (concat #b0 (bvredor g) #b000000000000000000000000000000)))))",
        "sat",
    ),
];

#[test]
#[timeout(60_000)]
fn all_logic_fp_query_over_free_operands_is_decided() {
    for (assertions, expected) in FREE_OPERAND_CASES {
        let text = format!(
            "(set-logic ALL)
             (declare-const f (_ BitVec 32))
             (declare-const g (_ BitVec 32))
             (declare-const k (_ BitVec 32))
             (declare-const h (_ BitVec 16))
             (define-fun F ((x (_ BitVec 32))) (_ FloatingPoint 8 24) ((_ to_fp 8 24) x))
             {assertions}
             (check-sat)"
        );
        let (outputs, gate) = crate::common::solve_authored_vec_with_gate_result(&text);
        assert_eq!(outputs, vec![expected], "{assertions}");
        if expected == "sat" {
            assert_eq!(gate.as_deref(), Some("confirmed-sat"), "{assertions}");
        }
    }
}
