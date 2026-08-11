// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for the supported, exactly lowered QF_EIA fragment.

use super::*;
use crate::{UnknownOrigin, UnknownReason};

fn solve_fact(fact: &str) -> Vec<String> {
    let input = format!("(set-logic QF_EIA)\n(assert {fact})\n(check-sat)\n");
    let commands = parse(&input).expect("parse QF_EIA fact");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("execute supported QF_EIA fact")
}

fn assert_fact_and_wrong_twin(term: &str, value: &str) {
    assert_eq!(solve_fact(&format!("(= {term} {value})")), ["sat"]);
    assert_eq!(solve_fact(&format!("(distinct {term} {value})")), ["unsat"]);
}

#[test]
fn ground_positive_powers_and_wrong_twins_decide() {
    assert_fact_and_wrong_twin("(** 2 10)", "1024");
    assert_fact_and_wrong_twin("(** (- 2) 3)", "(- 8)");
}

#[test]
fn zero_to_zero_and_wrong_twin_decide() {
    assert_fact_and_wrong_twin("(** 0 0)", "1");
}

#[test]
fn negative_exponent_rules_and_wrong_twins_decide() {
    // Every row here has a NONZERO denominator, so its value is FIXED by the
    // Ints theory's negative-exponent equation. `(** 0 (- 4))` is not such a
    // row and has its own test below: it lowers to `(div 1 0)`, which SMT-LIB
    // deliberately leaves under-specified, so it may never appear here.
    for (term, value) in [
        ("(** 1 (- 7))", "1"),
        ("(** (- 1) (- 3))", "(- 1)"),
        ("(** (- 1) (- 4))", "1"),
        ("(** 2 (- 3))", "0"),
        ("(** (- 2) (- 3))", "0"),
    ] {
        assert_fact_and_wrong_twin(term, value);
    }
}

/// `(** 0 (- 4))` lowers to `(div 1 (** 0 4))` = `(div 1 0)`, which SMT-LIB
/// leaves UNDER-SPECIFIED — and this row used to be asserted equal to `0`.
///
/// That expectation encoded behaviour AY deliberately no longer has. Pinning
/// `(div 1 0)` to a value was a WRONG-UNSAT soundness bug; `qf_lia.rs` records
/// it and guards against its return. So the row could only have been kept by
/// reintroducing the bug, which is why it moved here instead of being fixed in
/// place.
///
/// What replaces it is STRICTLY STRONGER than an equality would have been: the
/// value is pinned to nothing in EITHER direction, while congruence — that the
/// term is one consistent value — still holds.
#[test]
fn zero_to_a_negative_exponent_stays_under_specified() {
    // It really is `(div 1 0)`, not merely similar to it.
    assert_eq!(
        solve_fact("(distinct (** 0 (- 4)) (div 1 0))"),
        ["unsat"],
        "`(** 0 (- 4))` must lower to `(div 1 0)`"
    );

    // Under-specified: no value may be forced, and no value may be forbidden.
    // In particular BOTH a zero and a nonzero interpretation stay satisfiable.
    for value in ["0", "1", "(- 1)", "7"] {
        assert_eq!(
            solve_fact(&format!("(= (** 0 (- 4)) {value})")),
            ["sat"],
            "nothing may forbid `(** 0 (- 4))` from being {value}"
        );
        assert_eq!(
            solve_fact(&format!("(distinct (** 0 (- 4)) {value})")),
            ["sat"],
            "nothing may pin `(** 0 (- 4))` to {value}"
        );
    }

    // ... but it is ONE value, so it cannot differ from itself.
    assert_eq!(
        solve_fact("(distinct (** 0 (- 4)) (** 0 (- 4)))"),
        ["unsat"],
        "under-specified is not unconstrained: congruence still holds"
    );
}

#[test]
fn symbolic_exponent_is_accepted_and_returns_unknown() {
    let commands = parse(
        "(set-logic QF_EIA)\n\
         (declare-const exponent Int)\n\
         (assert (= (** 2 exponent) 4))\n\
         (check-sat)",
    )
    .expect("parse symbolic exponent");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("well-sorted symbolic exponent must be accepted");
    assert_eq!(output, ["unknown"]);
    assert_eq!(
        executor.unknown_reason(),
        Some(UnknownReason::UnsupportedArithmetic)
    );
    assert_eq!(
        executor.unknown_origin(),
        Some(UnknownOrigin::UnsupportedArithmeticFragment)
    );
}

#[test]
fn symbolic_exponent_in_assumption_is_accepted_and_returns_unknown() {
    let commands = parse(
        "(set-logic QF_EIA)\n\
         (declare-const exponent Int)\n\
         (check-sat-assuming ((= (** 2 exponent) 4)))",
    )
    .expect("parse symbolic exponent assumption");
    let mut executor = Executor::new();
    assert_eq!(executor.execute_all(&commands).unwrap(), ["unknown"]);
    assert_eq!(
        executor.unknown_reason(),
        Some(UnknownReason::UnsupportedArithmetic)
    );
    assert_eq!(
        executor.unknown_origin(),
        Some(UnknownOrigin::UnsupportedArithmeticFragment)
    );
}

#[test]
fn symbolic_exponent_in_objective_is_accepted_and_returns_unknown() {
    let commands = parse(
        "(set-logic QF_EIA)\n\
         (declare-const exponent Int)\n\
         (maximize (** 2 exponent))\n\
         (check-sat)",
    )
    .expect("parse symbolic exponent objective");
    let mut executor = Executor::new();
    assert_eq!(executor.execute_all(&commands).unwrap(), ["unknown"]);
    assert_eq!(
        executor.unknown_reason(),
        Some(UnknownReason::UnsupportedArithmetic)
    );
}
