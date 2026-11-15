// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pins for the two-branch assignment-block rewrite
//! (`executor/branch_assign_elim.rs`).
//!
//! Conditional store chains asserted as disjunctions of assignment
//! conjunctions starved the QF_ALIA search: the array equalities inside
//! the branches became Boolean atoms decided blind, and a two-step
//! pointer shape burned 220k+ decisions without a verdict (z3: `sat`
//! immediately). The rewrite turns a block whose two branches assign the
//! same variables under complementary guards into unconditional `ite`
//! definitions, which decide the same shape in ~1.2k decisions. The
//! `unsat` twin (the final bound contradicted by both branches) pins
//! that the rewrite is an equivalence, not a weakening.

use crate::Executor;
use ay_frontend::parse;

fn verdict_within(input: &str, timeout: std::time::Duration) -> String {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    executor.set_timeout(Some(timeout));
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    output
        .iter()
        .rev()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
}

const TWO_STEP_SAT: &str = r#"
(set-logic QF_ALIA)
(declare-const p0 Int) (declare-const a0 (Array Int Int)) (declare-const u0 Int)
(declare-const p1 Int) (declare-const a1 (Array Int Int)) (declare-const u1 Int)
(declare-const p2 Int) (declare-const a2 (Array Int Int))
(declare-const n Int)
(assert (> n 0))
(assert (= p0 0))
(assert (= u0 (select a0 p0)))
(assert (or (and (< p0 n) (= p1 (+ p0 1)) (= a1 (store a0 p0 u0)))
            (and (>= p0 n) (= p1 p0) (= a1 a0))))
(assert (= u1 (select a1 p1)))
(assert (or (and (< p1 n) (= p2 (+ p1 1)) (= a2 (store a1 p1 u1)))
            (and (>= p1 n) (= p2 p1) (= a2 a1))))
(assert (> p2 0))
(check-sat)
"#;

#[test]
fn two_step_conditional_store_chain_decides_sat() {
    assert_eq!(
        verdict_within(TWO_STEP_SAT, std::time::Duration::from_secs(30)),
        "sat"
    );
}

#[test]
fn two_step_conditional_store_chain_contradiction_stays_unsat() {
    // n = 1 forces p1 = 1 then p2 = 1, so (<= p2 0) holds in no branch:
    // the rewritten form must still refute (> p2 0)'s negation shape.
    let unsat = TWO_STEP_SAT
        .replace("(assert (> n 0))", "(assert (= n 1))")
        .replace("(assert (> p2 0))", "(assert (< p2 1))");
    assert_eq!(
        verdict_within(&unsat, std::time::Duration::from_secs(30)),
        "unsat"
    );
}
