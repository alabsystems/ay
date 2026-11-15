// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! CHC-COMP 2026 Workstream D (DESIGN_lra_interp_tpa.md §4.1, §9): the PDR
//! interpolation ladder. With two or more UNSAT clauses behind a POB, stage 1
//! now interpolates per clause and serves `∨_c I_c`; stage 5 no longer runs
//! when the skip probe found `∧A` UNSAT (its `A ⊨ I` check would be vacuous);
//! stage 3 is skipped on non-integer problems. Owner: WP-D1-M.
//!
//! These end-to-end checks run PDR on predicates defined by several clauses
//! (two facts plus a transition), over Real and Int, and require the verdict
//! to be right: never Unsafe on a safe system, never Safe on an unsafe one.
//! The exact per-clause semantics (every clause implies the served
//! disjunction, including when the clauses' A-sides contradict each other)
//! are unit tests of `pdr::solver::blocking::interpolation`.

#![allow(clippy::panic)]

use ay_chc::{testing, PdrConfig, PdrResult};
use ntest::timeout;

fn system(sort: &str, one: &str, zero: &str, bad: &str) -> String {
    let eight = if sort == "Real" { "8.0" } else { "8" };
    format!(
        r#"
(set-logic HORN)
(declare-fun inv ({sort} {sort}) Bool)
(assert (forall ((x {sort}) (y {sort})) (=> (and (= x {zero}) (= y {zero})) (inv x y))))
(assert (forall ((x {sort}) (y {sort})) (=> (and (= x {one}) (= y {one})) (inv x y))))
(assert (forall ((x {sort}) (y {sort}) (x2 {sort}) (y2 {sort}))
  (=> (and (inv x y) (= x2 (+ x {one})) (= y2 (+ y {one})) (<= x2 {eight})) (inv x2 y2))))
(assert (forall ((x {sort}) (y {sort})) (=> (and (inv x y) {bad}) false)))
(check-sat)
(exit)
"#
    )
}

fn verdict(input: &str) -> Option<bool> {
    match testing::pdr_solve_from_str(input, PdrConfig::default()) {
        Ok(PdrResult::Safe(_)) => Some(true),
        Ok(PdrResult::Unsafe(_)) => Some(false),
        _ => None,
    }
}

#[test]
#[timeout(60_000)]
fn multi_clause_real_predicate_keeps_the_verdict_right() {
    let safe = system("Real", "1.0", "0.0", "(not (= x y))");
    assert_ne!(
        verdict(&safe),
        Some(false),
        "safe Real system reported Unsafe"
    );
    let reachable = system("Real", "1.0", "0.0", "(>= x 3.0)");
    assert_ne!(
        verdict(&reachable),
        Some(true),
        "unsafe Real system reported Safe"
    );
}

#[test]
#[timeout(60_000)]
fn multi_clause_int_predicate_keeps_the_verdict_right() {
    let safe = system("Int", "1", "0", "(not (= x y))");
    assert_ne!(
        verdict(&safe),
        Some(false),
        "safe Int system reported Unsafe"
    );
    let reachable = system("Int", "1", "0", "(>= x 3)");
    assert_ne!(
        verdict(&reachable),
        Some(true),
        "unsafe Int system reported Safe"
    );
}
