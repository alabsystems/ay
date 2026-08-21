// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test: safe counting loops answered `sat` with a fabricated
//! 1-step counterexample carrying no assignments.
//!
//! Root cause: `init_must_summaries_from_facts` derived the level-0
//! must-summary (the set of states a fact clause PROVES reachable — an
//! UNDER-approximation) from the clause's body constraint alone. Head
//! arguments that are not plain variables contributed nothing:
//!
//! * a constant argument — `(rule (=> true (hdr #x00 n)))`
//! * a repeated variable — `(rule (=> true (inv #x00 n n)))` lost `a1 = a2`
//!
//! Both yield the summary `true`, i.e. "every state is proven reachable".
//! The must-reachability fast path (`reach_facts::find_match`) then matches
//! ANY proof obligation, `strengthen` reports `Unsafe`, and
//! `build_cex_from_reach_facts` emits a one-entry witness whose state is
//! `true` with no instances — which the counterexample verifier accepts
//! vacuously (its fact check is `SAT(true)`).
//!
//! Every problem below is SAFE by inspection: a counter starts at 0 and is
//! incremented only while `i < n`, so on exit `i == n` and the error clause
//! `¬(i < n) ∧ i ≠ n` is unsatisfiable. Reaching `error` from the initial
//! state in one step would require `n = 0 ∧ n ≠ 0`.
//!
//! Fix: pin head-argument positions that can be stated over the canonical
//! predicate variables (constants, and the repeats of an already-bound
//! variable). Compound arguments stay unpinned — their expressions mention
//! clause-local variables with no canonical counterpart, and admitting free
//! variables into a reach fact regresses the routes that consume it.
//!
//! `unknown` is an acceptable answer throughout: these tests guard SOUNDNESS,
//! not completeness. Only `sat` (error reachable) is a bug.

use ay_chc::{AdaptiveConfig, AdaptivePortfolio, ChcParser};
use ntest::timeout;
use std::time::Duration;

/// Counting loop with the cycle split over two predicates.
const SPLIT_CYCLE_2PRED: &str = r"
(set-logic HORN)
(declare-var i (_ BitVec 8))
(declare-var n (_ BitVec 8))
(declare-rel hdr ((_ BitVec 8) (_ BitVec 8)))
(declare-rel body ((_ BitVec 8) (_ BitVec 8)))
(declare-rel error ())
(rule (=> true (hdr #x00 n)))
(rule (=> (and (hdr i n) (bvult i n)) (body i n)))
(rule (=> (body i n) (hdr (bvadd i #x01) n)))
(rule (=> (and (hdr i n) (not (bvult i n)) (not (= i n))) error))
(query error)
";

/// The same loop with the increment in its own predicate.
const SPLIT_CYCLE_3PRED: &str = r"
(set-logic HORN)
(declare-var i (_ BitVec 8))
(declare-var n (_ BitVec 8))
(declare-var t (_ BitVec 8))
(declare-rel hdr ((_ BitVec 8) (_ BitVec 8)))
(declare-rel body ((_ BitVec 8) (_ BitVec 8)))
(declare-rel inc ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel error ())
(rule (=> true (hdr #x00 n)))
(rule (=> (and (hdr i n) (bvult i n)) (body i n)))
(rule (=> (and (body i n) (= t (bvadd i #x01))) (inc i n t)))
(rule (=> (inc i n t) (hdr t n)))
(rule (=> (and (hdr i n) (not (bvult i n)) (not (= i n))) error))
(query error)
";

/// As above plus the overflow obligation a bit-precise front end emits.
const SPLIT_CYCLE_OVERFLOW: &str = r"
(set-logic HORN)
(declare-var i (_ BitVec 8))
(declare-var n (_ BitVec 8))
(declare-var t (_ BitVec 8))
(declare-rel hdr ((_ BitVec 8) (_ BitVec 8)))
(declare-rel body ((_ BitVec 8) (_ BitVec 8)))
(declare-rel inc ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel error ())
(rule (=> true (hdr #x00 n)))
(rule (=> (and (hdr i n) (bvult i n)) (body i n)))
(rule (=> (and (body i n) (bvult (bvadd i #x01) i)) error))
(rule (=> (and (body i n) (= t (bvadd i #x01)) (not (bvult (bvadd i #x01) i))) (inc i n t)))
(rule (=> (inc i n t) (hdr t n)))
(rule (=> (and (hdr i n) (not (bvult i n)) (not (= i n))) error))
(query error)
";

/// One predicate, but the init clause repeats a head variable: `m` and `n`
/// are the same value, and the loop tests `m` while the assertion names `n`.
const REPEATED_HEAD_VAR: &str = r"
(set-logic HORN)
(declare-var i (_ BitVec 8))
(declare-var n (_ BitVec 8))
(declare-var m (_ BitVec 8))
(declare-rel inv ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)))
(declare-rel error ())
(rule (=> true (inv #x00 n n)))
(rule (=> (and (inv i n m) (bvult i m)) (inv (bvadd i #x01) n m)))
(rule (=> (and (inv i n m) (not (bvult i m)) (not (= i n))) error))
(query error)
";

/// A genuinely UNSAFE counting loop: the exit assertion `i == n + 1` fails.
/// Guards the fix against over-correcting into "never answers sat".
const GENUINELY_UNSAFE: &str = r"
(set-logic HORN)
(declare-var i (_ BitVec 8))
(declare-var n (_ BitVec 8))
(declare-rel hdr ((_ BitVec 8) (_ BitVec 8)))
(declare-rel body ((_ BitVec 8) (_ BitVec 8)))
(declare-rel error ())
(rule (=> true (hdr #x00 n)))
(rule (=> (and (hdr i n) (bvult i n)) (body i n)))
(rule (=> (body i n) (hdr (bvadd i #x01) n)))
(rule (=> (and (hdr i n) (not (bvult i n)) (not (= i (bvadd n #x01)))) error))
(query error)
";

fn solve(name: &str, source: &str) -> ay_chc::VerifiedChcResult {
    let problem = ChcParser::parse(source).unwrap_or_else(|e| panic!("parse {name}: {e:?}"));
    problem
        .validate()
        .unwrap_or_else(|e| panic!("validate {name}: {e:?}"));
    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10));
    AdaptivePortfolio::new(problem, config).solve()
}

/// A SAFE problem must never be reported UNSAFE. `unknown` is allowed.
fn assert_not_unsafe(name: &str, source: &str) {
    let result = solve(name, source);
    assert!(
        !result.is_unsafe(),
        "{name} is SAFE (a counter incremented only while i < n exits with i == n); \
         answering sat is a soundness bug. Got: {result:?}"
    );
}

#[test]
#[timeout(60000)]
fn split_cycle_2pred_is_not_unsafe() {
    assert_not_unsafe("split_cycle_2pred", SPLIT_CYCLE_2PRED);
}

#[test]
#[timeout(60000)]
fn split_cycle_3pred_is_not_unsafe() {
    assert_not_unsafe("split_cycle_3pred", SPLIT_CYCLE_3PRED);
}

#[test]
#[timeout(60000)]
fn split_cycle_with_overflow_check_is_not_unsafe() {
    assert_not_unsafe("split_cycle_overflow", SPLIT_CYCLE_OVERFLOW);
}

#[test]
#[timeout(60000)]
fn repeated_head_variable_keeps_its_equality() {
    assert_not_unsafe("repeated_head_var", REPEATED_HEAD_VAR);
}

/// The fix must not blind the solver to real counterexamples.
#[test]
#[timeout(60000)]
fn genuinely_unsafe_counting_loop_is_still_refuted() {
    let result = solve("genuinely_unsafe", GENUINELY_UNSAFE);
    assert!(
        result.is_unsafe(),
        "the exit assertion i == n+1 is false for n = 0; the solver must still refute it. \
         Got: {result:?}"
    );
}
