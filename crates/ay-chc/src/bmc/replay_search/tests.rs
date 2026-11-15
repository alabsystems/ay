// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The counterexample replay decides its branches without proofs, and
//! still confirms only a real counterexample.
//!
//! These problems have the shape of model-checker-consumer's realloc-grow twin, scaled
//! down. An acyclic DAG gives the exact acyclic lane one branch per fact. The
//! first branch is UNSAT only by bit-vector reasoning (constant folding cannot
//! close it). The query reads an array, so the branches go to the executor.

use super::{last_acceptance_under_verdict_only, BmcSolver};
use crate::parser::ChcParser;
use crate::smt::executor_adapter::{shed_search_executors_built, verdict_only_search_active};
use crate::ChcProblem;
use ntest::timeout;
use std::time::Duration;

/// `P` holds a byte `x` below 16 or above 32, and a memory `m` holding 7 at
/// `x`. The query asks for `x + 5 > 48`, which only the second fact can
/// reach, with the extra conjunct `bound`.
fn two_branch_problem(bound: &str) -> ChcProblem {
    let source = format!(
        "(set-logic HORN)
(declare-fun P ((Array (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8)) Bool)
(assert (forall ((m (Array (_ BitVec 8) (_ BitVec 8))) (x (_ BitVec 8)))
  (=> (and (bvult x #x10) (= (select m x) #x07)) (P m x))))
(assert (forall ((m (Array (_ BitVec 8) (_ BitVec 8))) (x (_ BitVec 8)))
  (=> (and (bvugt x #x20) (= (select m x) #x07)) (P m x))))
(assert (forall ((m (Array (_ BitVec 8) (_ BitVec 8))) (x (_ BitVec 8)))
  (=> (and (P m x) (bvugt (bvadd x #x05) #x30) (= (select m x) #x07) {bound}) false)))
(check-sat)
"
    );
    ChcParser::parse(&source).expect("the two-branch fixture parses")
}

fn replay(problem: &ChcProblem) -> Option<crate::pdr::Counterexample> {
    BmcSolver::replay_confirm_unsafe_on_problem(problem, 2, Duration::from_secs(30), None, false)
}

/// The replay confirms the counterexample behind the second branch, the
/// search reaches it through executors that skip the proof cycle, and the
/// acceptance step runs outside the verdict-only scope.
///
/// Counterfactuals: without `solve_replay_search` the search runs
/// proof-carrying, so no executor is built under the guard. On the full
/// realloc-grow twin that cost 10.2 s of executor time for the 11 UNSAT
/// branches before the SAT one, and a plain solve went `unknown`. With the
/// guard widened over the whole attempt, the acceptance step records a live
/// scope.
#[test]
#[timeout(120_000)]
fn the_replay_search_decides_branches_without_proofs_and_confirms_the_witness() {
    let problem = two_branch_problem("true");
    let built_before = shed_search_executors_built();
    let cex = replay(&problem).expect("x = 44 through the second fact reaches the query");
    assert!(
        shed_search_executors_built() > built_before,
        "the replay's branch decisions must run in a verdict-only search"
    );
    assert_eq!(
        last_acceptance_under_verdict_only(),
        Some(false),
        "the counterexample must be accepted outside the verdict-only scope"
    );
    assert!(
        !verdict_only_search_active(),
        "the verdict-only scope must not outlive the replay"
    );
    assert!(
        cex.ground_derivation.is_some(),
        "acceptance rests on a ground derivation over the clauses"
    );
}

/// Negative twin: with `x < 43` neither branch reaches the query. The
/// verdict-only search decides both branches UNSAT without proofs, and
/// the replay confirms nothing.
#[test]
#[timeout(120_000)]
fn the_replay_search_never_confirms_a_safe_problem() {
    let problem = two_branch_problem("(bvult x #x2b)");
    let built_before = shed_search_executors_built();
    assert!(
        replay(&problem).is_none(),
        "no counterexample exists, so the replay must not confirm one"
    );
    assert!(
        shed_search_executors_built() > built_before,
        "the safe twin's branches are decided in the same verdict-only search"
    );
    assert!(!verdict_only_search_active());
}
