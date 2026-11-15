// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transition validation substitutes away every top-level definition, so a
//! clause-local array pinned to a store chain does not keep the query in the
//! array theory (model-checker-consumer realloc-grow pre-discharge VC, 2026-10-14).

#![allow(clippy::unwrap_used, clippy::panic)]

use super::*;
use crate::pdr::{InvariantModel, PdrConfig, PredicateInterpretation};
use crate::{ChcParser, ChcProblem};
use std::sync::Arc;

fn bv(value: u128, width: u32) -> ChcExpr {
    ChcExpr::BitVec(value, width)
}

fn bv_var(name: &str, width: u32) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(width)))
}

fn op(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn validity_sort() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool))
}

/// `store(const true, 66, true)`: allocation 66 is live.
fn live_66() -> ChcExpr {
    ChcExpr::store(
        ChcExpr::const_array(ChcSort::BitVec(32), ChcExpr::Bool(true)),
        bv(66, 32),
        ChcExpr::Bool(true),
    )
}

/// The transition-validation query of a realloc step: `defs` scalar locals
/// pinned by top-level equalities, THEN the validity array pinned to
/// `live_66()`. The head says the step frees allocation
/// `extract(63, 32, concat(66, 0))` (= 66) and makes 67 live, which equals
/// `live_66()` with `freed` freed and 67 live, and bounds every scalar by
/// `bound`.
fn realloc_step_query(defs: usize, freed: u128, bound: u128) -> ChcExpr {
    let valid = ChcVar::new("obj_valid", validity_sort());
    let mut body: Vec<ChcExpr> = (0..defs)
        .map(|i| ChcExpr::eq(bv_var(&format!("x{i}"), 64), bv(i as u128 + 1, 64)))
        .collect();
    body.push(ChcExpr::eq(ChcExpr::var(valid.clone()), live_66()));
    let object = op(
        ChcOp::BvExtract(63, 32),
        vec![op(ChcOp::BvConcat, vec![bv(66, 32), bv(0, 32)])],
    );
    let after = ChcExpr::store(
        ChcExpr::store(ChcExpr::var(valid), object, ChcExpr::Bool(false)),
        bv(67, 32),
        ChcExpr::Bool(true),
    );
    let expected = ChcExpr::store(
        ChcExpr::store(live_66(), bv(freed, 32), ChcExpr::Bool(false)),
        bv(67, 32),
        ChcExpr::Bool(true),
    );
    let mut head = vec![ChcExpr::eq(after, expected)];
    head.extend((0..defs).map(|i| ChcExpr::bv_ule(bv_var(&format!("x{i}"), 64), bv(bound, 64))));
    ChcExpr::and(ChcExpr::and_all(body), ChcExpr::not(ChcExpr::and_all(head)))
}

fn has_array_var(expr: &ChcExpr) -> bool {
    expr.vars()
        .iter()
        .any(|v| matches!(v.sort, ChcSort::Array(_, _)))
}

/// Counterfactual: with nine definitions ahead of the array's, the former
/// eight-substitution cap left `obj_valid` (and so `store`/`select`) in the
/// query, which then went to the executor and, in the proof-carrying
/// posture, took about a second or came back `unknown`.
#[test]
fn an_array_pinned_after_nine_definitions_is_substituted_away() {
    let query = realloc_step_query(9, 66, 9);
    let (simplified, _) = PdrSolver::simplify_transition_query(query);
    assert!(
        !simplified.contains_array_ops() && !has_array_var(&simplified),
        "the validity array must be substituted away: {simplified}"
    );
    // Every definition substituted, the head folds to `true`: the
    // implication is valid and the query is refuted without a solver.
    assert_eq!(simplified, ChcExpr::Bool(false));
}

/// Negative twin (scalar): a head the body does not imply stays refutable
/// only by a model; substitution must not fold it to `false`.
#[test]
fn a_violated_scalar_head_is_not_refuted_by_substitution() {
    // x8 = 9 violates x8 <= 8.
    let (simplified, _) = PdrSolver::simplify_transition_query(realloc_step_query(9, 66, 8));
    assert_eq!(simplified, ChcExpr::Bool(true));
}

/// Negative twin (array): the head expects allocation 65 freed instead of
/// 66; the two ground store chains differ, so the query is not refuted.
#[test]
fn a_violated_array_head_is_not_refuted_by_substitution() {
    let (simplified, _) = PdrSolver::simplify_transition_query(realloc_step_query(9, 65, 9));
    assert_ne!(simplified, ChcExpr::Bool(false));
    assert!(!has_array_var(&simplified), "{simplified}");
}

/// Allocation 66 freed, then 67 made live; the error reads 67 as dead.
const REALLOC_STEP: &str = r#"(set-logic HORN)
(declare-rel pre ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)
  (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64) (_ BitVec 64)
  (Array (_ BitVec 32) Bool)))
(declare-rel post (Bool (_ BitVec 64)))
(declare-var a (Array (_ BitVec 32) Bool))
(declare-var b (Array (_ BitVec 32) Bool))
(declare-var v Bool)
(declare-var p (_ BitVec 64))
(declare-var x1 (_ BitVec 64))
(declare-var x2 (_ BitVec 64))
(declare-var x3 (_ BitVec 64))
(declare-var x4 (_ BitVec 64))
(declare-var x5 (_ BitVec 64))
(declare-var x6 (_ BitVec 64))
(declare-var x7 (_ BitVec 64))
(declare-var x8 (_ BitVec 64))
(declare-var x9 (_ BitVec 64))
(rule (=> (and (= x1 #x0000000000000001) (= x2 #x0000000000000002) (= x3 #x0000000000000003)
               (= x4 #x0000000000000004) (= x5 #x0000000000000005) (= x6 #x0000000000000006)
               (= x7 #x0000000000000007) (= x8 #x0000000000000008) (= x9 #x0000000000000009)
               (= p #x0000004200000000)
               (= a (store ((as const (Array (_ BitVec 32) Bool)) true) #x00000042 true)))
          (pre x1 x2 x3 x4 x5 x6 x7 x8 x9 p a)))
(rule (=> (and (pre x1 x2 x3 x4 x5 x6 x7 x8 x9 p a)
               (= b (store (store a ((_ extract 63 32) p) false) #x00000043 true))
               (= v (select b #x00000043)))
          (post v p)))
(rule (=> (and (post v p) (not v)) false))"#;

/// `pre`: the nine scalars and `p` pinned, then the array; `post`: the
/// liveness of 67 is `live`.
fn realloc_step_model(problem: &ChcProblem, live: bool) -> InvariantModel {
    let pre = problem.lookup_predicate("pre").unwrap();
    let post = problem.lookup_predicate("post").unwrap();
    let mut pre_vars: Vec<ChcVar> = (1..=9)
        .map(|i| ChcVar::new(format!("pre_x{i}"), ChcSort::BitVec(64)))
        .collect();
    pre_vars.push(ChcVar::new("pre_p", ChcSort::BitVec(64)));
    let pre_a = ChcVar::new("pre_a", validity_sort());
    let mut pre_facts: Vec<ChcExpr> = (1..=9u128)
        .zip(&pre_vars)
        .map(|(value, var)| ChcExpr::eq(ChcExpr::var(var.clone()), bv(value, 64)))
        .collect();
    pre_facts.push(ChcExpr::eq(
        ChcExpr::var(pre_vars[9].clone()),
        bv(0x42_0000_0000, 64),
    ));
    pre_facts.push(ChcExpr::eq(ChcExpr::var(pre_a.clone()), live_66()));
    pre_vars.push(pre_a);
    let post_v = ChcVar::new("post_v", ChcSort::Bool);
    let post_p = ChcVar::new("post_p", ChcSort::BitVec(64));
    let liveness = if live {
        ChcExpr::var(post_v.clone())
    } else {
        ChcExpr::not(ChcExpr::var(post_v.clone()))
    };
    let post_fact = ChcExpr::and(
        liveness,
        ChcExpr::eq(ChcExpr::var(post_p.clone()), bv(0x42_0000_0000, 64)),
    );
    let mut model = InvariantModel::new();
    model.set(
        pre,
        PredicateInterpretation::new(pre_vars, ChcExpr::and_all(pre_facts)),
    );
    model.set(
        post,
        PredicateInterpretation::new(vec![post_v, post_p], post_fact),
    );
    model
}

/// Per-rule validation on the ORIGINAL clauses, as the adaptive boundary runs
/// it for a back-translated model (no array scalarization).
fn validates(model: &InvariantModel, problem: &ChcProblem) -> bool {
    let config = PdrConfig {
        disable_array_scalarization: true,
        preserve_original_clauses: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem.clone(), config);
    verifier.verify_model_per_rule(model, std::time::Duration::from_secs(10))
}

#[test]
fn a_straight_line_model_over_a_pinned_array_validates() {
    let problem = ChcParser::parse(REALLOC_STEP).unwrap();
    assert!(validates(&realloc_step_model(&problem, true), &problem));
}

/// Negative twin: the model claims 67 dead after the step; the transition
/// makes it live, so the model must be refused.
#[test]
fn a_model_violated_through_the_pinned_array_is_refused() {
    let problem = ChcParser::parse(REALLOC_STEP).unwrap();
    assert!(!validates(&realloc_step_model(&problem, false), &problem));
}

/// `p` holds 0; the transition defines `y14` from `p`'s value through a chain
/// of increments listed from the last link back to the first.
const REVERSE_CHAIN: &str = r#"(set-logic HORN)
(declare-rel p ((_ BitVec 8)))
(declare-rel q ((_ BitVec 8)))
(declare-var x (_ BitVec 8))
(declare-var y0 (_ BitVec 8))
(declare-var y1 (_ BitVec 8))
(declare-var y2 (_ BitVec 8))
(declare-var y3 (_ BitVec 8))
(declare-var y4 (_ BitVec 8))
(declare-var y5 (_ BitVec 8))
(declare-var y6 (_ BitVec 8))
(declare-var y7 (_ BitVec 8))
(declare-var y8 (_ BitVec 8))
(declare-var y9 (_ BitVec 8))
(declare-var y10 (_ BitVec 8))
(declare-var y11 (_ BitVec 8))
(declare-var y12 (_ BitVec 8))
(declare-var y13 (_ BitVec 8))
(declare-var y14 (_ BitVec 8))
(rule (=> (= x #x00) (p x)))
(rule (=> (and (p x)
               (= y14 (bvadd y13 #x01)) (= y13 (bvadd y12 #x01)) (= y12 (bvadd y11 #x01)) (= y11 (bvadd y10 #x01))
               (= y10 (bvadd y9 #x01)) (= y9 (bvadd y8 #x01)) (= y8 (bvadd y7 #x01)) (= y7 (bvadd y6 #x01))
               (= y6 (bvadd y5 #x01)) (= y5 (bvadd y4 #x01)) (= y4 (bvadd y3 #x01)) (= y3 (bvadd y2 #x01))
               (= y2 (bvadd y1 #x01)) (= y1 (bvadd y0 #x01))
               (= y0 x))
          (q y14)))
(rule (=> (and (q x) (not (= x #x0e))) false))"#;

/// `p` is `x = 0` and `q` is `x = q_value`.
fn reverse_chain_model(problem: &ChcProblem, q_value: u128) -> InvariantModel {
    let mut model = InvariantModel::new();
    for (name, value) in [("p", 0), ("q", q_value)] {
        let pred = problem.lookup_predicate(name).unwrap();
        let var = ChcVar::new(format!("{name}_x"), ChcSort::BitVec(8));
        let fact = ChcExpr::eq(ChcExpr::var(var.clone()), bv(value, 8));
        model.set(pred, PredicateInterpretation::new(vec![var], fact));
    }
    model
}

/// The transition query folds to a constant once its sixteen definitions are
/// substituted, so a refuting model of it names no variable. The failure's
/// post-state must still be the real successor (`y14 = 14`), named again
/// from the elimination's trail in one pass. Re-deriving the chain from the
/// raw query alone takes one fixpoint pass per link, and past eight passes
/// the reconstruction's debug assertion panicked.
#[test]
fn a_reverse_listed_chain_names_the_successor_of_a_refuting_model() {
    let problem = ChcParser::parse(REVERSE_CHAIN).unwrap();
    assert!(validates(&reverse_chain_model(&problem, 14), &problem));
    let config = PdrConfig {
        disable_array_scalarization: true,
        preserve_original_clauses: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem.clone(), config);
    let (_, pre, _, post) = verifier
        .verify_model_fresh_with_failure(&reverse_chain_model(&problem, 13))
        .unwrap();
    let state_value = |state: &ChcExpr| match state {
        ChcExpr::Op(ChcOp::Eq, args) => match args[1].as_ref() {
            ChcExpr::BitVec(value, 8) => *value,
            other => panic!("state value {other}"),
        },
        other => panic!("state {other}"),
    };
    assert_eq!(state_value(&pre), 0);
    assert_eq!(state_value(&post), 14);
}
