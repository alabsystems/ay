// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for multi-predicate chain safety (#pdr-chain).
//!
//! PDR used to return Unknown on trivial acyclic predicate chains
//! (Init => P1, P1 /\ step => P2, ..., Pn /\ bad => false) under the
//! spacer-mode config, while the 1-predicate version solved Safe. Root
//! cause: `ImplicationCache::blocking_countermodels` kept
//! counterexample-to-inductiveness states recorded against *older, weaker*
//! frame constraints. Blocking the head POB records such a state; the
//! predecessor then gets its own frame lemma (strengthening the frame); the
//! retried head lemma — now genuinely inductive — was fast-rejected by the
//! stale cached state at every level until max_frames. Frame-epoch
//! invalidation (`note_frame_epoch`) fixes this.
//!
//! This capped every predicate-splitting transform (SPLIT-SYM, PC-SPLIT,
//! CONDENSE output shapes) whose output is a predicate chain.

use super::*;
use crate::pdr::PdrResult;

const CHAIN2_LIA: &str = r#"
(set-logic HORN)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P1 x))))
(assert (forall ((x Int) (y Int)) (=> (and (P1 x) (= y (+ x 1))) (P2 y))))
(assert (forall ((x Int)) (=> (and (P2 x) (< x 0)) false)))
(check-sat)
"#;

const CHAIN3_LIA: &str = r#"
(set-logic HORN)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int) Bool)
(declare-fun P3 (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P1 x))))
(assert (forall ((x Int) (y Int)) (=> (and (P1 x) (= y (+ x 1))) (P2 y))))
(assert (forall ((x Int) (y Int)) (=> (and (P2 x) (= y (+ x 1))) (P3 y))))
(assert (forall ((x Int)) (=> (and (P3 x) (< x 0)) false)))
(check-sat)
"#;

const CHAIN4_LIA: &str = r#"
(set-logic HORN)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int) Bool)
(declare-fun P3 (Int) Bool)
(declare-fun P4 (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P1 x))))
(assert (forall ((x Int) (y Int)) (=> (and (P1 x) (= y (+ x 1))) (P2 y))))
(assert (forall ((x Int) (y Int)) (=> (and (P2 x) (= y (+ x 1))) (P3 y))))
(assert (forall ((x Int) (y Int)) (=> (and (P3 x) (= y (+ x 1))) (P4 y))))
(assert (forall ((x Int)) (=> (and (P4 x) (< x 0)) false)))
(check-sat)
"#;

/// Same 3-predicate chain but stepping DOWN: P3 reaches x = -2 and the
/// query (P3 x /\ x < 0) is satisfiable. Pins against a false-Safe: the
/// chain fix may only make PDR try harder, never accept a bogus model.
const CHAIN3_LIA_UNSAFE: &str = r#"
(set-logic HORN)
(declare-fun P1 (Int) Bool)
(declare-fun P2 (Int) Bool)
(declare-fun P3 (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P1 x))))
(assert (forall ((x Int) (y Int)) (=> (and (P1 x) (= y (- x 1))) (P2 y))))
(assert (forall ((x Int) (y Int)) (=> (and (P2 x) (= y (- x 1))) (P3 y))))
(assert (forall ((x Int)) (=> (and (P3 x) (< x 0)) false)))
(check-sat)
"#;

const CHAIN3_BV32: &str = r#"
(set-logic HORN)
(declare-fun P1 ((_ BitVec 32)) Bool)
(declare-fun P2 ((_ BitVec 32)) Bool)
(declare-fun P3 ((_ BitVec 32)) Bool)
(assert (forall ((x (_ BitVec 32))) (=> (= x #x00000000) (P1 x))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (and (P1 x) (= y (bvor x #x00000001))) (P2 y))))
(assert (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
  (=> (and (P2 x) (= y (bvor x #x00000002))) (P3 y))))
(assert (forall ((x (_ BitVec 32))) (=> (and (P3 x) (= x #xffffffff)) false)))
(check-sat)
"#;

fn solve_with(smt2: &str, config: PdrConfig) -> PdrResult {
    let problem = ChcParser::parse(smt2).expect("chain fixture must parse");
    let mut solver = PdrSolver::new(problem, config);
    solver.solve()
}

/// The spacer-mode portfolio variant skips startup discovery, so safety must
/// come from the blocking loop itself — the config that exposed the stale
/// countermodel-cache stall (#pdr-chain).
fn spacer_config() -> PdrConfig {
    PdrConfig::portfolio_spacer_variant()
}

#[test]
fn spacer_variant_proves_2_predicate_chain_safe() {
    let result = solve_with(CHAIN2_LIA, spacer_config());
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "trivial 2-predicate chain must be proven Safe, got {result:?}"
    );
}

#[test]
fn spacer_variant_proves_3_predicate_chain_safe() {
    let result = solve_with(CHAIN3_LIA, spacer_config());
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "trivial 3-predicate chain must be proven Safe, got {result:?}"
    );
}

#[test]
fn spacer_variant_proves_4_predicate_chain_safe() {
    let result = solve_with(CHAIN4_LIA, spacer_config());
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "trivial 4-predicate chain must be proven Safe, got {result:?}"
    );
}

#[test]
fn spacer_variant_proves_3_predicate_bv32_chain_safe() {
    let result = solve_with(CHAIN3_BV32, spacer_config());
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "trivial 3-predicate BV32 chain must be proven Safe, got {result:?}"
    );
}

#[test]
fn default_config_proves_3_predicate_chain_safe() {
    let result = solve_with(CHAIN3_LIA, PdrConfig::default());
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "trivial 3-predicate chain must be proven Safe under default config, got {result:?}"
    );
}

#[test]
fn buggy_3_predicate_chain_stays_unsafe_spacer_variant() {
    let result = solve_with(CHAIN3_LIA_UNSAFE, spacer_config());
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "buggy 3-predicate chain must stay Unsafe (no false-Safe pin), got {result:?}"
    );
}

#[test]
fn buggy_3_predicate_chain_stays_unsafe_default_config() {
    let result = solve_with(CHAIN3_LIA_UNSAFE, PdrConfig::default());
    assert!(
        matches!(result, PdrResult::Unsafe(_)),
        "buggy 3-predicate chain must stay Unsafe under default config, got {result:?}"
    );
}
