// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! Regression tests for CHC issue #1615.
//!
//! This module tests benchmarks that regressed from SAT to timeout after Entry-CEGAR.
//! LocalVarEliminator unit tests moved to transform/local_var_elimination.rs (#3627).
//!
//! Part of #1615: CHC regression 27/55 to 21/55 after Entry-CEGAR

#[cfg(not(debug_assertions))]
use ay_chc::ChcParser;
#[cfg(not(debug_assertions))]
use ay_chc::{testing, EngineConfig, PdrConfig, PortfolioConfig, PortfolioResult};
#[cfg(not(debug_assertions))]
use std::time::Duration;

#[cfg(not(debug_assertions))]
fn parse_problem(smt: &str) -> ay_chc::ChcProblem {
    let problem =
        ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("CHC validation failed: {err}\nSMT2:\n{smt}"));
    problem
}

/// dtuc_000.smt2 - Two-phase counter with phase transfer
#[cfg(not(debug_assertions))]
const DTUC_000: &str = r#"(set-logic HORN)
(declare-fun |FUN| ( Int Int Int Int ) Bool)
(declare-fun |SAD| ( Int Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (and (= A 0) (= C 0))) (FUN A B C D))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) (=> (and (FUN A D B F) (and (= C (+ 1 A)) (not (<= F A)) (= E (+ 1 B)))) (FUN C D E F))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (FUN B A D E) (and (= B E) (= C E))) (SAD B C D E))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) (=> (and (SAD C B A F) (and (= D (+ (- 1) B)) (not (<= B 0)) (= E (+ (- 1) A)))) (SAD C D E F))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (SAD A C D B) (and (not (<= C 0)) (<= D 0))) false)))
(check-sat)
"#;

/// s_mutants_16_m_000.smt2 - Mutant counter pattern
#[cfg(not(debug_assertions))]
const S_MUTANTS_16_M_000: &str = r#"(set-logic HORN)
(declare-fun |itp| ( Int Int Int ) Bool)
(declare-fun |itp1| ( Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (and (= A 0) (not (<= 5 C)) (not (<= C 0)) (= B (* 3 C)))) (itp A B C))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (itp A B E) (and (= C (+ 1 A)) (not (<= 100 A)) (= D (+ 1 B)))) (itp C D E))))
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (itp A B C) (<= 100 A)) (itp1 A B C))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (itp1 A B E) (and (= C (+ 1 A)) (not (<= 120 A)) (= D (+ 1 B)))) (itp1 C D E))))
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (itp1 B C A) (and (or (not (<= C 132)) (not (>= C 3))) (<= 120 B))) false)))
(check-sat)
"#;

/// three_dots_moving_2_000.smt2 - Three moving points
#[cfg(not(debug_assertions))]
const THREE_DOTS_MOVING_2_000: &str = r#"(set-logic HORN)
(declare-fun |inv| ( Int Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (and (>= D (+ B (* (- 1) C))) (>= D (+ B (* (- 1) A))) (not (<= B A)) (>= D (+ C (* (- 2) A) B)))) (inv A B C D))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) (=> (and (inv B C F A) (let ((a!1 (and (= D (ite (<= B F) (+ 1 B) (+ (- 1) B))) (= E D) (= B C)))) (let ((a!2 (or (and (= D B) (= E (+ (- 1) C)) (not (= B C))) a!1))) (and (= G (+ (- 1) A)) a!2 (not (= C F)))))) (inv D E F G))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (inv A B C D) (and (<= D 0) (not (= B C)))) false)))
(check-sat)
"#;

#[cfg(not(debug_assertions))]
fn production_pdr_config() -> PdrConfig {
    let mut config = PdrConfig::production(false);
    config.max_frames = 50;
    config.max_iterations = 10_000;
    config.max_obligations = 100_000;
    config
}

#[cfg(not(debug_assertions))]
fn portfolio_config_with_preprocessing() -> PortfolioConfig {
    let pdr = production_pdr_config();
    PortfolioConfig::with_engines(vec![EngineConfig::Pdr(pdr.clone()), EngineConfig::Pdr(pdr)])
        .parallel_timeout(Some(Duration::from_secs(60)))
}

/// Regression: dtuc_000 should not return Unsafe (issue #1615)
/// This benchmark solves quickly (~1s) and must return Safe.
#[test]
#[cfg(not(debug_assertions))]
fn regression_dtuc_not_unsafe() {
    let problem = parse_problem(DTUC_000);
    let solver = testing::new_portfolio_solver(problem, portfolio_config_with_preprocessing());
    let result = solver.solve();
    assert!(
        matches!(&result, PortfolioResult::Safe(_)),
        "dtuc expected Safe, got: {result}"
    );
}

/// Regression: s_mutants_16_m_000 should not return Unsafe (issue #1615)
/// Solver has 60s internal timeout - test just verifies no false Unsafe.
///
/// Weak assertion intentional: this is a hard CHC-COMP benchmark that may
/// genuinely timeout (Unknown). The guard catches soundness regressions
/// (false Unsafe) without failing on expected timeouts. (#2493, #3868)
#[test]
#[cfg(not(debug_assertions))]
fn regression_s_mutants_not_unsafe() {
    let problem = parse_problem(S_MUTANTS_16_M_000);
    let solver = testing::new_portfolio_solver(problem, portfolio_config_with_preprocessing());
    let result = solver.solve();
    assert!(
        !matches!(&result, PortfolioResult::Unsafe(_)),
        "s_mutants REGRESSION: returned Unsafe, which is a soundness bug"
    );
}

/// Regression: three_dots_moving_2_000 should not return Unsafe (issue #1615)
/// Solver has 60s internal timeout - test just verifies no false Unsafe.
///
/// Weak assertion intentional: this is a hard CHC-COMP benchmark that may
/// genuinely timeout (Unknown). The guard catches soundness regressions
/// (false Unsafe) without failing on expected timeouts. (#2493, #3868)
#[test]
#[cfg(not(debug_assertions))]
fn regression_three_dots_not_unsafe() {
    let problem = parse_problem(THREE_DOTS_MOVING_2_000);
    let solver = testing::new_portfolio_solver(problem, portfolio_config_with_preprocessing());
    let result = solver.solve();
    assert!(
        !matches!(&result, PortfolioResult::Unsafe(_)),
        "three_dots REGRESSION: returned Unsafe, which is a soundness bug"
    );
}
