// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used, clippy::panic)]
use super::*;
use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
use crate::pdr::{CexVerificationResult, PdrConfig, PdrSolver};
use crate::{ClauseBody, ClauseHead, HornClause};
use ay_test_support::env::{lock_env, ScopedEnvVar};
use ntest::timeout;

fn create_large_acyclic_int_chain_for_exact_first_9004(pred_count: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let preds: Vec<_> = (0..pred_count)
        .map(|idx| problem.declare_predicate(&format!("ExactFirst{idx}"), vec![ChcSort::Int]))
        .collect();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(preds[0], vec![ChcExpr::int(0)]),
    ));

    for idx in 1..preds.len() {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(preds[idx - 1], vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(
                preds[idx],
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                *preds
                    .last()
                    .expect("exact-first chain has a tail predicate"),
                vec![ChcExpr::var(x.clone())],
            )],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(10_000))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_large_acyclic_bmc_prefers_exact_executor_before_concrete_prepass_9004() {
    let solver = BmcSolver::new(
        create_large_acyclic_int_chain_for_exact_first_9004(129),
        BmcConfig {
            max_depth: 129,
            acyclic_safe: true,
            ..BmcConfig::default()
        },
    );
    assert!(
        solver.prefer_exact_acyclic_executor_first(),
        "large acyclic-safe CHCs should enter the exact executor before concrete scalar BMC"
    );

    let small_solver = BmcSolver::new(
        create_large_acyclic_int_chain_for_exact_first_9004(128),
        BmcConfig {
            max_depth: 128,
            acyclic_safe: true,
            ..BmcConfig::default()
        },
    );
    assert!(
        !small_solver.prefer_exact_acyclic_executor_first(),
        "the exact-first routing is reserved for large acyclic CHC graphs by default"
    );

    let forced_small_solver = BmcSolver::new(
        create_large_acyclic_int_chain_for_exact_first_9004(2),
        BmcConfig {
            max_depth: 2,
            acyclic_safe: true,
            prefer_exact_acyclic_first: true,
            ..BmcConfig::default()
        },
    );
    assert!(
        forced_small_solver.prefer_exact_acyclic_executor_first(),
        "proof lanes can explicitly request exact acyclic expansion for small graphs"
    );

    let adaptive_solver = BmcSolver::new(
        create_large_acyclic_int_chain_for_exact_first_9004(129),
        BmcConfig {
            max_depth: 129,
            acyclic_safe: true,
            enable_adaptive_stepping: true,
            ..BmcConfig::default()
        },
    );
    assert!(
        !adaptive_solver.prefer_exact_acyclic_executor_first(),
        "adaptive stepping keeps its existing route"
    );
}

#[test]
fn test_bmc_simplifies_model_checker_consumer_slice_offset_bv_identities_9227() {
    let start = ChcExpr::var(ChcVar::new("start", ChcSort::BitVec(64)));
    let end = ChcExpr::var(ChcVar::new("end", ChcSort::BitVec(64)));
    let base = ChcExpr::BitVec(0x0000_0002_0000_0000, 64);
    let encoded_slice = ChcExpr::Op(
        ChcOp::BvConcat,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::BvSub,
                vec![Arc::new(end), Arc::new(start.clone())],
            )),
            Arc::new(ChcExpr::Op(
                ChcOp::BvAdd,
                vec![
                    Arc::new(base.clone()),
                    Arc::new(ChcExpr::Op(
                        ChcOp::BvMul,
                        vec![
                            Arc::new(ChcExpr::Op(
                                ChcOp::BvAdd,
                                vec![Arc::new(ChcExpr::BitVec(0, 64)), Arc::new(start.clone())],
                            )),
                            Arc::new(ChcExpr::BitVec(1, 64)),
                        ],
                    )),
                ],
            )),
        ],
    );
    let slice_offset = ChcExpr::Op(
        ChcOp::BvSDiv,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::BvSub,
                vec![
                    Arc::new(ChcExpr::Op(
                        ChcOp::BvExtract(63, 0),
                        vec![Arc::new(encoded_slice)],
                    )),
                    Arc::new(base),
                ],
            )),
            Arc::new(ChcExpr::BitVec(1, 64)),
        ],
    );

    assert_eq!(BmcSolver::simplify_bmc_expr(slice_offset), start);
}

#[test]
fn test_bmc_legacy_datatype_unsafe_downgraded_unknown() {
    let smt = r#"
(set-logic HORN)
(declare-datatype Box ((Box_mk (box_val Int))))
(declare-fun P (Box) Bool)
(assert (P (Box_mk 0)))
(assert (forall ((b Box)) (=> (and (P b) (= (box_val b) 0)) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(0)
            .with_acyclic_safe(true),
    );
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "legacy fallback Unsafe on datatype CHCs is conservatively downgraded, got {result:?}"
    );
    assert!(
        solver.stats().used_legacy_fallback,
        "regression must exercise the legacy fallback path"
    );
    assert!(
        solver.problem_uses_datatype_features(),
        "datatype features in encoded CHCs must keep the legacy Unsafe downgrade armed"
    );
}

#[test]
fn test_bmc_only_complex_query_unsat_fact_demotes_unknown_8865() {
    let smt = r#"
(set-logic HORN)
(declare-rel P ((_ BitVec 32)))
(rule (=> false (P #x00000000)))
(query P)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    assert_eq!(problem.facts().count(), 0);
    assert_eq!(problem.transitions().count(), 0);
    assert_eq!(problem.queries().count(), 1);
    assert!(problem.has_complex_query_only_vacuous_safety_shape());

    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig::default()
            .with_max_depth(1)
            .with_acyclic_safe(true),
    );
    let raw_result = solver.solve();
    assert!(
        matches!(raw_result, ChcEngineResult::Unknown),
        "raw acyclic-safe BMC must fail closed for complex unsat facts, got {raw_result:?}"
    );

    let verified_result = crate::engines::solve_bmc_only(
        problem,
        BmcConfig::default()
            .with_max_depth(1)
            .with_acyclic_safe(true),
    );
    assert!(
        matches!(verified_result, crate::VerifiedChcResult::Unknown(_)),
        "public BMC-only API must not expose a vacuous proof, got {verified_result:?}"
    );
}

#[test]
fn test_bmc_model_witness_verifies_multi_predicate_bool_guard_9604() {
    let smt = r#"
(set-logic HORN)
(declare-fun Base (Int Bool) Bool)
(declare-fun Mid (Int Bool) Bool)
(declare-fun Bad (Bool) Bool)

(assert (forall ((n Int) (b Bool) (v Bool))
    (=> (and (not b) (= v false)) (Base n v))))
(assert (forall ((n Int) (b Bool) (v Bool))
    (=> (and (= b true) (= v true)) (Base n v))))
(assert (forall ((n Int) (flag Bool) (c Int))
    (=> (and (Base n flag) (not (= (<= c 0) flag)) (= n (+ c 1)))
        (Mid c flag))))
(assert (forall ((x Int) (flag Bool))
    (=> (and (Mid x flag) (= x 0)) (Bad flag))))
(assert (forall ((flag Bool))
    (=> (and (Bad flag) (= flag false)) false)))

(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(problem.clone(), BmcConfig::default().with_max_depth(3));

    let ChcEngineResult::Unsafe(cex) = solver.solve() else {
        panic!("expected BMC to find the reachable query");
    };
    assert!(
        cex.witness.is_some(),
        "multi-predicate BMC Unsafe must carry a derivation witness"
    );

    let mut verifier = crate::PdrSolver::new(problem, crate::PdrConfig::default());
    assert_eq!(
        verifier.verify_counterexample(&cex),
        crate::CexVerificationResult::Valid,
        "BMC witness must validate against the source CHC"
    );
}

#[test]
fn test_bmc_bv_model_witness_verifies_original_trace() {
    let smt = r#"
(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(declare-fun Q ((_ BitVec 8)) Bool)

(assert (P #x00))
(assert (forall ((x (_ BitVec 8)))
    (=> (and (P x) (= x #x00)) (Q (bvadd x #x01)))))
(assert (forall ((y (_ BitVec 8)))
    (=> (and (Q y) (= y #x01)) false)))

(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(problem.clone(), BmcConfig::default().with_max_depth(2));

    let ChcEngineResult::Unsafe(cex) = solver.solve() else {
        panic!("expected BMC to find the reachable BV query");
    };
    assert!(
        cex.witness.is_some(),
        "BV BMC Unsafe must carry a derivation witness for source validation"
    );

    let mut verifier = crate::PdrSolver::new(problem, crate::PdrConfig::default());
    assert_eq!(
        verifier.verify_counterexample(&cex),
        crate::CexVerificationResult::Valid,
        "BV BMC witness must validate against the original CHC"
    );
}

#[test]
fn test_bmc_deep_bv_linear_witness_verifies_original_trace() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv ((_ BitVec 8)) Bool)

(assert (Inv #x00))
(assert (forall ((x (_ BitVec 8)))
    (=> (Inv x) (Inv (bvadd x #x01)))))
(assert (forall ((x (_ BitVec 8)))
    (=> (and (Inv x) (= x #x46)) false)))

(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 80,
            ..BmcConfig::default()
        },
    );

    let ChcEngineResult::Unsafe(cex) = solver.solve() else {
        panic!("expected BMC to find the deeper reachable BV-linear query");
    };
    assert!(
        cex.witness.is_some(),
        "deep BV-linear BMC Unsafe must carry a derivation witness for source validation"
    );

    let mut verifier = crate::PdrSolver::new(problem, crate::PdrConfig::default());
    assert_eq!(
        verifier.verify_counterexample(&cex),
        crate::CexVerificationResult::Valid,
        "deep BV-linear BMC witness must validate against the original CHC"
    );
}

#[test]
fn test_bmc_bv_scalar_mul_linear_witness_verifies_original_trace() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv ((_ BitVec 8)) Bool)

(assert (Inv #x00))
(assert (forall ((x (_ BitVec 8)))
    (=> (Inv x) (Inv (bvadd x #x01)))))
(assert (forall ((x (_ BitVec 8)))
    (=> (and (Inv x)
             (= (bvadd #x03 (bvmul #xff x)) #x00))
        false)))

(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 4,
            per_depth_timeout: Some(std::time::Duration::from_secs(1)),
            time_budget: Some(std::time::Duration::from_secs(10)),
            ..BmcConfig::default()
        },
    );

    let ChcEngineResult::Unsafe(cex) = solver.solve() else {
        panic!("expected BMC to find the scalar-mul BV-linear query");
    };
    assert!(
        cex.witness.is_some(),
        "scalar-mul BV-linear BMC Unsafe must carry a derivation witness"
    );

    let mut verifier = crate::PdrSolver::new(problem, crate::PdrConfig::default());
    assert_eq!(
        verifier.verify_counterexample(&cex),
        crate::CexVerificationResult::Valid,
        "scalar-mul BV-linear BMC witness must validate against the original CHC"
    );
}

#[test]
fn test_bmc_legacy_datatype_guard_ignores_unused_declaration() {
    let smt = r#"
(set-logic HORN)
(declare-datatype Box ((Box_mk (box_val Int))))
(declare-fun P (Int) Bool)
(assert (P 0))
(assert (forall ((x Int)) (=> (and (P x) (= x 0)) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    assert!(
        !problem.datatype_defs().is_empty(),
        "regression must include a parsed datatype declaration"
    );
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(0)
            .with_acyclic_safe(true),
    );
    assert!(
        !solver.problem_uses_datatype_features(),
        "unused datatype declarations must not trigger the legacy Unsafe downgrade"
    );

    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "unused datatype declarations must not downgrade a real Unsafe result, got {result:?}"
    );
}

#[test]
fn test_bmc_legacy_datatype_predicate_sort_keeps_guard_armed() {
    let smt = r#"
(set-logic HORN)
(declare-datatype Box ((Box_mk (box_val Int))))
(declare-fun P (Box) Bool)
(assert (forall ((b Box)) (P b)))
(assert (forall ((b Box)) (=> (P b) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(0)
            .with_acyclic_safe(true),
    );
    assert!(
        solver.problem_uses_datatype_features(),
        "datatype-sorted predicates must keep the legacy Unsafe downgrade armed"
    );
}

#[test]
fn test_bmc_legacy_datatype_array_sort_keeps_guard_armed() {
    let smt = r#"
(set-logic HORN)
(declare-datatype Box ((Box_mk (box_val Int))))
(declare-fun P ((Array Int Box)) Bool)
(assert (forall ((a (Array Int Box))) (P a)))
(assert (forall ((a (Array Int Box))) (=> (P a) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(0)
            .with_acyclic_safe(true),
    );
    assert!(
        solver.problem_uses_datatype_features(),
        "datatype nested in array predicate sorts must keep the guard armed"
    );
}

#[test]
fn test_bmc_legacy_scalar_const_array_with_unused_datatype_decl_not_armed() {
    // A declared-but-unused datatype must not arm the legacy Unsafe
    // downgrade just because a clause contains a purely scalar const array
    // (the previous blanket guard fired on ANY declaration; model-checker-consumer systems
    // always declare Option/Tuple datatypes even when unused).
    let smt = r#"
(set-logic HORN)
(declare-datatype Box ((Box_mk (box_val Int))))
(declare-fun P ((Array Int Int)) Bool)
(assert (forall ((a (Array Int Int))) (=> (= a ((as const (Array Int Int)) 0)) (P a))))
(assert (forall ((a (Array Int Int))) (=> (P a) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    assert!(
        !problem.datatype_defs().is_empty(),
        "regression must include a parsed datatype declaration"
    );
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(0)
            .with_acyclic_safe(true),
    );
    assert!(
        !solver.problem_uses_datatype_features(),
        "scalar const arrays with unused datatype declarations must not arm the guard"
    );
}

#[test]
fn test_bmc_legacy_datatype_valued_const_array_keeps_guard_armed() {
    let smt = r#"
(set-logic HORN)
(declare-datatype Box ((Box_mk (box_val Int))))
(declare-fun P (Int) Bool)
(assert (forall ((a (Array Int Box)) (x Int))
  (=> (= a ((as const (Array Int Box)) (Box_mk 0))) (P x))))
(assert (forall ((x Int)) (=> (P x) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(0)
            .with_acyclic_safe(true),
    );
    assert!(
        solver.problem_uses_datatype_features(),
        "datatype-valued const arrays must keep the legacy Unsafe downgrade armed"
    );
}

#[test]
fn test_bmc_executor_rejects_arithmetic_lt_on_bv_unknown_not_panic() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv ((_ BitVec 8)) Bool)
(assert (Inv #x00))
(assert (forall ((x (_ BitVec 8))) (=> (and (Inv x) (< x #x01)) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(problem, BmcConfig::default().with_max_depth(0));

    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "BMC executor should degrade unsupported BV arithmetic comparison to Unknown, got {result:?}",
    );
    assert!(
        solver.stats().used_executor_path,
        "regression should stop at the executor preflight boundary"
    );
    assert!(
        !solver.stats().used_legacy_fallback,
        "unsupported executor terms should not be handed to the legacy fallback"
    );
}
fn create_simple_unsafe_problem() -> ChcProblem {
    // A simple unsafe problem:
    // x = 0 => Inv(x)
    // Inv(x) => Inv(x + 1)
    // Inv(x) ∧ x >= 5 => false
    //
    // This is unsafe because starting from x=0, we reach x=5 in 5 steps
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) ∧ x >= 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_safe_problem() -> ChcProblem {
    // A safe problem:
    // x = 0 => Inv(x)
    // Inv(x) ∧ x < 3 => Inv(x + 1)
    // Inv(x) ∧ x >= 10 => false
    //
    // This is safe because x never exceeds 3
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) ∧ x < 3 => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) ∧ x >= 10 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Test BMC finds counterexample in unsafe problem with body predicate
///
/// With the level-based encoding (#108), BMC correctly handles body predicates.
/// This problem has:
/// - x = 0 => Inv(x)
/// - Inv(x) => Inv(x + 1)
/// - Inv(x) ∧ x >= 5 => false
///
/// BMC should find counterexample at depth 5 (5 transitions from x=0 to x=5)
#[test]
fn test_bmc_finds_unsafe_with_body_predicate() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            // BMC correctly finds counterexample
            // Level-based encoding finds counterexample at depth 6:
            // - Level 0: fact establishes Inv(0)
            // - Levels 1-5: transitions Inv(k) => Inv(k+1)
            // - Level 6: query Inv(x) ∧ x >= 5 checked (first level where x=5 is reachable)
            assert!(
                cex.steps.len() <= 11,
                "Expected depth <= 10, got {}",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample with level-based encoding (#108)");
        }
    }
}

/// Test BMC returns Unknown for safe problem
///
/// This problem is safe because x never exceeds 3, but BMC returns Unknown
/// (no counterexample found within bounds).
#[test]
fn test_bmc_unknown_for_safe_problem() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unknown => {
            // Expected - no counterexample within bounds for safe problem
        }
        ChcEngineResult::Unsafe(cex) => {
            panic!(
                "BMC incorrectly reported unsafe at depth {} for safe problem",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC returned unexpected result: {result:?}");
        }
    }
}

/// Test BMC finds counterexample at depth 0
///
/// When the initial state immediately violates the query, BMC should find it.
#[test]
fn test_bmc_finds_depth_0_counterexample() {
    // x = 5 => Inv(x)
    // Inv(x) ∧ x >= 5 => false
    //
    // Initial state x=5 immediately satisfies the query constraint.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 5,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            // BMC finds counterexample at depth 0 (1 step in trace)
            assert!(
                cex.steps.len() <= 1,
                "Expected counterexample at depth 0, got {} steps",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample at depth 0");
        }
    }
}

/// Test BMC on a problem where query has NO body predicate.
#[test]
fn test_bmc_bodyless_query_without_replayable_witness_demotes_unknown() {
    // Query: x >= 5 => false (NO body predicate)
    // This is a degenerate case: the query constraint can be satisfied without
    // deriving any source predicate fact, so BMC has no replayable original
    // predicate-vocabulary witness to emit.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: x >= 5 => false (NO Inv(x) in body!)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ClauseHead::False,
    ));

    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "bodyless query SAT must not be accepted without a replayable witness, got {result:?}"
    );
}

#[test]
fn test_bmc_spurious_extracted_witness_demotes_unknown() {
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(pred, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    let solver = BmcSolver::new(problem, BmcConfig::default().with_max_depth(0));
    let (instances, state) = solver
        .concrete_state_witness(pred, &[0])
        .expect("test predicate state should be representable");
    let witness = DerivationWitness {
        query_clause: Some(1),
        root: 0,
        entries: vec![DerivationWitnessEntry {
            predicate: pred,
            level: 0,
            state,
            incoming_clause: Some(0),
            premises: Vec::new(),
            instances,
        }],
    };

    let result = solver.verified_unsafe_from_witness(witness, "test spurious witness");

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "failed original-CHC replay must demote extracted BMC witness, got {result:?}"
    );
}

/// Regression test for #2805: query body args that are expressions
/// must be linked to level args via equalities (not silently dropped).
#[test]
fn test_bmc_query_expression_arg_no_spurious_counterexample() {
    // Fact: x = 0 => P(x)
    // Query: P(x + 1) /\ x >= 5 => false
    //
    // Real semantics: safe for all bounded depths (P(0) only, so P(6) unreachable).
    // Buggy semantics (dropping non-var arg equalities) gives spurious Unsafe:
    // P#k_0 unconstrained by x+1, with free x >= 5.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                p,
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            )],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 5,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "expected Unknown (no bounded CEX), got {result:?}"
    );
}

/// Create two-phase unsafe problem: inc x 0→10, switch pc 0→1, dec x forever.
/// Query: Inv(x,pc) ∧ x<0 => false (unsafe at depth ~22).
fn create_two_phase_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let pc = ChcVar::new("pc", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    let pc1 = ChcVar::new("pc1", ChcSort::Int);

    // Fact: x=0 ∧ pc=0 => Inv(x, pc)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())]),
    ));

    // Transition 1: Inv(x,pc) ∧ pc=0 ∧ x<2 => Inv(x+1, 0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(0)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // Transition 2: Inv(x,pc) ∧ pc=0 ∧ x>=2 => Inv(x, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                    ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::var(x.clone())),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // Transition 3: Inv(x,pc) ∧ pc=1 => Inv(x-1, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(1)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(-1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x1), ChcExpr::var(pc1)]),
    ));

    // Query: Inv(x,pc) ∧ x<0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc)])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Regression test for a two-phase unsafe system.
///
/// The original deep instance of this benchmark behaved more like a
/// performance benchmark than a unit test and was unstable across debug
/// environments. This compact instance preserves the two-phase structure
/// (count up in phase 0, then count down in phase 1 until x < 0) while
/// keeping the required BMC depth small enough for the lib test suite.
#[test]
#[timeout(20_000)]
fn test_bmc_two_phase_unsafe() {
    let problem = create_two_phase_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig {
            verbose: true,
            ..ChcEngineConfig::default()
        },
        max_depth: 8,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            assert!(
                cex.steps.len() <= 9,
                "Expected depth <= 8, got {}",
                cex.steps.len()
            );
        }
        _ => {
            panic!("BMC should find counterexample for two_phase_unsafe, got {result:?}");
        }
    }
}

/// Test acyclic_safe: BMC returns Safe when all depths exhausted.
///
/// The safe problem (x bounded by 3, query at x >= 10) has no counterexample
/// within any depth. With acyclic_safe=true, BMC should return Safe.
#[test]
fn test_bmc_acyclic_safe_returns_safe() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        acyclic_safe: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "Expected Safe for acyclic_safe with bounded safe problem, got {result:?}"
    );
}

/// Test acyclic_safe: BMC still returns Unsafe when counterexample exists.
///
/// Even with acyclic_safe=true, if a counterexample is found within the
/// depth bound, BMC should return Unsafe (not Safe).
#[test]
fn test_bmc_acyclic_safe_still_returns_unsafe() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        acyclic_safe: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "Expected Unsafe for reachable counterexample even with acyclic_safe, got {result:?}"
    );
}

/// Create a deep two-phase problem requiring depth ~22.
fn create_deep_two_phase_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let pc = ChcVar::new("pc", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);
    let pc1 = ChcVar::new("pc1", ChcSort::Int);

    // Fact: x=0, pc=0 => Inv(x, pc)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())]),
    ));

    // T1: Inv(x,pc), pc=0, x<10 => Inv(x+1, 0)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(0)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // T2: Inv(x,pc), pc=0, x>=10 => Inv(x, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(0)),
                    ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10)),
                    ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::var(x.clone())),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(x1.clone()), ChcExpr::var(pc1.clone())],
        ),
    ));

    // T3: Inv(x,pc), pc=1 => Inv(x-1, 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc.clone())])],
            Some(ChcExpr::and_all(
                [
                    ChcExpr::eq(ChcExpr::var(pc.clone()), ChcExpr::int(1)),
                    ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(-1)),
                    ),
                    ChcExpr::eq(ChcExpr::var(pc1.clone()), ChcExpr::int(1)),
                ]
                .iter()
                .cloned(),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x1), ChcExpr::var(pc1)]),
    ));

    // Query: Inv(x,pc), x<0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(pc)])],
            Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Test that acyclic_safe=false still returns Unknown (not Safe).
#[test]
fn test_bmc_non_acyclic_returns_unknown() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        acyclic_safe: false,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "Expected Unknown for non-acyclic BMC with safe problem, got {result:?}"
    );
}

// ============ #7969 Tests: Depth Scaling, Time Budget, K-Induction ============

/// Test default max_depth is 200 (#7969).
#[test]
fn test_bmc_default_max_depth_200() {
    let config = BmcConfig::default();
    assert_eq!(
        config.max_depth, 200,
        "Default max_depth should be 200 for HWMCC scaling"
    );
}

/// Test HWMCC preset configuration (#7969).
#[test]
fn test_bmc_hwmcc_config() {
    let config = BmcConfig::hwmcc();
    assert_eq!(config.max_depth, 500);
    assert_eq!(config.time_budget, Some(std::time::Duration::from_mins(2)));
    assert!(config.enable_k_induction);
    assert!(!config.acyclic_safe);
}

/// Test time budget stops BMC early (#7969).
///
/// With a 1ms budget and max_depth=200, BMC should stop well before depth 200
/// on the safe problem (which has no counterexample to find).
#[test]
fn test_bmc_time_budget_stops_early() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 200,
        time_budget: Some(std::time::Duration::from_millis(1)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let start = ay_core::time::Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();

    // Should return Unknown (stopped by budget), not try all 200 depths
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "Expected Unknown when budget exhausted, got {result:?}"
    );
    // Sanity: should complete quickly (budget is 1ms, solver overhead is small)
    assert!(
        elapsed < std::time::Duration::from_secs(5),
        "Budget should have stopped BMC quickly, but took {elapsed:?}"
    );
}

/// Test k-induction proves safety for bounded safe problem (#7969).
///
/// The safe problem (x bounded by 3, query at x >= 10) is k-inductive
/// because after 3 consecutive UNSAT depths, the induction step also holds.
#[test]
#[timeout(30_000)]
fn test_bmc_k_induction_finds_safe() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 20,
        enable_k_induction: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    // K-induction should prove safety (or at worst return Unknown if
    // the problem is not k-inductive at the attempted k values)
    assert!(
        matches!(result, ChcEngineResult::Safe(_) | ChcEngineResult::Unknown),
        "Expected Safe or Unknown with k-induction, got {result:?}"
    );
}

/// Test k-induction does not interfere with counterexample detection (#7969).
///
/// Even with k-induction enabled, if a counterexample is reachable within
/// the depth bound, BMC should still find and return it.
#[test]
fn test_bmc_k_induction_still_finds_unsafe() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        enable_k_induction: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "Expected Unsafe even with k-induction enabled, got {result:?}"
    );
}

/// Test deep two-phase at depth 200 with time budget (#7969).
///
/// The deep two-phase problem requires ~22 steps. With max_depth=200 and a
/// finite budget, BMC may find the counterexample or conservatively return
/// Unknown; it must not prove the unsafe benchmark Safe.
#[test]
#[timeout(60_000)]
fn test_bmc_deep_200_finds_counterexample_or_returns_unknown() {
    let problem = create_deep_two_phase_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig {
            verbose: true,
            ..ChcEngineConfig::default()
        },
        max_depth: 200,
        time_budget: Some(std::time::Duration::from_secs(30)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    match result {
        ChcEngineResult::Unsafe(cex) => {
            assert!(
                cex.steps.len() >= 20,
                "Expected depth >= 20, got {}",
                cex.steps.len()
            );
        }
        ChcEngineResult::Unknown => {}
        _ => panic!("BMC should not prove this unsafe benchmark safe, got {result:?}"),
    }
}

// ============ #7969 Tests: Adaptive Stepping, Stats, Deep Bug Finding ============

/// Test adaptive stepping config builder (#7969).
#[test]
fn test_bmc_adaptive_stepping_config() {
    let config = BmcConfig::default().with_adaptive_stepping(true);
    assert!(config.enable_adaptive_stepping);

    let config = BmcConfig::default().with_adaptive_stepping(false);
    assert!(!config.enable_adaptive_stepping);
}

/// Test deep_bug_finding preset (#7969).
#[test]
fn test_bmc_deep_bug_finding_config() {
    let config = BmcConfig::deep_bug_finding();
    assert_eq!(config.max_depth, 300);
    assert_eq!(config.time_budget, Some(std::time::Duration::from_mins(1)));
    assert!(!config.enable_k_induction);
    assert!(config.enable_adaptive_stepping);
}

/// Test HWMCC preset includes adaptive stepping (#7969).
#[test]
fn test_bmc_hwmcc_has_adaptive_stepping() {
    let config = BmcConfig::hwmcc();
    assert!(config.enable_adaptive_stepping);
    assert!(config.enable_k_induction);
}

/// Test stats tracking: simple unsafe problem records check count (#7969).
#[test]
fn test_bmc_stats_tracking_unsafe() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(matches!(result, ChcEngineResult::Unsafe(_)));

    let stats = solver.stats();
    assert!(
        stats.num_checks > 0,
        "Expected at least 1 check, got {}",
        stats.num_checks
    );
    assert!(stats.total_time_secs > 0.0, "Expected non-zero total time");
    // The counterexample is at depth 5-6, so we should have checked at most ~7 depths
    assert!(
        stats.max_depth_reached <= 10,
        "Expected max_depth_reached <= 10, got {}",
        stats.max_depth_reached
    );
}

/// Test stats tracking: safe problem with budget records budget exhaustion (#7969).
#[test]
fn test_bmc_stats_tracking_budget() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 200,
        time_budget: Some(std::time::Duration::from_millis(1)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(matches!(result, ChcEngineResult::Unknown));

    let stats = solver.stats();
    assert!(
        stats.budget_exhausted,
        "Expected budget_exhausted=true when budget is tiny"
    );
    assert!(
        !stats.exhausted_search,
        "budget stop must not be reported as an exhausted bounded search"
    );
}

/// Test stats tracking: sequential safe search marks bounded exhaustion only
/// after discharging the full configured depth bound.
#[test]
fn test_bmc_stats_tracking_exhausted_search() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(matches!(result, ChcEngineResult::Unknown));

    let stats = solver.stats();
    assert!(
        stats.exhausted_search,
        "fully discharged bounded search should be marked as exhausted"
    );
    assert!(
        !stats.budget_exhausted,
        "exhausted bounded search should not also be marked budget exhausted"
    );
}

/// Test adaptive stepping finds counterexample on simple unsafe problem (#7969).
///
/// Adaptive stepping should not prevent finding counterexamples - it only
/// changes which depths are checked, not the correctness.
#[test]
fn test_bmc_adaptive_stepping_finds_unsafe() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 20,
        enable_adaptive_stepping: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "Adaptive stepping should still find counterexample, got {result:?}"
    );
}

/// Test adaptive stepping with two-phase unsafe problem (#7969).
#[test]
#[timeout(20_000)]
fn test_bmc_adaptive_stepping_two_phase() {
    let problem = create_two_phase_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 20,
        enable_adaptive_stepping: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "Adaptive stepping should find two-phase counterexample, got {result:?}"
    );
}

/// Test k-induction stats tracking (#7969).
#[test]
#[timeout(30_000)]
fn test_bmc_k_induction_stats() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 20,
        enable_k_induction: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    let stats = solver.stats();
    // Whether k-induction succeeded or not, we should have tracked attempts
    if matches!(result, ChcEngineResult::Safe(_)) {
        assert!(
            stats.k_induction_proved,
            "Expected k_induction_proved=true when result is Safe"
        );
        assert!(
            stats.k_induction_k.is_some(),
            "Expected k_induction_k to be set"
        );
    }
    // Even if Unknown, attempts should have been recorded
    if stats.num_k_induction_attempts > 0 {
        assert!(
            stats.max_depth_reached >= super::K_INDUCTION_MIN_CONSECUTIVE_UNSAT,
            "K-induction should only be attempted after enough depths"
        );
    }
}

/// Test that adaptive stepping + k-induction combo works (#7969).
///
/// HWMCC preset uses both features. Verify they don't interfere.
#[test]
fn test_bmc_adaptive_plus_k_induction_unsafe() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 20,
        enable_k_induction: true,
        enable_adaptive_stepping: true,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "Both features enabled should still find counterexample, got {result:?}"
    );
}

/// Soundness regression test for #8734.
///
/// `test_array_int_pred.smt2` is SAFE (Z3: sat). BMC must NOT return Unsafe:
/// the benchmark has `(Array Int Int)`-sorted predicate parameters and no
/// reachable unsafe state. Before the fix, BMC returned `Unsafe` with a
/// counterexample that dropped all array arguments from the trace.
///
/// The test asserts that BMC does not emit `Unsafe`. BMC may legitimately
/// return `Unknown` (bounded exploration did not exhaust reachable states at
/// a shallow depth) — what it MUST NOT do is emit a spurious counterexample.
///
/// Originally (before #8745 was fixed) BMC was kept honest by an explicit
/// array-sort downgrade in `solve()`. That downgrade was removed in #8822
/// because the underlying SMT array unsoundness (#8745) was fixed in
/// d7cd99c09. Soundness on this input is now carried by the SMT layer, not
/// a BMC-level suppression.
///
/// `max_depth=1` is enough for the soundness check: the pre-fix bug surfaced
/// a spurious Unsafe at depth 1.
#[test]
#[timeout(30_000)]
fn test_bmc_array_int_pred_not_spurious_unsafe_8734() {
    let src = include_str!("../../../../benchmarks/chc/test_array_int_pred.smt2");
    let problem = crate::ChcParser::parse(src).expect("test_array_int_pred.smt2 should parse");
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 1,
        per_depth_timeout: Some(std::time::Duration::from_secs(5)),
        time_budget: Some(std::time::Duration::from_secs(10)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        !matches!(result, ChcEngineResult::Unsafe(_)),
        "BMC must not produce spurious Unsafe on safe array CHC (#8734), got {result:?}",
    );
}

#[test]
#[timeout(30_000)]
fn test_bmc_array_derivation_witness_replays_store_path_9692() {
    let src = r#"
(set-logic HORN)
(declare-fun |main@precall.split| () Bool)
(declare-fun |main@entry| ((Array Int Int)) Bool)
(assert
  (forall ((A (Array Int Int)))
    (=> true (main@entry A))))
(assert
  (forall ((A (Array Int Int)) (B (Array Int Int)) (C Int) (D Bool)
           (E (Array Int Int)) (F Bool) (G (Array Int Int))
           (H (Array Int Int)) (I Bool) (J Bool))
    (=>
      (and
        (main@entry A)
        (= E (store B C 1))
        (or (not I) (not F) (= G H))
        (or (not I) (not F) (= H E))
        (or (not I) (not F) (not D))
        (or (not I) (and F I))
        (or (not J) (and J I))
        (= J true)
        (= B (store A C 0)))
      main@precall.split)))
(assert
  (forall ((CHC_COMP_UNUSED Bool))
    (=> (and main@precall.split true) false)))
"#;
    let problem = crate::ChcParser::parse(src).expect("array store CHC should parse");
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig::default()
            .with_max_depth(2)
            .with_time_budget(std::time::Duration::from_secs(5))
            .with_per_depth_timeout(std::time::Duration::from_secs(5)),
    );

    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("BMC should find the shallow array counterexample, got {result:?}");
    };
    assert!(
        cex.witness.is_some(),
        "array BMC counterexample must carry a replayable derivation witness"
    );

    let mut verifier = PdrSolver::new(
        problem,
        PdrConfig {
            strict_proofs: true,
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        },
    );
    assert!(matches!(
        verifier.verify_counterexample(&cex),
        CexVerificationResult::Valid
    ));
}

/// Soundness regression test for #8734 (companion reproducer).
///
/// `array_2param_int_8660.smt2` is also SAFE. BMC must not return Unsafe
/// when arrays are involved. See the related test above for the primary
/// reproducer.
#[test]
#[timeout(30_000)]
fn test_bmc_array_2param_int_not_spurious_unsafe_8734() {
    let src = include_str!("../../../../benchmarks/chc/array_2param_int_8660.smt2");
    let problem = crate::ChcParser::parse(src).expect("array_2param_int_8660.smt2 should parse");
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 1,
        per_depth_timeout: Some(std::time::Duration::from_secs(5)),
        time_budget: Some(std::time::Duration::from_secs(10)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();

    assert!(
        !matches!(result, ChcEngineResult::Unsafe(_)),
        "BMC must not produce spurious Unsafe on safe 2-array CHC (#8734), got {result:?}",
    );
}

/// Telemetry regression for #8822.
///
/// After `solve()`, exactly one of `used_executor_path` or
/// `used_legacy_fallback` must be set so field diagnostics can tell which
/// code path produced the verdict. Before #8822 the two paths ran silently
/// with no observable difference between them.
#[test]
fn test_bmc_records_path_telemetry_8822() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 2,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let _ = solver.solve();
    let stats = solver.stats();

    assert!(
        stats.used_executor_path ^ stats.used_legacy_fallback,
        "BMC must record exactly one of executor/legacy path (#8822); \
         executor={} legacy={}",
        stats.used_executor_path,
        stats.used_legacy_fallback,
    );
}

/// Executor-backed BMC must honor `per_depth_timeout` on the persistent
/// activation-literal path before it can find a reachable counterexample.
#[test]
fn test_bmc_single_executor_respects_zero_per_depth_timeout() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        per_depth_timeout: Some(std::time::Duration::ZERO),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let queries: Vec<_> = solver.problem.queries().collect();

    let outcome = solver
        .solve_single_executor(&queries, 10)
        .expect("single-executor path should execute");

    match outcome {
        SingleExecutorOutcome::RetryFresh {
            start_depth,
            consecutive_unsat,
        } => {
            assert_eq!(
                start_depth, 0,
                "zero per-depth timeout should force fresh fallback at the first depth"
            );
            assert_eq!(
                consecutive_unsat, 0,
                "timed-out depth must not count as a proven UNSAT prefix"
            );
        }
        SingleExecutorOutcome::Solved(result) => {
            panic!(
                "single-executor path must not solve past a zero per-depth timeout, got {result:?}"
            );
        }
    }
}

/// Fresh-executor fallback must also respect `per_depth_timeout` instead of
/// continuing until it discovers the reachable counterexample.
#[test]
fn test_bmc_per_depth_fresh_respects_zero_per_depth_timeout() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        per_depth_timeout: Some(std::time::Duration::ZERO),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let queries: Vec<_> = solver.problem.queries().collect();

    let result = solver
        .solve_per_depth_fresh(&queries, 10, 0, 0, false)
        .expect("fresh executor path should execute");

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "zero per-depth timeout should keep fresh executor BMC inconclusive, got {result:?}"
    );
}

/// End-to-end solve should stay on the executor path and return `Unknown`
/// when each depth gets a zero timeout.
#[test]
fn test_bmc_executor_path_respects_zero_per_depth_timeout_end_to_end() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        per_depth_timeout: Some(std::time::Duration::ZERO),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);

    let result = solver.solve();
    let stats = solver.stats();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "zero per-depth timeout should prevent executor-backed BMC from reporting Unsafe, got {result:?}"
    );
    assert!(
        stats.used_executor_path,
        "BMC should report the executor path when timeout is handled without legacy fallback"
    );
    assert!(
        !stats.used_legacy_fallback,
        "per-depth timeout on the executor path should not force the legacy fallback"
    );
}

/// `acyclic_safe` must not turn an executor timeout / SMT unknown into `Safe`.
#[test]
fn test_bmc_acyclic_safe_zero_timeout_stays_unknown() {
    let problem = create_safe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        acyclic_safe: true,
        per_depth_timeout: Some(std::time::Duration::ZERO),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);

    let result = solver.solve();
    let stats = solver.stats();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "acyclic_safe must not claim Safe after executor timeout / unknown, got {result:?}"
    );
    assert!(
        !stats.exhausted_search,
        "timed-out acyclic_safe run must not be reported as an exhausted bounded search"
    );
}

/// When adaptive stepping skips bounds, the persistent executor path must hand
/// control to the sequential fresh-executor path before `acyclic_safe` can
/// claim `Safe`.
#[test]
fn test_bmc_single_executor_acyclic_safe_skipped_depths_retry_fresh() {
    let solver = BmcSolver::new(
        create_safe_problem(),
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 20,
            acyclic_safe: true,
            enable_adaptive_stepping: true,
            ..BmcConfig::default()
        },
    );

    match solver.finalize_single_executor_completion(Some(4)) {
        SingleExecutorOutcome::RetryFresh {
            start_depth,
            consecutive_unsat,
        } => {
            assert_eq!(
                start_depth, 4,
                "single-executor completion should resume from the first skipped depth"
            );
            assert_eq!(
                consecutive_unsat, 0,
                "skipped depths must not be treated as a proven UNSAT suffix"
            );
        }
        SingleExecutorOutcome::Solved(result) => {
            panic!(
                "acyclic_safe must not claim Safe with skipped depths still unchecked, got {result:?}"
            );
        }
    }
}

/// Fresh-executor fallback should be able to resume from a later depth without
/// replaying all earlier bounds. This keeps the fallback cheap when the
/// persistent activation-literal path goes Unknown at a deep bound.
#[test]
fn test_bmc_per_depth_fresh_can_resume_from_known_unsat_prefix() {
    let problem = create_simple_unsafe_problem();
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 10,
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let queries: Vec<_> = solver.problem.queries().collect();

    let result = solver
        .solve_per_depth_fresh(&queries, 10, 4, 4, false)
        .expect("fresh fallback should execute");

    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "resumed fresh fallback should still find the counterexample, got {result:?}"
    );

    let stats = solver.stats();
    assert!(
        stats.num_checks <= 3,
        "resumed fresh fallback should not replay depths 0..3; got {} checks",
        stats.num_checks
    );
    assert!(
        stats.max_depth_reached >= 4,
        "resume should begin at or after the requested depth, got {}",
        stats.max_depth_reached
    );
}

/// K-induction checks use the executor too, so a zero per-depth timeout must
/// demote the check to `None` instead of silently proving safety.
#[test]
fn test_bmc_k_induction_respects_zero_per_depth_timeout() {
    let problem = create_safe_problem();

    let baseline_solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 20,
            enable_k_induction: true,
            ..BmcConfig::default()
        },
    );
    let baseline = baseline_solver.try_k_induction_check(3);
    assert!(
        matches!(baseline, Some(ChcEngineResult::Safe(_))),
        "baseline k-induction check should prove the safe problem before the timeout regression guard, got {baseline:?}"
    );

    let timed_solver = BmcSolver::new(
        problem,
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 20,
            per_depth_timeout: Some(std::time::Duration::ZERO),
            enable_k_induction: true,
            ..BmcConfig::default()
        },
    );

    assert!(
        timed_solver.try_k_induction_check(3).is_none(),
        "zero per-depth timeout must prevent executor-backed k-induction from claiming Safe"
    );
}

// ============ Persistent-Executor Transition-System BMC (Phase 3 Layer B) ============

/// The TS-incremental path walks every depth on the persistent executor and,
/// on SAT, returns exactly the verdict that the existing per-depth fresh flat
/// path produces for the cex depth (unchanged-answers contract).
#[test]
#[timeout(60000)]
fn test_ts_incremental_matches_fresh_path_on_simple_unsafe_ts() {
    let problem = create_simple_unsafe_problem();
    let queries: Vec<_> = problem.queries().collect();

    let ts_solver = BmcSolver::new(problem.clone(), BmcConfig::default());
    let outcome = ts_solver.solve_transition_system_incremental(&queries, 10);
    let Some(SingleExecutorOutcome::Solved(ts_result)) = outcome else {
        panic!("expected Solved outcome from TS-incremental path, got {outcome:?}");
    };

    // The cex needs 5 transitions: the loop must have reached depth 5 on the
    // persistent executor (5 unsat depths + SAT at depth 5 + confirm check).
    let stats = ts_solver.stats();
    assert!(
        stats.max_depth_reached >= 5,
        "cex is at depth 5; recorded max depth {} is too shallow",
        stats.max_depth_reached
    );
    assert!(
        stats.num_checks >= 6,
        "expected at least 6 recorded depth checks, got {}",
        stats.num_checks
    );

    // Unchanged answers: the TS path must agree with the existing fresh path.
    let fresh_solver = BmcSolver::new(problem.clone(), BmcConfig::default());
    let fresh_result = fresh_solver
        .solve_per_depth_fresh(&queries, 10, 0, 0, false)
        .expect("fresh path returns a result");
    assert_eq!(
        std::mem::discriminant(&ts_result),
        std::mem::discriminant(&fresh_result),
        "TS-incremental verdict {ts_result:?} must match fresh-path verdict {fresh_result:?}"
    );
}

/// The TS-incremental path discharges all depths on a safe transition system
/// and yields Unknown (never Safe: acyclic_safe configs are gated off).
#[test]
#[timeout(60000)]
fn test_ts_incremental_safe_ts_exhausts_to_unknown() {
    let problem = create_safe_problem();
    let queries: Vec<_> = problem.queries().collect();
    let solver = BmcSolver::new(problem.clone(), BmcConfig::default());

    let outcome = solver.solve_transition_system_incremental(&queries, 6);
    match outcome {
        Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown)) => {}
        other => panic!("expected Unknown after exhausting all depths, got {other:?}"),
    }
    // All 7 depths (0..=6) must have been checked sequentially (no skips).
    assert_eq!(solver.stats().max_depth_reached, 6);
}

/// Inc-16 S1b probe clamp: with `ts_probe_clamp = Some((min_depth, after))`
/// the TS-incremental search stops EARLY (budget-exhausted Unknown) once
/// `min_depth` is verified cex-free and `after` has elapsed; with the clamp
/// disabled (None) the same safe problem walks every depth. Uses an
/// immediate clamp `(2, ZERO)` so the test is timing-independent.
#[test]
#[timeout(60000)]
fn test_ts_incremental_probe_clamp_stops_early() {
    let problem = create_safe_problem();
    let queries: Vec<_> = problem.queries().collect();
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            ts_probe_clamp: Some((2, std::time::Duration::ZERO)),
            ..BmcConfig::default()
        },
    );

    let outcome = solver.solve_transition_system_incremental(&queries, 6);
    match outcome {
        Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown)) => {}
        other => panic!("expected clamped Unknown, got {other:?}"),
    }
    assert!(
        solver.stats().budget_exhausted,
        "clamp exit must be recorded as a budget exit"
    );
    assert_eq!(
        solver.stats().max_depth_reached,
        2,
        "search must stop at the clamp depth, not walk all 6 depths"
    );
}

/// Inc-16 S1b probe clamp soundness: an unsafe TS whose cex is BELOW the
/// clamp depth still finds its counterexample (the clamp only fires on
/// cex-free depths at/past `min_depth`).
#[test]
#[timeout(60000)]
fn test_ts_incremental_probe_clamp_keeps_shallow_cex() {
    let problem = create_simple_unsafe_problem();
    let queries: Vec<_> = problem.queries().collect();
    // Cex is at depth 5; clamp at depth 6 (immediate timer) must not block it.
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            ts_probe_clamp: Some((6, std::time::Duration::ZERO)),
            ..BmcConfig::default()
        },
    );
    let outcome = solver.solve_transition_system_incremental(&queries, 10);
    match outcome {
        Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unsafe(_))) => {}
        other => panic!("expected Unsafe below the clamp depth, got {other:?}"),
    }
}

/// Multi-predicate problems are not transition systems: the TS-incremental
/// path must decline (return None) so the existing routes handle them.
#[test]
#[timeout(60000)]
fn test_ts_incremental_declines_multi_predicate_problems() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));
    assert!(
        problem.predicates().len() > 1,
        "fixture must be multi-predicate"
    );

    let queries: Vec<_> = problem.queries().collect();
    let solver = BmcSolver::new(problem.clone(), BmcConfig::default());
    assert!(
        solver
            .solve_transition_system_incremental(&queries, 5)
            .is_none(),
        "TS-incremental path must decline non-TS problems"
    );
}

/// Adaptive stepping skips depths, which is unsound for the exact-depth TS
/// queries; acyclic-safe configs expect Safe on exhaustion which this path
/// never produces. Both must be gated off.
#[test]
#[timeout(60000)]
fn test_ts_incremental_declines_adaptive_and_acyclic_safe_configs() {
    let problem = create_simple_unsafe_problem();
    let queries: Vec<_> = problem.queries().collect();

    let adaptive = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            enable_adaptive_stepping: true,
            ..BmcConfig::default()
        },
    );
    assert!(adaptive
        .solve_transition_system_incremental(&queries, 5)
        .is_none());

    let acyclic = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            acyclic_safe: true,
            ..BmcConfig::default()
        },
    );
    assert!(acyclic
        .solve_transition_system_incremental(&queries, 5)
        .is_none());
}

/// End-to-end: BmcSolver::solve still produces the Unsafe verdict on the
/// simple unsafe transition system with the TS-incremental route wired in.
#[test]
#[timeout(60000)]
fn test_bmc_solve_unsafe_ts_end_to_end_with_ts_incremental() {
    let problem = create_simple_unsafe_problem();
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 10,
            ..BmcConfig::default()
        },
    );
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "expected Unsafe, got {result:?}"
    );
}

// ============================================================================
// inc-9: multipred SingleLoop persistent-executor lane + cex replay verifier
// ============================================================================

/// Cyclic LINEAR multipred UNSAT problem (mirrors the eldarica reve shape):
///   x = 0                  => P(x)
///   P(x) ∧ x ≤ 5 ∧ x' = x+1 => P(x')
///   P(x) ∧ x ≥ 3           => Q(x)
///   Q(x) ∧ x ≥ 3           => false
/// Shortest refutation: P(0)→P(1)→P(2)→P(3)→Q(3)→false (5 clause applications).
fn create_multipred_cyclic_unsafe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xn = ChcVar::new("xn", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and(
                ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
                ChcExpr::eq(
                    ChcExpr::var(xn.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(xn)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// SAFE variant: the loop is bounded at x ≤ 5 but the query needs x ≥ 100.
fn create_multipred_cyclic_safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let xn = ChcVar::new("xn", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and(
                ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
                ChcExpr::eq(
                    ChcExpr::var(xn.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(xn)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(3))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(100))),
        ),
        ClauseHead::False,
    ));
    problem
}

/// inc-9: the multipred SingleLoop lane finds and witness-verifies the
/// refutation of a cyclic linear multipred problem end-to-end.
#[test]
#[timeout(120000)]
fn test_bmc_multipred_linear_cyclic_unsafe_via_singleloop_lane() {
    let solver = BmcSolver::new(
        create_multipred_cyclic_unsafe_problem(),
        BmcConfig {
            max_depth: 20,
            ..BmcConfig::default()
        },
    );
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("expected Unsafe, got {result:?}");
    };
    let witness = cex
        .witness
        .expect("multipred BMC Unsafe must carry a witness");
    assert!(
        !witness.entries.is_empty(),
        "witness must contain derivation entries"
    );
}

/// inc-9: the multipred lane never claims Safe (or Unsafe) on a safe cyclic
/// problem — depth exhaustion is Unknown.
#[test]
#[timeout(120000)]
fn test_bmc_multipred_linear_cyclic_safe_returns_unknown() {
    let solver = BmcSolver::new(
        create_multipred_cyclic_safe_problem(),
        BmcConfig {
            max_depth: 12,
            ..BmcConfig::default()
        },
    );
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "expected Unknown on safe problem, got {result:?}"
    );
}

/// inc-9 replay verifier: confirms a genuine refutation with a verified
/// witness, using only a depth hint (no engine trace).
#[test]
#[timeout(120000)]
fn test_replay_confirm_unsafe_on_problem_confirms_genuine() {
    let problem = create_multipred_cyclic_unsafe_problem();
    let cex = BmcSolver::replay_confirm_unsafe_on_problem(
        &problem,
        5,
        std::time::Duration::from_secs(30),
        None,
        false,
    )
    .expect("replay must confirm the genuine refutation");
    assert!(
        cex.witness.is_some_and(|w| !w.entries.is_empty()),
        "confirmed replay must carry a verified witness"
    );
}

/// inc-9 replay verifier: NEVER confirms anything on a safe problem
/// (fail closed), even with a generous depth hint.
#[test]
#[timeout(120000)]
fn test_replay_confirm_unsafe_on_problem_rejects_safe() {
    let problem = create_multipred_cyclic_safe_problem();
    assert!(
        BmcSolver::replay_confirm_unsafe_on_problem(
            &problem,
            12,
            std::time::Duration::from_secs(30),
            None,
            false,
        )
        .is_none(),
        "replay must fail closed on a safe problem"
    );
}

/// inc-9 replay verifier: nonlinear problems are out of scope and rejected.
#[test]
#[timeout(60000)]
fn test_replay_confirm_unsafe_rejects_nonlinear() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // Nonlinear: two body predicates.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (p, vec![ChcExpr::var(x.clone())]),
                (p, vec![ChcExpr::var(x.clone())]),
            ],
            None,
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));
    assert!(BmcSolver::replay_confirm_unsafe_on_problem(
        &problem,
        5,
        std::time::Duration::from_secs(10),
        None,
        false,
    )
    .is_none());
}

/// inc-9 gate g2 regression: witness-free cex verification on a problem with
/// NO transition-system encoding must never return Spurious. On a genuinely
/// unsafe multipred problem the bounded replay upgrades to Valid; on a safe
/// multipred problem it stays Unknown.
#[test]
#[timeout(120000)]
fn test_verify_without_witness_multipred_replay_valid_and_unknown_not_spurious() {
    use crate::pdr::counterexample::CounterexampleStep;

    let make_cex = |preds: &[PredicateId]| Counterexample {
        steps: preds
            .iter()
            .map(|p| CounterexampleStep::new(*p, FxHashMap::default()))
            .collect(),
        witness: None,
        ground_derivation: None,
    };

    // Unsafe problem: replay confirms → Valid.
    let problem = create_multipred_cyclic_unsafe_problem();
    let preds: Vec<PredicateId> = problem.predicates().iter().map(|p| p.id).collect();
    let mut verifier = PdrSolver::new(
        problem,
        PdrConfig {
            strict_proofs: true,
            preserve_original_clauses: true,
            disable_array_scalarization: true,
            ..PdrConfig::default()
        },
    );
    let cex = make_cex(&[preds[0], preds[0], preds[0], preds[0], preds[1]]);
    assert_eq!(
        verifier.verify_counterexample(&cex),
        CexVerificationResult::Valid,
        "replay must confirm the genuine multipred refutation"
    );

    // Safe problem: no replay confirmation → Unknown, NEVER Spurious.
    let problem = create_multipred_cyclic_safe_problem();
    let preds: Vec<PredicateId> = problem.predicates().iter().map(|p| p.id).collect();
    let mut verifier = PdrSolver::new(
        problem,
        PdrConfig {
            strict_proofs: true,
            preserve_original_clauses: true,
            disable_array_scalarization: true,
            ..PdrConfig::default()
        },
    );
    let cex = make_cex(&[preds[0], preds[1]]);
    assert_eq!(
        verifier.verify_counterexample(&cex),
        CexVerificationResult::Unknown,
        "'cannot encode' must be Unknown, never definitively Spurious (g2)"
    );
}

/// inc-9: `disable_cex_replay` keeps validation contexts from recursing into
/// another bounded-BMC replay — without an encoding they return Unknown even
/// on a genuinely unsafe problem.
#[test]
#[timeout(60000)]
fn test_verify_without_witness_disable_cex_replay_returns_unknown() {
    use crate::pdr::counterexample::CounterexampleStep;

    let problem = create_multipred_cyclic_unsafe_problem();
    let preds: Vec<PredicateId> = problem.predicates().iter().map(|p| p.id).collect();
    let config = PdrConfig {
        disable_cex_replay: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    let cex = Counterexample {
        steps: vec![
            CounterexampleStep::new(preds[0], FxHashMap::default()),
            CounterexampleStep::new(preds[1], FxHashMap::default()),
        ],
        witness: None,
        ground_derivation: None,
    };
    assert_eq!(
        verifier.verify_counterexample(&cex),
        CexVerificationResult::Unknown
    );
}

/// Adversarial review (inc-9): a fabricated witness whose only entry is an
/// "axiom" (`incoming_clause: None`) claiming an UNREACHABLE state must NOT
/// verify as Valid on a SAFE problem. The entry-verification loop skips
/// axiom entries entirely, so acceptance would rest only on the query-clause
/// consistency check — which the fabricated state satisfies by construction.
#[test]
#[timeout(60000)]
fn test_adversarial_axiom_only_witness_rejected_on_safe_problem() {
    let problem = create_multipred_cyclic_safe_problem();
    let q = problem.predicates()[1].id;

    // Borrow BMC's state/instances constructor for Q(100).
    let bmc = BmcSolver::new(problem.clone(), BmcConfig::default().with_max_depth(0));
    let (instances, state) = bmc
        .concrete_state_witness(q, &[100])
        .expect("Q(100) state should be representable");

    let witness = DerivationWitness {
        query_clause: Some(3),
        root: 0,
        entries: vec![DerivationWitnessEntry {
            predicate: q,
            level: 0,
            state,
            incoming_clause: None, // "axiom": skipped by entry verification
            premises: Vec::new(),
            instances,
        }],
    };
    let cex = Counterexample::with_witness(
        vec![crate::pdr::counterexample::CounterexampleStep::new(
            q,
            FxHashMap::default(),
        )],
        witness,
    );

    // Mirror the adaptive/final validation solver config.
    let config = PdrConfig {
        strict_proofs: true,
        preserve_original_clauses: true,
        disable_array_scalarization: true,
        disable_cex_replay: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    let result = verifier.verify_counterexample(&cex);
    assert!(
        !matches!(result, CexVerificationResult::Valid),
        "axiom-only fabricated witness for unreachable Q(100) verified as Valid \
         on a SAFE problem: {result:?}"
    );
}

/// Adversarial review (inc-9): a CYCLIC witness (entry premising itself via an
/// identity rule) must NOT verify as Valid — it is not a well-founded
/// derivation. Problem is SAFE (P = {0}); the witness claims P(100) justified
/// by P(100) through `P(x) => P(x)`.
#[test]
#[timeout(60000)]
fn test_adversarial_cyclic_witness_rejected_on_safe_problem() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    // clause 0: x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // clause 1: P(x) => P(x)  (identity rule)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // clause 2: P(x) /\ x >= 100 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(100))),
        ),
        ClauseHead::False,
    ));

    let bmc = BmcSolver::new(problem.clone(), BmcConfig::default().with_max_depth(0));
    let (instances, state) = bmc
        .concrete_state_witness(p, &[100])
        .expect("P(100) state should be representable");

    let witness = DerivationWitness {
        query_clause: Some(2),
        root: 0,
        entries: vec![DerivationWitnessEntry {
            predicate: p,
            level: 1,
            state,
            incoming_clause: Some(1), // identity rule
            premises: vec![0],        // SELF-CYCLE: justified by itself
            instances,
        }],
    };
    let cex = Counterexample::with_witness(
        vec![crate::pdr::counterexample::CounterexampleStep::new(
            p,
            FxHashMap::default(),
        )],
        witness,
    );

    let config = PdrConfig {
        strict_proofs: true,
        preserve_original_clauses: true,
        disable_array_scalarization: true,
        disable_cex_replay: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem, config);
    let result = verifier.verify_counterexample(&cex);
    assert!(
        !matches!(result, CexVerificationResult::Valid),
        "cyclic self-justifying witness for unreachable P(100) verified as Valid \
         on a SAFE problem: {result:?}"
    );
}

// The bounded tree-unfolding refutation handles a branching counterexample —
// a rule body with two applications of the same predicate — which the
// level-flat BMC encoding collapses. P(1) is a fact; P(x)&P(y)&z=x+y => P(z);
// the query P(2) => false is unsafe via P(2) <- P(1),P(1).
#[test]
fn bounded_tree_refutation_finds_branching_counterexample() {
    let input = r#"
(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x01) (P x))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (z (_ BitVec 8)))
  (=> (and (P x) (P y) (= z (bvadd x y))) (P z))))
(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (= x #x02)) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(input).expect("parse");
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 8,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );
    let r = solver.solve_bounded_tree_refutation(6, std::time::Duration::from_secs(15), 6000);
    assert!(
        matches!(r, ChcEngineResult::Unsafe(_)),
        "branching-tree counterexample must be a validated Unsafe, got {r:?}"
    );
}

// Soundness: the bounded tree refutation must NEVER fabricate an Unsafe on a
// SAFE problem (it may only return Unknown; it never claims Safe).
#[test]
fn bounded_tree_refutation_no_false_unsafe_on_safe() {
    // P counts up from 0 by 1; query fires only if P(x) & x <u 0 (never).
    let input = r#"
(set-logic HORN)
(declare-fun P ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (P x))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (P x) (= y (bvadd x #x01))) (P y))))
(assert (forall ((x (_ BitVec 8))) (=> (and (P x) (bvult x #x00)) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(input).expect("parse");
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 8,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );
    let r = solver.solve_bounded_tree_refutation(6, std::time::Duration::from_secs(5), 6000);
    assert!(
        !matches!(r, ChcEngineResult::Unsafe(_)),
        "must not fabricate Unsafe on a SAFE problem, got {r:?}"
    );
}

// Datatype refutation isolation pin. The built-in Nat instance exercises the
// lane without consulting ambient files or process configuration.
#[test]
#[timeout(120_000)]
fn datatype_refutation_on_bounded_instance() {
    fn run(input: &str, depth: usize, budget: std::time::Duration) -> ChcEngineResult {
        let problem = crate::parser::ChcParser::parse(input).expect("datatype CHC should parse");
        assert!(
            problem.has_datatype_sorts(),
            "datatype diagnostic must actually exercise datatype sorts"
        );
        let solver = BmcSolver::new(
            problem,
            BmcConfig {
                max_depth: depth,
                acyclic_safe: false,
                ..BmcConfig::default()
            },
        );
        solver.solve_datatype_bounded_refutation(depth, budget, 24_000)
    }

    const BUILTIN: &str = r#"
(set-logic HORN)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun P (Nat) Bool)
(assert (P zero))
(assert (forall ((n Nat)) (=> (P n) (P (succ n)))))
(assert (forall ((n Nat)) (=> (and (P n) (= n (succ (succ zero)))) false)))
(check-sat)
"#;
    let _guard = lock_env();
    let _enabled = ScopedEnvVar::unset("AY_CHC_DISABLE_DT_BMC");
    let builtin = run(BUILTIN, 3, std::time::Duration::from_secs(15));
    assert!(
        matches!(builtin, ChcEngineResult::Unsafe(_)),
        "built-in datatype chain must produce validated Unsafe, got {builtin:?}"
    );
}

// General BMC isolation pin. The built-in linear counter proves that the
// isolated solve performs checks and returns a validated counterexample.
#[test]
fn bmc_isolation_solves_bounded_fixture() {
    let mut builtin_config = BmcConfig::with_engine_config(8, true, None);
    builtin_config.time_budget = Some(std::time::Duration::from_secs(10));
    let builtin_solver = BmcSolver::new(create_simple_unsafe_problem(), builtin_config);
    let builtin = builtin_solver.solve();
    let builtin_stats = builtin_solver.stats.borrow();
    assert!(
        matches!(builtin, ChcEngineResult::Unsafe(_)),
        "built-in isolated BMC must produce validated Unsafe, got {builtin:?}"
    );
    assert!(
        builtin_stats.num_checks > 0,
        "isolated BMC must issue at least one satisfiability check"
    );
    drop(builtin_stats);
}

// Compares the datatype-BMC lane's formula forms on a built-in fixture. Probes
// the drop_inj1 depth-0 RAW
// indicator-gated disjunction, the node-arg-eliminated disjunction, and a
// COMMITTED conjunction. Solver improvements may make more than one form SAT;
// the test asserts only sound capability boundaries plus the known committed
// conjunction result.
#[test]
#[timeout(60_000)]
fn diag_dt_bmc_formula_forms() {
    let input = r#"
(set-logic HORN)
(declare-datatypes ((list_298 0)) (((nil_331 ) (cons_296  (head_592 Int) (tail_594 list_298)))))
(declare-fun |drop_59| ( list_298 Int list_298 ) Bool)
(assert (forall ( (A list_298) (v_1 Int) (v_2 list_298) )
  (=> (and (and true (= 0 v_1) (= v_2 A))) (drop_59 A v_1 v_2))))
(assert (forall ( (A list_298) (B Int) (C list_298) (D Int) (E list_298) (F Int) )
  (=> (and (drop_59 C F E) (and (= B (+ 1 F)) (= A (cons_296 D E)))) (drop_59 C B A))))
(assert (forall ( (A Int) (B Int) (v_2 list_298) (v_3 list_298) )
  (=> (and (and (= A (+ 1 B)) (= v_2 nil_331) (= v_3 nil_331))) (drop_59 v_2 A v_3))))
(assert (forall ( (A list_298) (B Int) (C Int) (D list_298) )
  (=> (and (drop_59 A C D) (drop_59 A B D) (not (= B C))) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(input).expect("parse");
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            max_depth: 4,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );
    let raw = solver.dt_bmc_debug_raw_conjuncts(0);
    eprintln!("=== RAW depth-0 conjuncts ({}) ===", raw.len());
    for c in &raw {
        eprintln!("  {c}");
    }
    let probe = |label: &str, f: &ChcExpr| {
        let mut smt = problem.make_smt_context();
        smt.set_executor_first_check_sat(true);
        let tag = match smt.check_sat_with_timeout(f, std::time::Duration::from_secs(10)) {
            SmtResult::Sat(_) => "SAT",
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                "UNSAT"
            }
            SmtResult::Unknown => "UNKNOWN",
        };
        eprintln!("FORM {label}: executor-first -> {tag}");
        tag
    };
    // Compare raw and node-arg-eliminated disjunctions with one committed form.
    let raw_tag = probe("raw_disjunction", &ChcExpr::and_all(raw.clone()));
    let (elim, _) = BmcSolver::eliminate_dt_bmc_intermediate_defs(&raw);
    let elim_tag = probe("node_arg_elim_disjunction", &elim);
    // Committed conjunction (premise1 = clause 0, premise2 = clause 2): SAT.
    let mut m: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for (n, v) in [
        ("__tree_ind_0", true),
        ("__tree_ind_1", false),
        ("__tree_ind_2", false),
        ("__tree_ind_3", true),
    ] {
        m.insert(n.to_string(), ChcExpr::Bool(v));
    }
    let committed: Vec<ChcExpr> = raw
        .iter()
        .flat_map(|c| {
            BmcSolver::simplify_bmc_expr(c.substitute_name_map(&m)).collect_conjuncts_nontrivial()
        })
        .collect();
    let committed_tag = probe("committed_conjunction", &ChcExpr::and_all(committed));
    assert_ne!(
        raw_tag, "UNSAT",
        "raw indicator disjunction has a known satisfying branch"
    );
    assert_ne!(
        elim_tag, "UNSAT",
        "node-eliminated disjunction has a known satisfying branch"
    );
    assert_eq!(
        committed_tag, "SAT",
        "selected committed branch must be decisively satisfiable"
    );
}

// ---------------------------------------------------------------------------
// Datatype-aware bounded BMC refutation (#chc25-adt-bmc). The flat/level BMC
// encoding bails on datatype (ADT) sorts, so these ADT-LIA unsafe instances —
// a finite constructor counterexample reaching a bad state — degraded to
// Unknown. `solve_datatype_bounded_refutation` refutes them soundly (bounded
// tree unfolding decided by ay-dpll's native datatype theory; every candidate
// replayed against the ORIGINAL clauses).
// ---------------------------------------------------------------------------

// Serialize the env-var kill-switch test with the other DT-BMC tests on the one
// workspace env lock (`lock_env`) so the process-global `AY_CHC_DISABLE_DT_BMC`
// cannot race a concurrent solve.

// A genuine multi-step ADT refutation over a recursive datatype: P holds for
// every Nat reachable from `zero` by `succ`, and the query flags P(succ(succ
// zero)) as bad. The counterexample is the finite chain
// zero -> succ zero -> succ(succ zero), which only a datatype-aware bounded
// unfolding can find. The reconstructed witness (concrete constructor values)
// must replay Valid on the original clauses -> a validated Unsafe.
#[test]
// The timeout wrapper includes time spent waiting for the process-wide env
// lock.  Keep this above the aggregate budget of the serialized DT-BMC tests;
// otherwise a healthy test can time out before its body starts.
#[timeout(300_000)]
fn datatype_bounded_refutation_finds_nat_counterexample() {
    let _guard = lock_env();
    // Enabled for the whole test; restored on scope exit.
    let _enabled = ScopedEnvVar::unset("AY_CHC_DISABLE_DT_BMC");
    let input = r#"
(set-logic HORN)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun P (Nat) Bool)
(assert (forall ((n Nat)) (=> (= n zero) (P n))))
(assert (forall ((n Nat) (m Nat)) (=> (and (P n) (= m (succ n))) (P m))))
(assert (forall ((n Nat)) (=> (and (P n) (= n (succ (succ zero)))) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(input).expect("parse");
    assert!(
        problem.has_datatype_sorts(),
        "fixture must have a datatype-sorted predicate argument"
    );
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 8,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );
    let r = solver.solve_datatype_bounded_refutation(6, std::time::Duration::from_secs(30), 6000);
    assert!(
        matches!(r, ChcEngineResult::Unsafe(_)),
        "reachable ADT bad state must be a replay-validated Unsafe, got {r:?}"
    );
}

// Soundness pin: a SAFE datatype problem must NEVER be reported Unsafe. P
// counts up from `zero` by `succ`; the query fires only if P(n) & n = zero &
// (is-succ n) — an unsatisfiable guard, so the bad state is unreachable. The
// lane may only return Unknown here; a fabricated Unsafe would be a wrong
// answer (the campaign's cardinal sin).
#[test]
#[timeout(300_000)]
fn datatype_bounded_refutation_no_false_unsafe_on_safe() {
    let _guard = lock_env();
    // Enabled for the whole test; restored on scope exit.
    let _enabled = ScopedEnvVar::unset("AY_CHC_DISABLE_DT_BMC");
    let input = r#"
(set-logic HORN)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun P (Nat) Bool)
(assert (forall ((n Nat)) (=> (= n zero) (P n))))
(assert (forall ((n Nat) (m Nat)) (=> (and (P n) (= m (succ n))) (P m))))
(assert (forall ((n Nat)) (=> (and (P n) (= n zero) ((_ is succ) n)) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(input).expect("parse");
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 8,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );
    let r = solver.solve_datatype_bounded_refutation(6, std::time::Duration::from_secs(10), 6000);
    assert!(
        !matches!(r, ChcEngineResult::Unsafe(_)),
        "must not fabricate Unsafe on a SAFE datatype problem, got {r:?}"
    );
}

// Kill switch: with `AY_CHC_DISABLE_DT_BMC` set, the lane returns Unknown even
// on the known-unsafe fixture (it never runs), so the capability can be turned
// off without touching any other route.
#[test]
#[timeout(300_000)]
fn datatype_bounded_refutation_kill_switch_returns_unknown() {
    let _guard = lock_env();
    let input = r#"
(set-logic HORN)
(declare-datatypes ((Nat 0)) (((zero) (succ (pred Nat)))))
(declare-fun P (Nat) Bool)
(assert (forall ((n Nat)) (=> (= n (succ (succ zero))) (P n))))
(assert (forall ((n Nat)) (=> (and (P n) (= n (succ (succ zero)))) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(input).expect("parse");
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 8,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );
    let disabled = {
        let _disable = ScopedEnvVar::set("AY_CHC_DISABLE_DT_BMC", "1");
        solver.solve_datatype_bounded_refutation(6, std::time::Duration::from_secs(10), 6000)
    };
    assert!(
        matches!(disabled, ChcEngineResult::Unknown),
        "kill switch must suppress the lane (Unknown), got {disabled:?}"
    );
    // Sanity: with the switch cleared the same fixture is refuted, proving the
    // Unknown above came from the switch and not from an unsolvable fixture.
    let enabled =
        solver.solve_datatype_bounded_refutation(6, std::time::Duration::from_secs(30), 6000);
    assert!(
        matches!(enabled, ChcEngineResult::Unsafe(_)),
        "with the switch cleared the fixture must refute, got {enabled:?}"
    );
}

// Round-trip pin for the intermediate-variable ELIMINATION pass
// (#chc25-adt-bmc-unblock). This is the CHC-COMP25 ADT-LIA
// `productive_use_of_failure_drop_inj1` shape, inlined: an injectivity
// violation over `list_298`. A fact clause makes `drop_59 nil k nil` hold for
// ANY k (`A = B+1`, B universally quantified), so the query `drop(A,C,D) ∧
// drop(A,B,D) ∧ B≠C ⇒ false` has a DEPTH-0 counterexample (`drop nil 0 nil`
// via clause 0 and `drop nil 1 nil` via clause 2).
//
// The lane commits one clause selection, eliminates equality-defined node-arg
// variables, and reconstructs them into a replay-validated Unsafe witness. The
// raw indicator-gated formula historically returned `unknown`; newer executor
// model completion can decide this fixture directly, so raw incompleteness is
// no longer a precondition. The reconstructed witness must still carry the
// intermediate DATATYPE values (nil/cons), which the replay gate independently
// re-checks against the original clauses.
#[test]
#[timeout(300_000)]
fn datatype_bounded_refutation_elimination_round_trips_drop_inj1() {
    let _guard = lock_env();
    // Enabled for the whole test; restored on scope exit.
    let _enabled = ScopedEnvVar::unset("AY_CHC_DISABLE_DT_BMC");
    let input = r#"
(set-logic HORN)
(declare-datatypes ((list_298 0)) (((nil_331 ) (cons_296  (head_592 Int) (tail_594 list_298)))))
(declare-fun |drop_59| ( list_298 Int list_298 ) Bool)
(assert (forall ( (A list_298) (v_1 Int) (v_2 list_298) )
  (=> (and (and true (= 0 v_1) (= v_2 A))) (drop_59 A v_1 v_2))))
(assert (forall ( (A list_298) (B Int) (C list_298) (D Int) (E list_298) (F Int) )
  (=> (and (drop_59 C F E) (and (= B (+ 1 F)) (= A (cons_296 D E)))) (drop_59 C B A))))
(assert (forall ( (A Int) (B Int) (v_2 list_298) (v_3 list_298) )
  (=> (and (and (= A (+ 1 B)) (= v_2 nil_331) (= v_3 nil_331))) (drop_59 v_2 A v_3))))
(assert (forall ( (A list_298) (B Int) (C Int) (D list_298) )
  (=> (and (drop_59 A C D) (drop_59 A B D) (not (= B C))) false)))
(check-sat)
"#;
    let _no_elim = ScopedEnvVar::unset("AY_DT_BMC_NO_ELIM");
    let problem = crate::parser::ChcParser::parse(input).expect("parse");
    assert!(
        problem.has_datatype_sorts(),
        "fixture must have a datatype-sorted predicate argument"
    );
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            max_depth: 4,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );

    // The raw indicator-gated disjunction is satisfiable. It may be either Sat
    // (newer executor capability) or Unknown (the historical fallback trigger),
    // but it must never be reported Unsat.
    let raw = solver.dt_bmc_debug_raw_conjuncts(0);
    let (_, raw_eliminated_vars) = BmcSolver::eliminate_dt_bmc_intermediate_defs(&raw);
    assert!(
        raw_eliminated_vars
            .iter()
            .any(|var| matches!(&var.sort, ChcSort::Datatype { .. })),
        "fixture must exercise reconstruction of an eliminated datatype node argument; \
         eliminated={raw_eliminated_vars:?}"
    );
    let raw_disjunctive = ChcExpr::and_all(raw.clone());
    let mut smt = problem.make_smt_context();
    smt.set_executor_first_check_sat(true);
    let raw_verdict =
        smt.check_sat_with_timeout(&raw_disjunctive, std::time::Duration::from_secs(15));
    assert!(
        matches!(raw_verdict, SmtResult::Sat(_) | SmtResult::Unknown),
        "the known-satisfiable raw unfolding must not be reported Unsat, got {raw_verdict:?}"
    );

    // The lane resolves the disjunction into committed conjunctions, eliminates
    // the intermediate node-arg vars, and emits a replay-validated Unsafe at
    // depth 0 regardless of whether the raw capability above was Sat or Unknown.
    let converted =
        solver.solve_datatype_bounded_refutation(2, std::time::Duration::from_secs(30), 6000);
    let ChcEngineResult::Unsafe(cex) = converted else {
        panic!("the lane must produce replay-validated Unsafe, got {converted:?}");
    };

    // The reconstructed witness must carry concrete DATATYPE values (nil/cons):
    // the replay gate already re-validated the whole derivation against the
    // original clauses, and here we assert the intermediate ADT values actually
    // round-tripped into the witness (not just the LIA scalars).
    let witness = cex
        .witness
        .expect("a validated Unsafe cex must carry a derivation witness");
    let has_dt_value = witness.entries.iter().any(|e| {
        e.instances
            .values()
            .any(|v| matches!(v, SmtValue::Datatype(_, _)))
    });
    assert!(
        has_dt_value,
        "reconstructed witness must carry intermediate datatype (list) values; \
         entries={:?}",
        witness.entries
    );
}

// ---------------------------------------------------------------------------
// Committed-chain refutation on the IntDualyzer BV programs (CHC-COMP26
// eldarica-misc/BV/IntDualyzer). Their counterexample is a single deep
// straight-line derivation to the asserted-failure point (no branching);
// `solve_committed_chain_refutation` finds and VALIDATES it. Built-in safe and
// unsafe chains pin the behavior. External corpus campaigns live in bounded
// examples so ordinary tests are hermetic.
fn committed_chain(input: &str) -> ChcEngineResult {
    let problem = crate::parser::ChcParser::parse(input).expect("benchmark should parse");
    let solver = BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 8,
            acyclic_safe: false,
            ..BmcConfig::default()
        },
    );
    solver.solve_committed_chain_refutation(std::time::Duration::from_secs(15))
}

#[test]
fn committed_chain_refutes_bounded_unsafe_target() {
    const BUILTIN_UNSAFE: &str = r#"
(set-logic HORN)
(declare-fun P0 ((_ BitVec 8)) Bool)
(declare-fun P1 ((_ BitVec 8)) Bool)
(declare-fun P2 ((_ BitVec 8)) Bool)
(assert (P0 #x00))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (P0 x) (= y (bvadd x #x01))) (P1 y))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (P1 x) (= y (bvadd x #x01))) (P2 y))))
(assert (forall ((x (_ BitVec 8))) (=> (and (P2 x) (= x #x02)) false)))
(check-sat)
"#;
    let builtin = committed_chain(BUILTIN_UNSAFE);
    assert!(
        matches!(builtin, ChcEngineResult::Unsafe(_)),
        "built-in committed chain must produce validated Unsafe, got {builtin:?}"
    );
}

#[test]
fn committed_chain_leaves_two_step_unreachable_guard_not_unsafe() {
    const BUILTIN_SAFE: &str = r#"
(set-logic HORN)
(declare-fun P0 ((_ BitVec 8)) Bool)
(declare-fun P1 ((_ BitVec 8)) Bool)
(declare-fun P2 ((_ BitVec 8)) Bool)
(assert (P0 #x00))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (P0 x) (= y (bvadd x #x01))) (P1 y))))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (P1 x) (= y (bvadd x #x01))) (P2 y))))
(assert (forall ((x (_ BitVec 8))) (=> (and (P2 x) (= x #x03)) false)))
(check-sat)
"#;
    let builtin = committed_chain(BUILTIN_SAFE);
    assert!(
        !matches!(builtin, ChcEngineResult::Unsafe(_)),
        "two-step chain reaches only #x02, not #x03; got {builtin:?}"
    );
}

// ===== #chc25-bmc-sweep: sweep past a spurious/unconfirmable shallow SAT =====

/// SOUNDNESS (non-negotiable): with the sweep-past-spurious-SAT policy ON
/// (default), a SAFE problem must NEVER be reported Unsafe, even though the
/// sweep now advances past shallow SATs instead of terminating on the first
/// one. `bmc_sat_result` only yields Unsafe when the witness replays as Valid
/// against the original clauses, which fails closed on safe problems, so every
/// depth here classifies as `Advance` and the run exhausts to Safe/Unknown.
#[test]
#[timeout(120000)]
fn test_sweep_past_spurious_safe_problem_never_unsafe() {
    assert!(
        BmcConfig::default().sweep_past_spurious_sat,
        "sweep must be ON by default for this soundness test"
    );
    for problem in [
        create_safe_problem(),
        create_multipred_cyclic_safe_problem(),
    ] {
        let solver = BmcSolver::new(
            problem,
            BmcConfig::default()
                .with_max_depth(12)
                .with_time_budget(std::time::Duration::from_secs(20)),
        );
        let result = solver.solve();
        assert!(
            !matches!(result, ChcEngineResult::Unsafe(_)),
            "sweep must never fabricate Unsafe on a safe problem, got {result:?}"
        );
    }
}

/// RECURSION / TERMINATION SAFETY: the sweep's strict check is the
/// already-present, NON-recursive `bmc_sat_result` (witness extraction + a
/// `PdrSolver` replay whose own `disable_cex_replay` stops it re-entering BMC),
/// so advancing past a spurious SAT launches NO nested BMC — the search cannot
/// loop BMC→confirm→BMC. The `#[timeout]` is the termination assertion: an
/// unbounded loop would blow the deadline. The verdict must still be the
/// genuine refutation (Unsafe with a witness).
#[test]
#[timeout(120000)]
fn test_sweep_past_spurious_terminates_and_refutes_unsafe() {
    let solver = BmcSolver::new(
        create_simple_unsafe_problem(),
        BmcConfig::default()
            .with_max_depth(20)
            .with_time_budget(std::time::Duration::from_secs(30)),
    );
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("expected Unsafe on a genuinely unsafe problem, got {result:?}");
    };
    assert!(
        cex.witness.is_some_and(|w| !w.entries.is_empty()),
        "the refutation must carry a verified derivation witness"
    );
}

/// Genuine SHALLOW counterexample (the positive-control shape): a depth-0/1 cex
/// must still be found under the sweep policy — the bounded confirmation
/// validates it quickly and the lane returns Unsafe rather than sweeping past
/// it. `create_two_phase_unsafe_problem` reaches its error in a couple of
/// steps.
#[test]
#[timeout(120000)]
fn test_sweep_past_spurious_preserves_genuine_shallow_cex() {
    let solver = BmcSolver::new(
        create_two_phase_unsafe_problem(),
        BmcConfig::default()
            .with_max_depth(20)
            .with_time_budget(std::time::Duration::from_secs(30)),
    );
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "a genuine shallow counterexample must still be refuted, got {result:?}"
    );
}

/// #42 (model-checker-consumer #39 bisect): the proof cross-check role must NOT sweep past
/// spurious shallow SATs — on a problem another engine just proved Safe no
/// witness can ever validate, so the sweep is pure wasted budget. Default
/// (counterexample-hunting) keeps the sweep ON.
#[test]
fn cross_check_config_disables_spurious_sat_sweep_42() {
    assert!(
        !BmcConfig::cross_check().sweep_past_spurious_sat,
        "cross_check() must disable the spurious-SAT sweep"
    );
    assert!(
        BmcConfig::default().sweep_past_spurious_sat,
        "default config must keep the sweep enabled for counterexample hunting"
    );
}

#[test]
fn trace_get_value_keeps_exact_neighbors_of_unavailable_array_read_9185() {
    let bv32 = ChcSort::BitVec(32);
    let array = ChcVar::new(
        "Init#0_0",
        ChcSort::Array(Box::new(bv32.clone()), Box::new(bv32.clone())),
    );
    let values = vec![
        BmcTraceValue::Var(ChcVar::new("Init#0", ChcSort::Bool)),
        BmcTraceValue::ArraySelectPath {
            array: array.clone(),
            indices: vec![(ChcExpr::BitVec(0, 32), bv32.clone())],
            value_sort: bv32.clone(),
        },
        BmcTraceValue::ArraySelectPath {
            array: array.clone(),
            indices: vec![(ChcExpr::BitVec(38, 32), bv32.clone())],
            value_sort: bv32,
        },
        BmcTraceValue::Var(ChcVar::new("Bad#1", ChcSort::Bool)),
    ];
    let outputs = vec![
        "sat".to_string(),
        "(error \"model value for array |Init#0_0| is not available\")".to_string(),
        "((Init#0 true))".to_string(),
        "(((select Init#0_0 (_ bv0 32)) #x00000000))".to_string(),
        "(error \"value of (select Init#0_0 (_ bv38 32)) is not available\")".to_string(),
        "((Bad#1 true))".to_string(),
    ];

    let mut model = FxHashMap::default();
    BmcSolver::parse_trace_get_value_outputs_into_model(&mut model, &values, &outputs);

    assert_eq!(model.get("Init#0"), Some(&SmtValue::Bool(true)));
    assert_eq!(model.get("Bad#1"), Some(&SmtValue::Bool(true)));
    assert_eq!(
        model.get("Init#0_0"),
        Some(&SmtValue::ArrayMap {
            default: Box::new(SmtValue::BitVec(0, 32)),
            entries: vec![(SmtValue::BitVec(0, 32), SmtValue::BitVec(0, 32))],
        })
    );

    let mut commands = String::new();
    BmcSolver::append_trace_get_value_commands(&mut commands, &values);
    assert_eq!(commands.matches("(get-value (").count(), values.len());
}

#[test]
fn trace_get_value_reconstructs_nested_array_reads_with_collided_array_keys() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(int_array.clone()));
    let f = ChcVar::new("F", nested);
    let p = ChcVar::new("P", int_array.clone());
    let e = ChcVar::new("E", int_array.clone());
    let p_read = ChcExpr::select(
        ChcExpr::select(ChcExpr::var(f.clone()), ChcExpr::var(p.clone())),
        ChcExpr::int(0),
    );
    let e_read = ChcExpr::select(
        ChcExpr::select(ChcExpr::var(f.clone()), ChcExpr::var(e.clone())),
        ChcExpr::int(0),
    );

    let mut values = Vec::new();
    let mut seen = FxHashSet::default();
    BmcSolver::collect_trace_array_selects(&p_read, &mut values, &mut seen);
    BmcSolver::collect_trace_array_selects(&e_read, &mut values, &mut seen);
    assert_eq!(
        values.len(),
        2,
        "each scalar nested leaf must be observed exactly once"
    );
    assert!(values.iter().all(|value| matches!(
        value,
        BmcTraceValue::ArraySelectPath { indices, .. } if indices.len() == 2
    )));

    // This is the lossy executor rendering seen on the Solidity shard: P and E
    // print as the same const array even though the exact leaf observations
    // differ. The finite completion must separate only that collided key and
    // install both nested cells.
    let zero_array = SmtValue::ConstArray(Box::new(SmtValue::Int(0)));
    let mut model = FxHashMap::default();
    model.insert("P".to_string(), zero_array.clone());
    model.insert(
        "E".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            // Extensionally equal to P despite a different representation.
            entries: vec![(SmtValue::Int(5), SmtValue::Int(0))],
        },
    );
    model.insert("F".to_string(), SmtValue::ConstArray(Box::new(zero_array)));
    let outputs = vec![
        "(((select (select F P) 0) 1))".to_string(),
        "(((select (select F E) 0) 2))".to_string(),
    ];
    BmcSolver::parse_trace_get_value_outputs_into_model(&mut model, &values, &outputs);

    assert_ne!(
        model.get("P"),
        model.get("E"),
        "incompatible leaves force the rendered array-valued keys apart"
    );
    assert_eq!(evaluate_expr(&p_read, &model), Some(SmtValue::Int(1)));
    assert_eq!(evaluate_expr(&e_read, &model), Some(SmtValue::Int(2)));
    assert_eq!(
        evaluate_expr(&ChcExpr::ne(p_read, e_read), &model),
        Some(SmtValue::Bool(true))
    );
}

#[test]
fn trace_get_value_reconstruction_reaches_array_key_dependency_fixpoint() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(int_array.clone()));
    let f = ChcVar::new("F", nested);
    let e = ChcVar::new("E", int_array);
    let outer_read = ChcExpr::select(
        ChcExpr::select(ChcExpr::var(f.clone()), ChcExpr::var(e.clone())),
        ChcExpr::int(0),
    );
    let key_read = ChcExpr::select(ChcExpr::var(e.clone()), ChcExpr::int(5));

    // Deliberately collect the dependent outer read first. A one-pass
    // reconstruction installs F's cell under E=const(0), then changes E while
    // installing E[5]=9, and loses the outer observation.
    let mut values = Vec::new();
    let mut seen = FxHashSet::default();
    BmcSolver::collect_trace_array_selects(&outer_read, &mut values, &mut seen);
    BmcSolver::collect_trace_array_selects(&key_read, &mut values, &mut seen);

    let zero_array = SmtValue::ConstArray(Box::new(SmtValue::Int(0)));
    let mut model = FxHashMap::default();
    model.insert("E".to_string(), zero_array.clone());
    model.insert("F".to_string(), SmtValue::ConstArray(Box::new(zero_array)));
    let outputs = vec![
        "(((select (select F E) 0) 7))".to_string(),
        "(((select E 5) 9))".to_string(),
    ];
    BmcSolver::parse_trace_get_value_outputs_into_model(&mut model, &values, &outputs);

    assert_eq!(evaluate_expr(&key_read, &model), Some(SmtValue::Int(9)));
    assert_eq!(
        evaluate_expr(&outer_read, &model),
        Some(SmtValue::Int(7)),
        "the outer cell must be reinstalled under E's finalized concrete value"
    );
}

#[test]
fn trace_reconstruction_separates_collided_composite_array_keys() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let key_source_sort = (0..4).fold(int_array.clone(), |value_sort, _| {
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(value_sort))
    });
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(int_array.clone()));
    let j = ChcVar::new("J", nested);
    let e = ChcVar::new("E", key_source_sort.clone());
    let c = ChcVar::new("C", key_source_sort.clone());
    let h = ChcVar::new("H", ChcSort::Int);
    let select_four = |array: &ChcVar| {
        (0..4).fold(ChcExpr::var(array.clone()), |read, _| {
            ChcExpr::select(read, ChcExpr::var(h.clone()))
        })
    };
    let e_key = select_four(&e);
    let c_key = select_four(&c);
    let e_read = ChcExpr::select(
        ChcExpr::select(ChcExpr::var(j.clone()), e_key.clone()),
        ChcExpr::int(0),
    );
    let c_read = ChcExpr::select(
        ChcExpr::select(ChcExpr::var(j.clone()), c_key.clone()),
        ChcExpr::int(0),
    );

    let mut model = FxHashMap::default();
    model.insert(
        "J".to_string(),
        BmcSolver::default_smt_value_for_sort(&j.sort).expect("nested array has a default"),
    );
    let default_key_source =
        BmcSolver::default_smt_value_for_sort(&key_source_sort).expect("array has a default");
    model.insert("E".to_string(), default_key_source.clone());
    model.insert("C".to_string(), default_key_source);
    model.insert("H".to_string(), SmtValue::Int(0));

    let observations = vec![
        BmcArrayObservation {
            array: j.clone(),
            indices: vec![
                (e_key.clone(), int_array.clone()),
                (ChcExpr::int(0), ChcSort::Int),
            ],
            value: SmtValue::Int(1),
        },
        BmcArrayObservation {
            array: j,
            indices: vec![(c_key.clone(), int_array), (ChcExpr::int(0), ChcSort::Int)],
            value: SmtValue::Int(2),
        },
    ];
    BmcSolver::reconstruct_trace_array_observations(&mut model, &observations);

    assert_ne!(
        evaluate_expr(&e_key, &model),
        evaluate_expr(&c_key, &model),
        "the composite C[H][H][H][H] key must be finitely separated"
    );
    assert_eq!(evaluate_expr(&e_read, &model), Some(SmtValue::Int(1)));
    assert_eq!(evaluate_expr(&c_read, &model), Some(SmtValue::Int(2)));
}

#[test]
fn nested_select_formula_abstraction_covers_prefix_and_query_consistently() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(int_array.clone()));
    let f = ChcVar::new("F", nested);
    let p = ChcVar::new("P", int_array);
    let leaf = ChcExpr::select(
        ChcExpr::select(ChcExpr::var(f), ChcExpr::var(p)),
        ChcExpr::int(0),
    );
    let prefix = ChcExpr::ge(leaf.clone(), ChcExpr::int(0));
    let query = ChcExpr::ne(leaf.clone(), ChcExpr::int(7));

    let abstraction = BmcSolver::abstract_nested_select_formula(
        std::slice::from_ref(&prefix),
        &[vec![query.clone()]],
        3,
        &FxHashSet::default(),
        None,
    )
    .expect("the nested scalar select should be abstracted across the full formula");
    let abstract_prefix = abstraction.prefix_conjuncts;
    let abstract_groups = abstraction.query_groups;
    let aliases = abstraction.select_aliases;

    assert_eq!(
        aliases.len(),
        1,
        "structurally identical reads must share one alias"
    );
    assert_eq!(aliases[0].original, leaf);
    let replacement = [(
        aliases[0].original.clone(),
        ChcExpr::var(aliases[0].alias.clone()),
    )];
    let expected_prefix = prefix.substitute_expr_pairs(&replacement);
    let expected_query = query.substitute_expr_pairs(&replacement);
    assert_eq!(
        abstract_prefix,
        vec![expected_prefix],
        "the rule-prefix occurrence must be relaxed"
    );
    assert_eq!(
        abstract_groups,
        vec![vec![expected_query]],
        "the same alias must be reused in the query without changing its Boolean skeleton"
    );
}

#[test]
fn nested_select_formula_abstraction_budget_covers_more_than_64_prefix_reads() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(int_array.clone()));
    let f = ChcVar::new("F", nested);
    let p = ChcVar::new("P", int_array);
    let make_prefix = |count: usize| {
        (0..count)
            .map(|index| {
                let leaf = ChcExpr::select(
                    ChcExpr::select(ChcExpr::var(f.clone()), ChcExpr::var(p.clone())),
                    ChcExpr::int(i128::try_from(index).expect("small test index fits i128")),
                );
                ChcExpr::ge(leaf, ChcExpr::int(0))
            })
            .collect::<Vec<_>>()
    };

    let prefix = make_prefix(65);
    let abstraction = BmcSolver::abstract_nested_select_formula(
        &prefix,
        &[vec![ChcExpr::Bool(true)]],
        7,
        &FxHashSet::default(),
        None,
    )
    .expect("the bounded candidate abstraction must cover a 65-read accumulated prefix");
    let abstract_prefix = abstraction.prefix_conjuncts;
    let aliases = abstraction.select_aliases;
    assert_eq!(aliases.len(), 65);
    assert_eq!(abstract_prefix.len(), prefix.len());
    let mut remaining_nested_leaves = Vec::new();
    let mut seen_nested_leaves = FxHashSet::default();
    let mut traversal_budget = BmcNestedArrayTraversalBudget::new(MAX_PREPROCESSING_NODES, None);
    for expr in &abstract_prefix {
        BmcSolver::collect_nested_select_alias_terms(
            expr,
            &mut remaining_nested_leaves,
            &mut seen_nested_leaves,
            &mut traversal_budget,
        )
        .expect("the test prefix stays within the traversal budget");
    }
    assert!(
        remaining_nested_leaves.is_empty(),
        "every nested leaf must be replaced while its surrounding constraint remains"
    );

    let over_budget = make_prefix(MAX_NESTED_SELECT_CANDIDATE_ALIASES + 1);
    assert!(
        BmcSolver::abstract_nested_select_formula(
            &over_budget,
            &[vec![ChcExpr::Bool(true)]],
            16,
            &FxHashSet::default(),
            None,
        )
        .is_none(),
        "candidate generation must remain hard-capped"
    );
}

#[test]
fn nested_array_candidate_walk_budget_fails_closed_during_traversal() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(int_array.clone()));
    let f = ChcVar::new("F", nested);
    let p = ChcVar::new("P", int_array);
    let leaf = ChcExpr::select(
        ChcExpr::select(ChcExpr::var(f), ChcExpr::var(p)),
        ChcExpr::int(0),
    );
    let formula = ChcExpr::and_all([
        ChcExpr::eq(leaf.clone(), ChcExpr::int(0)),
        ChcExpr::eq(leaf, ChcExpr::int(1)),
    ]);
    let mut leaves = Vec::new();
    let mut seen = FxHashSet::default();
    let mut budget = BmcNestedArrayTraversalBudget::new(1, None);

    assert_eq!(
        BmcSolver::collect_nested_select_alias_terms(&formula, &mut leaves, &mut seen, &mut budget,),
        Err(BmcNestedArrayCandidateAbort::NodeBudgetOrDeadline),
        "candidate traversal must stop at its shared node budget"
    );
}

#[test]
fn nested_array_candidate_equality_graph_is_hard_capped() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(int_array));
    let variables: Vec<ChcVar> = (0..=MAX_NESTED_ARRAY_CANDIDATE_EQUALITIES + 1)
        .map(|index| ChcVar::new(format!("A{index}"), nested.clone()))
        .collect();
    let equalities: Vec<ChcExpr> = variables
        .windows(2)
        .map(|pair| ChcExpr::eq(ChcExpr::var(pair[0].clone()), ChcExpr::var(pair[1].clone())))
        .collect();
    let mut budget = BmcNestedArrayTraversalBudget::new(MAX_PREPROCESSING_NODES, None);

    assert!(
        matches!(
            BmcSolver::nested_array_var_equivalences(equalities.iter(), &mut budget),
            Err(BmcNestedArrayCandidateAbort::EqualityCap)
        ),
        "an adversarial equality graph must fail closed at the edge cap"
    );
}

#[test]
fn nested_array_candidate_rejects_nonvariable_select_roots_before_tokenization() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let nested = ChcSort::Array(Box::new(ChcSort::Int), Box::new(int_array.clone()));
    let f = ChcVar::new("F", nested);
    let value = ChcVar::new("V", int_array.clone());
    let output = ChcVar::new("O", int_array);
    let stored = ChcExpr::store(ChcExpr::var(f), ChcExpr::int(0), ChcExpr::var(value));
    let nonvariable_root_read = ChcExpr::select(stored, ChcExpr::int(0));
    let formula = ChcExpr::eq(ChcExpr::var(output), nonvariable_root_read);

    assert!(
        BmcSolver::abstract_nested_select_formula(
            std::slice::from_ref(&formula),
            &[vec![ChcExpr::Bool(true)]],
            4,
            &FxHashSet::default(),
            None,
        )
        .is_none(),
        "tokenizing the store below this select would be ill-typed, so the candidate must fail closed"
    );
}

#[test]
fn nested_array_candidate_scalarizes_state_and_reconstructs_array_valued_reads() {
    let int_array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let field_map = ChcSort::Array(Box::new(ChcSort::Int), Box::new(int_array.clone()));
    let nested = ChcSort::Array(Box::new(int_array.clone()), Box::new(field_map));
    let f = ChcVar::new("F", nested.clone());
    let g = ChcVar::new("G", nested);
    let key = ChcVar::new("P", int_array.clone());
    let output = ChcVar::new("O", int_array.clone());
    let read = |array: &ChcVar| {
        ChcExpr::select(
            ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::var(key.clone())),
            ChcExpr::int(3),
        )
    };
    let f_read = read(&f);
    let g_read = read(&g);
    let prefix = ChcExpr::and_all([
        ChcExpr::eq(ChcExpr::var(f.clone()), ChcExpr::var(g.clone())),
        ChcExpr::eq(ChcExpr::var(output), f_read.clone()),
    ]);
    let query = ChcExpr::eq(g_read.clone(), ChcExpr::var(key.clone()));

    let abstraction = BmcSolver::abstract_nested_select_formula(
        std::slice::from_ref(&prefix),
        &[vec![query]],
        9,
        &FxHashSet::default(),
        None,
    )
    .expect("array-valued reads and nested state should both be abstracted");

    assert_eq!(abstraction.select_aliases.len(), 2);
    assert_eq!(abstraction.state_tokens.len(), 2);
    assert_eq!(abstraction.equal_state.len(), 1);
    let mut residual_budget = BmcNestedArrayTraversalBudget::new(MAX_PREPROCESSING_NODES, None);
    assert!(
        abstraction
            .prefix_conjuncts
            .iter()
            .chain(abstraction.query_groups.iter().flatten())
            .all(|expr| matches!(
                BmcSolver::expr_contains_nested_array_sort(expr, &mut residual_budget),
                Ok(false)
            )),
        "the candidate formula must contain no nested-array roots"
    );

    let candidate_exprs: Vec<&ChcExpr> = abstraction
        .prefix_conjuncts
        .iter()
        .chain(abstraction.query_groups.iter().flatten())
        .collect();
    let mut declared = FxHashSet::default();
    let mut candidate_smt = String::from("(set-logic AUFLIA)\n");
    for expr in &candidate_exprs {
        for variable in expr.vars() {
            if declared.insert(variable.name.clone()) {
                candidate_smt.push_str(&format!(
                    "(declare-const {} {})\n",
                    quote_symbol(&variable.name),
                    sort_to_smtlib(&variable.sort)
                ));
            }
        }
        candidate_smt.push_str(&format!(
            "(assert {})\n",
            InvariantModel::expr_to_smtlib(expr)
        ));
    }
    candidate_smt.push_str("(check-sat)\n");
    assert!(
        ay_frontend::parse(&candidate_smt).is_ok(),
        "scalarizing nested state must preserve SMT typing"
    );

    let observed_value = SmtValue::ConstArray(Box::new(SmtValue::Int(7)));
    let mut model = FxHashMap::default();
    model.insert(
        key.name.clone(),
        BmcSolver::default_smt_value_for_sort(&key.sort).expect("flat array has a default"),
    );
    for alias in &abstraction.select_aliases {
        model.insert(alias.alias.name.clone(), observed_value.clone());
    }
    let completed = BmcSolver::reconstruct_nested_select_aliases(
        &mut model,
        &abstraction.select_aliases,
        &abstraction.state_tokens,
        &abstraction.equal_state,
    );

    assert_eq!(completed, 2);
    assert_eq!(evaluate_expr(&f_read, &model), Some(observed_value.clone()));
    assert_eq!(evaluate_expr(&g_read, &model), Some(observed_value));
    assert_eq!(
        model.get(&f.name),
        model.get(&g.name),
        "directly equal nested state must share one reconstructed finite value"
    );
    assert!(
        abstraction
            .state_tokens
            .iter()
            .all(|token| !model.contains_key(&token.alias.name)),
        "candidate-only scalar tokens must not leak into exact replay"
    );
}

#[test]
#[timeout(30_000)]
fn nested_select_observation_candidate_is_not_a_verdict() {
    let src = r#"
(set-logic HORN)
(declare-fun Observe () Bool)
(assert
  (forall
    ((F (Array (Array Int Int) (Array Int Int)))
     (G (Array (Array Int Int) (Array Int Int)))
     (P (Array Int Int)))
    (=>
      (and
        (= F G)
        (not
          (=
            (select (select F P) 0)
            (select (select G P) 0))))
      Observe)))
(assert (=> Observe false))
"#;
    let problem = crate::ChcParser::parse(src).expect("nested-array CHC should parse");
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(0)
            .with_time_budget(std::time::Duration::from_secs(10))
            .with_per_depth_timeout(std::time::Duration::from_secs(10)),
    );
    let queries: Vec<_> = solver.problem.queries().collect();

    let mut level_conjuncts = Vec::new();
    solver.compile_level_flat(0, &mut level_conjuncts);
    let query_groups = solver.compile_query_groups(&queries, 0);
    assert!(
        BmcSolver::abstract_nested_select_formula(
            &[],
            &query_groups,
            0,
            &FxHashSet::default(),
            None,
        )
        .is_none(),
        "the nullary query has no leaves; this regression requires prefix abstraction"
    );
    let model = solver
        .try_nested_select_observation_candidate(
            &level_conjuncts,
            &query_groups,
            0,
            false,
            Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(10)),
        )
        .expect("the relaxed disequality should yield a finite candidate");

    assert!(
        matches!(
            solver.classify_flat_sat(&model, 0, &queries),
            FlatSatOutcome::Advance
        ),
        "a relaxed SAT assignment that violates F = G must fail unchanged original-clause replay"
    );
}

fn chccomp25_solidity_slice_result(name: &str) -> Option<ChcEngineResult> {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join("benchmarks/chc/chc-comp25-benchmarks/solidity/no_adts/unit_tests/abi")
        .join(name);
    let input = std::fs::read_to_string(path).ok()?;
    let problem = crate::parser::ChcParser::parse(&input).expect("slice benchmark should parse");
    let summary = crate::portfolio::PreprocessSummary::build(problem, false);
    let bmc = BmcConfig::default()
        .with_max_depth(16)
        .with_time_budget(std::time::Duration::from_secs(10))
        .with_per_depth_timeout(std::time::Duration::from_secs(10));
    let config =
        crate::portfolio::PortfolioConfig::with_engines(vec![crate::portfolio::EngineConfig::Bmc(
            bmc,
        )])
        .parallel(false)
        .timeout(Some(std::time::Duration::from_secs(10)))
        .preprocessing(false);
    Some(crate::portfolio::PortfolioSolver::from_summary(summary, config).solve())
}

#[test]
#[ignore = "requires the downloaded CHC-COMP-25 Solidity corpus"]
#[timeout(30_000)]
fn nested_select_candidate_refutes_both_chccomp25_array_slice_targets() {
    for name in [
        "abi_encode_array_slice.sol_0_no_adts_000.smt2",
        "abi_encode_packed_array_slice.sol_0_no_adts_000.smt2",
    ] {
        let Some(result) = chccomp25_solidity_slice_result(name) else {
            eprintln!("SKIP {name}: corpus not present");
            continue;
        };
        assert!(
            matches!(result, ChcEngineResult::Unsafe(_)),
            "{name} (Z3: unsat / CHC unsafe) must produce a replay-validated Unsafe, got {result:?}"
        );
    }
}

fn flat_observation_phase_problem(query_value: i128) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("Observe", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(predicate, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(predicate, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(query_value))),
        ),
        ClauseHead::False,
    ));
    problem
}

#[test]
#[timeout(60000)]
fn flat_bmc_unsat_depths_execute_no_model_observation_commands_9185() {
    let problem = flat_observation_phase_problem(1);

    reset_trace_observation_commands_for_tests();
    let acyclic = BmcSolver::new(problem.clone(), BmcConfig::default());
    let acyclic_queries: Vec<_> = acyclic.problem.queries().collect();
    assert!(matches!(
        acyclic.solve_acyclic_exhaustive_once(&acyclic_queries, 3),
        Some(ChcEngineResult::Safe(_))
    ));
    assert_eq!(
        trace_observation_command_count_for_tests(),
        0,
        "acyclic UNSAT must not build or execute model observations"
    );

    reset_trace_observation_commands_for_tests();
    let persistent = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            enable_adaptive_stepping: false,
            ..BmcConfig::default()
        },
    );
    let persistent_queries: Vec<_> = persistent.problem.queries().collect();
    assert!(matches!(
        persistent.solve_single_executor(&persistent_queries, 3),
        Some(SingleExecutorOutcome::Solved(ChcEngineResult::Unknown))
    ));
    assert!(persistent.stats().num_checks > 0);
    assert_eq!(
        trace_observation_command_count_for_tests(),
        0,
        "persistent UNSAT depths must not build or execute model observations"
    );

    reset_trace_observation_commands_for_tests();
    let fresh = BmcSolver::new(problem, BmcConfig::default());
    let fresh_queries: Vec<_> = fresh.problem.queries().collect();
    assert!(matches!(
        fresh.solve_per_depth_fresh(&fresh_queries, 3, 0, 0, false),
        Some(ChcEngineResult::Unknown)
    ));
    assert!(fresh.stats().num_checks > 0);
    assert_eq!(
        trace_observation_command_count_for_tests(),
        0,
        "fresh UNSAT depths must not build or execute model observations"
    );
}

#[test]
#[timeout(60000)]
fn flat_bmc_sat_executes_one_model_and_one_command_per_trace_value_9185() {
    let problem = flat_observation_phase_problem(0);
    let solver = BmcSolver::new(problem, BmcConfig::default());
    let queries: Vec<_> = solver.problem.queries().collect();

    reset_trace_observation_commands_for_tests();
    assert!(matches!(
        solver.solve_per_depth_fresh(&queries, 0, 0, 0, false),
        Some(ChcEngineResult::Unsafe(_))
    ));
    assert_eq!(
        trace_observation_command_count_for_tests(),
        3,
        "one get-model plus singleton observations for Observe#0 and Observe#0_0"
    );
}

// ===== Polynomial-DAG budget compliance (model-checker-consumer wishlist item 3) =====

/// Wide acyclic Int DAG whose predicate indices run OPPOSITE to the chain
/// direction, so the polynomial-DAG lane's arg-constant/arg-bound fixpoints
/// (which scan `ordered_cone` in ascending index order) propagate only ONE
/// predicate per round — O(preds) rounds x O(preds x arity x clauses)
/// simplification work per round. This reproduces the wishlist-item-3 shape
/// where the encoding phases dominated wall time and previously ran with no
/// deadline poll at all.
///
/// Two rule variants per hop (distinct constraints, agreeing ground head
/// values) keep the constant inference resolving every round AND put the
/// path count at 2^(preds-1), far over the exact-expansion cap, forcing the
/// polynomial DAG encoding.
fn create_reversed_acyclic_int_dag_for_budget(pred_count: usize, arity: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let preds: Vec<_> = (0..pred_count)
        .map(|idx| problem.declare_predicate(&format!("BudgetDag{idx}"), vec![ChcSort::Int; arity]))
        .collect();
    let vars: Vec<ChcVar> = (0..arity)
        .map(|k| ChcVar::new(format!("x{k}"), ChcSort::Int))
        .collect();
    let var_args: Vec<ChcExpr> = vars.iter().map(|v| ChcExpr::var(v.clone())).collect();

    // Entry fact on the HIGHEST predicate index (chain position 0).
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(
            preds[pred_count - 1],
            (0..arity).map(|k| ChcExpr::int(k as i64)).collect(),
        ),
    ));

    // Chain hops toward LOWER predicate indices: preds[i+1] -> preds[i].
    for idx in (0..pred_count - 1).rev() {
        let head_args: Vec<ChcExpr> = vars
            .iter()
            .map(|v| ChcExpr::add(ChcExpr::var(v.clone()), ChcExpr::int(1)))
            .collect();
        for constraint in [
            ChcExpr::ge(ChcExpr::var(vars[0].clone()), ChcExpr::int(0)),
            ChcExpr::le(ChcExpr::var(vars[0].clone()), ChcExpr::int(1_000_000)),
        ] {
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![(preds[idx + 1], var_args.clone())], Some(constraint)),
                ClauseHead::Predicate(preds[idx], head_args.clone()),
            ));
        }
    }

    // Unreachable query on the chain tail (x0 grows from 0, never -1).
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(preds[0], var_args.clone())],
            Some(ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::int(-1))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// MODEL_CHECKER_CONSUMER wishlist item 3 regression: a tiny time budget on a large
/// acyclic system must yield Unknown with `stats.budget_exhausted` QUICKLY —
/// previously the polynomial-DAG encoding's inference fixpoints and
/// per-clause simplification ran unbounded (>150s on coroutine-shaped
/// cones; tens of seconds on this synthetic shape) before any deadline
/// poll fired.
#[test]
#[timeout(120_000)]
fn test_polynomial_dag_budget_compliance_returns_unknown_quickly() {
    let problem = create_reversed_acyclic_int_dag_for_budget(300, 10);
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 300,
        acyclic_safe: true,
        time_budget: Some(std::time::Duration::from_millis(50)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let start = ay_core::time::Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();

    assert!(
        matches!(result, ChcEngineResult::Unknown),
        "expected Unknown on budget expiry, got {result:?}"
    );
    assert!(
        solver.stats().budget_exhausted,
        "budget expiry must set stats.budget_exhausted (classified as the \
         Unknown-budget verdict by classify_bmc_only_unknown)"
    );
    // Generous wall bound to avoid load flake; the point is that the lane no
    // longer runs the whole encoding (tens of seconds) past a 50ms budget.
    assert!(
        elapsed < std::time::Duration::from_secs(10),
        "polynomial-DAG lane must honor its deadline, took {elapsed:?}"
    );
}

/// Deadline expiry inside the interval collector must surface as
/// `Err(DagBudgetExpired)` — NEVER as the `Ok(false)` infeasibility answer,
/// which the arg-bounds fixpoint uses to SKIP a clause's contribution
/// (asserting under-joined bounds as facts would risk a false Safe).
#[test]
fn test_interval_bounds_expiry_distinct_from_infeasibility() {
    let x = ChcVar::new("x", ChcSort::Int);
    // A conjunct set that IS infeasible: x < 0 and x > 0.
    let conjuncts = vec![
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
    ];

    // Already-expired deadline: expiry must win over the infeasibility
    // answer so callers can never mistake a timeout for a proof fact.
    let mut env = FxHashMap::default();
    let expired = BmcSolver::collect_conjunct_interval_bounds(
        &conjuncts,
        &mut env,
        Some(ay_core::time::Instant::now()),
    );
    assert!(
        matches!(expired, Err(DagBudgetExpired)),
        "expired deadline must return Err(DagBudgetExpired), got {expired:?}"
    );

    // No deadline: the genuine infeasibility answer is preserved.
    let mut env = FxHashMap::default();
    let infeasible = BmcSolver::collect_conjunct_interval_bounds(&conjuncts, &mut env, None);
    assert!(
        matches!(infeasible, Ok(false)),
        "infeasible conjuncts without a deadline must return Ok(false), got {infeasible:?}"
    );
}

// ===== Int-free interval-machinery skip (model-checker-consumer wishlist item 4c) =====

/// Branching acyclic BV(8) chain: `pred_count-1` hops, two rules per hop
/// (`x+1` / `x+2`), so the path count is 2^(pred_count-1) and the
/// polynomial-DAG encoding is forced once it exceeds the 1024-path cap.
/// No Int-sorted args anywhere, so every clause takes the item-4c
/// interval-machinery skip path.
fn create_branching_acyclic_bv_chain(pred_count: usize, query_value: u128) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let preds: Vec<_> = (0..pred_count)
        .map(|idx| problem.declare_predicate(&format!("BvChain{idx}"), vec![ChcSort::BitVec(8)]))
        .collect();
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(preds[0], vec![ChcExpr::BitVec(0, 8)]),
    ));
    for idx in 1..pred_count {
        for step in [1u128, 2u128] {
            problem.add_clause(HornClause::new(
                ClauseBody::predicates_only(vec![(preds[idx - 1], vec![ChcExpr::var(x.clone())])]),
                ClauseHead::Predicate(
                    preds[idx],
                    vec![ChcExpr::Op(
                        ChcOp::BvAdd,
                        vec![
                            Arc::new(ChcExpr::var(x.clone())),
                            Arc::new(ChcExpr::BitVec(step, 8)),
                        ],
                    )],
                ),
            ));
        }
    }
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(preds[pred_count - 1], vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x),
                ChcExpr::BitVec(query_value, 8),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

/// Item 4c soundness: skipping the Int-interval machinery on Int-free
/// clauses must not change verdicts. After 11 branching BV steps from 0
/// (+1/+2 per step) the reachable range is [11, 22]; 200 is unreachable,
/// so the polynomial-DAG lane must still prove Safe.
#[test]
#[timeout(120_000)]
fn test_polynomial_dag_bv_chain_safe_with_interval_skip() {
    let problem = create_branching_acyclic_bv_chain(12, 200);
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 12,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        time_budget: Some(std::time::Duration::from_mins(1)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "unreachable BV query must stay Safe with the interval machinery skipped, got {result:?}"
    );
}

/// Item 4c soundness, unsafe-shape direction: 11 IS reachable (all-`+1`
/// path), so the lane must never claim Safe with the interval machinery
/// skipped. (The polynomial-DAG lane's derivation-witness builder evaluates
/// only Bool/Int sorts — `concrete_eval_for_sort` — so a BV SAT model
/// yields no replayable witness and the lane reports the sound Unknown
/// rather than Unsafe; that pre-existing incompleteness is independent of
/// the interval-machinery skip, which this test pins.)
#[test]
#[timeout(120_000)]
fn test_polynomial_dag_bv_chain_reachable_query_never_safe_with_interval_skip() {
    let problem = create_branching_acyclic_bv_chain(12, 11);
    let config = BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 12,
        acyclic_safe: true,
        prefer_exact_acyclic_first: true,
        time_budget: Some(std::time::Duration::from_mins(1)),
        ..BmcConfig::default()
    };
    let solver = BmcSolver::new(problem, config);
    let result = solver.solve();
    assert!(
        !matches!(result, ChcEngineResult::Safe(_)),
        "reachable BV query must never be proved Safe, got {result:?}"
    );
}

// ==========================================================================
// Multi-lane query encoding (model-checker-consumer item 4 residual).
//
// `expand_nullary_fail_queries` rewrites a single nullary `(query error)`
// into ONE query per `body => error` clause, so the problem handed to the
// level-BMC lane carries MANY queries whose bodies mention DIFFERENT
// predicates ("lanes"). Reachability of the original `error` is the
// DISJUNCTION over those queries; the level loop must encode it that way.
// ==========================================================================

/// Two independent lanes off a shared fact:
/// - `A(0)`
/// - `B(x) :- A(y), x > y`       (the reachable lane, nondeterministic so
///   the concrete-scalar prepass does not apply)
/// - `C(x) :- A(y), x < y`       (the unreachable-query lane)
///
/// `multi_query` switches between the pre-expansion shape (only the
/// reachable lane is a query) and the post-expansion shape (both lanes are
/// queries). Both shapes describe the SAME reachability of `false`: lane B
/// at level 1 with `x = 1`. Lane C's query (`x = 99`) is never satisfiable
/// (`C` only holds strictly below 0).
fn create_multi_lane_query_problem(multi_query: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("LaneA", vec![ChcSort::Int]);
    let b = problem.declare_predicate("LaneB", vec![ChcSort::Int]);
    let c = problem.declare_predicate("LaneC", vec![ChcSort::Int]);
    let g = problem.declare_predicate("LaneGate", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(a, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(g, vec![ChcExpr::int(0)]),
    ));
    // Two body predicates: keeps the concrete-scalar prepass inapplicable so
    // the level-encoded lane (the one the scalarized probe uses) actually runs.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (a, vec![ChcExpr::var(y.clone())]),
                (g, vec![ChcExpr::var(z.clone())]),
            ],
            Some(ChcExpr::and(
                ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
                ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::int(0)),
            )),
        ),
        ClauseHead::Predicate(b, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(a, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(
                ChcExpr::var(x.clone()),
                ChcExpr::var(y.clone()),
            )),
        ),
        ClauseHead::Predicate(c, vec![ChcExpr::var(x.clone())]),
    ));

    // Lane C's query first, so a "first query only" encoding picks the
    // unsatisfiable one and the ordering dependence is visible.
    if multi_query {
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(c, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(99))),
            ),
            ClauseHead::False,
        ));
    }
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(b, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn solve_multi_lane_level_bmc(multi_query: bool) -> ChcEngineResult {
    // Mirrors `run_scalarized_collapse_probe`'s level-BMC configuration.
    let solver = BmcSolver::new(
        create_multi_lane_query_problem(multi_query),
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 6,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: Some(std::time::Duration::from_mins(1)),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        },
    );
    solver.solve()
}

#[test]
#[timeout(120_000)]
fn test_level_bmc_converts_single_query_lane() {
    let result = solve_multi_lane_level_bmc(false);
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "single-query lane must convert, got {result:?}"
    );
}

#[test]
#[timeout(120_000)]
fn test_level_bmc_converts_multi_lane_queries() {
    let result = solve_multi_lane_level_bmc(true);
    assert!(
        matches!(result, ChcEngineResult::Unsafe(_)),
        "the SAME reachability expressed as several queries over different \
         predicate lanes must still convert, got {result:?}"
    );
}

/// The multi-lane UNSAFE verdict must be backed by a concrete derivation that
/// validates on the ORIGINAL clauses by pure ground evaluation — the same
/// check the transform-lane landing performs. This is the anti-fabrication
/// side of the multi-query encoding: the disjunction may only report Unsafe
/// for a lane that genuinely fires, and the derivation must name the query
/// clause it reached.
#[test]
#[timeout(120_000)]
fn test_level_bmc_multi_lane_unsafe_derivation_ground_validates() {
    let problem = create_multi_lane_query_problem(true);
    let solver = BmcSolver::new(
        problem.clone(),
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 6,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: Some(std::time::Duration::from_mins(1)),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        },
    );
    let ChcEngineResult::Unsafe(cex) = solver.solve() else {
        panic!("multi-lane query problem must convert to Unsafe");
    };
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("multi-lane Unsafe must carry a ground derivation");
    crate::ground_derivation::validate_ground_derivation(&problem, derivation)
        .expect("multi-lane ground derivation must validate on the ORIGINAL clauses");
    // The derivation's root must be one of the problem's query clauses, so
    // an enclosing back-translation can line the landing up with the query
    // that was actually reached.
    let root_clause = derivation.steps[derivation.query_step].clause_index;
    assert!(
        matches!(problem.clauses()[root_clause].head, ClauseHead::False),
        "the derivation root must be a query clause, got clause {root_clause}"
    );
}

/// SAFE variant of the multi-lane shape: same three lanes, but each query is
/// guarded where its OWN lane can never be. `LaneB` only ever holds values
/// strictly above 0 and `LaneC` only values strictly below 0, so `LaneB < 0`
/// and `LaneC > 0` are both unreachable — yet each guard IS satisfiable by the
/// OTHER lane's states, which is precisely what a lane-conflating encoding
/// would exploit.
fn create_safe_multi_lane_query_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("LaneA", vec![ChcSort::Int]);
    let b = problem.declare_predicate("LaneB", vec![ChcSort::Int]);
    let c = problem.declare_predicate("LaneC", vec![ChcSort::Int]);
    let g = problem.declare_predicate("LaneGate", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(a, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(g, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (a, vec![ChcExpr::var(y.clone())]),
                (g, vec![ChcExpr::var(z.clone())]),
            ],
            Some(ChcExpr::and(
                ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
                ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::int(0)),
            )),
        ),
        ClauseHead::Predicate(b, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(a, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::var(y))),
        ),
        ClauseHead::Predicate(c, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(b, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(c, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    problem
}

/// A SAFE multi-lane problem: several queries over different predicates, none
/// of them reachable. Disjoining the lanes must not manufacture reachability
/// by satisfying one lane's guard with another lane's state.
#[test]
#[timeout(120_000)]
fn test_level_bmc_safe_multi_lane_queries_never_unsafe() {
    let solver = BmcSolver::new(
        create_safe_multi_lane_query_problem(),
        BmcConfig {
            base: ChcEngineConfig::default(),
            max_depth: 6,
            acyclic_safe: false,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: None,
            time_budget: Some(std::time::Duration::from_mins(1)),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            proof_cross_check: false,
            ts_probe_clamp: None,
            sweep_past_spurious_sat: true,
        },
    );
    let result = solver.solve();
    assert!(
        !matches!(result, ChcEngineResult::Unsafe(_)),
        "SAFE multi-lane query problem was reported UNSAFE — the disjunction \
         conflated lanes, got {result:?}"
    );
}

// ==========================================================================
// Level-BMC query-extraction residuals (model-checker-consumer item 4 follow-up).
//
// `expand_nullary_fail_queries` produces query shapes the level lane's
// model->derivation extraction never had to handle before:
//   (A) a query whose body predicate has NO defining clauses ("dead lane"),
//   (B) a query whose body mentions MORE THAN ONE predicate.
// Both used to fail closed and mask a genuine counterexample in another lane.
// ==========================================================================

/// Level-BMC configuration mirroring the model-checker-consumer driver's scalarized probe.
fn residual_level_bmc_config() -> BmcConfig {
    BmcConfig {
        base: ChcEngineConfig::default(),
        max_depth: 6,
        acyclic_safe: false,
        prefer_exact_acyclic_first: false,
        per_depth_timeout: None,
        time_budget: Some(std::time::Duration::from_mins(1)),
        enable_k_induction: false,
        enable_adaptive_stepping: false,
        proof_cross_check: false,
        ts_probe_clamp: None,
        sweep_past_spurious_sat: true,
    }
}

/// RESIDUAL A — dead-lane masking.
///
/// `DeadLane` is DECLARED but has no defining clause, so it is unreachable in
/// the least model. Its query is listed FIRST. `Step` carries the genuine
/// counterexample (`Step(1)` at level 1).
///
/// `reachable_tail` selects between the UNSAFE shape (`Step(x), x = 1`, which
/// fires) and the SAFE analogue (`Step(x), x < 0`, which cannot: `Step` only
/// ever holds values strictly above 0).
fn create_dead_lane_query_problem(reachable_tail: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let init = problem.declare_predicate("DeadInit", vec![ChcSort::Int]);
    let gate = problem.declare_predicate("DeadGate", vec![ChcSort::Int]);
    let step = problem.declare_predicate("DeadStep", vec![ChcSort::Int]);
    // Declared, never defined: the dead lane.
    let dead = problem.declare_predicate("DeadLane", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(init, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(gate, vec![ChcExpr::int(0)]),
    ));
    // Two body predicates keep the concrete-scalar prepass inapplicable, so
    // the level-encoded lane really runs.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (init, vec![ChcExpr::var(y.clone())]),
                (gate, vec![ChcExpr::var(z.clone())]),
            ],
            Some(ChcExpr::and(
                ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
                ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::int(0)),
            )),
        ),
        ClauseHead::Predicate(step, vec![ChcExpr::var(x.clone())]),
    ));

    // The dead lane's query comes FIRST: its level flag is unconstrained
    // unless the encoding pins undefined predicates to false, so a
    // "first satisfied query wins" root selection latches onto it.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(dead, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(7))),
        ),
        ClauseHead::False,
    ));
    let tail = if reachable_tail {
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))
    } else {
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(0))
    };
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(step, vec![ChcExpr::var(x)])], Some(tail)),
        ClauseHead::False,
    ));

    problem
}

/// A dead lane (query over a predicate with no defining clauses) must not
/// mask a genuine counterexample sitting in another lane.
///
/// Before the fix the free `DeadLane#k` flag made the query disjunction
/// trivially SAT at every depth, root selection latched onto the dead query,
/// and extraction failed — every depth degraded to Unknown.
#[test]
#[timeout(120_000)]
fn test_level_bmc_dead_first_lane_does_not_mask_counterexample() {
    let problem = create_dead_lane_query_problem(true);
    let solver = BmcSolver::new(problem.clone(), residual_level_bmc_config());
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!(
            "a dead FIRST query lane must not mask the reachable lane's \
             counterexample, got {result:?}"
        );
    };
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("dead-lane Unsafe must carry a ground derivation");
    crate::ground_derivation::validate_ground_derivation(&problem, derivation)
        .expect("dead-lane ground derivation must validate on the ORIGINAL clauses");
}

/// Anti-fabrication for RESIDUAL A: the SAME dead lane with an UNREACHABLE
/// tail query must never be reported Unsafe. Pinning undefined predicates to
/// false may only remove spurious models, never manufacture one.
#[test]
#[timeout(120_000)]
fn test_level_bmc_safe_dead_lane_never_unsafe() {
    let solver = BmcSolver::new(
        create_dead_lane_query_problem(false),
        residual_level_bmc_config(),
    );
    let result = solver.solve();
    assert!(
        !matches!(result, ChcEngineResult::Unsafe(_)),
        "SAFE dead-lane problem was reported UNSAFE — a query over an \
         undefined predicate was treated as reachable, got {result:?}"
    );
}

/// RESIDUAL B — a query whose body mentions MORE THAN ONE predicate.
///
/// `LeftStep` and `RightStep` are independent nondeterministic successors of
/// their own facts. The single query needs BOTH at the same level.
///
/// `reachable` selects the UNSAFE shape (`LeftStep(1) & RightStep(2)`, both
/// reachable at level 1) and the SAFE analogue (`RightStep(-5)`, which cannot
/// hold: `RightStep` only ever holds values strictly above 0).
fn create_multi_body_query_problem(reachable: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let left = problem.declare_predicate("MbqLeft", vec![ChcSort::Int]);
    let right = problem.declare_predicate("MbqRight", vec![ChcSort::Int]);
    let gate = problem.declare_predicate("MbqGate", vec![ChcSort::Int]);
    let left_step = problem.declare_predicate("MbqLeftStep", vec![ChcSort::Int]);
    let right_step = problem.declare_predicate("MbqRightStep", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let w = ChcVar::new("w", ChcSort::Int);

    for pred in [left, right, gate] {
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(pred, vec![ChcExpr::int(0)]),
        ));
    }
    for (base, head) in [(left, left_step), (right, right_step)] {
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![
                    (base, vec![ChcExpr::var(y.clone())]),
                    (gate, vec![ChcExpr::var(z.clone())]),
                ],
                Some(ChcExpr::and(
                    ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
                    ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::int(0)),
                )),
            ),
            ClauseHead::Predicate(head, vec![ChcExpr::var(x.clone())]),
        ));
    }

    let right_value = if reachable { 2 } else { -5 };
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (left_step, vec![ChcExpr::var(x.clone())]),
                (right_step, vec![ChcExpr::var(w.clone())]),
            ],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1)),
                ChcExpr::eq(ChcExpr::var(w), ChcExpr::int(right_value)),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

/// A query with several body predicates must be identified as the derivation
/// root and carry a premise per body predicate.
///
/// Before the fix `model_root_query` skipped every multi-body-predicate query
/// outright, so the only query in this problem was never selected and the
/// level lane returned Unknown.
#[test]
#[timeout(120_000)]
fn test_level_bmc_multi_body_predicate_query_converts() {
    let problem = create_multi_body_query_problem(true);
    let solver = BmcSolver::new(problem.clone(), residual_level_bmc_config());
    let result = solver.solve();
    let ChcEngineResult::Unsafe(cex) = result else {
        panic!("a reachable multi-body-predicate query must convert, got {result:?}");
    };
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("multi-body-predicate Unsafe must carry a ground derivation");
    crate::ground_derivation::validate_ground_derivation(&problem, derivation)
        .expect("multi-body-predicate derivation must validate on the ORIGINAL clauses");
    let query_step = &derivation.steps[derivation.query_step];
    assert_eq!(
        query_step.premises.len(),
        2,
        "the query step must carry one premise per body predicate"
    );
}

/// Anti-fabrication for RESIDUAL B: a multi-body-predicate query that is
/// genuinely unreachable must never be reported Unsafe.
#[test]
#[timeout(120_000)]
fn test_level_bmc_safe_multi_body_predicate_query_never_unsafe() {
    let solver = BmcSolver::new(
        create_multi_body_query_problem(false),
        residual_level_bmc_config(),
    );
    let result = solver.solve();
    assert!(
        !matches!(result, ChcEngineResult::Unsafe(_)),
        "SAFE multi-body-predicate query was reported UNSAFE, got {result:?}"
    );
}

/// Direct encoding-level discriminator for RESIDUAL A: a predicate with NO
/// defining clause must have its level flag pinned to FALSE at every level, in
/// BOTH level encodings. Leaving it free is what let a dead query lane satisfy
/// the query disjunction at every depth.
#[test]
fn test_level_encodings_pin_undefined_predicate_flags_false() {
    let problem = create_dead_lane_query_problem(true);
    let solver = BmcSolver::new(problem, residual_level_bmc_config());
    for level in 0..3 {
        let expected = ChcExpr::not(ChcExpr::Var(ChcVar::new(
            format!("DeadLane#{level}"),
            ChcSort::Bool,
        )));
        for (label, conjuncts) in [
            ("compile_level", {
                let mut out = Vec::new();
                solver.compile_level(level, &mut out);
                out
            }),
            ("compile_level_flat", {
                let mut out = Vec::new();
                solver.compile_level_flat(level, &mut out);
                out
            }),
        ] {
            assert!(
                conjuncts.contains(&expected),
                "{label} at level {level} left the undefined predicate DeadLane's \
                 flag free; conjuncts: {conjuncts:?}"
            );
        }
    }
}

/// Direct extraction-level discriminator for the RETRY half of RESIDUAL A.
///
/// The model below satisfies BOTH queries' compiled conjuncts, but the FIRST
/// one is the dead lane (`DeadLane` has no defining clause, so no derivation
/// can be built for it). Root selection must move on to the second query
/// instead of giving up — otherwise an unextractable lane masks a lane whose
/// derivation is right there in the model.
///
/// This exercises `model_derivation_witnesses` on a HAND-BUILT model, so it is
/// independent of the encoding-level dead-lane pin.
#[test]
fn test_model_root_selection_retries_past_unextractable_lane() {
    let solver = BmcSolver::new(
        create_dead_lane_query_problem(true),
        residual_level_bmc_config(),
    );
    // Query clauses must come from the SOLVER's own problem: root
    // identification recovers a clause index by pointer identity.
    let queries: Vec<&HornClause> = solver
        .problem
        .clauses()
        .iter()
        .filter(|clause| clause.is_query())
        .collect();
    assert_eq!(queries.len(), 2, "fixture must have both query lanes");

    let model: FxHashMap<String, SmtValue> = [
        ("DeadInit#0".to_string(), SmtValue::Bool(true)),
        ("DeadInit#0_0".to_string(), SmtValue::Int(0)),
        ("DeadGate#0".to_string(), SmtValue::Bool(true)),
        ("DeadGate#0_0".to_string(), SmtValue::Int(0)),
        ("DeadStep#1".to_string(), SmtValue::Bool(true)),
        ("DeadStep#1_0".to_string(), SmtValue::Int(1)),
        // The dead lane, satisfied in the model but underivable.
        ("DeadLane#1".to_string(), SmtValue::Bool(true)),
        ("DeadLane#1_0".to_string(), SmtValue::Int(7)),
    ]
    .into_iter()
    .collect();

    let candidates = solver.model_derivation_witnesses(&model, 1, &queries);
    let extracted = candidates
        .first()
        .expect("root selection must retry past the dead lane and extract the live one");
    let ground = solver
        .ground_derivation_from_witness(extracted, &model, 1)
        .expect("the live lane's witness must reshape into a ground derivation");
    crate::ground_derivation::validate_ground_derivation(&solver.problem, &ground)
        .expect("retried-lane derivation must validate on the ORIGINAL clauses");
    let query_clause = ground.steps[ground.query_step].clause_index;
    assert_eq!(
        query_clause,
        solver.problem.clauses().len() - 1,
        "the derivation must land on the SECOND (live) query, not the dead first one"
    );
}

/// A body that applies one predicate twice must never be reported `Safe`.
///
/// `P(0). P(1). false :- P(x), P(y), x != y.` is plainly unsafe — `P(0)` and
/// `P(1)` with `0 != 1` derive `false`. The level-flat encoding names level
/// arguments by `(predicate, level, index)` only, so both body occurrences of
/// `P` share one argument tuple and the encoding silently asserts `x == y`.
/// Every depth then comes back UNSAT for a reason that has nothing to do with
/// the program, and an `acyclic_safe` run used to read that exhaustion as
/// `Safe` — a wrong answer.
///
/// `BmcSolver::solve` now fails closed to `Unknown` on any such problem.
#[test]
fn repeated_body_predicate_never_reports_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(assert (P 0))
(assert (P 1))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (P y) (not (= x y))) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(4)
            .with_acyclic_safe(true),
    );
    let result = solver.solve();
    assert!(
        !matches!(result, ChcEngineResult::Safe(_)),
        "a genuinely unsafe problem must never be reported Safe, got {result:?}"
    );
}

/// The fail-closed guard must not fire on bodies it does not apply to.
///
/// Distinct body predicates share no level argument, so the level-flat encoding
/// represents them exactly and `acyclic_safe` exhaustion stays sound.
#[test]
fn distinct_body_predicates_still_reach_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (P 0))
(assert (Q 0))
(assert (forall ((x Int) (y Int)) (=> (and (P x) (Q y) (> x 100) (> y 100)) false)))
(check-sat)
"#;
    let problem = crate::parser::ChcParser::parse(smt).unwrap();
    let solver = BmcSolver::new(
        problem,
        BmcConfig::default()
            .with_max_depth(2)
            .with_acyclic_safe(true),
    );
    let result = solver.solve();
    assert!(
        matches!(result, ChcEngineResult::Safe(_)),
        "distinct body predicates are encoded exactly; this must stay Safe, got {result:?}"
    );
}
