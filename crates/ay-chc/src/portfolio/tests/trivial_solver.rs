// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn pdr_only_preprocessing_config() -> PortfolioConfig {
    PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: true,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    }
}

fn pdr_only_bv_native_solver(problem: ChcProblem) -> PortfolioSolver {
    let summary = PreprocessSummary::build_bv_native(problem, false);
    PortfolioSolver::from_summary(summary, pdr_only_preprocessing_config())
}

#[test]
fn test_try_solve_trivial_safe_returns_valid_model() {
    // Regression test for #2254: `try_solve_trivial` used to return `Safe` with an empty
    // model even when the problem contains predicates, which later fails model validation.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            assert!(!model.is_empty(), "Safe model should not be empty");
            assert!(matches!(
                solver.validate_safe(&model),
                ValidationResult::Valid
            ));
        }
        _ => panic!("Expected Safe from try_solve_trivial"),
    }
}

#[test]
fn test_predicate_free_safe_returns_model_verifying_original_problem() {
    // Regression for #8900: preprocessing can inline an acyclic predicate chain
    // to a predicate-free UNSAT query. The Safe result must return the
    // back-translated original model, not a placeholder P(x)=true model.
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (P x) (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (not (= x 0))) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("predicate chain should parse");
    let original_problem = problem.clone();
    let solver = PortfolioSolver::new(problem, pdr_only_preprocessing_config());
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            assert!(!model.is_empty(), "Safe model should be materialized");
            let mut verifier = crate::pdr::PdrSolver::new(original_problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&model),
                "trivial Safe result must verify on the original problem"
            );
        }
        other => panic!("Expected Safe from predicate-free trivial path, got {other:?}"),
    }
}

#[test]
fn test_predicate_free_nested_array_query_simplifies_after_inlining_9185() {
    let input = r#"
(set-logic HORN)
(declare-datatype Option_bv64 ((None_Option_bv64) (Some_Option_bv64 (value_Option_bv64 (_ BitVec 64)))))
(declare-var _test_ref_to_nested_array_1 (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))))
(declare-var _test_ref_to_nested_array_1__out (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))))
(declare-var _test_ref_to_nested_array_10 Bool)
(declare-var _test_ref_to_nested_array_10__out Bool)
(declare-rel test_ref_to_nested_array__bb0 ((Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))) Bool))
(declare-rel test_ref_to_nested_array__bb1 ((Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))) Bool))
(declare-rel test_ref_to_nested_array__bb2 ((Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))) Bool))
(declare-rel test_ref_to_nested_array__bb3 ((Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32))) Bool))
(declare-rel error ())
(rule (=> true (test_ref_to_nested_array__bb0 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10)))
(rule (=> (and (test_ref_to_nested_array__bb0 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10) (not (= (bvult #x0000000000000001 #x0000000000000002) true))) error))
(rule (=> (and (test_ref_to_nested_array__bb0 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10) (= _test_ref_to_nested_array_1__out (store (store ((as const (Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 32)))) __default_elem___chc_array_2) #x0000000000000000 (store (store ((as const (Array (_ BitVec 64) (_ BitVec 32))) #x00000000) #x0000000000000000 #x00000001) #x0000000000000001 #x00000002)) #x0000000000000001 (store (store ((as const (Array (_ BitVec 64) (_ BitVec 32))) #x00000000) #x0000000000000000 #x00000003) #x0000000000000001 #x00000004)))) (test_ref_to_nested_array__bb1 _test_ref_to_nested_array_1__out _test_ref_to_nested_array_10)))
(rule (=> (test_ref_to_nested_array__bb1 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10) (test_ref_to_nested_array__bb2 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10)))
(rule (=> (and (and (test_ref_to_nested_array__bb2 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10) (= _test_ref_to_nested_array_10__out (= (select (select _test_ref_to_nested_array_1 #x0000000000000001) #x0000000000000000) #x00000003))) (= (select (select _test_ref_to_nested_array_1 #x0000000000000001) #x0000000000000000) #x00000003)) (test_ref_to_nested_array__bb3 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10__out)))
(rule (=> (and (test_ref_to_nested_array__bb2 _test_ref_to_nested_array_1 _test_ref_to_nested_array_10) (not (= (select (select _test_ref_to_nested_array_1 #x0000000000000001) #x0000000000000000) #x00000003))) error))
(query error)
"#;
    let problem =
        ChcParser::parse(input).expect("model-checker-consumer nested-array CHC should parse");
    let solver = pdr_only_bv_native_solver(problem);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "expected trivial Safe for inlined nested-array query, got {result:?}"
    );
}

#[test]
fn test_predicate_free_box_bool_array_state_simplifies_after_inlining_9185() {
    let input = r#"
(set-logic HORN)
(declare-var obj_size (Array (_ BitVec 32) (_ BitVec 32)))
(declare-var obj_size__out (Array (_ BitVec 32) (_ BitVec 32)))
(declare-rel test_box_bool__bb0 ((Array (_ BitVec 32) (_ BitVec 32))))
(declare-rel test_box_bool__bb1 ((Array (_ BitVec 32) (_ BitVec 32))))
(declare-rel test_box_bool__bb2 ((Array (_ BitVec 32) (_ BitVec 32))))
(declare-rel error ())
(rule (=> (= (select obj_size #x00000000) #x00000000) (test_box_bool__bb0 obj_size)))
(rule (=> (and (test_box_bool__bb0 obj_size) (= obj_size__out (store obj_size #x00000026 #x00000001))) (test_box_bool__bb1 obj_size__out)))
(rule (=> (test_box_bool__bb1 obj_size) (test_box_bool__bb2 obj_size)))
(rule (=> (and (test_box_bool__bb2 obj_size) (not (or (= (select obj_size #x00000026) #x00000000) (= (select obj_size #x00000026) #x00000001)))) error))
(query error)
"#;
    let problem =
        ChcParser::parse(input).expect("model-checker-consumer box-bool CHC should parse");
    let solver = pdr_only_bv_native_solver(problem);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "expected trivial Safe for inlined box-bool array state, got {result:?}"
    );
}

#[test]
fn test_predicate_free_option_bv_query_simplifies_after_inlining_9476() {
    let input = r#"
(set-logic HORN)
(declare-datatype Option_u8 ((None_Option_u8) (Some_Option_u8 (value_Option_u8 (_ BitVec 8)))))
(declare-var _test_option_array_simple_4 Bool)
(declare-var _test_option_array_simple_4__out Bool)
(declare-var _test_option_array_simple_1_at_0x0_bv64 (_ BitVec 9))
(declare-var _test_option_array_simple_1_at_0x0_bv64__out (_ BitVec 9))
(declare-rel test_option_array_simple__bb0 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb1 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb2 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb3 ((_ BitVec 9) Bool))
(declare-rel error ())
(rule (=> true (test_option_array_simple__bb0 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb0 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (= _test_option_array_simple_1_at_0x0_bv64__out (ite ((_ is Some_Option_u8) ((as Some_Option_u8 Option_u8) #x04)) (concat #b1 (value_Option_u8 ((as Some_Option_u8 Option_u8) #x04))) #b000000000))) (test_option_array_simple__bb1 _test_option_array_simple_1_at_0x0_bv64__out _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb1 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (= _test_option_array_simple_4__out (= (ite (not (= ((_ extract 8 8) _test_option_array_simple_1_at_0x0_bv64) #b0)) ((as Some_Option_u8 Option_u8) ((_ extract 7 0) ((_ extract 7 0) _test_option_array_simple_1_at_0x0_bv64))) (as None_Option_u8 Option_u8)) ((as Some_Option_u8 Option_u8) #x04)))) (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4__out)))
(rule (=> (and (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) _test_option_array_simple_4) (test_option_array_simple__bb3 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (not _test_option_array_simple_4)) error))
(query error)
"#;
    let problem =
        ChcParser::parse(input).expect("model-checker-consumer option/BV CHC should parse");
    let original_problem = problem.clone();
    let summary = PreprocessSummary::build_bv_native(problem, false);
    let solver = PortfolioSolver::from_summary(summary, pdr_only_preprocessing_config());
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            assert!(!model.is_empty(), "Safe model should be materialized");
            let mut verifier = crate::pdr::PdrSolver::new(original_problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&model),
                "trivial Safe result must verify on the original Option/BV problem"
            );
        }
        other => panic!("Expected Safe from inlined Option/BV trivial path, got {other:?}"),
    }
}

#[test]
fn test_expanded_nullary_option_bv_query_simplifies_after_inlining_9476() {
    let input = r#"
(set-logic HORN)
(declare-datatype Option_bv64 ((None_Option_bv64) (Some_Option_bv64 (value_Option_bv64 (_ BitVec 64)))))
(declare-datatype Option_u8 ((None_Option_u8) (Some_Option_u8 (value_Option_u8 (_ BitVec 8)))))
(declare-var _test_option_array_simple_4 Bool)
(declare-var _test_option_array_simple_4__out Bool)
(declare-var _test_option_array_simple_1_at_0x0_bv64 (_ BitVec 9))
(declare-var _test_option_array_simple_1_at_0x0_bv64__out (_ BitVec 9))
(declare-rel test_option_array_simple__bb0 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb1 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb2 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb3 ((_ BitVec 9) Bool))
(declare-rel error ())
(rule (=> true (test_option_array_simple__bb0 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb0 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (= _test_option_array_simple_1_at_0x0_bv64__out (ite ((_ is Some_Option_u8) ((as Some_Option_u8 Option_u8) #x04)) (concat #b1 (value_Option_u8 ((as Some_Option_u8 Option_u8) #x04))) #b000000000))) (test_option_array_simple__bb1 _test_option_array_simple_1_at_0x0_bv64__out _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb1 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (= _test_option_array_simple_4__out (= (ite (not (= ((_ extract 8 8) _test_option_array_simple_1_at_0x0_bv64) #b0)) ((as Some_Option_u8 Option_u8) ((_ extract 7 0) ((_ extract 7 0) _test_option_array_simple_1_at_0x0_bv64))) (as None_Option_u8 Option_u8)) ((as Some_Option_u8 Option_u8) #x04)))) (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4__out)))
(rule (=> (and (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) _test_option_array_simple_4) (test_option_array_simple__bb3 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (not _test_option_array_simple_4)) error))
(query error)
"#;
    let mut problem =
        ChcParser::parse(input).expect("model-checker-consumer option/BV CHC should parse");
    assert!(
        problem.expand_nullary_fail_queries(false),
        "test setup must exercise the native-driver expanded query path"
    );
    let solver = pdr_only_bv_native_solver(problem);
    let result = solver.solve();

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "expected trivial Safe after expanding nullary error query, got {result:?}"
    );
}

#[test]
fn test_adaptive_expanded_nullary_option_bv_query_safe_9476() {
    use crate::{AdaptiveConfig, AdaptivePortfolio, VerifiedChcResult};
    use std::time::Duration;

    let input = r#"
(set-logic HORN)
(declare-datatype Option_bv64 ((None_Option_bv64) (Some_Option_bv64 (value_Option_bv64 (_ BitVec 64)))))
(declare-datatype Option_u8 ((None_Option_u8) (Some_Option_u8 (value_Option_u8 (_ BitVec 8)))))
(declare-var _test_option_array_simple_4 Bool)
(declare-var _test_option_array_simple_4__out Bool)
(declare-var _test_option_array_simple_1_at_0x0_bv64 (_ BitVec 9))
(declare-var _test_option_array_simple_1_at_0x0_bv64__out (_ BitVec 9))
(declare-rel test_option_array_simple__bb0 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb1 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb2 ((_ BitVec 9) Bool))
(declare-rel test_option_array_simple__bb3 ((_ BitVec 9) Bool))
(declare-rel error ())
(rule (=> true (test_option_array_simple__bb0 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb0 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (= _test_option_array_simple_1_at_0x0_bv64__out (ite ((_ is Some_Option_u8) ((as Some_Option_u8 Option_u8) #x04)) (concat #b1 (value_Option_u8 ((as Some_Option_u8 Option_u8) #x04))) #b000000000))) (test_option_array_simple__bb1 _test_option_array_simple_1_at_0x0_bv64__out _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb1 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (= _test_option_array_simple_4__out (= (ite (not (= ((_ extract 8 8) _test_option_array_simple_1_at_0x0_bv64) #b0)) ((as Some_Option_u8 Option_u8) ((_ extract 7 0) ((_ extract 7 0) _test_option_array_simple_1_at_0x0_bv64))) (as None_Option_u8 Option_u8)) ((as Some_Option_u8 Option_u8) #x04)))) (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4__out)))
(rule (=> (and (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) _test_option_array_simple_4) (test_option_array_simple__bb3 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4)))
(rule (=> (and (test_option_array_simple__bb2 _test_option_array_simple_1_at_0x0_bv64 _test_option_array_simple_4) (not _test_option_array_simple_4)) error))
(query error)
"#;
    let mut problem =
        ChcParser::parse(input).expect("model-checker-consumer option/BV CHC should parse");
    assert!(
        problem.expand_nullary_fail_queries(false),
        "test setup must exercise the native-driver expanded query path"
    );
    let mut config = AdaptiveConfig::with_budget(Duration::from_secs(2), false);
    config.strict_proofs = true;
    let solver = AdaptivePortfolio::new(problem, config);
    let (result, _report) = solver.solve_with_budget_report();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "expected adaptive Safe after expanding nullary error query, got {result:?}"
    );
}

#[test]
fn test_try_solve_trivial_unsat_query_safe_returns_valid_model() {
    // Regression coverage for #2254: query-constraint UNSAT path should return a valid model.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x)]),
    ));

    // Query: q = 0 /\ q != 0 => false (UNSAT)
    let q = ChcVar::new("q", ChcSort::Int);
    let unsat = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(q.clone()), ChcExpr::int(0)),
        ChcExpr::ne(ChcExpr::var(q), ChcExpr::int(0)),
    );
    problem.add_clause(HornClause::query(ClauseBody::constraint(unsat)));

    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Safe(model) => {
            assert!(!model.is_empty(), "Safe model should not be empty");
            assert!(matches!(
                solver.validate_safe(&model),
                ValidationResult::Valid
            ));
        }
        _ => panic!("Expected Safe from try_solve_trivial (unsat query constraints)"),
    }
}

/// Mock back-translator with NON-identity transform memory, simulating any
/// real (problem-changing) preprocessing stack. Witness translation is a
/// passthrough; only the memory report matters for these tests.
struct NonIdentityMockTranslator;

impl crate::transform::BackTranslator for NonIdentityMockTranslator {
    fn translate_validity(
        &self,
        witness: crate::transform::ValidityWitness,
    ) -> crate::transform::ValidityWitness {
        witness
    }

    fn translate_invalidity(
        &self,
        witness: crate::transform::InvalidityWitness,
    ) -> crate::transform::InvalidityWitness {
        witness
    }

    fn transform_memory(&self) -> crate::transform::TransformMemoryReport {
        crate::transform::TransformMemoryReport::reversible("mock-non-identity")
    }
}

/// Rank-6 review MUST-FIX A (wrong-Unsat path), fail-closed leg: when the
/// transform stack is non-identity, a satisfiable query constraint on the
/// TRANSFORMED problem must NEVER become an unconfirmed Unsafe. Here the
/// original problem is SAFE and the transformed problem simulates a buggy
/// transform that collapsed it to a predicate-free satisfiable query;
/// `try_solve_trivial` must fail the original-clause confirmation and return
/// `None` (fall through to the engines).
#[test]
fn test_try_solve_trivial_nonidentity_transform_never_unconfirmed_unsafe() {
    let original = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Mid (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Mid x))))
(assert (forall ((x Int)) (=> (and (Mid x) (not (= x 0))) false)))
(check-sat)
"#,
    )
    .expect("safe chain should parse");

    // Simulated buggy transform output: predicate-free, trivially SAT query.
    let mut transformed = ChcProblem::new();
    transformed.add_clause(HornClause::query(ClauseBody::empty()));

    let summary = PreprocessSummary {
        original_problem: original,
        transformed_problem: transformed,
        back_translator: Box::new(NonIdentityMockTranslator),
        bv_abstracted: false,
        transform_memory: crate::transform::TransformMemoryReport::reversible("mock-non-identity"),
    };
    let solver = PortfolioSolver::from_summary(summary, pdr_only_preprocessing_config());

    let result = solver.try_solve_trivial();
    assert!(
        !matches!(result, Some(PortfolioResult::Unsafe(_))),
        "non-identity transform stack must never produce an unconfirmed trivial Unsafe; got {result:?}"
    );
    assert!(
        result.is_none(),
        "original problem is SAFE: confirmation must fail closed to the engines; got {result:?}"
    );
}

/// Rank-6 review MUST-FIX A probe, confirmed-Unsafe leg: a tiny fully
/// collapsible UNSAFE chain (fact -> mid -> exit, query with a REACHABLE bug)
/// under graph collapse reaches the trivial path with a NON-identity
/// transform stack. The Unsafe verdict must still be produced — and only via
/// `confirm_trivial_unsafe_on_original` (the unconfirmed return is gated on
/// an identity-grade stack, see the fail-closed test above).
#[test]
fn test_try_solve_trivial_graph_collapse_unsafe_chain_confirmed_on_original() {
    let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Mid (Int) Bool)
(declare-fun Exit (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Mid x))))
(assert (forall ((x Int)) (=> (Mid x) (Exit x))))
(assert (forall ((x Int)) (=> (and (Exit x) (= x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("unsafe chain should parse");
    let summary = PreprocessSummary::build_with_graph_collapse(problem, false, true);
    assert!(
        !summary.transform_memory.is_identity_grade(),
        "graph-collapse stack must be non-identity: {}",
        summary.transform_memory.diagnostic_summary()
    );
    let solver = PortfolioSolver::from_summary(summary, pdr_only_preprocessing_config());

    let result = solver.try_solve_trivial();
    assert!(
        matches!(result, Some(PortfolioResult::Unsafe(_))),
        "reachable bug must stay Unsafe after original-clause confirmation; got {result:?}"
    );
}

#[test]
fn test_try_solve_trivial_sat_query_returns_unsafe() {
    // Regression coverage for #2254: satisfiable query constraint should return Unsafe.
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::empty()));

    let config = PortfolioConfig {
        external_cancellation: None,
        engines: vec![EngineConfig::Pdr(PdrConfig::default())],
        parallel: false,
        timeout: None,
        parallel_timeout: None,
        verbose: false,

        enable_preprocessing: false,
        engine_budgets: ay_core::kani_compat::DetHashMap::default(),
        memory_budget: None,
        strict_proofs: false,
    };
    let solver = PortfolioSolver::new(problem, config);
    let result = solver.solve();

    match result {
        PortfolioResult::Unsafe(cex) => {
            assert!(
                cex.steps.is_empty(),
                "Trivial unsafe should return empty-step counterexample"
            );
        }
        _ => panic!("Expected Unsafe from try_solve_trivial (sat query constraint)"),
    }
}
