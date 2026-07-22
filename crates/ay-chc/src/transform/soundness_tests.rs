// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Soundness regression tests for CHC preprocessing passes (#7903).
//!
//! Each test constructs a CHC problem with a known answer (Safe or Unsafe),
//! applies one or more preprocessing transforms, and verifies that the
//! transformed problem preserves the original satisfiability.
//!
//! Focus areas:
//! - Variable renaming / fresh variable capture avoidance
//! - Clause simplification preserving satisfiability
//! - Predicate inlining (unique-def and multi-def)
//! - Dead parameter elimination liveness analysis
//! - Local variable elimination (equality substitution + one-sided bounds)
//! - Back-translation producing valid witnesses for the original problem
//! - Full preprocessing pipeline end-to-end

use super::Transformer;
use crate::parser::ChcParser;
use crate::pdr::{InvariantModel, PdrConfig, PdrResult, PdrSolver, PredicateInterpretation};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};
use crate::transform::{
    ClauseInliner, DeadParamEliminator, DtFlattener, LocalVarEliminator,
    SolidityArrayDtProjectionTransformer, TransformationPipeline,
};
use crate::{
    BmcConfig, BmcSolver, ChcDtConstructor, ChcDtSelector, ChcEngineResult, ChcExpr, ChcProblem,
    ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use std::sync::Arc;

// ============================================================================
// Helpers
// ============================================================================

fn parse(smt: &str) -> ChcProblem {
    ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"))
}

/// Solve a problem with a single PDR engine, non-parallel.
fn solve_with_pdr(problem: ChcProblem) -> PortfolioResult {
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    let solver = PortfolioSolver::new(problem, config);
    solver.solve()
}

/// Assert that a result is Safe.
fn assert_safe(result: &PortfolioResult, context: &str) {
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "{context}: expected Safe, got {result:?}"
    );
}

/// Assert that a result is Unsafe.
fn assert_unsafe(result: &PortfolioResult, context: &str) {
    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "{context}: expected Unsafe, got {result:?}"
    );
}

// ============================================================================
// 1. ClauseInliner soundness: Safe problems
// ============================================================================

/// Unique-definition inlining on a Safe counter problem.
///
/// Init(x) <= x = 0; Loop(y) <= Init(y); Loop(y+1) <= Loop(y), y < 10;
/// false <= Loop(z), z < 0.
///
/// After inlining Init, the problem must remain Safe and the solver must
/// produce a valid invariant for the original problem via back-translation.
#[test]
fn soundness_inline_unique_def_safe_counter() {
    let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Loop (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (Init x))))
(assert (forall ((y Int)) (=> (Init y) (Loop y))))
(assert (forall ((y Int) (y2 Int))
    (=> (and (Loop y) (= y2 (+ y 1)) (< y 10)) (Loop y2))))
(assert (forall ((z Int)) (=> (and (Loop z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    // Transform
    let result = Box::new(ClauseInliner::new()).transform(problem.clone());

    // Inliner should remove Init — check by name lookup in transformed problem
    assert!(
        result.problem.lookup_predicate("Init").is_none(),
        "Init should be inlined away (no predicate named 'Init' in transformed problem)"
    );

    // Solve the transformed problem
    let mut solver = PdrSolver::new(result.problem.clone(), PdrConfig::default());
    match solver.solve() {
        PdrResult::Safe(model) => {
            // Back-translate and verify against original
            let translated = result.back_translator.translate_validity(model);
            let mut verifier = PdrSolver::new(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&translated),
                "Back-translated model must be valid for original problem"
            );
        }
        other => panic!("Expected Safe, got {other:?}"),
    }
}

/// Unique-definition inlining on an Unsafe problem.
///
/// Init(x) <= x = 100; Loop(y) <= Init(y); false <= Loop(z), z > 50.
/// This is Unsafe because Init starts at 100 which violates z > 50.
#[test]
fn soundness_inline_unique_def_unsafe() {
    let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Loop (Int) Bool)

(assert (forall ((x Int)) (=> (= x 100) (Init x))))
(assert (forall ((y Int)) (=> (Init y) (Loop y))))
(assert (forall ((z Int)) (=> (and (Loop z) (> z 50)) false)))

(check-sat)
"#;
    let problem = parse(input);

    // Transform
    let result = Box::new(ClauseInliner::new()).transform(problem.clone());

    // After full inlining, the problem should reduce to a query with SAT body.
    // Solve via portfolio to check the result.
    let portfolio_result = solve_with_pdr(result.problem);
    assert_unsafe(&portfolio_result, "Inlined problem should be Unsafe");

    // The original must also be Unsafe
    let orig_result = solve_with_pdr(problem);
    assert_unsafe(&orig_result, "Original problem should be Unsafe");
}

/// Multi-definition inlining preserves Unsafe verdict.
///
/// P has two defining clauses: P(x) <= x=5 and P(x) <= x=200.
/// Query: false <= P(z), z > 100. The second definition makes it Unsafe.
#[test]
fn soundness_inline_multi_def_unsafe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 5) (P x))))
(assert (forall ((x Int)) (=> (= x 200) (P x))))
(assert (forall ((z Int)) (=> (and (P z) (> z 100)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());
    let transformed_result = solve_with_pdr(result.problem);
    assert_unsafe(
        &transformed_result,
        "Multi-def inlined problem should be Unsafe",
    );

    let orig_result = solve_with_pdr(problem);
    assert_unsafe(&orig_result, "Original multi-def problem should be Unsafe");
}

/// Multi-definition inlining must not drop definitions for predicates that are
/// introduced by another inlined multi-definition body.
///
/// P and Q both have multiple definitions, and P's definitions call Q. If both
/// are selected in one non-recursive batch, P expansion leaves Q calls behind
/// after Q's definitions were removed, hiding the reachable query.
#[test]
fn soundness_inline_multi_def_dependency_batch_unsafe_9604() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (Q x))))
(assert (forall ((x Int)) (=> (= x 1) (Q x))))
(assert (forall ((x Int)) (=> (Q x) (P x))))
(assert (forall ((x Int)) (=> (and (Q x) (= x 2)) (P x))))
(assert (forall ((z Int)) (=> (and (P z) (= z 1)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());
    let transformed_result =
        BmcSolver::new(result.problem, BmcConfig::default().with_max_depth(3)).solve();
    assert!(
        matches!(transformed_result, ChcEngineResult::Unsafe(_)),
        "Multi-def dependency batch must preserve reachable Unsafe for BMC, got {transformed_result:?}",
    );
}

/// Multi-definition inlining preserves Safe verdict.
///
/// P(x) <= x=0; P(x) <= x=1. Query: false <= P(z), z > 10.
/// Both definitions are small, so the query is unsatisfiable.
#[test]
fn soundness_inline_multi_def_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int)) (=> (= x 1) (P x))))
(assert (forall ((z Int)) (=> (and (P z) (> z 10)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());
    let transformed_result = solve_with_pdr(result.problem);
    assert_safe(
        &transformed_result,
        "Multi-def inlined problem should be Safe",
    );
}

/// Chain inlining: A -> B -> C, all unique-def.
/// Tests that transitive inlining through a chain preserves Safe.
#[test]
fn soundness_inline_chain_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun C (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int)) (=> (A x) (B x))))
(assert (forall ((x Int)) (=> (B x) (C x))))
(assert (forall ((z Int)) (=> (and (C z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());

    // After full chain inlining, only query remains
    assert!(
        result.problem.clauses().iter().all(HornClause::is_query),
        "All clauses should be queries after full chain inlining"
    );

    let transformed_result = solve_with_pdr(result.problem);
    assert_safe(&transformed_result, "Chain-inlined problem should be Safe");
}

/// Complex head expressions: P(x+1) <= x >= 0.
/// Inlining into Q(y) <= P(y) must create correct equality constraint.
#[test]
fn soundness_inline_complex_head_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)

(assert (forall ((x Int)) (=> (>= x 0) (P (+ x 1)))))
(assert (forall ((y Int)) (=> (P y) (Q y))))
(assert (forall ((z Int)) (=> (and (Q z) (<= z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());
    let transformed_result = solve_with_pdr(result.problem);
    assert_safe(
        &transformed_result,
        "Complex-head inlined problem should be Safe (x+1 >= 1 > 0)",
    );
}

// ============================================================================
// 2. DeadParamEliminator soundness
// ============================================================================

/// Dead parameter elimination on Safe problem: unused param must not change verdict.
#[test]
fn soundness_dead_param_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (= x 0) (P x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (P x y) (= x2 (+ x 1)) (< x 10)) (P x2 y2))))
(assert (forall ((z Int) (w Int)) (=> (and (P z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);
    let orig_result = solve_with_pdr(problem.clone());
    assert_safe(&orig_result, "Original should be Safe");

    let pipeline = TransformationPipeline::new().with(DeadParamEliminator::new());
    let result = pipeline.transform(problem.clone());

    // Should have eliminated y
    assert_eq!(
        result.problem.predicates()[0].arity(),
        1,
        "Dead param y should be eliminated"
    );

    let transformed_result = solve_with_pdr(result.problem.clone());
    assert_safe(
        &transformed_result,
        "Dead param eliminated problem should be Safe",
    );

    // Verify back-translation produces valid model for original problem
    if let PortfolioResult::Safe(model) = transformed_result {
        let translated = result.back_translator.translate_validity(model);
        let mut verifier = PdrSolver::new(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(&translated),
            "Back-translated model must be valid for original problem after dead param elim"
        );
    }
}

/// Dead parameter elimination on Unsafe problem: must not make it appear Safe.
#[test]
fn soundness_dead_param_unsafe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (= x 100) (P x y))))
(assert (forall ((z Int) (w Int)) (=> (and (P z w) (> z 50)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let pipeline = TransformationPipeline::new().with(DeadParamEliminator::new());
    let result = pipeline.transform(problem.clone());

    let transformed_result = solve_with_pdr(result.problem);
    assert_unsafe(
        &transformed_result,
        "Dead param eliminated problem should remain Unsafe",
    );
}

/// Constrained parameter must NOT be eliminated: back-translation must still work.
///
/// P(x, y) with y = 42 in init. If y is erroneously eliminated, the invariant
/// loses precision and may validate incorrectly.
#[test]
fn soundness_dead_param_constrained_stays_live() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

(assert (forall ((x Int) (y Int))
    (=> (and (= x 0) (= y 42)) (P x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (P x y) (= x2 (+ x 1)) (= y2 (+ y 1)) (< x 10)) (P x2 y2))))
(assert (forall ((z Int) (w Int))
    (=> (and (P z w) (< w 0)) false)))

(check-sat)
"#;
    let problem = parse(input);
    let eliminator = DeadParamEliminator::new();
    let (new_problem, _) = eliminator.eliminate(&problem);

    // y is constrained (= y 42) and (< w 0) in query -> must stay live
    assert_eq!(
        new_problem.predicates()[0].arity(),
        2,
        "Both params should be live (y is constrained in init and query)"
    );

    let result = solve_with_pdr(new_problem);
    assert_safe(&result, "Problem with both live params should be Safe");
}

/// Body-to-body join variable must not be eliminated.
///
/// R(c) <= P(c, d) /\ Q(e, d)  -- d joins P and Q
/// If d's position is eliminated from P or Q, the join is broken.
#[test]
fn soundness_dead_param_join_var_preserved() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 5)) (P x y))))
(assert (forall ((a Int) (b Int)) (=> (and (= a 1) (= b 5)) (Q a b))))
(assert (forall ((c Int) (d Int) (e Int))
    (=> (and (P c d) (Q e d)) (R c))))
(assert (forall ((z Int)) (=> (and (R z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let pipeline = TransformationPipeline::new().with(DeadParamEliminator::new());
    let result = pipeline.transform(problem.clone());

    let transformed_result = solve_with_pdr(result.problem);
    assert_safe(&transformed_result, "Problem with join vars should be Safe");

    let orig_result = solve_with_pdr(problem);
    assert_safe(&orig_result, "Original problem should be Safe");
}

// ============================================================================
// 3. LocalVarEliminator soundness
// ============================================================================

/// Local var elimination via equality substitution: Safe problem.
///
/// Clause: P(x+1) <= P(x), x >= 0, y = x + 5
/// Variable y is local (not in pred args), can be eliminated.
#[test]
fn soundness_local_var_elim_equality_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int) (x2 Int))
    (=> (and (P x) (= y (+ x 5)) (= x2 (+ x 1)) (< x 10)) (P x2))))
(assert (forall ((z Int)) (=> (and (P z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);

    // Verify transformed problem is still valid
    result.validate().unwrap();

    let transformed_result = solve_with_pdr(result);
    assert_safe(
        &transformed_result,
        "Local var eliminated problem should be Safe",
    );

    let orig_result = solve_with_pdr(problem);
    assert_safe(&orig_result, "Original problem should be Safe");
}

/// Local var elimination: one-sided bound (lower only) elimination.
///
/// Clause has y >= 5 where y is local. Dropping that conjunct should be sound
/// because y can always be chosen to satisfy it.
#[test]
fn soundness_local_var_elim_one_sided_bound_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (y Int) (x2 Int))
    (=> (and (P x) (>= y 5) (= x2 (+ x 1)) (< x 10)) (P x2))))
(assert (forall ((z Int)) (=> (and (P z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);
    result.validate().unwrap();

    let transformed_result = solve_with_pdr(result);
    assert_safe(
        &transformed_result,
        "One-sided bound eliminated problem should be Safe",
    );
}

/// Local var elimination must NOT drop a variable with BOTH lower and upper bounds.
///
/// Clause has y >= 0 AND y <= 10 where y is local and appears in constraint
/// but not in predicate args. The conjunction is satisfiable but dropping it
/// could change the problem if y appears elsewhere in constraints.
/// This test verifies that both-sided bound vars are left alone.
#[test]
fn soundness_local_var_elim_two_sided_bound_preserved() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let x2 = ChcVar::new("x2", ChcSort::Int);

    // P(x) <= x = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x2) <= P(x), y >= 0, y <= 10, x2 = x + 1, x < 10
    // y has BOTH lower and upper bounds -> should NOT be eliminated
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::and_all(vec![
                ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
                ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(10)),
                ChcExpr::eq(
                    ChcExpr::var(x2.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ),
                ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
            ])),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x2)]),
    ));

    // false <= P(z), z < 0
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(z), ChcExpr::int(0))),
    )));

    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);

    // Problem should remain Safe
    let transformed_result = solve_with_pdr(result);
    assert_safe(
        &transformed_result,
        "Two-sided bound preserved problem should be Safe",
    );
}

/// Local var elimination on Unsafe problem must preserve the Unsafe verdict.
#[test]
fn soundness_local_var_elim_unsafe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 100) (P x))))
(assert (forall ((z Int)) (=> (and (P z) (> z 50)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);

    let transformed_result = solve_with_pdr(result);
    assert_unsafe(
        &transformed_result,
        "Local var eliminated problem should remain Unsafe",
    );
}

/// Trivially false clause elimination.
///
/// LocalVarEliminator drops clauses whose constraint simplifies to `false`.
/// This must not drop reachable clauses.
#[test]
fn soundness_local_var_elim_trivially_false_clause_removed() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // P(x) <= x = 0  (valid init)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) <= y = 0, y = 1  (becomes false after local-var substitution)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and_all([
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(1)),
        ])),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // false <= P(z), z < 0
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(z), ChcExpr::int(0))),
    )));

    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);

    // The trivially false clause should be removed
    assert!(
        result.clauses().len() < problem.clauses().len(),
        "Trivially false clause should be removed"
    );

    // Problem should still be Safe
    let transformed_result = solve_with_pdr(result);
    assert_safe(
        &transformed_result,
        "Problem with trivially false clause removed should be Safe",
    );
}

// ============================================================================
// 4. Full pipeline soundness
// ============================================================================

/// Full preprocessing pipeline (DeadParam + LocalVar + ClauseInliner)
/// on a multi-predicate Safe problem.
#[test]
fn soundness_full_pipeline_safe_multi_predicate() {
    let input = r#"
(set-logic HORN)
(declare-fun Init (Int Int) Bool)
(declare-fun Step (Int Int) Bool)

(assert (forall ((x Int) (y Int))
    (=> (and (= x 0) (= y 0)) (Init x y))))
(assert (forall ((x Int) (y Int))
    (=> (Init x y) (Step x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (Step x y) (= x2 (+ x 1)) (= y2 (+ y 1)) (< x 10)) (Step x2 y2))))
(assert (forall ((x Int) (y Int))
    (=> (and (Step x y) (< x 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    // Apply full pipeline
    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem.clone());

    let transformed_result = solve_with_pdr(result.problem.clone());
    assert_safe(
        &transformed_result,
        "Full pipeline transformed problem should be Safe",
    );

    // Back-translate and verify
    if let PortfolioResult::Safe(model) = transformed_result {
        let translated = result.back_translator.translate_validity(model);
        let mut verifier = PdrSolver::new(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(&translated),
            "Back-translated model must be valid for original problem"
        );
    }
}

/// Full preprocessing pipeline on an Unsafe problem.
#[test]
fn soundness_full_pipeline_unsafe() {
    let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Step (Int) Bool)

(assert (forall ((x Int)) (=> (= x 100) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Step x))))
(assert (forall ((z Int)) (=> (and (Step z) (> z 50)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem.clone());

    let transformed_result = solve_with_pdr(result.problem);
    assert_unsafe(
        &transformed_result,
        "Full pipeline transformed problem should be Unsafe",
    );
}

// ============================================================================
// 5. Variable capture avoidance in inlining
// ============================================================================

/// Variable capture: body-local variables in inlined clause must not collide
/// with variables in the calling clause.
///
/// Def: P(x) <= x > 0 AND y = x + 1 (y is body-local)
/// Use: Q(w) <= P(w) AND y = 42
/// If y is not freshened during inlining, the constraint y = x+1 from P
/// would collide with y = 42 in Q's clause, potentially making the
/// combined constraint unsatisfiable when it should be satisfiable.
#[test]
fn soundness_inline_variable_capture_avoidance() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let w = ChcVar::new("w", ChcSort::Int);

    // P(x) <= x >= 0 AND y = x + 1 (y is body-local)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![],
            Some(ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
                ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // Q(w) <= P(w) AND y = 42
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(w.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(42))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(w)]),
    ));

    // false <= Q(z), z < 0
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(z), ChcExpr::int(0))),
    )));

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());

    // After inlining, Q should still be satisfiable (w >= 0 from P, y=42 in Q)
    // The inlined clause must have freshened y from P's body to avoid capture.
    let transformed_result = solve_with_pdr(result.problem);
    assert_safe(
        &transformed_result,
        "Variable capture avoidance: inlined problem should be Safe",
    );
}

// ============================================================================
// 6. Predicate compaction soundness
// ============================================================================

/// After inlining removes predicates, the remaining predicates are compacted
/// (IDs re-assigned). The new-to-old mapping must be correct for back-translation.
#[test]
fn soundness_predicate_compaction_back_translation() {
    let input = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)
(declare-fun C (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int)) (=> (A x) (B x))))
(assert (forall ((x Int) (x2 Int))
    (=> (and (B x) (= x2 (+ x 1)) (< x 10)) (B x2))))
(assert (forall ((x Int)) (=> (B x) (C x))))
(assert (forall ((z Int)) (=> (and (C z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());

    // A and C should be inlined (unique non-recursive defs).
    // B should remain (has self-loop + base case = 2 definitions, blocked by unique-def).
    // Actually A has unique def, C has unique def. B has base case from A-inlining + self-loop.
    // After inlining A into B's base, B has 2 definitions (one from inlined A, one self-loop).
    // With the self-loop, B is NOT eligible for multi-def inlining (self-recursive).
    // C has unique def depending on B -> C can be inlined.

    let transformed_result = solve_with_pdr(result.problem.clone());
    assert_safe(&transformed_result, "Compacted problem should be Safe");

    if let PortfolioResult::Safe(model) = transformed_result {
        let translated = result.back_translator.translate_validity(model);
        // Back-translated model should have interpretations for all original predicates
        for pred in problem.predicates() {
            assert!(
                translated.get(&pred.id).is_some(),
                "Back-translated model must have interpretation for predicate '{}' (id={})",
                pred.name,
                pred.id.index()
            );
        }
        let mut verifier = PdrSolver::new(problem, PdrConfig::default());
        assert!(
            verifier.verify_model(&translated),
            "Back-translated compacted model must verify against original"
        );
    }
}

// ============================================================================
// 7. CompositeBackTranslator ordering
// ============================================================================

/// The CompositeBackTranslator must apply sub-translators in reverse
/// transformation order. Verify that a pipeline of DeadParamElim + ClauseInliner
/// correctly composes back-translations.
#[test]
fn soundness_composite_back_translator_ordering() {
    let input = r#"
(set-logic HORN)
(declare-fun Init (Int Int) Bool)
(declare-fun Loop (Int Int) Bool)

(assert (forall ((x Int) (y Int))
    (=> (= x 0) (Init x y))))
(assert (forall ((x Int) (y Int))
    (=> (Init x y) (Loop x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (Loop x y) (= x2 (+ x 1)) (< x 10)) (Loop x2 y2))))
(assert (forall ((z Int) (w Int))
    (=> (and (Loop z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    // DeadParam eliminates y, then ClauseInliner inlines Init
    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem.clone());

    let mut solver = PdrSolver::new(result.problem.clone(), PdrConfig::default());
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = result.back_translator.translate_validity(model);

            // Check all original predicates have interpretations
            for pred in problem.predicates() {
                assert!(
                    translated.get(&pred.id).is_some(),
                    "Back-translated model must include pred '{}' (composite back-translator)",
                    pred.name,
                );
            }

            let mut verifier = PdrSolver::new(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&translated),
                "Composite back-translator must produce valid model"
            );
        }
        other => panic!("Expected Safe, got {other:?}"),
    }
}

// ============================================================================
// 8. PreprocessSummary end-to-end
// ============================================================================

/// Full PreprocessSummary.build() on an LIA Safe problem must produce the
/// same verdict and a valid back-translated model.
#[test]
fn soundness_preprocess_summary_safe() {
    use crate::portfolio::PreprocessSummary;

    let input = r#"
(set-logic HORN)
(declare-fun Init (Int Int) Bool)
(declare-fun Loop (Int Int) Bool)

(assert (forall ((x Int) (y Int))
    (=> (and (= x 0) (= y 0)) (Init x y))))
(assert (forall ((x Int) (y Int))
    (=> (Init x y) (Loop x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (Loop x y) (= x2 (+ x 1)) (= y2 (+ y 1)) (< x 10)) (Loop x2 y2))))
(assert (forall ((z Int) (w Int))
    (=> (and (Loop z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);
    let summary = PreprocessSummary::build(problem.clone(), false);

    // Solve the transformed problem directly
    let mut solver = PdrSolver::new(summary.transformed_problem.clone(), PdrConfig::default());
    match solver.solve() {
        PdrResult::Safe(model) => {
            let translated = summary.back_translator.translate_validity(model);
            let mut verifier = PdrSolver::new(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&translated),
                "PreprocessSummary back-translated model must be valid"
            );
        }
        PdrResult::Unsafe(_) => panic!("Expected Safe from preprocessed problem"),
        PdrResult::Unknown => {
            // PDR may return Unknown on some transformed problems - that is
            // not a soundness issue, just incompleteness. Only check if we
            // get a definitive Safe result.
        }
        PdrResult::NotApplicable => {
            // PDR declared this problem class not applicable.
        }
    }
}

/// PreprocessSummary on Unsafe problem must not flip verdict.
#[test]
fn soundness_preprocess_summary_unsafe() {
    use crate::portfolio::PreprocessSummary;

    let input = r#"
(set-logic HORN)
(declare-fun Init (Int) Bool)
(declare-fun Step (Int) Bool)

(assert (forall ((x Int)) (=> (= x 100) (Init x))))
(assert (forall ((x Int)) (=> (Init x) (Step x))))
(assert (forall ((z Int)) (=> (and (Step z) (> z 50)) false)))

(check-sat)
"#;
    let problem = parse(input);
    let summary = PreprocessSummary::build(problem.clone(), false);

    let result = solve_with_pdr(summary.transformed_problem);
    assert_unsafe(
        &result,
        "PreprocessSummary transformed Unsafe problem must remain Unsafe",
    );
}

// ============================================================================
// 9. Edge cases
// ============================================================================

/// Empty problem (no predicates, no clauses) should be handled gracefully.
#[test]
fn soundness_empty_problem() {
    let problem = ChcProblem::new();

    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem);

    assert_eq!(result.problem.clauses().len(), 0);
    assert_eq!(result.problem.predicates().len(), 0);
}

/// Problem with only a query (no init/step clauses): trivially Safe.
#[test]
fn soundness_query_only() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);

    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(z), ChcExpr::int(0))),
    )));

    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem);

    // Query should survive (head is False, never inlined)
    assert_eq!(result.problem.clauses().len(), 1);
    assert!(result.problem.clauses()[0].is_query());
}

/// Self-recursive predicate must NOT be inlined (termination guard).
#[test]
fn soundness_self_recursive_not_inlined() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (P x))))
(assert (forall ((x Int) (x2 Int))
    (=> (and (P x) (= x2 (+ x 1)) (< x 10)) (P x2))))
(assert (forall ((z Int)) (=> (and (P z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    let result = Box::new(ClauseInliner::new()).transform(problem.clone());

    // P is self-recursive and has multiple defs, so it must NOT be inlined
    let has_p = result
        .problem
        .clauses()
        .iter()
        .any(|c| c.head.predicate_id().is_some());
    assert!(has_p, "Self-recursive P must not be inlined away");

    // Both original and transformed should be Safe
    let transformed_result = solve_with_pdr(result.problem);
    assert_safe(
        &transformed_result,
        "Problem with self-recursive pred should be Safe",
    );
}

/// Cyclic definitions A(x) <= B(x); B(x) <= A(x) must not cause infinite loop.
#[test]
fn soundness_cyclic_definitions_terminate() {
    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // A(x) <= B(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(b, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(a, vec![ChcExpr::var(x.clone())]),
    ));

    // B(x) <= A(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(a, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(b, vec![ChcExpr::var(x.clone())]),
    ));

    // false <= A(z), z > 0
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(a, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(0))),
    )));

    // This must terminate (not loop forever)
    let result = Box::new(ClauseInliner::new()).transform(problem);

    // At least one cyclic predicate must survive
    let has_pred = result
        .problem
        .clauses()
        .iter()
        .any(|c| c.head.predicate_id().is_some());
    assert!(has_pred, "At least one cyclic predicate must remain");
}

/// Regression: constraint-size limit prevents blowup from aggressive inlining.
/// A predicate with a very large constraint should NOT be inlined.
#[test]
fn soundness_constraint_size_limit() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // Build a large constraint: x >= 0 AND x >= 1 AND ... AND x >= 20000
    let mut conjuncts = Vec::new();
    for i in 0..20000 {
        conjuncts.push(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(i)));
    }
    let big_constraint = ChcExpr::and_all(conjuncts);

    // P(x) <= big_constraint
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(big_constraint),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // Q(y) <= P(y)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y)]),
    ));

    // false <= Q(z)
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        q,
        vec![ChcExpr::var(z)],
    )])));

    let result = Box::new(ClauseInliner::new()).transform(problem);

    // P's constraint exceeds the size limit (10000), so P should NOT be inlined.
    // Use name lookup since predicate IDs may be remapped by compaction.
    let p_new_id = result.problem.lookup_predicate("P");
    assert!(
        p_new_id.is_some(),
        "P should still exist after inlining (constraint exceeds size limit)"
    );
    let p_new = p_new_id.unwrap();
    let has_p_in_body = result
        .problem
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == p_new));
    assert!(
        has_p_in_body,
        "P should appear in clause bodies (not inlined due to size limit)"
    );
}

// ============================================================================
// 10. Differential tests: original vs. transformed on benchmark-style problems
// ============================================================================

/// Count-to-N safe problem: both original and transformed must agree.
#[test]
fn soundness_differential_count_to_n_safe() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

(assert (forall ((x Int) (n Int))
    (=> (and (= x 0) (>= n 0)) (P x n))))
(assert (forall ((x Int) (n Int) (x2 Int))
    (=> (and (P x n) (= x2 (+ x 1)) (< x n)) (P x2 n))))
(assert (forall ((x Int) (n Int))
    (=> (and (P x n) (> x (+ n 1))) false)))

(check-sat)
"#;
    let problem = parse(input);

    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem.clone());

    // Both should produce the same verdict
    let orig = solve_with_pdr(problem);
    let transformed = solve_with_pdr(result.problem);

    // If either returns Unknown (solver incompleteness), skip comparison
    if matches!(orig, PortfolioResult::Unknown) || matches!(transformed, PortfolioResult::Unknown) {
        return;
    }

    let orig_safe = matches!(orig, PortfolioResult::Safe(_));
    let transformed_safe = matches!(transformed, PortfolioResult::Safe(_));
    assert_eq!(
        orig_safe, transformed_safe,
        "Original and transformed must agree: orig_safe={orig_safe}, transformed_safe={transformed_safe}"
    );
}

/// Regression for #7997: end-to-end inlining + PDR solve + back-translation
/// for a signed triple-sum pattern where Outer(C) <= Inner(A, B) /\ C = A + B.
///
/// After inlining Outer, only Inner remains. PDR produces a model for Inner,
/// then back-translation must synthesize Outer's interpretation by eliminating
/// clause-local variables A, B through the linear equality C = A + B.
///
/// The back-translated model must validate against the original (pre-inlining) problem.
#[test]
fn soundness_inline_signed_triple_sum_back_translate() {
    let input = r#"
(set-logic HORN)
(declare-fun Inner (Int Int) Bool)
(declare-fun Outer (Int) Bool)

; Inner init: A = 0, B = 0
(assert (forall ((A Int) (B Int))
    (=> (and (= A 0) (= B 0)) (Inner A B))))

; Inner step: A' = A + 2, B' = B + 1
(assert (forall ((A Int) (B Int) (A2 Int) (B2 Int))
    (=> (and (Inner A B) (= A2 (+ A 2)) (= B2 (+ B 1)) (< A 20))
        (Inner A2 B2))))

; Outer(C) <= Inner(A, B) /\ C = A + B  (signed-sum link)
(assert (forall ((A Int) (B Int) (C Int))
    (=> (and (Inner A B) (>= A 20) (= C (+ A B)))
        (Outer C))))

; Safety: Outer(C) implies C >= 0
(assert (forall ((C Int))
    (=> (and (Outer C) (< C 0)) false)))

(check-sat)
"#;
    let problem = parse(input);

    // Transform: Outer should be inlined (unique non-recursive def)
    let result = Box::new(ClauseInliner::new()).transform(problem.clone());

    // After inlining Outer, only Inner should remain
    assert!(
        result.problem.lookup_predicate("Outer").is_none(),
        "Outer should be inlined away"
    );

    // Solve the transformed problem with PDR
    let mut solver = PdrSolver::new(result.problem.clone(), PdrConfig::default());
    match solver.solve() {
        PdrResult::Safe(model) => {
            // Back-translate: must synthesize Outer's interpretation
            let translated = result.back_translator.translate_validity(model);

            // Outer must have an interpretation (the bug in #7997)
            let outer_id = problem
                .lookup_predicate("Outer")
                .expect("original problem should have Outer");
            assert!(
                translated.get(&outer_id).is_some(),
                "BUG #7997: back-translation failed to synthesize Outer's interpretation \
                 with signed-sum defining clause C = A + B"
            );

            // The interpretation must be closed (no clause-local variables)
            let outer_interp = translated.get(&outer_id).unwrap();
            let allowed: ay_core::kani_compat::DetHashSet<ChcVar> =
                outer_interp.vars.iter().cloned().collect();
            assert!(
                outer_interp
                    .formula
                    .vars()
                    .into_iter()
                    .all(|var| allowed.contains(&var)),
                "BUG #7997: Outer's back-translated interpretation contains \
                 clause-local variables: {} (vars: {:?})",
                outer_interp.formula,
                outer_interp.vars,
            );

            // Print synthesized interpretations for debugging
            for (pred_id, interp) in translated.iter() {
                let pred_name = problem
                    .predicates()
                    .iter()
                    .find(|p| p.id == *pred_id)
                    .map(|p| p.name.as_str())
                    .unwrap_or("?");
                eprintln!(
                    "  {pred_name} (P{}): {:?} -> {}",
                    pred_id.index(),
                    interp
                        .vars
                        .iter()
                        .map(|v| v.name.as_str())
                        .collect::<Vec<_>>(),
                    interp.formula
                );
            }

            // Verify the back-translated model against the original problem
            let mut verifier = PdrSolver::new(problem, PdrConfig::default());
            assert!(
                verifier.verify_model(&translated),
                "BUG #7997: back-translated model must validate on the original problem"
            );
        }
        other => panic!("Expected Safe, got {other:?}"),
    }
}

/// Dillig-style problem: x increments, y tracks x, query checks relationship.
#[test]
fn soundness_differential_dillig_style() {
    let input = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)

(assert (forall ((x Int) (y Int))
    (=> (and (= x 0) (= y 0)) (Inv x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (Inv x y) (= x2 (+ x 1)) (= y2 (+ y 1)) (< x 100)) (Inv x2 y2))))
(assert (forall ((x Int) (y Int))
    (=> (and (Inv x y) (not (= x y))) false)))

(check-sat)
"#;
    let problem = parse(input);

    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem.clone());

    // Both should be Safe (x = y is an inductive invariant)
    let orig = solve_with_pdr(problem);
    assert_safe(&orig, "Dillig-style original should be Safe");

    let transformed = solve_with_pdr(result.problem);
    assert_safe(&transformed, "Dillig-style transformed should be Safe");
}

fn solidity_balance_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Balance".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkBalance".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "balance".to_string(),
                    sort: ChcSort::BitVec(256),
                },
                ChcDtSelector {
                    name: "live".to_string(),
                    sort: ChcSort::Bool,
                },
            ],
        }]),
    }
}

fn solidity_state_sort(balance_sort: ChcSort) -> ChcSort {
    ChcSort::Datatype {
        name: "State".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mkState".to_string(),
            selectors: vec![ChcDtSelector {
                name: "balances".to_string(),
                sort: ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(balance_sort)),
            }],
        }]),
    }
}

fn add_solidity_array_dt_defs(problem: &mut ChcProblem, balance_sort: ChcSort) {
    problem.add_datatype_def(
        "Balance".to_string(),
        vec![(
            "mkBalance".to_string(),
            vec![
                ("balance".to_string(), ChcSort::BitVec(256)),
                ("live".to_string(), ChcSort::Bool),
            ],
        )],
    );
    problem.add_datatype_def(
        "State".to_string(),
        vec![(
            "mkState".to_string(),
            vec![(
                "balances".to_string(),
                ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(balance_sort)),
            )],
        )],
    );
}

fn solidity_array_dt_init_problem() -> (ChcProblem, PredicateId) {
    let balance_sort = solidity_balance_sort();
    let state_sort = solidity_state_sort(balance_sort.clone());
    let state_var = ChcVar::new("s", state_sort.clone());

    let mut problem = ChcProblem::new();
    add_solidity_array_dt_defs(&mut problem, balance_sort);
    let inv = problem.declare_predicate("Inv", vec![state_sort]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(state_var)]),
    ));
    (problem, inv)
}

/// #9395 route boundary: the useful Solidity `Array K SingleCtorDT`
/// projection appears only after the outer state wrapper is DT-flattened.
/// This test exercises the composed backtranslator and then validates the
/// reconstructed invariant on the original datatype/array problem.
#[test]
fn soundness_dt_flatten_solidity_projection_model_validates_on_original() {
    let balance_sort = solidity_balance_sort();
    let state_sort = solidity_state_sort(balance_sort.clone());
    let state_var = ChcVar::new("s", state_sort.clone());
    let balances = ChcExpr::FuncApp(
        "balances".to_string(),
        ChcSort::Array(
            Box::new(ChcSort::BitVec(160)),
            Box::new(balance_sort.clone()),
        ),
        vec![Arc::new(ChcExpr::var(state_var.clone()))],
    );
    let selected_balance = ChcExpr::FuncApp(
        "balance".to_string(),
        ChcSort::BitVec(256),
        vec![Arc::new(ChcExpr::select(balances, ChcExpr::BitVec(4, 160)))],
    );

    let mut problem = ChcProblem::new();
    add_solidity_array_dt_defs(&mut problem, balance_sort);
    let inv = problem.declare_predicate("Inv", vec![state_sort.clone()]);

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(state_var.clone())])]),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(state_var.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(state_var)])],
            Some(ChcExpr::ne(selected_balance, ChcExpr::BitVec(9, 256))),
        ),
        ClauseHead::False,
    ));

    let transformed = TransformationPipeline::new()
        .with(DtFlattener::new())
        .with(SolidityArrayDtProjectionTransformer::new())
        .transform(problem.clone());
    assert_eq!(
        transformed.problem.predicates()[0].arg_sorts,
        vec![
            ChcSort::Array(
                Box::new(ChcSort::BitVec(160)),
                Box::new(ChcSort::BitVec(256)),
            ),
            ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(ChcSort::Bool)),
        ],
        "DtFlattener must expose the array-of-DT field before projection splits it"
    );

    let balance_array = ChcVar::new(
        "balance_array",
        transformed.problem.predicates()[0].arg_sorts[0].clone(),
    );
    let live_array = ChcVar::new(
        "live_array",
        transformed.problem.predicates()[0].arg_sorts[1].clone(),
    );
    let projected_formula = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(balance_array.clone()), ChcExpr::BitVec(4, 160)),
        ChcExpr::BitVec(9, 256),
    );
    let mut projected_model = InvariantModel::new();
    projected_model.set(
        inv,
        PredicateInterpretation::new(vec![balance_array, live_array], projected_formula),
    );

    let original_model = transformed
        .back_translator
        .translate_validity(projected_model);
    assert!(
        crate::engines::validate_external_invariant_model(
            &problem,
            &original_model,
            &PdrConfig::default(),
        )
        .expect("external invariant validation should not panic"),
        "composed DtFlattener -> SolidityArrayDtProjection backtranslation must validate on the original problem"
    );
}

#[test]
fn soundness_dt_flatten_solidity_projection_raw_array_model_rejected_on_original() {
    let (problem, inv) = solidity_array_dt_init_problem();
    let transformed = TransformationPipeline::new()
        .with(DtFlattener::new())
        .with(SolidityArrayDtProjectionTransformer::new())
        .transform(problem.clone());
    assert_eq!(
        transformed.problem.predicates()[0].arity(),
        2,
        "DtFlattener followed by projection should expose two field-array args"
    );

    let balance_array = ChcVar::new(
        "balance_array",
        transformed.problem.predicates()[0].arg_sorts[0].clone(),
    );
    let live_array = ChcVar::new(
        "live_array",
        transformed.problem.predicates()[0].arg_sorts[1].clone(),
    );
    let raw_array_formula = ChcExpr::eq(
        ChcExpr::var(balance_array.clone()),
        ChcExpr::var(balance_array.clone()),
    );
    let mut projected_model = InvariantModel::new();
    projected_model.set(
        inv,
        PredicateInterpretation::new(vec![balance_array, live_array], raw_array_formula),
    );

    let original_model = transformed
        .back_translator
        .translate_validity(projected_model);
    let interp = original_model
        .get(&inv)
        .expect("backtranslation should retain the predicate entry");
    assert!(
        interp.vars.is_empty(),
        "raw projected arrays are unsupported and must poison the composed model"
    );
    assert!(
        !crate::engines::validate_external_invariant_model(
            &problem,
            &original_model,
            &PdrConfig::default(),
        )
        .expect("external invariant validation should not panic"),
        "poisoned composed backtranslation must be rejected on the original problem"
    );
}
