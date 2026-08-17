// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for dead parameter elimination.

#![allow(clippy::unwrap_used)]

use super::super::{BvToBoolBitBlaster, LocalVarEliminator, Transformer};
use super::*;
use crate::parser::ChcParser;
use crate::pdr::PdrConfig;
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult, PortfolioSolver};

fn parse_problem(smt: &str) -> ChcProblem {
    ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"))
}

/// Test: Predicate with unused parameter gets it eliminated.
///
/// P(x, y) where y is never referenced in constraints or other applications.
#[test]
fn test_dead_param_simple_unused() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

; P(x, y) <= x = 0
(assert (forall ((x Int) (y Int))
    (=> (= x 0) (P x y))))

; P(x', y') <= P(x, y) /\ x' = x + 1 /\ x < 10
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (P x y) (= x2 (+ x 1)) (< x 10)) (P x2 y2))))

; false <= P(z, w) /\ z < 0
(assert (forall ((z Int) (w Int))
    (=> (and (P z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    assert_eq!(problem.predicates()[0].arity(), 2);

    let eliminator = DeadParamEliminator::new();
    let (new_problem, position_map) = eliminator.eliminate(&problem);

    // y is dead — should be eliminated
    let mapping = &position_map[&PredicateId::new(0)];
    assert_eq!(mapping.len(), 2);
    assert!(mapping[0].is_some(), "x should be live");
    assert!(mapping[1].is_none(), "y should be dead");

    // New predicate should have arity 1
    assert_eq!(new_problem.predicates()[0].arity(), 1);

    // Problem should still be solvable
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    let solver = PortfolioSolver::new(new_problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "Problem should be Safe after dead param elimination: {result:?}"
    );
}

/// Test: All parameters are live — nothing should be eliminated.
#[test]
fn test_dead_param_all_live() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

; P(x, y) <= x = 0 /\ y = 0
(assert (forall ((x Int) (y Int))
    (=> (and (= x 0) (= y 0)) (P x y))))

; P(x', y') <= P(x, y) /\ x' = x + 1 /\ y' = y + 1 /\ x < 10
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (P x y) (= x2 (+ x 1)) (= y2 (+ y 1)) (< x 10)) (P x2 y2))))

; false <= P(z, w) /\ z < 0
(assert (forall ((z Int) (w Int))
    (=> (and (P z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    let eliminator = DeadParamEliminator::new();
    let (new_problem, position_map) = eliminator.eliminate(&problem);

    // Both parameters are live
    let mapping = &position_map[&PredicateId::new(0)];
    assert!(mapping[0].is_some(), "x should be live");
    assert!(mapping[1].is_some(), "y should be live");

    // Arity unchanged
    assert_eq!(new_problem.predicates()[0].arity(), 2);
}

/// Test: Multiple dead parameters eliminated.
#[test]
fn test_dead_param_multiple_dead() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int Int Int) Bool)

; P(x, a, b, c) <= x = 0
(assert (forall ((x Int) (a Int) (b Int) (c Int))
    (=> (= x 0) (P x a b c))))

; P(x', a', b', c') <= P(x, a, b, c) /\ x' = x + 1 /\ x < 10
(assert (forall ((x Int) (a Int) (b Int) (c Int) (x2 Int) (a2 Int) (b2 Int) (c2 Int))
    (=> (and (P x a b c) (= x2 (+ x 1)) (< x 10)) (P x2 a2 b2 c2))))

; false <= P(z, d, e, f) /\ z < 0
(assert (forall ((z Int) (d Int) (e Int) (f Int))
    (=> (and (P z d e f) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    assert_eq!(problem.predicates()[0].arity(), 4);

    let eliminator = DeadParamEliminator::new();
    let (new_problem, position_map) = eliminator.eliminate(&problem);

    let mapping = &position_map[&PredicateId::new(0)];
    assert!(mapping[0].is_some(), "x should be live");
    assert!(mapping[1].is_none(), "a should be dead");
    assert!(mapping[2].is_none(), "b should be dead");
    assert!(mapping[3].is_none(), "c should be dead");

    // Arity should be 1
    assert_eq!(new_problem.predicates()[0].arity(), 1);
}

/// Test: Variable shared between body and head of different predicates
/// is dead if never constrained.
///
/// In "Q(a, b) <= P(a, b)", b passes from P to Q but never appears in
/// any constraint. Both P and Q can drop position 1 without affecting
/// satisfiability. This is correct: the link carries no information.
#[test]
fn test_dead_param_cross_pred_unconstrained_is_dead() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; P(x, y) <= x = 0
(assert (forall ((x Int) (y Int))
    (=> (= x 0) (P x y))))

; Q(a, b) <= P(a, b)
(assert (forall ((a Int) (b Int))
    (=> (P a b) (Q a b))))

; false <= Q(z, w) /\ z < 0
(assert (forall ((z Int) (w Int))
    (=> (and (Q z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    let eliminator = DeadParamEliminator::new();
    let (new_problem, _position_map) = eliminator.eliminate(&problem);

    // b is never in any constraint → dead in both P and Q.
    assert_eq!(
        new_problem.predicates()[0].arity(),
        1,
        "P should have only x (b is dead)"
    );
    assert_eq!(
        new_problem.predicates()[1].arity(),
        1,
        "Q should have only a (b is dead)"
    );
}

/// Test: Variable shared between predicates stays live when constrained.
///
/// When b is used in a constraint on one side, liveness propagates through
/// the body→head link to keep the position live in all connected predicates.
#[test]
fn test_dead_param_cross_pred_constrained_stays_live() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)

; P(x, y) <= x = 0 /\ y = 42
(assert (forall ((x Int) (y Int))
    (=> (and (= x 0) (= y 42)) (P x y))))

; Q(a, b) <= P(a, b)
(assert (forall ((a Int) (b Int))
    (=> (P a b) (Q a b))))

; false <= Q(z, w) /\ z < 0
(assert (forall ((z Int) (w Int))
    (=> (and (Q z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    let eliminator = DeadParamEliminator::new();
    let (new_problem, _position_map) = eliminator.eliminate(&problem);

    // y is in a constraint (= y 42) → P position 1 is live.
    // b links to y through "Q(a,b) <= P(a,b)" → Q position 1 is live
    // via Step 5 liveness propagation.
    assert_eq!(
        new_problem.predicates()[0].arity(),
        2,
        "P should keep both (y constrained)"
    );
    assert_eq!(
        new_problem.predicates()[1].arity(),
        2,
        "Q should keep both (b linked to constrained y)"
    );
}

/// Test: Array parameter that can't be scalarized gets eliminated if dead.
#[test]
fn test_dead_param_array_sort() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int (Array Int Int)) Bool)

; P(x, a) <= x = 0
(assert (forall ((x Int) (a (Array Int Int)))
    (=> (= x 0) (P x a))))

; P(x', a') <= P(x, a) /\ x' = x + 1 /\ x < 10
(assert (forall ((x Int) (a (Array Int Int)) (x2 Int) (a2 (Array Int Int)))
    (=> (and (P x a) (= x2 (+ x 1)) (< x 10)) (P x2 a2))))

; false <= P(z, b) /\ z < 0
(assert (forall ((z Int) (b (Array Int Int)))
    (=> (and (P z b) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    assert_eq!(problem.predicates()[0].arity(), 2);
    assert!(matches!(
        problem.predicates()[0].arg_sorts[1],
        ChcSort::Array { .. }
    ));

    let eliminator = DeadParamEliminator::new();
    let (new_problem, position_map) = eliminator.eliminate(&problem);

    let mapping = &position_map[&PredicateId::new(0)];
    assert!(mapping[0].is_some(), "x should be live");
    assert!(mapping[1].is_none(), "array param should be dead");

    // After elimination, predicate has arity 1 with no array sort
    assert_eq!(new_problem.predicates()[0].arity(), 1);
    assert!(
        !matches!(
            new_problem.predicates()[0].arg_sorts[0],
            ChcSort::Array { .. }
        ),
        "remaining param should not be array"
    );

    // Problem should be solvable by PDR now (no array sort gate)
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    let solver = PortfolioSolver::new(new_problem, config);
    let result = solver.solve();
    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "Problem should be Safe after dead array param elimination: {result:?}"
    );
}

mod frame_conditions;

/// Test: Body-to-body cross-predicate join variable must stay live.
///
/// When variable b appears in two DIFFERENT body predicates (P and Q),
/// removing position for b from either would break the join constraint.
/// This must stay live even after the Step 4 fix.
#[test]
fn test_dead_param_body_join_stays_live() {
    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(declare-fun Q (Int Int) Bool)
(declare-fun R (Int) Bool)

; P(x, y) <= x = 0
(assert (forall ((x Int) (y Int))
    (=> (= x 0) (P x y))))

; Q(a, b) <= a = 1
(assert (forall ((a Int) (b Int))
    (=> (= a 1) (Q a b))))

; R(c) <= P(c, d) /\ Q(e, d)
; d is a join variable between P and Q in the body
(assert (forall ((c Int) (d Int) (e Int))
    (=> (and (P c d) (Q e d)) (R c))))

; false <= R(z) /\ z < 0
(assert (forall ((z Int))
    (=> (and (R z) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);
    let eliminator = DeadParamEliminator::new();
    let (_new_problem, position_map) = eliminator.eliminate(&problem);

    // d joins P and Q in the body of the R-rule. Position 1 in both P and Q
    // must be live because d is a body-to-body join variable.
    let p_mapping = &position_map[&PredicateId::new(0)];
    assert!(
        p_mapping[1].is_some(),
        "P position 1 (join var d) must be live"
    );

    let q_mapping = &position_map[&PredicateId::new(1)];
    assert!(
        q_mapping[1].is_some(),
        "Q position 1 (join var d) must be live"
    );
}

#[test]
fn test_dead_param_query_reachable_position_survives_renamed_clause_chain_6784() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let seed = ChcVar::new("seed", ChcSort::Int);
    let src = ChcVar::new("src", ChcSort::Int);
    let query = ChcVar::new("query", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::var(seed)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(src.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::add(ChcExpr::var(src), ChcExpr::int(1))]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(query.clone())])],
        Some(ChcExpr::lt(ChcExpr::var(query), ChcExpr::int(0))),
    )));

    let eliminator = DeadParamEliminator::new();
    let (_new_problem, position_map) = eliminator.eliminate(&problem);

    let p_mapping = &position_map[&p];
    assert!(
        p_mapping[0].is_some(),
        "query-reachable P position must stay live across renamed clause chain (#6784)"
    );

    let q_mapping = &position_map[&q];
    assert!(
        q_mapping[0].is_some(),
        "downstream query position must stay live in Q (#6784)"
    );
}

#[test]
fn test_dead_param_bv_bool_query_reachability_6784() {
    let input = r#"
(set-logic HORN)
(declare-fun |bb0| ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun |bb1| ((Array (_ BitVec 32) Bool)) Bool)
(declare-fun |bb2| ((_ BitVec 32) (Array (_ BitVec 32) Bool)) Bool)

(assert
  (forall ((obj_valid (Array (_ BitVec 32) Bool)))
    (=> (= obj_valid ((as const (Array (_ BitVec 32) Bool)) true))
        (bb0 obj_valid))))

(assert
  (forall ((obj_valid (Array (_ BitVec 32) Bool)))
    (=> (bb0 obj_valid)
        (bb1 obj_valid))))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
    (=> (bb1 obj_valid)
        (bb2 x obj_valid))))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
    (=> (and (bb2 x obj_valid)
             (not (select obj_valid #x00000002)))
        false)))

(assert
  (forall ((x (_ BitVec 32)) (obj_valid (Array (_ BitVec 32) Bool)))
    (=> (and (bb2 x obj_valid)
             (not (bvsgt x #x00000000)))
        false)))

(check-sat)
(exit)
"#;
    let problem = parse_problem(input);
    let after_local_var = Box::new(LocalVarEliminator::new()).transform(problem);
    let after_bitblast = Box::new(BvToBoolBitBlaster::new()).transform(after_local_var.problem);
    let bitblasted_problem = after_bitblast.problem;
    let bb2 = bitblasted_problem
        .lookup_predicate("bb2")
        .expect("bb2 predicate must survive BV-to-Bool preprocessing");

    let eliminator = DeadParamEliminator::new();
    let (_new_problem, position_map) = eliminator.eliminate(&bitblasted_problem);
    let bb2_mapping = &position_map[&bb2];

    assert_eq!(
        bb2_mapping.len(),
        33,
        "bb2 should expand to 32 Bool bits plus the array payload"
    );
    assert!(
        bb2_mapping.iter().take(32).any(Option::is_some),
        "at least one BV-derived bb2 x_b* position must stay live after preprocessing (#6784)"
    );
    assert!(
        bb2_mapping[32].is_some(),
        "bb2 array payload must stay live for the select query (#6784)"
    );
}

/// Test: Transformer trait integration
#[test]
fn test_dead_param_transformer_trait() {
    use super::super::TransformationPipeline;

    let input = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)

; P(x, y) <= x = 0
(assert (forall ((x Int) (y Int))
    (=> (= x 0) (P x y))))

; P(x', y') <= P(x, y) /\ x' = x + 1 /\ x < 10
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (P x y) (= x2 (+ x 1)) (< x 10)) (P x2 y2))))

; false <= P(z, w) /\ z < 0
(assert (forall ((z Int) (w Int))
    (=> (and (P z w) (< z 0)) false)))

(check-sat)
"#;
    let problem = parse_problem(input);

    let pipeline = TransformationPipeline::new().with(DeadParamEliminator::new());
    let result = pipeline.transform(problem);

    assert_eq!(result.problem.predicates()[0].arity(), 1);

    // Solve and back-translate
    let config = PortfolioConfig::with_engines(vec![EngineConfig::Pdr(PdrConfig::default())])
        .parallel(false);
    let solver = PortfolioSolver::new(result.problem, config);
    match solver.solve() {
        PortfolioResult::Safe(invariant) => {
            let back = result.back_translator.translate_validity(invariant);
            // Back-translated invariant should have arity 2 for the predicate
            let interp = back.get(&PredicateId::new(0)).unwrap();
            assert_eq!(
                interp.vars.len(),
                2,
                "back-translated interpretation should have original arity"
            );
        }
        other => panic!("Expected Safe, got {other:?}"),
    }
}
