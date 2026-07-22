// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::lemma_cluster::LemmaInstance;
use crate::pdr::PdrConfig;
use crate::{ChcParser, ChcSort, ChcVar};

fn make_var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

#[test]
fn test_collect_conjuncts_nontrivial() {
    let a = ChcExpr::Var(ChcVar::new("a", ChcSort::Bool));
    let b = ChcExpr::Var(ChcVar::new("b", ChcSort::Bool));
    let c = ChcExpr::Var(ChcVar::new("c", ChcSort::Bool));

    // Single expression
    let conjs = a.collect_conjuncts_nontrivial();
    assert_eq!(conjs.len(), 1);

    // Nested conjunction: (a ∧ (b ∧ c))
    let nested = ChcExpr::and(a.clone(), ChcExpr::and(b, c));
    let conjs = nested.collect_conjuncts_nontrivial();
    assert_eq!(conjs.len(), 3);

    // With true
    let with_true = ChcExpr::and(ChcExpr::Bool(true), a);
    let conjs = with_true.collect_conjuncts_nontrivial();
    assert_eq!(conjs.len(), 1);
}

#[test]
fn test_try_cluster_subsume_rejects_single_member() {
    // Cluster with only 1 member should return None (precondition failure)
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    // Pattern: x >= k
    let pattern = ChcExpr::ge(make_var("x"), ChcExpr::Var(pattern_var.clone()));

    let mut cluster = LemmaCluster::new(pred_id, pattern, vec![pattern_var]);
    // Add only one member
    cluster.add_member(LemmaInstance::new(1, vec![5]));

    let result = solver.try_cluster_subsume(&cluster, 1);
    assert!(result.is_none(), "single member cluster should not subsume");
}

#[test]
fn test_try_cluster_subsume_rejects_empty_cluster() {
    // Cluster with 0 members should return None
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = ChcExpr::ge(make_var("x"), ChcExpr::Var(pattern_var.clone()));

    let cluster = LemmaCluster::new(pred_id, pattern, vec![pattern_var]);
    // No members added

    let result = solver.try_cluster_subsume(&cluster, 1);
    assert!(result.is_none(), "empty cluster should not subsume");
}

#[test]
fn test_try_cluster_subsume_rejects_too_many_pattern_vars() {
    // Cluster with > MAX_PATTERN_VARS should return None
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int Int Int Int Int Int) Bool)
(assert (forall ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int) (g Int))
    (=> (and (= a 0) (= b 0) (= c 0) (= d 0) (= e 0) (= f 0) (= g 0))
        (inv a b c d e f g))))
(assert (forall ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int) (g Int))
    (=> (and (inv a b c d e f g) (< a 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.get_predicate_by_name("inv").unwrap().id;
    // Create 7 pattern variables (> MAX_PATTERN_VARS = 6)
    let pattern_vars: Vec<_> = (0..7)
        .map(|i| ChcVar::new(format!("__gg_k{i}"), ChcSort::Int))
        .collect();

    // Pattern: a >= k0 ∧ b >= k1 ∧ ... ∧ g >= k6
    let pattern = pattern_vars
        .iter()
        .enumerate()
        .fold(ChcExpr::Bool(true), |acc, (i, var)| {
            let names = ["a", "b", "c", "d", "e", "f", "g"];
            ChcExpr::and(
                acc,
                ChcExpr::ge(make_var(names[i]), ChcExpr::Var(var.clone())),
            )
        });

    let mut cluster = LemmaCluster::new(pred_id, pattern, pattern_vars);
    // Add 2 members
    cluster.add_member(LemmaInstance::new(1, vec![1, 2, 3, 4, 5, 6, 7]));
    cluster.add_member(LemmaInstance::new(2, vec![2, 3, 4, 5, 6, 7, 8]));

    let result = solver.try_cluster_subsume(&cluster, 1);
    assert!(
        result.is_none(),
        "cluster with too many pattern vars should not subsume"
    );
}

#[test]
fn test_try_cluster_subsume_with_two_members_runs_without_panic() {
    // Cluster with 2 members should be eligible. Tests that the function
    // handles CC results gracefully without panicking.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = ChcExpr::eq(make_var("x"), ChcExpr::Var(pattern_var.clone()));

    let mut cluster = LemmaCluster::new(pred_id, pattern, vec![pattern_var]);
    cluster.add_member(LemmaInstance::new(1, vec![5]));
    cluster.add_member(LemmaInstance::new(2, vec![10]));

    // Result may be None or Some - either is valid
    let _ = solver.try_cluster_subsume(&cluster, 1);
}

#[test]
fn test_try_cluster_subsume_three_collinear_points_runs_without_panic() {
    // Cluster with 3 collinear points enables CC to find linear constraints
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let k0 = ChcVar::new("__gg_k0", ChcSort::Int);
    let k1 = ChcVar::new("__gg_k1", ChcSort::Int);
    let pattern = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::Var(k0.clone())),
        ChcExpr::ge(make_var("y"), ChcExpr::Var(k1.clone())),
    );

    let mut cluster = LemmaCluster::new(pred_id, pattern, vec![k0, k1]);
    // 3 collinear points: (0,0), (1,1), (2,2) - all on y = x line
    cluster.add_member(LemmaInstance::new(1, vec![0, 0]));
    cluster.add_member(LemmaInstance::new(2, vec![1, 1]));
    cluster.add_member(LemmaInstance::new(3, vec![2, 2]));

    // Result depends on inductiveness - either None or Some is valid
    let _ = solver.try_cluster_subsume(&cluster, 1);
}

#[test]
fn test_weaken_until_implied_keeps_necessary_conjuncts() {
    // Test that weaken_until_implied keeps conjuncts when full_cc doesn't
    // imply the remaining formula after dropping them.
    //
    // Algorithm: For each conjunct, check if full_cc => (formula without that conjunct).
    // If yes, drop it. If no, keep it.
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // full_cc: x >= 0 ∧ x <= 10 (bounded range)
    let full_cc = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::int(0)),
        ChcExpr::le(make_var("x"), ChcExpr::int(10)),
    );

    // projected: x >= 5 ∧ x <= 7 (more restrictive than full_cc)
    // Neither can be dropped because:
    // - Dropping x >= 5: full_cc doesn't imply (x <= 7) alone (counterexample: x = 0)
    // - Dropping x <= 7: full_cc doesn't imply (x >= 5) alone (counterexample: x = 0)
    let projected = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::int(5)),
        ChcExpr::le(make_var("x"), ChcExpr::int(7)),
    );

    let result = solver.weaken_until_implied(&full_cc, &projected);
    // Neither conjunct should be droppable
    let conjs = result.collect_conjuncts_nontrivial();
    assert!(
        conjs.len() >= 2,
        "should keep both conjuncts since full_cc doesn't imply either alone, got: {result}"
    );
}

#[test]
fn test_weaken_until_implied_drops_redundant_conjuncts() {
    // Test that weaken_until_implied drops fully redundant conjuncts
    let smt2 = r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // full_cc: x >= 0 ∧ x <= 10
    let full_cc = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::int(0)),
        ChcExpr::le(make_var("x"), ChcExpr::int(10)),
    );

    // projected: x >= -5 ∧ x <= 15 (both weaker than full_cc)
    let projected = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::int(-5)),
        ChcExpr::le(make_var("x"), ChcExpr::int(15)),
    );

    let result = solver.weaken_until_implied(&full_cc, &projected);
    // When full_cc implies all conjuncts of projected, result is `true`
    assert_eq!(
        result,
        ChcExpr::Bool(true),
        "when full_cc implies all of projected, result should be true"
    );
}
