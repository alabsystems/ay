// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use std::sync::Arc;

fn create_simple_loop_problem() -> ChcProblem {
    // x = 0 => Inv(x)
    // Inv(x) /\ x < 10 => Inv(x + 1)
    // Inv(x) /\ x >= 10 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_trivial_problem() -> ChcProblem {
    // x = 0 => Inv(x)
    // Inv(x) /\ x >= 5 => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_multi_pred_problem() -> ChcProblem {
    // P(x) /\ x < 10 => Q(x+1)
    // Q(y) /\ y < 20 => P(y+1)
    // P(x) /\ x >= 15 => false
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) /\ x < 10 => Q(x+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Q(y) /\ y < 20 => P(y+1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(20))),
        ),
        ClauseHead::Predicate(p, vec![ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1))]),
    ));

    // P(x) /\ x >= 15 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(15))),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_classify_simple_loop() {
    let problem = create_simple_loop_problem();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 1);
    assert_eq!(features.num_clauses, 3);
    assert!(features.is_linear);
    assert!(features.is_single_predicate);
    assert!(!features.uses_arrays);
    assert!(!features.uses_real);
    assert_eq!(features.num_transitions, 1);
    assert_eq!(features.num_facts, 1);
    assert_eq!(features.num_queries, 1);
    assert_eq!(features.class, ProblemClass::SimpleLoop);

    // Extended features (#7915)
    assert_eq!(features.scc_count, 1);
    assert_eq!(features.max_scc_size, 1);
    assert_eq!(features.dag_depth, 1);
    assert!(features.max_clause_variables > 0);
    assert!(features.mean_clause_variables > 0.0);
    assert!(!features.has_multiplication);
    assert!(!features.has_mod_div);
    assert!(!features.has_ite);
    assert_eq!(features.self_loop_ratio, 1.0); // single transition is a self-loop
    assert_eq!(features.max_predicate_arity, 1);
}

#[test]
fn test_tautological_single_predicate_transition_stays_simple_loop() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));

    let features = ProblemClassifier::classify(&problem);
    assert_eq!(features.num_transitions, 1);
    assert!(!features.has_cycles);
    assert_eq!(features.class, ProblemClass::SimpleLoop);
}

#[test]
fn test_classify_trivial() {
    let problem = create_trivial_problem();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 1);
    assert_eq!(features.num_clauses, 2);
    assert!(features.is_single_predicate);
    assert_eq!(features.class, ProblemClass::Trivial);
}

#[test]
fn test_classify_multi_pred() {
    let problem = create_multi_pred_problem();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 2);
    assert!(!features.is_single_predicate);
    assert!(features.is_linear);
    // Has a cycle: P -> Q -> P
    assert!(features.has_cycles);
    assert_eq!(features.class, ProblemClass::MultiPredLinear);

    // Extended features (#7915) — cycle P->Q->P forms a single cyclic SCC
    assert_eq!(features.scc_count, 1);
    assert_eq!(features.max_scc_size, 2);
    assert_eq!(features.dag_depth, 1);
    assert_eq!(features.max_predicate_arity, 1);
}

/// Create an entry-exit-only problem (Golem's isTrivial pattern)
/// This has no predicates - just queries with constraints
fn create_entry_exit_only_safe() -> ChcProblem {
    // x > 5 /\ x < 3 => false  (UNSAT - safe)
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // Query with unsatisfiable constraint
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(3)),
        )),
        ClauseHead::False,
    ));

    problem
}

fn create_entry_exit_only_unsafe() -> ChcProblem {
    // x > 0 /\ x < 10 => false  (SAT - unsafe)
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    // Query with satisfiable constraint
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10)),
        )),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_classify_entry_exit_only() {
    // Safe case
    let problem = create_entry_exit_only_safe();
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 0);
    assert_eq!(features.num_clauses, 1);
    assert!(features.is_entry_exit_only);
    assert_eq!(features.class, ProblemClass::EntryExitOnly);

    // Unsafe case
    let problem = create_entry_exit_only_unsafe();
    let features = ProblemClassifier::classify(&problem);

    assert!(features.is_entry_exit_only);
    assert_eq!(features.class, ProblemClass::EntryExitOnly);
}

#[test]
fn test_entry_exit_only_not_regular_problem() {
    // Regular problems with predicates should NOT be entry-exit-only
    let problem = create_simple_loop_problem();
    let features = ProblemClassifier::classify(&problem);
    assert!(!features.is_entry_exit_only);

    let problem = create_trivial_problem();
    let features = ProblemClassifier::classify(&problem);
    assert!(!features.is_entry_exit_only);
}

#[test]
fn test_constraint_feature_scanning() {
    // Problem with multiplication in constraint: x * y > 10 => false
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::gt(
            ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::int(10),
        )),
        ClauseHead::False,
    ));

    let features = ProblemClassifier::classify(&problem);
    assert!(features.has_multiplication);
    assert!(!features.has_mod_div);
    assert!(!features.has_ite);
    assert_eq!(features.max_clause_variables, 2);
}

#[test]
fn test_extended_features_dag_depth() {
    // Linear chain: P -> Q -> R (no cycles, DAG depth 3)
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Int]);
    let r = problem.declare_predicate("R", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));
    // P(x) => Q(x, x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(x.clone())]),
    ));
    // Q(x, _) => R(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(x.clone())])],
            None,
        ),
        ClauseHead::Predicate(r, vec![ChcExpr::var(x.clone())]),
    ));
    // R(x) /\ x >= 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let features = ProblemClassifier::classify(&problem);
    assert_eq!(features.num_predicates, 3);
    assert!(!features.has_cycles);
    assert_eq!(features.scc_count, 3); // 3 singleton SCCs
    assert_eq!(features.max_scc_size, 1);
    assert!(features.dag_depth >= 3); // chain P->Q->R
    assert_eq!(features.max_predicate_arity, 2); // Q has arity 2
    assert_eq!(features.self_loop_ratio, 0.0); // no self-loops
}

#[test]
fn test_tautological_self_loop_does_not_make_dag_cyclic() {
    // model-checker-consumer fixedpoint output leaves terminal basic blocks with rules like
    // P(x) /\ C => P(x). They are reachability no-ops and should not block
    // the complete acyclic BMC proof lane.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))),
        ),
        ClauseHead::False,
    ));

    assert!(problem.has_cycles(), "raw graph still has the self-edge");
    let features = ProblemClassifier::classify(&problem);
    assert!(!features.has_cycles);
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert_eq!(features.dag_depth, 2);
}

fn create_triangle_location_diff_bound_problem(sort: ChcSort, non_diff_sum: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let pred_sorts = vec![sort.clone(); 12];
    let p = problem.declare_predicate("P", pred_sorts.clone());
    let q = problem.declare_predicate("Q", pred_sorts.clone());
    let r = problem.declare_predicate("R", pred_sorts);
    let vars: Vec<_> = (0..12)
        .map(|index| ChcVar::new(format!("x{index}"), sort.clone()))
        .collect();

    let args = || vars.iter().cloned().map(ChcExpr::var).collect::<Vec<_>>();

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(triangle_eq(
            &sort,
            triangle_var(&vars, 0),
            triangle_var(&vars, 1),
        )),
        ClauseHead::Predicate(p, args()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(triangle_le_diff_zero(
            &sort,
            triangle_var(&vars, 1),
            triangle_var(&vars, 2),
        )),
        ClauseHead::Predicate(q, args()),
    ));

    let transition_constraint = if non_diff_sum {
        triangle_le_sum_zero(&sort, triangle_var(&vars, 0), triangle_var(&vars, 1))
    } else {
        triangle_le_diff_zero(&sort, triangle_var(&vars, 0), triangle_var(&vars, 1))
    };
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, args()), (q, args())], Some(transition_constraint)),
        ClauseHead::Predicate(r, args()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(r, args())],
            Some(triangle_gt_diff_zero(
                &sort,
                triangle_var(&vars, 0),
                triangle_var(&vars, 1),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_triangle_location_closure_problem(sort: ChcSort) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let pred_sorts = vec![sort.clone(); 12];
    let lturn = problem.declare_predicate("lturn", pred_sorts.clone());
    let step_lturn = problem.declare_predicate("step_lturn", pred_sorts.clone());
    let combined_lturn = problem.declare_predicate("combined_lturn", pred_sorts);
    let marker = problem.declare_predicate("CHC_COMP_FALSE", Vec::new());
    let vars: Vec<_> = (0..16)
        .map(|index| ChcVar::new(format!("x{index}"), sort.clone()))
        .collect();

    let args = || {
        (0..12)
            .map(|index| triangle_var(&vars, index))
            .collect::<Vec<_>>()
    };
    let rotated_args = |a: usize, b: usize, c: usize| {
        vec![
            triangle_var(&vars, 8),
            triangle_var(&vars, 0),
            triangle_var(&vars, 1),
            triangle_var(&vars, 2),
            triangle_var(&vars, 3),
            triangle_var(&vars, 4),
            triangle_var(&vars, 5),
            triangle_var(&vars, 6),
            triangle_var(&vars, a),
            triangle_var(&vars, b),
            triangle_var(&vars, c),
            triangle_var(&vars, 7),
        ]
    };
    let closure_equalities = || {
        ChcExpr::and_all([
            triangle_eq(&sort, triangle_var(&vars, 12), triangle_var(&vars, 8)),
            triangle_eq(&sort, triangle_var(&vars, 13), triangle_var(&vars, 8)),
            triangle_eq(&sort, triangle_var(&vars, 14), triangle_var(&vars, 8)),
        ])
    };

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and_all([
            triangle_le_diff_zero(&sort, triangle_var(&vars, 5), triangle_var(&vars, 10)),
            triangle_le_diff_zero(&sort, triangle_var(&vars, 5), triangle_var(&vars, 8)),
            triangle_le_diff_zero(&sort, triangle_var(&vars, 6), triangle_var(&vars, 1)),
        ])),
        ClauseHead::Predicate(lturn, args()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and_all([
            triangle_le_diff_zero(&sort, triangle_var(&vars, 5), triangle_var(&vars, 1)),
            triangle_le_diff_zero(&sort, triangle_var(&vars, 6), triangle_var(&vars, 10)),
            triangle_le_diff_zero(&sort, triangle_var(&vars, 1), triangle_var(&vars, 9)),
        ])),
        ClauseHead::Predicate(step_lturn, args()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(lturn, args())], Some(ChcExpr::Bool(true))),
        ClauseHead::Predicate(combined_lturn, args()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(step_lturn, args())], Some(ChcExpr::Bool(true))),
        ClauseHead::Predicate(combined_lturn, args()),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (combined_lturn, rotated_args(12, 9, 11)),
                (step_lturn, rotated_args(13, 10, 9)),
                (combined_lturn, rotated_args(14, 11, 10)),
            ],
            Some(closure_equalities()),
        ),
        ClauseHead::Predicate(lturn, rotated_args(11, 10, 9)),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (combined_lturn, rotated_args(8, 11, 13)),
                (step_lturn, rotated_args(15, 11, 10)),
                (combined_lturn, rotated_args(14, 11, 10)),
                (combined_lturn, rotated_args(8, 15, 11)),
                (step_lturn, rotated_args(8, 10, 11)),
            ],
            Some(closure_equalities()),
        ),
        ClauseHead::Predicate(step_lturn, rotated_args(8, 11, 10)),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (combined_lturn, rotated_args(12, 9, 11)),
                (step_lturn, rotated_args(11, 9, 10)),
                (combined_lturn, rotated_args(13, 10, 9)),
                (combined_lturn, rotated_args(14, 11, 10)),
            ],
            Some(closure_equalities()),
        ),
        ClauseHead::Predicate(marker, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(marker, Vec::new())], None),
        ClauseHead::False,
    ));

    problem
}

fn triangle_var(vars: &[ChcVar], index: usize) -> ChcExpr {
    ChcExpr::var(vars[index].clone())
}

fn triangle_zero(sort: &ChcSort) -> ChcExpr {
    match sort {
        ChcSort::Int => ChcExpr::int(0),
        ChcSort::BitVec(width) => ChcExpr::BitVec(0, *width),
        _ => unreachable!("test helper only supports Int and BV"),
    }
}

fn triangle_eq(sort: &ChcSort, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    match sort {
        ChcSort::Int | ChcSort::BitVec(_) => ChcExpr::eq(left, right),
        _ => unreachable!("test helper only supports Int and BV"),
    }
}

fn triangle_le_diff_zero(sort: &ChcSort, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    match sort {
        ChcSort::Int => ChcExpr::le(
            ChcExpr::add(left, ChcExpr::mul(ChcExpr::int(-1), right)),
            ChcExpr::int(0),
        ),
        ChcSort::BitVec(_) => bv_cmp(
            ChcOp::BvSLe,
            bv_bin(
                ChcOp::BvAdd,
                left,
                bv_bin(ChcOp::BvMul, triangle_bv_minus_one(sort), right),
            ),
            triangle_zero(sort),
        ),
        _ => unreachable!("test helper only supports Int and BV"),
    }
}

fn triangle_gt_diff_zero(sort: &ChcSort, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    match sort {
        ChcSort::Int => ChcExpr::gt(
            ChcExpr::add(left, ChcExpr::mul(ChcExpr::int(-1), right)),
            ChcExpr::int(0),
        ),
        ChcSort::BitVec(_) => bv_cmp(
            ChcOp::BvSGt,
            bv_bin(
                ChcOp::BvAdd,
                left,
                bv_bin(ChcOp::BvMul, triangle_bv_minus_one(sort), right),
            ),
            triangle_zero(sort),
        ),
        _ => unreachable!("test helper only supports Int and BV"),
    }
}

fn triangle_le_sum_zero(sort: &ChcSort, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    match sort {
        ChcSort::Int => ChcExpr::le(ChcExpr::add(left, right), ChcExpr::int(0)),
        ChcSort::BitVec(_) => bv_cmp(
            ChcOp::BvSLe,
            bv_bin(ChcOp::BvAdd, left, right),
            triangle_zero(sort),
        ),
        _ => unreachable!("test helper only supports Int and BV"),
    }
}

fn bv_bin(op: ChcOp, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(left), Arc::new(right)])
}

fn bv_cmp(op: ChcOp, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(left), Arc::new(right)])
}

fn triangle_bv_minus_one(sort: &ChcSort) -> ChcExpr {
    let ChcSort::BitVec(width) = sort else {
        unreachable!("test helper only supports BV")
    };
    let value = if *width == 128 {
        u128::MAX
    } else {
        (1u128 << *width) - 1
    };
    ChcExpr::BitVec(value, *width)
}

#[test]
fn test_triangle_location_diff_bounds_int_routes_out_of_multi_pred_complex() {
    let problem = create_triangle_location_diff_bound_problem(ChcSort::Int, false);
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 3);
    assert_eq!(features.max_predicate_arity, 12);
    assert!(!features.is_linear);
    assert!(!features.uses_arrays);
    assert!(!features.uses_real);
    assert!(!features.uses_datatypes);
    assert!(features.is_triangle_location_diff_bounds);
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
}

#[test]
fn test_triangle_location_diff_bounds_bv32_routes_out_of_multi_pred_complex() {
    let problem = create_triangle_location_diff_bound_problem(ChcSort::BitVec(32), false);
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 3);
    assert_eq!(features.max_predicate_arity, 12);
    assert!(!features.is_linear);
    assert!(features.is_triangle_location_diff_bounds);
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
}

#[test]
fn test_triangle_location_detector_rejects_non_diff_bound_sum() {
    let problem = create_triangle_location_diff_bound_problem(ChcSort::Int, true);
    let features = ProblemClassifier::classify(&problem);

    assert!(!features.is_linear);
    assert!(!features.is_triangle_location_diff_bounds);
    assert_eq!(features.class, ProblemClass::MultiPredComplex);
}

#[test]
fn test_triangle_location_detector_accepts_nullary_false_marker() {
    let mut problem = create_triangle_location_diff_bound_problem(ChcSort::Int, false);
    let marker = problem.declare_predicate("CHC_COMP_FALSE", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(marker, Vec::new())], None),
        ClauseHead::False,
    ));

    let features = ProblemClassifier::classify(&problem);

    assert!(features.is_triangle_location_diff_bounds);
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
}

#[test]
fn test_triangle_location_detector_accepts_first_smoke_closure_shape() {
    let problem = create_triangle_location_closure_problem(ChcSort::Int);
    let features = ProblemClassifier::classify(&problem);

    assert_eq!(features.num_predicates, 4);
    assert_eq!(features.max_predicate_arity, 12);
    assert!(!features.is_linear);
    assert!(features.is_triangle_location_diff_bounds);
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
}
