// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::tla2_cluster::{
    Tla2SolverProgramBackend, Tla2SolverProgramKind, Tla2TransitionClusterCompileTiming,
    Tla2TransitionClusterEpochs, Tla2TransitionClusterExpressionRejection,
    Tla2TransitionClusterGuardMetadata, Tla2TransitionClusterRejection, Tla2TransitionScalarSort,
    TLA2_TRANSITION_CLUSTER_STATS_PREFIX,
};
use super::*;
use crate::{
    canonical_vars_for_pred, engines, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, HornClause, InvariantModel, PdrConfig, PredicateId, PredicateInterpretation,
};
use std::sync::Arc;

fn make_test_system() -> TransitionSystem {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);

    TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        // init: x = 0
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        // trans: x_next = x + 1
        ChcExpr::eq(
            ChcExpr::var(x_next),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
        // query: x >= 10
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10)),
    )
}

fn make_high_arity_linear_problem(arity: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int; arity]);

    let fact_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(1)))
        .collect();
    problem.add_clause(HornClause::fact(ChcExpr::Bool(true), inv, fact_args));

    let body_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(2)))
        .collect();
    let head_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(3)))
        .collect();
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, body_args)]),
        ClauseHead::Predicate(inv, head_args),
    ));

    let query_args: Vec<ChcExpr> = (0..arity)
        .map(|i| ChcExpr::add(ChcExpr::int(i as i64), ChcExpr::int(4)))
        .collect();
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv, query_args,
    )])));

    problem
}

fn tla2_cluster_epochs() -> Tla2TransitionClusterEpochs {
    Tla2TransitionClusterEpochs {
        constraints: 17,
        theory_atoms: 19,
        basis: 0,
        trail: 23,
        config: 29,
    }
}

fn make_tla2_action_cluster_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Bool]);
    let inc = problem.declare_action("Inc");
    let stutter = problem.declare_action("Stutter");

    let x = ChcVar::new("x", ChcSort::Int);
    let ok = ChcVar::new("ok", ChcSort::Bool);

    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0), ChcExpr::Bool(true)],
    ));

    // Insert Stutter before Inc to prove extraction sorts clusters by action ID,
    // not by transition-clause insertion order.
    problem.add_clause_with_action(
        HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::var(ok.clone())),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())]),
        ),
        stutter,
    );

    problem.add_clause_with_action(
        HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::and(
                    ChcExpr::var(ok.clone()),
                    ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(3)),
                )),
            ),
            ClauseHead::Predicate(
                inv,
                vec![
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::var(ok.clone()),
                ],
            ),
        ),
        inc,
    );

    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok)])],
        Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(10))),
    )));

    problem
}

fn assert_flat_and_arity(expr: &ChcExpr, expected_arity: usize, label: &str) {
    let args = match expr {
        ChcExpr::Op(ChcOp::And, args) => args,
        other => panic!("{label} should be an n-ary And, got {other:?}"),
    };

    assert_eq!(
        args.len(),
        expected_arity,
        "{label} conjunction arity mismatch"
    );
    assert!(
        args.iter()
            .all(|arg| !matches!(arg.as_ref(), ChcExpr::Op(ChcOp::And, _))),
        "{label} should not contain nested And nodes"
    );
}

fn contains_var_equality(expr: &ChcExpr, lhs: &ChcVar, rhs: &ChcVar) -> bool {
    fn visit(expr: &ChcExpr, lhs: &ChcExpr, rhs: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let left = args[0].as_ref();
                let right = args[1].as_ref();
                (left == lhs && right == rhs) || (left == rhs && right == lhs)
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args.iter().any(|arg| visit(arg, lhs, rhs)),
            ChcExpr::ConstArray(_ks, value) => visit(value, lhs, rhs),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => false,
        }
    }

    visit(expr, &ChcExpr::var(lhs.clone()), &ChcExpr::var(rhs.clone()))
}

fn contains_ite(expr: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Ite, _) => true,
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|arg| contains_ite(arg))
        }
        ChcExpr::ConstArray(_ks, value) => contains_ite(value),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => false,
    }
}

fn make_vmt_style_bool_control_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Bool]);
    let x = ChcVar::new("x", ChcSort::Int);
    let mode = ChcVar::new("mode", ChcSort::Bool);

    problem.add_clause(HornClause::fact(
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::var(mode.clone()),
        ),
        inv,
        vec![ChcExpr::var(x.clone()), ChcExpr::var(mode.clone())],
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(x.clone()), ChcExpr::var(mode.clone())],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::ite(
                    ChcExpr::var(mode.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                ),
                ChcExpr::not(ChcExpr::var(mode.clone())),
            ],
        ),
    ));

    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(mode)])],
        Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0))),
    )));

    (problem, inv)
}

fn make_deterministic_bv_bool_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(8), ChcSort::Bool]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let ok = ChcVar::new("ok", ChcSort::Bool);

    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::BitVec(0, 8), ChcExpr::Bool(true)],
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
            Some(ChcExpr::and(
                ChcExpr::var(ok.clone()),
                ChcExpr::Op(
                    ChcOp::BvULt,
                    vec![
                        Arc::new(ChcExpr::var(x.clone())),
                        Arc::new(ChcExpr::BitVec(250, 8)),
                    ],
                ),
            )),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![
                        Arc::new(ChcExpr::var(x.clone())),
                        Arc::new(ChcExpr::BitVec(1, 8)),
                    ],
                ),
                ChcExpr::not(ChcExpr::var(ok.clone())),
            ],
        ),
    ));

    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok)])],
        Some(ChcExpr::Op(
            ChcOp::BvUGt,
            vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::BitVec(10, 8))],
        )),
    )));

    problem
}

fn make_nondeterministic_bv_bool_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::BitVec(0, 8)],
    ));

    for step in [1, 2] {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(
                inv,
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

    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x.clone())])],
        Some(ChcExpr::Op(
            ChcOp::BvUGt,
            vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::BitVec(10, 8))],
        )),
    )));

    problem
}

fn make_mixed_theory_bv_int_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::BitVec(8), ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let i = ChcVar::new("i", ChcSort::Int);

    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::BitVec(0, 8), ChcExpr::int(0)],
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(x.clone()), ChcExpr::var(i.clone())],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![
                        Arc::new(ChcExpr::var(x.clone())),
                        Arc::new(ChcExpr::BitVec(1, 8)),
                    ],
                ),
                ChcExpr::add(ChcExpr::var(i.clone()), ChcExpr::int(1)),
            ],
        ),
    ));

    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x), ChcExpr::var(i.clone())])],
        Some(ChcExpr::ge(ChcExpr::var(i), ChcExpr::int(10))),
    )));

    problem
}

#[test]
fn test_version_var() {
    let x = ChcVar::new("x", ChcSort::Int);

    // Time 0 should return original
    let v0 = TransitionSystem::version_var(&x, 0);
    assert_eq!(v0.name, "x");

    // Time 1 should suffix
    let v1 = TransitionSystem::version_var(&x, 1);
    assert_eq!(v1.name, "x_1");

    // Time 5 should suffix
    let v5 = TransitionSystem::version_var(&x, 5);
    assert_eq!(v5.name, "x_5");
}

#[test]
fn deterministic_bv_bool_recognizer_accepts_total_single_transition() {
    let problem = make_deterministic_bv_bool_problem();
    let ts = TransitionSystem::from_chc_problem(&problem).expect("extract transition system");

    let recognized = ts
        .recognize_deterministic_bv_bool()
        .expect("deterministic Bool/BV system should be recognized");

    assert_eq!(recognized.predicate, PredicateId(0));
    assert_eq!(recognized.vars.len(), 2);
    assert_eq!(recognized.next_assignments.len(), 2);
    assert!(recognized.has_transition_guard);
    assert_eq!(recognized.next_assignments[0].current.name, "v0");
    assert_eq!(recognized.next_assignments[0].next.name, "v0_next");
    assert_eq!(recognized.next_assignments[1].current.name, "v1");
    assert_eq!(recognized.next_assignments[1].next.name, "v1_next");
    assert_eq!(recognized.metadata.bool_state_vars, 1);
    assert_eq!(recognized.metadata.bv_state_vars, 1);
    assert_eq!(recognized.metadata.total_bv_width, 8);
    assert_eq!(recognized.metadata.total_state_bits, 9);
    assert_eq!(recognized.metadata.max_bv_width, 8);
    assert_eq!(recognized.metadata.transition_conjuncts, 4);
    assert_eq!(recognized.metadata.guard_conjuncts, 2);
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_nondeterministic_transitions() {
    let problem = make_nondeterministic_bv_bool_problem();
    let ts = TransitionSystem::from_chc_problem(&problem).expect("extract transition system");

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "multiple transition clauses produce an alternative relation and must fail closed"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_mixed_theory_state() {
    let problem = make_mixed_theory_bv_int_problem();
    let ts = TransitionSystem::from_chc_problem(&problem).expect("extract transition system");

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "BV plus Int state is mixed-theory and must fail closed"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_unsupported_array_terms() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let x_next = ChcVar::new("x_next", ChcSort::BitVec(8));
    let arr = ChcVar::new(
        "arr",
        ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::BitVec(8))),
    );
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::var(x.clone())),
            ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(arr), ChcExpr::int(0)),
                ChcExpr::var(x),
            ),
        ),
        ChcExpr::Bool(false),
    );

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "array select/store syntax must fail closed before deterministic routing"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_unsupported_datatype_terms() {
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let flag_next = ChcVar::new("flag_next", ChcSort::Bool);
    let dt_sort = ChcSort::Datatype {
        name: "Node".to_string(),
        constructors: Arc::new(Vec::new()),
    };
    let node = ChcVar::new("node", dt_sort);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![flag.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(flag_next), ChcExpr::var(flag.clone())),
            ChcExpr::FuncApp(
                "is_nil".to_string(),
                ChcSort::Bool,
                vec![Arc::new(ChcExpr::var(node))],
            ),
        ),
        ChcExpr::Bool(false),
    );

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "datatype constructor/selector/tester syntax must fail closed"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_real_and_nonlinear_arithmetic() {
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let flag_next = ChcVar::new("flag_next", ChcSort::Bool);
    let real_local = ChcVar::new("r", ChcSort::Real);
    let real_ts = TransitionSystem::new(
        PredicateId(0),
        vec![flag.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(flag_next.clone()), ChcExpr::var(flag.clone())),
            ChcExpr::ge(ChcExpr::var(real_local), ChcExpr::Real(0, 1)),
        ),
        ChcExpr::Bool(false),
    );
    assert!(
        real_ts.recognize_deterministic_bv_bool().is_none(),
        "Real arithmetic constraints must fail closed"
    );

    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let x_next = ChcVar::new("x_next", ChcSort::BitVec(8));
    let bv_as_int = ChcExpr::Op(ChcOp::Bv2Nat, vec![Arc::new(ChcExpr::var(x.clone()))]);
    let nonlinear_ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::var(x)),
            ChcExpr::ge(ChcExpr::mul(bv_as_int.clone(), bv_as_int), ChcExpr::int(0)),
        ),
        ChcExpr::Bool(false),
    );
    assert!(
        nonlinear_ts.recognize_deterministic_bv_bool().is_none(),
        "integer nonlinear arithmetic derived from BV terms must fail closed"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_duplicate_next_assignments() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let x_next = ChcVar::new("x_next", ChcSort::BitVec(8));
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x_next.clone()), ChcExpr::var(x.clone())),
            ChcExpr::eq(
                ChcExpr::var(x_next),
                ChcExpr::Op(
                    ChcOp::BvAdd,
                    vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::BitVec(1, 8))],
                ),
            ),
        ),
        ChcExpr::Bool(false),
    );

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "duplicate assignments for the same next-state variable are ambiguous"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_next_assignment_sort_mismatch() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let flag = ChcVar::new("flag", ChcSort::Bool);
    let x_next = ChcVar::new("x_next", ChcSort::BitVec(8));
    let flag_next = ChcVar::new("flag_next", ChcSort::Bool);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone(), flag],
        ChcExpr::Bool(true),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::var(x.clone())),
            ChcExpr::eq(ChcExpr::var(flag_next), ChcExpr::var(x)),
        ),
        ChcExpr::Bool(false),
    );

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "next-state assignment RHS sort must match the next-state variable"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_shadow_vars_with_same_name() {
    let x8 = ChcVar::new("x", ChcSort::BitVec(8));
    let x8_next = ChcVar::new("x_next", ChcSort::BitVec(8));
    let x16_shadow = ChcVar::new("x", ChcSort::BitVec(16));
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x8.clone()],
        ChcExpr::Bool(true),
        ChcExpr::eq(ChcExpr::var(x8_next), ChcExpr::var(x16_shadow)),
        ChcExpr::Bool(false),
    );

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "shadow vars with the same name but different sort must not count as state vars"
    );
}

#[test]
fn deterministic_bv_bool_recognizer_rejects_next_name_collisions() {
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let x_next_state = ChcVar::new("x_next", ChcSort::BitVec(8));
    let x_next = ChcVar::new("x_next", ChcSort::BitVec(8));
    let x_next_next = ChcVar::new("x_next_next", ChcSort::BitVec(8));
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone(), x_next_state.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x_next), ChcExpr::var(x)),
            ChcExpr::eq(ChcExpr::var(x_next_next), ChcExpr::var(x_next_state)),
        ),
        ChcExpr::Bool(false),
    );

    assert!(
        ts.recognize_deterministic_bv_bool().is_none(),
        "state vars that collide with generated _next vars must fail closed"
    );
}

#[test]
fn test_k_transition_zero() {
    let ts = make_test_system();
    let unrolled = ts.k_transition(0);
    assert_eq!(unrolled, ChcExpr::Bool(true));
}

#[test]
fn test_k_transition_one() {
    let ts = make_test_system();
    let unrolled = ts.k_transition(1);

    // Should be: x_1 = x + 1
    // Variables in the formula
    let vars = unrolled.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(var_names.contains(&"x"));
    assert!(var_names.contains(&"x_1"));
}

#[test]
fn test_k_transition_multiple() {
    let ts = make_test_system();
    let unrolled = ts.k_transition(3);

    // Should contain variables at times 0, 1, 2, 3
    let vars = unrolled.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();
    assert!(var_names.contains(&"x"));
    assert!(var_names.contains(&"x_1"));
    assert!(var_names.contains(&"x_2"));
    assert!(var_names.contains(&"x_3"));
}

#[test]
fn test_transition_at_keeps_numeric_suffix_next_var_canonical() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_1 = ChcVar::new("x_1", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::eq(
            ChcExpr::var(x_1),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
        ChcExpr::Bool(false),
    );

    let transition = ts.transition_at(0);
    let var_names: FxHashSet<_> = transition.vars().into_iter().map(|v| v.name).collect();

    assert!(var_names.contains("x"));
    assert!(var_names.contains("x_1"));
    assert!(
        !var_names.contains("x_1__t0"),
        "numeric-suffix next-state var must not be renamed as a local: {transition:?}"
    );
}

#[test]
fn test_transition_at_versions_local_vars_per_timestep() {
    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::and_all([
            ChcExpr::eq(
                ChcExpr::var(x_next),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y.clone())),
            ),
            ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(0)),
        ]),
        ChcExpr::Bool(false),
    );

    let transition_0 = ts.transition_at(0);
    let vars_0: FxHashSet<_> = transition_0.vars().into_iter().map(|v| v.name).collect();
    assert!(vars_0.contains("y__t0"));
    assert!(!vars_0.contains("y"));

    let transition_1 = ts.transition_at(1);
    let vars_1: FxHashSet<_> = transition_1.vars().into_iter().map(|v| v.name).collect();
    assert!(vars_1.contains("y__t1"));
    assert!(!vars_1.contains("y"));

    let unrolled = ts.k_transition(2);
    let unrolled_vars: FxHashSet<_> = unrolled.vars().into_iter().map(|v| v.name).collect();
    assert!(unrolled_vars.contains("y__t0"));
    assert!(unrolled_vars.contains("y__t1"));
    assert!(!unrolled_vars.contains("y"));
}

#[test]
fn test_init_and_neg_init_version_local_vars_per_timestep() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::eq(
            ChcExpr::var(x),
            ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1)),
        ),
        ChcExpr::Bool(true),
        ChcExpr::Bool(false),
    );

    let init_0 = ts.init_at(0);
    let init_vars_0: FxHashSet<_> = init_0.vars().into_iter().map(|v| v.name).collect();
    assert!(init_vars_0.contains("y__i0"));
    assert!(!init_vars_0.contains("y"));

    let neg_init_2 = ts.neg_init_at(2);
    let neg_init_vars_2: FxHashSet<_> = neg_init_2.vars().into_iter().map(|v| v.name).collect();
    assert!(neg_init_vars_2.contains("y__ni2"));
    assert!(!neg_init_vars_2.contains("y"));
}

#[test]
fn test_query_and_neg_query_version_local_vars_per_timestep() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::and_all([
            ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0)),
            ChcExpr::gt(
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
                ChcExpr::int(5),
            ),
        ]),
    );

    let query_1 = ts.query_at(1);
    let query_vars_1: FxHashSet<_> = query_1.vars().into_iter().map(|v| v.name).collect();
    assert!(query_vars_1.contains("y__q1"));
    assert!(!query_vars_1.contains("y"));

    let neg_query_3 = ts.neg_query_at(3);
    let neg_query_vars_3: FxHashSet<_> = neg_query_3.vars().into_iter().map(|v| v.name).collect();
    assert!(neg_query_vars_3.contains("y__nq3"));
    assert!(!neg_query_vars_3.contains("y"));
}

#[test]
fn test_init_at() {
    let ts = make_test_system();

    // init at time 0: x = 0
    let init0 = ts.init_at(0);
    let vars = init0.vars();
    assert!(vars.iter().any(|v| v.name == "x"));

    // init at time 2: x_2 = 0
    let init2 = ts.init_at(2);
    let vars = init2.vars();
    assert!(vars.iter().any(|v| v.name == "x_2"));
}

#[test]
fn test_state_var_names() {
    let ts = make_test_system();
    let names = ts.state_var_names();
    assert!(names.contains("x"));
    assert_eq!(names.len(), 1);
}

#[test]
fn test_shift_versioned_state_vars() {
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // x_2 shifted by +1 should become x_3
    let x2 = ChcVar::new("x_2", ChcSort::Int);
    let expr = ChcExpr::var(x2);
    let shifted = ts.shift_versioned_state_vars(&expr, 1);
    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x_3"));

    // x shifted by +1 should become x_1
    let expr = ChcExpr::var(x);
    let shifted = ts.shift_versioned_state_vars(&expr, 1);
    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x_1"));

    // x shifted by -1 should stay x (clamped at 0)
    let shifted = ts.shift_versioned_state_vars(&expr, -1);
    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x"));
}

#[test]
fn test_rename_state_vars_at_time1_to_time2() {
    // TPA "shift_only_next": v1 → v2, keep v0 fixed
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // Expression with all three time versions: x + x_1 + x_2
    let x0 = ChcVar::new("x", ChcSort::Int);
    let x1 = ChcVar::new("x_1", ChcSort::Int);
    let x2 = ChcVar::new("x_2", ChcSort::Int);
    let expr = ChcExpr::add(
        ChcExpr::add(ChcExpr::var(x0), ChcExpr::var(x1)),
        ChcExpr::var(x2),
    );

    // rename_state_vars_at(1, 2): x_1 → x_2, but x and x_2 unchanged
    let shifted = ts.rename_state_vars_at(&expr, 1, 2);
    let vars = shifted.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();

    // x should remain (time 0 unchanged)
    assert!(var_names.contains(&"x"), "time-0 var should be unchanged");
    // x_1 should become x_2
    assert!(!var_names.contains(&"x_1"), "x_1 should have been renamed");
    // x_2 appears (both original x_2 and renamed x_1)
    assert!(var_names.contains(&"x_2"), "should contain x_2");
}

#[test]
fn test_rename_state_vars_at_time2_to_time1() {
    // TPA "clean_interpolant": v2 → v1
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // Expression with time-2 vars: x_2 >= 0
    let x2 = ChcVar::new("x_2", ChcSort::Int);
    let expr = ChcExpr::ge(ChcExpr::var(x2), ChcExpr::int(0));

    // rename_state_vars_at(2, 1): x_2 → x_1
    let shifted = ts.rename_state_vars_at(&expr, 2, 1);
    let vars = shifted.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();

    assert!(!var_names.contains(&"x_2"), "x_2 should have been renamed");
    assert!(var_names.contains(&"x_1"), "should now contain x_1");
}

#[test]
fn test_rename_state_vars_at_same_timestep() {
    // Noop case: rename_state_vars_at(1, 1) should return identical expression
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    let x1 = ChcVar::new("x_1", ChcSort::Int);
    let expr = ChcExpr::var(x1);
    let shifted = ts.rename_state_vars_at(&expr, 1, 1);

    let vars = shifted.vars();
    assert!(vars.iter().any(|v| v.name == "x_1"), "should be unchanged");
}

#[test]
fn test_rename_state_vars_at_time0_to_time1() {
    // Can also shift time-0 to time-1 if needed
    let x = ChcVar::new("x", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x.clone()],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // x >= 0 (time-0)
    let expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));

    // rename_state_vars_at(0, 1): x → x_1
    let shifted = ts.rename_state_vars_at(&expr, 0, 1);
    let vars = shifted.vars();

    assert!(
        !vars.iter().any(|v| v.name == "x"),
        "x should have been renamed"
    );
    assert!(
        vars.iter().any(|v| v.name == "x_1"),
        "should now contain x_1"
    );
}

#[test]
fn test_rename_state_vars_at_multiple_vars() {
    // Test with multiple state variables
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let ts = TransitionSystem::new(
        PredicateId(0),
        vec![x, y],
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
        ChcExpr::Bool(true),
    );

    // x_1 + y_1 = 0
    let x1 = ChcVar::new("x_1", ChcSort::Int);
    let y1 = ChcVar::new("y_1", ChcSort::Int);
    let expr = ChcExpr::eq(
        ChcExpr::add(ChcExpr::var(x1), ChcExpr::var(y1)),
        ChcExpr::int(0),
    );

    // rename_state_vars_at(1, 2): x_1 → x_2, y_1 → y_2
    let shifted = ts.rename_state_vars_at(&expr, 1, 2);
    let vars = shifted.vars();
    let var_names: Vec<_> = vars.iter().map(|v| v.name.as_str()).collect();

    assert!(!var_names.contains(&"x_1"), "x_1 should be renamed");
    assert!(!var_names.contains(&"y_1"), "y_1 should be renamed");
    assert!(var_names.contains(&"x_2"), "should contain x_2");
    assert!(var_names.contains(&"y_2"), "should contain y_2");
}

#[test]
fn test_extract_transition_with_expression_body_args() {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);

    // Init: Inv(0, 1)
    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0), ChcExpr::int(1)],
    ));

    let x = ChcVar::new("x", ChcSort::Int);

    // Trans: Inv(x, x + 1) => Inv(x + 1, x + 2)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![
                ChcExpr::var(x.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(2)),
            ],
        ),
    ));

    // Query: Inv(0, 1) => false
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::int(0), ChcExpr::int(1)],
    )])));

    let ts = TransitionSystem::from_chc_problem(&problem).unwrap();

    // Transition should use canonical vars (v0, v1, v0_next, v1_next), not user var `x`.
    let trans_vars = ts.transition.vars();
    let var_names: Vec<_> = trans_vars.iter().map(|v| v.name.as_str()).collect();
    assert!(
        !var_names.contains(&"x"),
        "transition should not contain user var 'x': {:?}",
        ts.transition
    );
}

#[test]
fn test_extract_transition_adds_equality_for_shared_body_and_head_var_issue_4729() {
    let problem = make_shared_body_head_var_problem_issue_4729();
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("single-predicate linear problem should extract");
    let current_f = ChcVar::new("v2", ChcSort::Int);
    let next_f = ChcVar::new("v2_next", ChcSort::Int);

    assert!(
        contains_var_equality(&ts.transition, &next_f, &current_f),
        "transition must constrain shared arg with v2_next = v2; got {:?}",
        ts.transition
    );
}

#[test]
fn test_vmt_style_bool_control_extraction_preserves_guarded_update() {
    let (problem, _) = make_vmt_style_bool_control_problem();
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("minimized VMT-style Bool-control problem should extract");

    assert_eq!(
        ts.vars.iter().map(|var| &var.sort).collect::<Vec<_>>(),
        vec![&ChcSort::Int, &ChcSort::Bool]
    );
    assert!(
        contains_ite(&ts.transition),
        "Bool-controlled arithmetic update should remain visible in transition: {:?}",
        ts.transition
    );

    let transition_vars: FxHashSet<_> = ts
        .transition
        .vars()
        .into_iter()
        .map(|var| var.name)
        .collect();
    for expected in ["v0", "v1", "v0_next", "v1_next"] {
        assert!(
            transition_vars.contains(expected),
            "transition should preserve canonical state var {expected}; got {transition_vars:?}"
        );
    }
}

#[test]
fn test_vmt_style_bool_control_manual_invariant_validates_on_original_chc() {
    let (problem, inv) = make_vmt_style_bool_control_problem();
    let vars = canonical_vars_for_pred(&problem, inv).expect("Inv canonical vars");
    let mut model = InvariantModel::new();
    model.set(
        inv,
        PredicateInterpretation::new(
            vars.clone(),
            ChcExpr::ge(ChcExpr::var(vars[0].clone()), ChcExpr::int(0)),
        ),
    );

    let valid = engines::validate_external_invariant_model(&problem, &model, &PdrConfig::default())
        .expect("original CHC model validation should not error");
    assert!(
        valid,
        "manual Bool-control invariant must validate against the original CHC"
    );
}

fn make_shared_body_head_var_problem_issue_4729() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate(
        "inv",
        vec![ChcSort::Int, ChcSort::Int, ChcSort::Int, ChcSort::Int],
    );
    let zeros = vec![ChcExpr::int(0); 4];

    problem.add_clause(HornClause::fact(ChcExpr::Bool(true), inv, zeros.clone()));

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    let f = ChcVar::new("F", ChcSort::Int);
    let g = ChcVar::new("G", ChcSort::Int);

    // F appears in both body arg 2 and head arg 2. Without the #4729 fix,
    // body substitution consumes F first and head substitution becomes a no-op.
    let transition_constraint = ChcExpr::and_all([
        ChcExpr::eq(
            ChcExpr::var(d.clone()),
            ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(e.clone()),
            ChcExpr::add(ChcExpr::var(c.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(g.clone()),
            ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::var(f.clone())),
        ),
    ]);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![
                    ChcExpr::var(b),
                    ChcExpr::var(c),
                    ChcExpr::var(f.clone()),
                    ChcExpr::var(a),
                ],
            )],
            Some(transition_constraint),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::var(d),
                ChcExpr::var(e),
                ChcExpr::var(f),
                ChcExpr::var(g),
            ],
        ),
    ));

    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv, zeros,
    )])));

    problem
}

#[test]
fn test_from_chc_problem_high_arity_constraints_flat_and_drop_safe() {
    // #2508: high-arity argument lists must build flat n-ary conjunctions.
    // If this regresses to chained binary And nodes, dropping these formulas can overflow.
    const ARITY: usize = 4_096;

    let problem = make_high_arity_linear_problem(ARITY);
    let ts = TransitionSystem::from_chc_problem(&problem)
        .expect("high-arity linear problem should extract");

    assert_flat_and_arity(&ts.init, ARITY, "init");
    assert_flat_and_arity(&ts.transition, ARITY * 2, "transition");
    assert_flat_and_arity(&ts.query, ARITY, "query");

    // Exercise normal recursive ownership teardown without leak workarounds.
    drop(ts);
}

#[test]
fn tla2_transition_cluster_extraction_is_stable_and_solver_program_shaped() {
    let problem = make_tla2_action_cluster_problem();
    let epochs = tla2_cluster_epochs();
    let guards = Tla2TransitionClusterGuardMetadata::conservative();

    let first = TransitionSystem::tla2_transition_cluster_requests(&problem, epochs, guards)
        .expect("TLA2 action clusters should extract");
    let second = TransitionSystem::tla2_transition_cluster_requests(&problem, epochs, guards)
        .expect("TLA2 action clusters should extract deterministically");

    assert_eq!(first, second);
    assert_eq!(first.len(), 2);

    let inc = &first[0];
    let stutter = &first[1];
    assert_eq!(inc.cluster.action_name, "Inc");
    assert_eq!(stutter.cluster.action_name, "Stutter");
    assert_eq!(inc.cluster.clauses.len(), 1);
    assert_eq!(stutter.cluster.clauses.len(), 1);
    assert_eq!(inc.cluster.clauses[0].clause_index, 2);
    assert_eq!(inc.cluster.clauses[0].transition_ordinal, 1);
    assert_eq!(stutter.cluster.clauses[0].clause_index, 1);
    assert_eq!(stutter.cluster.clauses[0].transition_ordinal, 0);

    assert_eq!(inc.cluster.state_vars.len(), 2);
    assert_eq!(inc.cluster.state_vars[0].name, "v0");
    assert_eq!(
        inc.cluster.state_vars[0].sort,
        Tla2TransitionScalarSort::Int
    );
    assert_eq!(inc.cluster.state_vars[1].name, "v1");
    assert_eq!(
        inc.cluster.state_vars[1].sort,
        Tla2TransitionScalarSort::Bool
    );

    let descriptor = &inc.solver_program;
    assert!(inc.is_metadata_only());
    assert_eq!(
        descriptor.kind,
        Tla2SolverProgramKind::Tla2TransitionCluster
    );
    assert_eq!(
        descriptor.backend,
        Tla2SolverProgramBackend::ExternalCodegenBackend
    );
    assert!(descriptor.requires_external_codegen_backend_only());
    assert_eq!(
        descriptor.compile_timing,
        Tla2TransitionClusterCompileTiming::BackgroundOnly
    );
    assert_eq!(
        descriptor.stats_prefix,
        TLA2_TRANSITION_CLUSTER_STATS_PREFIX
    );
    assert_eq!(
        inc.profile_key.stats_prefix(),
        TLA2_TRANSITION_CLUSTER_STATS_PREFIX
    );
    assert_eq!(descriptor.guards, guards);
    assert!(descriptor.guards.satisfies_conservative_contract());
    assert_eq!(descriptor.invalidation_key.epochs, epochs);
    assert!(descriptor
        .invalidation_key
        .is_valid_for(descriptor.invalidation_key));
    assert_eq!(
        descriptor.semantic_version,
        descriptor.invalidation_key.semantic_hash
    );
    assert_eq!(
        inc.profile_key.shape_hash,
        descriptor.invalidation_key.shape_hash
    );
    assert_eq!(
        inc.profile_key.semantic_hash,
        descriptor.invalidation_key.semantic_hash
    );
    assert_ne!(
        inc.profile_key.stable_hash(),
        stutter.profile_key.stable_hash()
    );
}

#[test]
fn tla2_transition_cluster_guards_fail_closed_on_non_conservative_caps() {
    let problem = make_tla2_action_cluster_problem();
    let epochs = tla2_cluster_epochs();

    let mut stricter_guards = Tla2TransitionClusterGuardMetadata::conservative();
    stricter_guards.max_cluster_clauses = 1;
    assert!(stricter_guards.satisfies_conservative_contract());
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&problem, epochs, stricter_guards)
            .expect("stricter per-cluster cap should remain useful")
            .len(),
        2
    );

    let mut relaxed_clause_cap = Tla2TransitionClusterGuardMetadata::conservative();
    relaxed_clause_cap.max_cluster_clauses =
        relaxed_clause_cap.max_cluster_clauses.saturating_add(1);
    assert!(!relaxed_clause_cap.satisfies_conservative_contract());
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&problem, epochs, relaxed_clause_cap),
        Err(Tla2TransitionClusterRejection::GuardLimitOutOfRange {
            max_cluster_clauses: relaxed_clause_cap.max_cluster_clauses,
            max_expr_nodes: relaxed_clause_cap.max_expr_nodes,
        })
    );

    let mut relaxed_expr_cap = Tla2TransitionClusterGuardMetadata::conservative();
    relaxed_expr_cap.max_expr_nodes = relaxed_expr_cap.max_expr_nodes.saturating_add(1);
    assert!(!relaxed_expr_cap.satisfies_conservative_contract());
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&problem, epochs, relaxed_expr_cap),
        Err(Tla2TransitionClusterRejection::GuardLimitOutOfRange {
            max_cluster_clauses: relaxed_expr_cap.max_cluster_clauses,
            max_expr_nodes: relaxed_expr_cap.max_expr_nodes,
        })
    );

    let mut zero_cap = Tla2TransitionClusterGuardMetadata::conservative();
    zero_cap.max_expr_nodes = 0;
    assert!(!zero_cap.satisfies_conservative_contract());
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&problem, epochs, zero_cap),
        Err(Tla2TransitionClusterRejection::GuardLimitOutOfRange {
            max_cluster_clauses: zero_cap.max_cluster_clauses,
            max_expr_nodes: zero_cap.max_expr_nodes,
        })
    );
}

#[test]
fn tla2_transition_cluster_extraction_fails_closed_for_unsupported_cases() {
    let epochs = tla2_cluster_epochs();
    let guards = Tla2TransitionClusterGuardMetadata::conservative();

    let mut missing_actions = ChcProblem::new();
    let inv = missing_actions.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    missing_actions.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0)],
    ));
    missing_actions.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    missing_actions.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::var(x)],
    )])));
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&missing_actions, epochs, guards),
        Err(Tla2TransitionClusterRejection::MissingActionDecomposition)
    );

    let mut untagged = ChcProblem::new();
    let inv = untagged.declare_predicate("Inv", vec![ChcSort::Int]);
    let _action = untagged.declare_action("Step");
    let x = ChcVar::new("x", ChcSort::Int);
    untagged.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0)],
    ));
    untagged.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    untagged.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::var(x)],
    )])));
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&untagged, epochs, guards),
        Err(Tla2TransitionClusterRejection::UntaggedTransition { clause_index: 1 })
    );

    let mut unsupported_sort = ChcProblem::new();
    let inv = unsupported_sort.declare_predicate("Inv", vec![ChcSort::Real]);
    let step = unsupported_sort.declare_action("Step");
    let r = ChcVar::new("r", ChcSort::Real);
    unsupported_sort.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::Real(0, 1)],
    ));
    unsupported_sort.add_clause_with_action(
        HornClause::new(
            ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(r.clone())])]),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(r)]),
        ),
        step,
    );
    unsupported_sort.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::Real(1, 1)],
    )])));
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&unsupported_sort, epochs, guards),
        Err(Tla2TransitionClusterRejection::UnsupportedStateSort {
            var_name: "v0".to_string(),
            sort: ChcSort::Real,
        })
    );

    let mut unsupported_expr = ChcProblem::new();
    let inv = unsupported_expr.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Bool]);
    let step = unsupported_expr.declare_action("Step");
    let x = ChcVar::new("x", ChcSort::Int);
    let ok = ChcVar::new("ok", ChcSort::Bool);
    unsupported_expr.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0), ChcExpr::Bool(true)],
    ));
    unsupported_expr.add_clause_with_action(
        HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::and(
                    ChcExpr::var(ok.clone()),
                    ChcExpr::eq(
                        ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                        ChcExpr::var(x.clone()),
                    ),
                )),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())]),
        ),
        step,
    );
    unsupported_expr.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::var(x), ChcExpr::var(ok)],
    )])));
    assert_eq!(
        TransitionSystem::tla2_transition_cluster_requests(&unsupported_expr, epochs, guards),
        Err(Tla2TransitionClusterRejection::UnsupportedExpression {
            clause_index: 1,
            reason: Tla2TransitionClusterExpressionRejection::UnsupportedOperator,
        })
    );
}

/// Rank-3 frame folding (gap-attribution): constant + alias chains collapse,
/// bindings are re-conjoined so the result stays EQUIVALENT to the input.
#[test]
fn test_fold_frame_constants_and_aliases_equivalence_shape() {
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let z = ChcExpr::var(ChcVar::new("z", ChcSort::Int));
    // (x = 0) ∧ (y = x) ∧ (z > y)
    let formula = ChcExpr::and_all([
        ChcExpr::eq(x.clone(), ChcExpr::Int(0)),
        ChcExpr::eq(y.clone(), x.clone()),
        ChcExpr::gt(z.clone(), y.clone()),
    ]);
    let folded = TransitionSystem::fold_frame_constants_and_aliases(&formula);

    // The comparison must now be against the constant: z > 0 appears.
    let folded_str = format!("{folded:?}");
    assert!(
        folded_str.contains("Gt") && folded_str.contains("Int(0)"),
        "z>y should fold to z>0: {folded_str}"
    );
    // Equivalence: bindings for x and y are re-conjoined (x = 0 and y = 0/x).
    let vars: Vec<String> = folded.vars().iter().map(|v| v.name.clone()).collect();
    assert!(
        vars.contains(&"x".to_string()) && vars.contains(&"y".to_string()),
        "bindings must keep substituted vars in the formula (equivalence): {vars:?}"
    );
    // A contradictory class still reduces to false via substituted equalities.
    let contra = ChcExpr::and_all([
        ChcExpr::eq(x.clone(), ChcExpr::Int(0)),
        ChcExpr::eq(x.clone(), ChcExpr::Int(1)),
    ]);
    let folded_contra =
        TransitionSystem::fold_frame_constants_and_aliases(&contra).simplify_constants();
    let s = format!("{folded_contra:?}");
    assert!(
        s.contains("Bool(false)"),
        "x=0 ∧ x=1 must fold to false: {s}"
    );
}

/// Gap-attribution isolation pin (task #27): run the exact base, depth-one,
/// and induction-step checks on a deterministic built-in transition system,
/// and round-trip their standalone SMT-LIB exports in a temporary directory.
/// External exports live in an explicitly bounded example.
#[test]
fn gap_attr_k1_check_isolation_round_trips() {
    fn sort_str(s: &ChcSort) -> &'static str {
        match s {
            ChcSort::Bool => "Bool",
            ChcSort::Int => "Int",
            ChcSort::Real => "Real",
            other => panic!("unexpected sort in diag: {other:?}"),
        }
    }

    fn isolate_checks(
        ts: &TransitionSystem,
        output_dir: &std::path::Path,
        assert_builtin_verdicts: bool,
    ) {
        let checks: Vec<(&str, ChcExpr, bool)> = vec![
            (
                "base_init_bad",
                ChcExpr::and_all([ts.init_at(0), ts.query_at(0)]),
                false,
            ),
            (
                "bmc_k1",
                ChcExpr::and_all([ts.init_at(0), ts.transition_at(0), ts.query_at(1)]),
                false,
            ),
            (
                "indstep_k1",
                ChcExpr::and_all([ts.neg_query_at(0), ts.transition_at(0), ts.query_at(1)]),
                true,
            ),
        ];

        for (name, formula, expect_sat) in &checks {
            let mut ctx = crate::smt::SmtContext::new();
            let result = ctx.check_sat_with_executor_fallback_timeout(
                formula,
                std::time::Duration::from_secs(10),
            );
            if assert_builtin_verdicts {
                assert!(
                    if *expect_sat {
                        result.is_sat()
                    } else {
                        result.is_unsat()
                    },
                    "{name} returned an unexpected built-in verdict: {result:?}"
                );
            }

            let mut script = String::from("(set-logic QF_LIA)\n");
            let mut seen = std::collections::BTreeSet::new();
            for v in formula.vars() {
                if seen.insert(v.name.clone()) {
                    script.push_str(&format!(
                        "(declare-const |{}| {})\n",
                        v.name,
                        sort_str(&v.sort)
                    ));
                }
            }
            for conj in formula.conjuncts() {
                script.push_str(&format!(
                    "(assert {})\n",
                    crate::InvariantModel::expr_to_smtlib(conj)
                ));
            }
            script.push_str("(check-sat)\n");
            let out = output_dir.join(format!("diag_syn2_{name}.smt2"));
            std::fs::write(&out, &script).expect("write isolated check");
            assert_eq!(
                std::fs::read_to_string(&out).expect("read isolated check"),
                script,
                "SMT-LIB export must round-trip byte-for-byte"
            );
        }
    }

    let builtin_dir = tempfile::tempdir().expect("temporary diagnostic directory");
    isolate_checks(&make_test_system(), builtin_dir.path(), true);
}
