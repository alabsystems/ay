// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::classifier::{ProblemClass, ProblemClassifier};
use crate::engine_result::ValidationEvidence;
use crate::pdr::{
    Counterexample, CounterexampleStep, InvariantModel, PdrConfig, PdrResult,
    PredicateInterpretation,
};
use crate::portfolio::{EngineConfig, PortfolioResult, PreprocessSummary};
use crate::ChcParser;
use crate::{
    BmcSolver, ChcDtConstructor, ChcDtSelector, ChcExpr, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, VerifiedChcResult,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use ay_test_support::env::{lock_env, ScopedEnvVar};
use ntest::timeout;
use std::time::Duration;

// The one workspace env choke point: serialized, restore-on-exit env mutation
// (unifies the former ghost_pair_env_lock onto it).
fn create_simple_loop() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    // x = 0 => Inv(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));

    // Inv(x) /\ x < 5 => Inv(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Inv(x) /\ x > 5 => false (safe: x never exceeds 5)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_identity_simple_loop(arg_sort: ChcSort) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![arg_sort.clone()]);
    let x = ChcVar::new("x", arg_sort);

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

    problem
}

fn create_const_key_array_cegar_safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let inv = problem.declare_predicate("Inv", vec![arr_sort.clone()]);
    let array = ChcVar::new("a", arr_sort);
    let idx = ChcVar::new("i", ChcSort::Int);
    let key_three_is_42 = ChcExpr::eq(
        ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::Int(3)),
        ChcExpr::Int(42),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(key_three_is_42.clone()),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(array.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(array.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::var(idx.clone())),
                ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::var(idx)),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(array.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(array)])],
            Some(ChcExpr::not(key_three_is_42)),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_reducible_lia_array_chain() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let predicates: Vec<_> = (0..REDUCED_LIA_ARRAY_ROUTE_MIN_ORIGINAL_PREDICATES)
        .map(|index| problem.declare_predicate(format!("P{index}"), vec![array_sort.clone()]))
        .collect();
    let array = ChcVar::new("a", array_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(predicates[0], vec![ChcExpr::var(array.clone())]),
    ));
    for pair in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(pair[0], vec![ChcExpr::var(array.clone())])]),
            ClauseHead::Predicate(pair[1], vec![ChcExpr::var(array.clone())]),
        ));
    }
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                *predicates.last().expect("nonempty predicate chain"),
                vec![ChcExpr::var(array.clone())],
            )],
            Some(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::int(0)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::Predicate(
            *predicates.last().expect("nonempty predicate chain"),
            vec![ChcExpr::store(
                ChcExpr::var(array.clone()),
                ChcExpr::int(1),
                ChcExpr::select(ChcExpr::var(array.clone()), ChcExpr::int(0)),
            )],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                *predicates.last().expect("nonempty predicate chain"),
                vec![ChcExpr::var(array.clone())],
            )],
            Some(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(array), ChcExpr::int(0)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::False,
    ));
    problem
}

/// Reducible array-carrying wrapper graph around a scalar bounded loop.
///
/// The direct all-true model cannot prove the Safe variant because `x >= 7`
/// is satisfiable without the loop invariant. The verified interval candidate
/// `0 <= x <= 6` makes it infeasible after preprocessing. Setting
/// `reachable_query` instead asks for reachable `x = 3`, pinning fail-closed
/// behavior for the same transform and routing shape.
fn create_reducible_interval_lia_array_problem(reachable_query: bool) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let predicates: Vec<_> = (0..REDUCED_LIA_ARRAY_ROUTE_MIN_ORIGINAL_PREDICATES)
        .map(|index| {
            problem.declare_predicate(
                format!("IntervalWrapper{index}"),
                vec![array_sort.clone(), ChcSort::Int],
            )
        })
        .collect();
    let array = ChcVar::new("interval_array", array_sort);
    let x = ChcVar::new("interval_x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            predicates[0],
            vec![ChcExpr::var(array.clone()), ChcExpr::int(0)],
        ),
    ));
    for pair in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(
                pair[0],
                vec![ChcExpr::var(array.clone()), ChcExpr::var(x.clone())],
            )]),
            ClauseHead::Predicate(
                pair[1],
                vec![ChcExpr::var(array.clone()), ChcExpr::var(x.clone())],
            ),
        ));
    }
    let loop_predicate = *predicates.last().expect("nonempty predicate chain");
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                loop_predicate,
                vec![ChcExpr::var(array.clone()), ChcExpr::var(x.clone())],
            )],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(6))),
        ),
        ClauseHead::Predicate(
            loop_predicate,
            vec![
                ChcExpr::var(array.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ],
        ),
    ));
    let query = if reachable_query {
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(3))
    } else {
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(7))
    };
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(loop_predicate, vec![ChcExpr::var(array), ChcExpr::var(x)])],
        Some(query),
    )));
    problem
}

fn create_reducible_queryless_lia_array_chain() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let predicates: Vec<_> = (0..REDUCED_LIA_ARRAY_ROUTE_MIN_ORIGINAL_PREDICATES)
        .map(|index| problem.declare_predicate(format!("Reach{index}"), vec![array_sort.clone()]))
        .collect();
    let dead = problem.declare_predicate("Dead", vec![array_sort.clone()]);
    let array = ChcVar::new("a", array_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(predicates[0], vec![ChcExpr::var(array.clone())]),
    ));
    for pair in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(pair[0], vec![ChcExpr::var(array.clone())])]),
            ClauseHead::Predicate(pair[1], vec![ChcExpr::var(array.clone())]),
        ));
    }
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        dead,
        vec![ChcExpr::var(array)],
    )])));
    problem
}

fn create_array_argument_constant_safe_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let p = problem.declare_predicate("P", vec![ChcSort::Int, arr_sort.clone()]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, arr_sort.clone()]);
    let x = ChcVar::new("x", ChcSort::Int);
    let a = ChcVar::new("a", arr_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::Int(0), ChcExpr::var(a.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(a.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::Int(0))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(a.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone()), ChcExpr::var(a)])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::Int(1))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_deterministic_bv_bool_unsafe_loop() -> ChcProblem {
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
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())],
        )]),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::Op(
                    crate::ChcOp::BvAdd,
                    vec![
                        std::sync::Arc::new(ChcExpr::var(x.clone())),
                        std::sync::Arc::new(ChcExpr::BitVec(1, 8)),
                    ],
                ),
                ChcExpr::var(ok.clone()),
            ],
        ),
    ));

    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok)])],
        Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(2, 8))),
    )));

    problem
}

fn create_bv_bool_control_safe_loop() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Bool, ChcSort::BitVec(8)]);
    let pc = ChcVar::new("pc", ChcSort::Bool);
    let x = ChcVar::new("x", ChcSort::BitVec(8));

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::not(ChcExpr::var(pc.clone()))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(pc.clone()), ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            inv,
            vec![ChcExpr::var(pc.clone()), ChcExpr::var(x.clone())],
        )]),
        ClauseHead::Predicate(inv, vec![ChcExpr::Bool(false), ChcExpr::var(x.clone())]),
    ));

    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(inv, vec![ChcExpr::var(pc.clone()), ChcExpr::var(x)])],
        Some(ChcExpr::var(pc)),
    )));

    problem
}

#[test]
fn test_complex_query_only_unsat_fact_validated_safe_8865_w10() {
    // #8865 demoted this shape (query-only, syntactically unreachable, BV
    // signature) to Unknown because the empty-model acyclic proof was not
    // proof-grade. The w10 front-end fix upgrades it to a PROPERLY VALIDATED
    // Safe: constant interpretations (false for query-feeding predicates) are
    // materialized and fully verified against the original clauses. The
    // fail-closed Unknown remains the fallback when validation cannot pass.
    let smt = r#"
(set-logic HORN)
(declare-rel P ((_ BitVec 32)))
(rule (=> false (P #x00000000)))
(query P)
"#;
    let problem = ChcParser::parse(smt).expect("fixture parses");
    assert!(problem.has_bv_sorts());
    assert_eq!(problem.facts().count(), 0);
    assert_eq!(problem.transitions().count(), 0);
    assert_eq!(problem.queries().count(), 1);
    assert!(problem.has_complex_query_only_vacuous_safety_shape());

    let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default());
    let result = adaptive.solve();
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "syntactically unreachable query-only problem must be validated Safe, got {result:?}"
    );

    let budget_adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let (budget_result, budget_report) = budget_adaptive.solve_with_budget_report();
    assert!(
        matches!(budget_result, VerifiedChcResult::Safe(_)),
        "budget-report path must return the validated Safe, got {budget_result:?}"
    );
    assert!(
        budget_report.entries.is_empty(),
        "guarded budget-report path must not run a portfolio engine"
    );

    let expanded_smt = r#"
(set-logic HORN)
(declare-rel State ((_ BitVec 32)))
(declare-rel error ())
(rule (=> false error))
(query error)
"#;
    let mut expanded = ChcParser::parse(expanded_smt).expect("expanded fixture parses");
    assert!(
        !expanded.expand_nullary_fail_queries(false),
        "false-body nullary-error rule is pruned before expansion"
    );
    assert_eq!(expanded.facts().count(), 0);
    assert_eq!(expanded.transitions().count(), 0);
    assert_eq!(expanded.queries().count(), 1);
    assert!(expanded.has_complex_query_only_vacuous_safety_shape());

    let expanded_adaptive = AdaptivePortfolio::new(expanded, AdaptiveConfig::test_default());
    let (expanded_result, expanded_report) = expanded_adaptive.solve_with_budget_report();
    assert!(
        matches!(expanded_result, VerifiedChcResult::Safe(_)),
        "expanded nullary-error query must be validated Safe, got {expanded_result:?}"
    );
    assert!(
        expanded_report.entries.is_empty(),
        "expanded nullary-error guard must not run a portfolio engine"
    );
}

#[test]
fn test_false_bodied_query_vc_shape_validated_safe_w10() {
    // Reduced model-checker-consumer VC shape (task25): datatype declarations, many
    // query-less relations, and a single `(rule (=> false error))` +
    // `(query error)`. The false-bodied rule is pruned at ingest, leaving the
    // nullary query predicate with no defining clauses — trivially Safe. The
    // front end must return a validated Safe (was: Unknown in 7ms via the
    // #8865 fail-closed guard).
    let smt = r#"
(set-logic HORN)
(declare-datatype Option_bv64 ((None_Option_bv64) (Some_Option_bv64 (value_Option_bv64 (_ BitVec 64)))))
(declare-rel bb0 ((_ BitVec 64) Bool))
(declare-rel bb1 ((_ BitVec 64) (_ BitVec 64)))
(declare-rel error ())
(declare-rel error_p4 ())
(rule (=> false error))
(query error)
"#;
    let problem = ChcParser::parse(smt).expect("fixture parses");
    assert_eq!(problem.facts().count(), 0);
    assert_eq!(problem.transitions().count(), 0);
    assert_eq!(problem.queries().count(), 1);
    assert!(problem.has_complex_query_only_vacuous_safety_shape());

    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let result = adaptive.solve();
    let VerifiedChcResult::Safe(inv) = &result else {
        panic!("false-bodied-query VC must be validated Safe, got {result:?}");
    };
    // The certificate must be total over the declared signature (unreferenced
    // relations get constant-false interpretations).
    assert!(
        !inv.model().is_empty(),
        "validated Safe must carry a non-empty invariant model"
    );
}

#[test]
fn test_false_bodied_query_reachable_error_control_stays_unsafe_w10() {
    // Control for the w10 trivial-Safe front end: a query whose predicate IS
    // reachable (satisfiable fact body) must remain Unsafe — the vacuous-Safe
    // path must never fire for it. The false-bodied rule for `dead` is pruned
    // at ingest, but `P` keeps its satisfiable fact, so the guard shape does
    // not hold and the normal engines find the counterexample.
    let smt = r#"
(set-logic HORN)
(declare-var x (_ BitVec 32))
(declare-rel P ((_ BitVec 32)))
(declare-rel dead ())
(rule (=> false dead))
(rule (=> (= x #x00000001) (P x)))
(query P)
"#;
    let problem = ChcParser::parse(smt).expect("fixture parses");
    assert!(
        !problem.has_complex_query_only_vacuous_safety_shape(),
        "reachable-query control must not match the vacuous-safety shape"
    );

    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let result = adaptive.solve();
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "reachable error must stay Unsafe, got {result:?}"
    );
}

fn create_unsafe_simple_loop() -> ChcProblem {
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

    // Inv(x) /\ x >= 5 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(5))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn solidity_route_balance_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "Balance".to_string(),
        constructors: std::sync::Arc::new(vec![ChcDtConstructor {
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

fn solidity_route_state_sort(balance_sort: ChcSort) -> ChcSort {
    ChcSort::Datatype {
        name: "State".to_string(),
        constructors: std::sync::Arc::new(vec![ChcDtConstructor {
            name: "mkState".to_string(),
            selectors: vec![ChcDtSelector {
                name: "balances".to_string(),
                sort: ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(balance_sort)),
            }],
        }]),
    }
}

fn create_solidity_array_dt_route_problem(make_unsafe: bool) -> ChcProblem {
    let balance_sort = solidity_route_balance_sort();
    let state_sort = solidity_route_state_sort(balance_sort.clone());
    let state_var = ChcVar::new("s", state_sort.clone());

    let mut problem = ChcProblem::new();
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
    let inv = problem.declare_predicate("Inv", vec![state_sort]);

    if make_unsafe {
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(state_var.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(inv, vec![ChcExpr::var(state_var)])]),
            ClauseHead::False,
        ));
    } else {
        let balances = ChcExpr::FuncApp(
            "balances".to_string(),
            ChcSort::Array(
                Box::new(ChcSort::BitVec(160)),
                Box::new(solidity_route_balance_sort()),
            ),
            vec![std::sync::Arc::new(ChcExpr::var(state_var.clone()))],
        );
        let selected_balance = ChcExpr::FuncApp(
            "balance".to_string(),
            ChcSort::BitVec(256),
            vec![std::sync::Arc::new(ChcExpr::select(
                balances,
                ChcExpr::BitVec(4, 160),
            ))],
        );
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
    }

    problem
}

fn create_tla_action_cluster_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Bool]);
    let step = problem.declare_action("Step");
    let x = ChcVar::new("x", ChcSort::Int);
    let ok = ChcVar::new("ok", ChcSort::Bool);

    problem.add_clause(HornClause::fact(
        ChcExpr::Bool(true),
        inv,
        vec![ChcExpr::int(0), ChcExpr::Bool(true)],
    ));
    problem.add_clause_with_action(
        HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(ok.clone())])],
                Some(ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(x.clone()),
                        ChcExpr::sub(ChcExpr::var(x.clone()), ChcExpr::int(-1)),
                    ),
                    ChcExpr::var(ok.clone()),
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
        step,
    );
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        inv,
        vec![ChcExpr::var(x), ChcExpr::var(ok)],
    )])));

    problem
}

fn create_acyclic_model_checker_consumer_array_bv_chain() -> ChcProblem {
    parse_benchmark(
        r#"
(set-logic HORN)
(declare-fun bb0 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb1 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb2 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb3 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)
(declare-fun bb4 ((Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32)) (Array (_ BitVec 64) (_ BitVec 8)) (_ BitVec 64)) Bool)

; Entry: object 1 is valid, has size 4, and address 8 stores 0x42.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000001 true))
        (= os (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000001 #x00000004))
        (= addr #x0000000000000008)
        (= m (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) addr #x42))
      )
      (bb0 ov os m addr)
    )
  )
)

; Acyclic basic-block chain: bb0 -> bb1 -> bb2 -> bb3 -> bb4.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and (bb0 ov os m addr) (select ov #x00000001))
      (bb1 ov os m addr)
    )
  )
)

(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb1 ov os m addr)
        (= (select os #x00000001) #x00000004)
      )
      (bb2 ov os m addr)
    )
  )
)

(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb2 ov os m addr)
        (= addr #x0000000000000008)
      )
      (bb3 ov os m addr)
    )
  )
)

(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb3 ov os m addr)
        (= (select m addr) #x42)
      )
      (bb4 ov os m addr)
    )
  )
)

; Safety query: all invariants established above must hold at bb4.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (bb4 ov os m addr)
        (or
          (not (select ov #x00000001))
          (not (= (select os #x00000001) #x00000004))
          (not (= addr #x0000000000000008))
          (not (= (select m addr) #x42))
        )
      )
      false
    )
  )
)

(check-sat)
"#,
        "acyclic_model_checker_consumer_array_bv_chain",
    )
}

fn create_acyclic_int_unsafe_chain_8663() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p0 = problem.declare_predicate("P0", vec![ChcSort::Int]);
    let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
    let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p0, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p0, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            p1,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p1, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            p2,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p2, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(2))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_acyclic_scalar_bv2nat_safe_chain_9604() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p0 = problem.declare_predicate("B0", vec![ChcSort::BitVec(8)]);
    let p1 = problem.declare_predicate("B1", vec![ChcSort::BitVec(8)]);
    let p2 = problem.declare_predicate("B2", vec![ChcSort::BitVec(8)]);
    let x = ChcVar::new("x", ChcSort::BitVec(8));
    let bv2nat = |expr: ChcExpr| ChcExpr::Op(crate::ChcOp::Bv2Nat, vec![std::sync::Arc::new(expr)]);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p0, vec![ChcExpr::BitVec(2, 8)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p0, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                bv2nat(ChcExpr::var(x.clone())),
                ChcExpr::int(2),
            )),
        ),
        ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p1, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(p2, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p2, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ne(bv2nat(ChcExpr::var(x)), ChcExpr::int(2))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_acyclic_int_safe_chain_9303() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p0 = problem.declare_predicate("P0_safe", vec![ChcSort::Int]);
    let p1 = problem.declare_predicate("P1_safe", vec![ChcSort::Int]);
    let p2 = problem.declare_predicate("P2_safe", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p0, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p0, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            p1,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p1, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            p2,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p2, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_large_acyclic_int_safe_chain_9004() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let preds: Vec<_> = (0..130)
        .map(|idx| problem.declare_predicate(&format!("P{idx}_safe"), vec![ChcSort::Int]))
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
                *preds.last().expect("nonempty predicate chain"),
                vec![ChcExpr::var(x.clone())],
            )],
            Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(999))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_large_acyclic_bounded_square_safe_chain_9004() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let preds: Vec<_> = (0..130)
        .map(|idx| problem.declare_predicate(&format!("P{idx}_square"), vec![ChcSort::Int]))
        .collect();
    let done = problem.declare_predicate("Done_square", vec![ChcSort::Int]);
    let n = ChcVar::new("n", ChcSort::Int);
    let p = ChcVar::new("p", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and_all([
            ChcExpr::ge(ChcExpr::var(n.clone()), ChcExpr::int(0)),
            ChcExpr::le(ChcExpr::var(n.clone()), ChcExpr::int(100)),
        ])),
        ClauseHead::Predicate(preds[0], vec![ChcExpr::var(n.clone())]),
    ));

    for idx in 1..preds.len() {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(preds[idx - 1], vec![ChcExpr::var(n.clone())])]),
            ClauseHead::Predicate(preds[idx], vec![ChcExpr::var(n.clone())]),
        ));
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                *preds.last().expect("nonempty predicate chain"),
                vec![ChcExpr::var(n.clone())],
            )],
            Some(ChcExpr::eq(
                ChcExpr::var(p.clone()),
                ChcExpr::mul(ChcExpr::var(n.clone()), ChcExpr::var(n)),
            )),
        ),
        ClauseHead::Predicate(done, vec![ChcExpr::var(p.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(done, vec![ChcExpr::var(p.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(p), ChcExpr::int(10_201))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_large_acyclic_split_square_query_safe_chain_9004() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let preds: Vec<_> = (0..130)
        .map(|idx| problem.declare_predicate(&format!("P{idx}_split_square"), vec![ChcSort::Int]))
        .collect();
    let done = problem.declare_predicate("Done_split_square", vec![ChcSort::Int, ChcSort::Bool]);
    let n = ChcVar::new("n", ChcSort::Int);
    let overflow = ChcVar::new("overflow", ChcSort::Bool);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and_all([
            ChcExpr::ge(ChcExpr::var(n.clone()), ChcExpr::int(0)),
            ChcExpr::le(ChcExpr::var(n.clone()), ChcExpr::int(50)),
        ])),
        ClauseHead::Predicate(preds[0], vec![ChcExpr::var(n.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and_all([
            ChcExpr::ge(ChcExpr::var(n.clone()), ChcExpr::int(51)),
            ChcExpr::le(ChcExpr::var(n.clone()), ChcExpr::int(100)),
        ])),
        ClauseHead::Predicate(preds[0], vec![ChcExpr::var(n.clone())]),
    ));

    for idx in 1..preds.len() {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(preds[idx - 1], vec![ChcExpr::var(n.clone())])]),
            ClauseHead::Predicate(preds[idx], vec![ChcExpr::var(n.clone())]),
        ));
    }

    let square = ChcExpr::mul(ChcExpr::var(n.clone()), ChcExpr::var(n.clone()));
    let overflow_guard = ChcExpr::or(
        ChcExpr::lt(square.clone(), ChcExpr::int(0)),
        ChcExpr::ge(square.clone(), ChcExpr::int(4_294_967_296_i64)),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                *preds.last().expect("nonempty predicate chain"),
                vec![ChcExpr::var(n.clone())],
            )],
            Some(ChcExpr::eq(ChcExpr::var(overflow.clone()), overflow_guard)),
        ),
        ClauseHead::Predicate(
            done,
            vec![ChcExpr::var(n.clone()), ChcExpr::var(overflow.clone())],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                done,
                vec![ChcExpr::var(n.clone()), ChcExpr::var(overflow.clone())],
            )],
            Some(ChcExpr::or(
                ChcExpr::var(overflow),
                ChcExpr::ge(square, ChcExpr::int(10_201)),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_acyclic_int_unsafe_diamond_8663() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let entry = problem.declare_predicate("Entry", vec![ChcSort::Int]);
    let left = problem.declare_predicate("Left", vec![ChcSort::Int]);
    let right = problem.declare_predicate("Right", vec![ChcSort::Int]);
    let join = problem.declare_predicate("Join", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(entry, vec![ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(entry, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            left,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(entry, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(
            right,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(2))],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (left, vec![ChcExpr::var(x.clone())]),
                (right, vec![ChcExpr::var(y.clone())]),
            ],
            Some(ChcExpr::eq(
                ChcExpr::var(z.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            )),
        ),
        ClauseHead::Predicate(join, vec![ChcExpr::var(z.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(join, vec![ChcExpr::var(z.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(z), ChcExpr::int(3))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn parse_benchmark(input: &str, label: &str) -> ChcProblem {
    ChcParser::parse(input).unwrap_or_else(|err| panic!("parse {label}: {err}"))
}

#[test]
fn test_adaptive_statistics_profile_tla_transition_clusters_without_native_dispatch() {
    let solver = AdaptivePortfolio::new(
        create_tla_action_cluster_problem(),
        AdaptiveConfig::default(),
    );
    let stats = solver.statistics();

    assert_eq!(stats.tla_transition_cluster_applications, 1);
    assert_eq!(stats.native_code_helper_applications, 0);
    assert_eq!(stats.native_code_helper_compile_attempts, 0);
}

#[allow(dead_code)]
fn assert_adaptive_benchmark_is_not_safe(input: &str, label: &str) {
    let problem = parse_benchmark(input, label);
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(15),
            verbose: false,
            ..AdaptiveConfig::test_default()
        },
    );

    match adaptive.solve() {
        VerifiedChcResult::Safe(_) => {
            panic!("Adaptive false-SAT regression (#7688): {label} must not return Safe");
        }
        VerifiedChcResult::Unsafe(_) | VerifiedChcResult::Unknown(_) => {}
    }
}

/// #chc25-lra-convergence adversarial pin: an UNSAFE Real (LRA) transition
/// system must never be proved Safe. `x` starts at 0.0 and increments by 1.0
/// each step; the property `x < 3.0` is violated once `x` reaches 3.0, so the
/// only sound verdicts are Unsafe or Unknown. This guards the new LRA Farkas
/// interpolation from fabricating a bogus inductive invariant.
#[test]
#[timeout(60000)]
fn test_lra_unsafe_real_transition_never_safe() {
    let smt = r#"
(set-logic HORN)
(declare-fun Inv (Real) Bool)
(assert (forall ((x Real)) (=> (= x 0.0) (Inv x))))
(assert (forall ((x Real) (y Real)) (=> (and (Inv x) (= y (+ x 1.0))) (Inv y))))
(assert (forall ((x Real)) (=> (and (Inv x) (>= x 3.0)) false)))
(check-sat)
"#;
    assert_adaptive_benchmark_is_not_safe(smt, "lra_unbounded_counter_unsafe");
}

fn false_model_for_first_predicate(problem: &ChcProblem) -> InvariantModel {
    let pred = problem
        .predicates()
        .first()
        .expect("test problem should have a predicate");
    let canonical_vars = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
        .collect();
    let mut model = InvariantModel::new();
    model.set(
        pred.id,
        PredicateInterpretation::new(canonical_vars, ChcExpr::Bool(false)),
    );
    model
}

fn true_model_for_first_predicate(problem: &ChcProblem) -> InvariantModel {
    let pred = problem
        .predicates()
        .first()
        .expect("test problem should have a predicate");
    let canonical_vars = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
        .collect();
    let mut model = InvariantModel::new();
    model.set(
        pred.id,
        PredicateInterpretation::new(canonical_vars, ChcExpr::Bool(true)),
    );
    model
}

fn empty_counterexample_for_first_predicate(problem: &ChcProblem, depth: usize) -> Counterexample {
    let pred = problem
        .predicates()
        .first()
        .expect("test problem should have a predicate")
        .id;
    Counterexample::new(
        (0..=depth)
            .map(|_| CounterexampleStep::new(pred, FxHashMap::default()))
            .collect(),
    )
}

fn read_decision_log_entries(path: &std::path::Path) -> Vec<serde_json::Value> {
    std::fs::read_to_string(path)
        .expect("decision log should be written")
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("valid JSONL row"))
        .collect()
}

fn create_phase_bounded_safe_problem(num_phases: usize) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);

    let phase = ChcVar::new("phase", ChcSort::Int);
    let x = ChcVar::new("x", ChcSort::Int);
    let phase1 = ChcVar::new("phase1", ChcSort::Int);
    let x1 = ChcVar::new("x1", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(phase.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        )),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(phase.clone()), ChcExpr::var(x.clone())],
        ),
    ));

    for k in 0..(num_phases as i64) {
        let constraint = ChcExpr::and_all([
            ChcExpr::eq(ChcExpr::var(phase.clone()), ChcExpr::int(k)),
            ChcExpr::eq(ChcExpr::var(phase1.clone()), ChcExpr::int(k + 1)),
            ChcExpr::eq(
                ChcExpr::var(x1.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ),
        ]);
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(
                    inv,
                    vec![ChcExpr::var(phase.clone()), ChcExpr::var(x.clone())],
                )],
                Some(constraint),
            ),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::var(phase1.clone()), ChcExpr::var(x1.clone())],
            ),
        ));
    }

    let expected_x = 10 + num_phases as i64;
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![ChcExpr::var(phase.clone()), ChcExpr::var(x.clone())],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(phase), ChcExpr::int(num_phases as i64)),
                ChcExpr::Op(
                    crate::ChcOp::Not,
                    vec![std::sync::Arc::new(ChcExpr::eq(
                        ChcExpr::var(x),
                        ChcExpr::int(expected_x),
                    ))],
                ),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_adaptive_classifies_simple_loop() {
    let problem = create_simple_loop();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
}

#[test]
fn test_complex_loop_dispatch_does_not_claim_bmc_evidence_source_regression() {
    let src = include_str!("adaptive.rs");
    let branch_start = src
        .find("ProblemClass::ComplexLoop => {")
        .expect("adaptive.rs should define the complex-loop dispatch arm");
    let branch_end = src[branch_start..]
        .find("ProblemClass::MultiPredLinear =>")
        .map(|offset| branch_start + offset)
        .expect("complex-loop arm should be followed by MultiPredLinear");
    let branch = &src[branch_start..branch_end];

    assert!(
        branch.contains("complex_loop_validation_evidence"),
        "complex-loop dispatch must route through the shared evidence helper"
    );
    assert!(
        !branch.contains("ValidationEvidence::BmcCounterexample"),
        "complex-loop dispatch must not claim constructive BMC evidence for every Unsafe"
    );
}

#[test]
fn test_adaptive_solves_simple_loop() {
    let problem = create_simple_loop();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(10),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::test_default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: problem is safe
        }
        VerifiedChcResult::Unknown(_) => {
            panic!("Adaptive portfolio returned Unknown on a trivial safe loop.")
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!("Problem is safe, should not return Unsafe");
        }
    }
}

#[test]
#[cfg_attr(debug_assertions, timeout(20_000))]
#[cfg_attr(not(debug_assertions), timeout(10_000))]
fn test_adt_lia_isaplanner_last_singleton_safe_validates_9700() {
    let smt = r#"
(set-logic HORN)
(declare-datatypes ((list_6 0)) (((nil_6) (cons_6 (head_12 Int) (tail_12 list_6)))))
(declare-fun |last_1| (Int list_6) Bool)

(assert
  (forall ((A list_6) (B list_6) (C Int) (D Int) (E list_6) (F Int))
    (=>
      (and
        (last_1 C A)
        (and (= B (cons_6 F (cons_6 D E))) (= A (cons_6 D E))))
      (last_1 C B))))
(assert
  (forall ((A list_6) (B Int))
    (=>
      (and (= A (cons_6 B nil_6)))
      (last_1 B A))))
(assert
  (forall ((v_0 Int) (v_1 list_6))
    (=>
      (and (and true (= 0 v_0) (= v_1 nil_6)))
      (last_1 v_0 v_1))))
(assert
  (forall ((A list_6) (B Int) (C Int))
    (=>
      (and
        (last_1 B A)
        (and (not (= B C)) (= A (cons_6 C nil_6))))
      false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt).expect("ADT-LIA fixture parses");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(5)),
    );

    let result = adaptive.solve();
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "ADT-LIA constructor-case invariant should validate as Safe, got {result:?}"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_acyclic_array_bv_bmc_probe_is_not_unsafe_8663() {
    let problem = create_acyclic_model_checker_consumer_array_bv_chain();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            verbose: true,
            ..AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10))
        },
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(features.is_linear);
    assert!(!features.has_cycles);
    assert!(features.uses_arrays);
    assert!(adaptive.problem.has_bv_sorts());

    let result = adaptive
        .try_acyclic_bmc_probe(&features, None)
        .map(|(result, _evidence)| result);
    assert!(
        !matches!(result, Some(PortfolioResult::Unsafe(_))),
        "acyclic BMC probe must not report Unsafe for the safe array/BV chain, got {result:?}"
    );

    assert!(
        !matches!(adaptive.solve(), VerifiedChcResult::Unsafe(_)),
        "adaptive solver must not return Unsafe on the acyclic array/BV chain"
    );
}

#[test]
fn test_acyclic_bmc_budget_uses_full_remaining_for_array_dags_165() {
    let problem = create_acyclic_model_checker_consumer_array_bv_chain();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert!(!features.has_cycles);
    assert!(features.uses_arrays);
    assert_eq!(
        AdaptivePortfolio::acyclic_bmc_stage_budget(&features, Duration::from_secs(45)),
        Duration::from_secs(45)
    );
}

#[test]
fn test_acyclic_bmc_budget_keeps_non_array_cap_165() {
    let problem = create_acyclic_int_safe_chain_9303();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert!(!features.has_cycles);
    assert!(!features.uses_arrays);
    assert_eq!(
        AdaptivePortfolio::acyclic_bmc_stage_budget(&features, Duration::from_secs(45)),
        Duration::from_secs(13)
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_acyclic_probe_accepts_scalar_empty_model_evidence_9303() {
    let problem = create_acyclic_int_safe_chain_9303();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(!features.has_cycles);
    assert!(!features.uses_arrays);

    let proof_result = adaptive.try_acyclic_bmc_probe(&features, None);
    match proof_result {
        Some((PortfolioResult::Safe(model), ValidationEvidence::FullVerification)) => assert!(
            !model.is_empty(),
            "acyclic BMC Safe may be accepted only with a real invariant model"
        ),
        Some((
            PortfolioResult::Safe(model),
            ValidationEvidence::ScalarAcyclicBmcExhaustive { .. },
        )) => assert!(
            model.is_empty(),
            "scalar acyclic BMC evidence is reserved for empty-model exhaustive proofs"
        ),
        None => {}
        other => panic!(
            "scalar acyclic BMC Safe must carry either a model or scalar exhaustive evidence, got {other:?}"
        ),
    }

    assert!(
        !matches!(adaptive.solve(), VerifiedChcResult::Unsafe(_)),
        "safe acyclic benchmark must not become unsafe while BMC empty-model Safe fails closed"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_exact_bv_to_int_acyclic_probe_validates_scalar_bv2nat_safe_9604() {
    let problem = create_acyclic_scalar_bv2nat_safe_chain_9604();
    let adaptive = AdaptivePortfolio::new(
        problem.clone(),
        AdaptiveConfig {
            verbose: true,
            ..AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10))
        },
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(!features.has_cycles);
    assert!(!features.uses_arrays);
    assert!(adaptive.problem.has_bv_sorts());

    let int_summary = PreprocessSummary::build_int_only(problem, false);
    assert!(
        !int_summary.had_bitwise_uf_fallback(),
        "exact scalar bv2nat chain must not use bitwise UF fallback"
    );
    assert!(
        !int_summary.transformed_problem.has_bv_sorts(),
        "exact BvToInt summary should remove scalar BV predicate state"
    );

    let proof_result = adaptive.run_preprocessed_acyclic_bmc_probe(
        int_summary,
        &features,
        Duration::from_secs(5),
        "test-exact-BvToInt",
        true,
    );
    let Some((PortfolioResult::Safe(model), ValidationEvidence::FullVerification)) = proof_result
    else {
        panic!(
            "exact-BvToInt scalar acyclic discharge should validate on the original bv2nat CHC, \
             got {proof_result:?}"
        );
    };
    assert!(
        !model.is_empty(),
        "validated BvToInt discharge must carry original predicate interpretations"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_preprocessed_query_only_bv_dag_translates_and_validates_model_9716() {
    let problem = parse_benchmark(
        r#"
(set-logic HORN)
(declare-var x (_ BitVec 32))
(declare-rel P ((_ BitVec 32)))
(declare-rel error ())
(rule (=> (= x #x0000002a) (P x)))
(rule (=> (and (P x) (not (= x #x0000002a))) error))
(query error)
"#,
        "preprocessed-query-only-bv-dag-9716",
    );
    let adaptive = AdaptivePortfolio::new(
        problem.clone(),
        AdaptiveConfig {
            verbose: true,
            ..AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10))
        },
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(!features.has_cycles);
    assert!(adaptive.problem.has_bv_sorts());

    let summary = PreprocessSummary::build_int_only(problem, true);
    assert!(
        !summary.had_bitwise_uf_fallback(),
        "the regression input should stay on exact BvToInt"
    );
    assert_eq!(
        summary.transformed_problem.predicates().len(),
        0,
        "exact preprocessing should inline the DAG into query-only clauses"
    );
    assert!(
        summary
            .transformed_problem
            .clauses()
            .iter()
            .all(|c| c.is_query()),
        "collapsed problem should contain only query clauses"
    );

    let proof_result = adaptive.run_preprocessed_acyclic_bmc_probe(
        summary,
        &features,
        Duration::from_secs(5),
        "test-query-only",
        true,
    );
    let Some((PortfolioResult::Safe(model), ValidationEvidence::FullVerification)) = proof_result
    else {
        panic!("query-only preprocessed DAG should validate as Safe, got {proof_result:?}");
    };
    assert!(
        !model.is_empty(),
        "the transformed empty proof must be back-translated into original predicate interpretations"
    );

    assert!(matches!(
        adaptive.finalize_verified_result(
            PortfolioResult::Safe(model),
            ValidationEvidence::FullVerification
        ),
        VerifiedChcResult::Safe(_)
    ));
}

#[test]
fn test_final_demotes_unvalidated_preprocessed_query_only_discharge_9716() {
    let problem = create_acyclic_scalar_bv2nat_safe_chain_9604();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Safe(InvariantModel::default()),
        ValidationEvidence::PreprocessedQueryOnlyDischarge { query_count: 1 },
    );

    assert!(matches!(result, VerifiedChcResult::Unknown(_)));
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_large_non_array_acyclic_linear_graph_uses_direct_dag_bmc_9004() {
    let problem = create_large_acyclic_int_safe_chain_9004();
    let validation_problem = problem.clone();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            verbose: true,
            ..AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10))
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(!features.has_cycles);
    assert!(features.is_linear);
    assert!(!features.uses_arrays);
    assert!(AdaptivePortfolio::is_large_acyclic_linear_graph(&features));
    assert_eq!(
        AdaptivePortfolio::acyclic_bmc_stage_budget(&features, Duration::from_secs(45)),
        Duration::from_secs(45)
    );

    let proof_result = adaptive.try_acyclic_bmc_probe(&features, None);
    let Some((
        PortfolioResult::Safe(model),
        ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth },
    )) = proof_result
    else {
        panic!(
            "large non-array acyclic BMC empty-model Safe should be accepted with scalar exhaustive evidence, got {proof_result:?}"
        );
    };
    assert!(
        model.is_empty(),
        "scalar exhaustive BMC evidence must carry the empty certificate"
    );
    assert_eq!(
        crate::acyclic_cert_cache::lookup_acyclic_bmc_safe(&adaptive.problem),
        Some(max_depth),
        "the direct exact BMC proof on the original problem must populate the reuse cache"
    );

    let zero_budget = PdrConfig {
        solve_timeout: Some(Duration::ZERO),
        ..PdrConfig::default()
    };
    assert!(
        !crate::engines::validate_external_invariant_model(
            &validation_problem,
            &InvariantModel::new(),
            &zero_budget,
        )
        .expect("zero-budget validation should fail closed, not error"),
        "a cache hit must not bypass the zero-budget rejection"
    );

    let cancelled = crate::CancellationToken::new();
    cancelled.cancel();
    let cancelled_config = PdrConfig::default().with_cancellation_token(Some(cancelled));
    assert!(
        !crate::engines::validate_external_invariant_model(
            &validation_problem,
            &InvariantModel::new(),
            &cancelled_config,
        )
        .expect("pre-cancelled validation should fail closed, not error"),
        "a cache hit must not bypass pre-cancellation"
    );

    assert!(
        crate::engines::validate_external_invariant_model(
            &validation_problem,
            &InvariantModel::new(),
            &PdrConfig::default(),
        )
        .expect("cached exact BMC proof should validate without error"),
        "an eligible external empty certificate should reuse the direct exact BMC proof"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_budget_report_uses_original_exact_bv_acyclic_probe_9227() {
    let mut input = String::from("(set-logic HORN)\n");
    for index in 0..40 {
        input.push_str(&format!(
            "(declare-rel P{index} ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)))\n"
        ));
    }
    input.push_str("(declare-rel error ())\n");
    input.push_str("(declare-var start (_ BitVec 64))\n");
    input.push_str("(declare-var end (_ BitVec 64))\n");
    input.push_str("(declare-var off (_ BitVec 64))\n");
    input.push_str(
        "(rule (=> (and (bvule start end) (bvule end (_ bv5 64)) \
         (bvule off (_ bv4 64)) (bvule (bvadd start off) (_ bv4 64))) \
         (P0 start end off)))\n",
    );
    for index in 0..39 {
        input.push_str(&format!(
            "(rule (=> (P{index} start end off) (P{} start end off)))\n",
            index + 1
        ));
    }
    input.push_str("(rule (=> (and (P39 start end off) (bvult (bvadd start off) start)) error))\n");
    input.push_str("(query error)\n");

    let problem = ChcParser::parse(&input).expect("acyclic BV budget-report fixture should parse");
    let validation_problem = problem.clone();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            verbose: true,
            ..AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10))
        },
    );
    let (result, report) = adaptive.solve_with_budget_report();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "budget-report API must use the original exact-BV acyclic proof route for high-arity model-checker-consumer-shaped CHCs, got {result:?}"
    );
    assert!(
        report.entries.is_empty(),
        "acyclic proof prepass should solve before launching budget-report portfolio engines"
    );

    let external_validation = crate::engines::validate_external_invariant_model(
        &validation_problem,
        &InvariantModel::new(),
        &PdrConfig::default(),
    )
    .expect("empty scalar acyclic BMC certificate validation should not error");
    assert!(
        external_validation,
        "model-checker-consumer-facing external validation must accept established scalar acyclic BMC evidence"
    );
}

#[test]
fn test_external_empty_bmc_certificate_rejects_unsafe_acyclic_bv_9227() {
    let input = r#"
(set-logic HORN)
(declare-rel P0 ((_ BitVec 8)))
(declare-rel P1 ((_ BitVec 8)))
(declare-rel error ())
(declare-var x (_ BitVec 8))
(rule (=> true (P0 #x00)))
(rule (=> (P0 x) (P1 x)))
(rule (=> (P1 x) error))
(query error)
"#;
    let problem = ChcParser::parse(input).expect("unsafe acyclic BV fixture should parse");
    let accepted = crate::engines::validate_external_invariant_model(
        &problem,
        &InvariantModel::new(),
        &PdrConfig::default(),
    )
    .expect("unsafe empty-model validation should not error");

    assert!(
        !accepted,
        "empty scalar acyclic BMC validation must reject reachable-error CHCs"
    );
}

#[test]
fn test_external_empty_bmc_certificate_strips_dead_end_cycle_8578() {
    let input = r#"
(set-logic HORN)
(declare-rel P (Int))
(declare-rel Dead (Int))
(declare-rel error ())
(declare-var x Int)
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (< x 0)) error))
(rule (=> (P x) (Dead x)))
(rule (=> (Dead x) (Dead (+ x 1))))
(query error)
"#;
    let problem = ChcParser::parse(input).expect("dead-end-cycle fixture should parse");
    assert!(
        problem.has_cycles(),
        "the original problem must retain the dead-end self-loop"
    );

    let accepted = crate::engines::validate_external_invariant_model(
        &problem,
        &InvariantModel::new(),
        &PdrConfig::default(),
    )
    .expect("external empty-certificate validation should not error");

    assert!(
        accepted,
        "external validation must replay the safe acyclic query cone after stripping the dead end"
    );
}

#[test]
fn test_external_empty_bmc_certificate_dead_end_strip_rejects_reachable_error_8578() {
    let input = r#"
(set-logic HORN)
(declare-rel P (Int))
(declare-rel Dead (Int))
(declare-rel error ())
(declare-var x Int)
(rule (=> (= x 0) (P x)))
(rule (=> (and (P x) (= x 0)) error))
(rule (=> (P x) (Dead x)))
(rule (=> (Dead x) (Dead (+ x 1))))
(query error)
"#;
    let problem = ChcParser::parse(input).expect("unsafe dead-end-cycle fixture should parse");
    assert!(
        problem.has_cycles(),
        "the original problem must retain the dead-end self-loop"
    );

    let accepted = crate::engines::validate_external_invariant_model(
        &problem,
        &InvariantModel::new(),
        &PdrConfig::default(),
    )
    .expect("unsafe external empty-certificate validation should not error");

    assert!(
        !accepted,
        "stripping a query-irrelevant cycle must not hide a reachable error"
    );
}

#[test]
fn test_bounded_square_linearization_rewrites_nia_to_lia_9004() {
    let n = ChcVar::new("n", ChcSort::Int);
    let p = ChcVar::new("p", ChcSort::Int);
    let square = ChcExpr::mul(ChcExpr::var(n.clone()), ChcExpr::var(n.clone()));
    let mut conjuncts = vec![
        ChcExpr::eq(ChcExpr::var(p.clone()), square.clone()),
        ChcExpr::or(
            ChcExpr::lt(square.clone(), ChcExpr::int(0)),
            ChcExpr::ge(square, ChcExpr::int(4_294_967_296_i64)),
        ),
        ChcExpr::le(ChcExpr::var(p), ChcExpr::int(10_000)),
    ];

    let rewritten =
        BmcSolver::linearize_bounded_square_conjuncts_for_test(&mut conjuncts, &[("n", 0, 100)]);
    let formula = ChcExpr::and_all(conjuncts);

    assert_eq!(rewritten, 1);
    assert!(
        !formula.contains_nonlinear_mul(),
        "bounded square linearization should remove nonlinear multiplication, got {formula:?}"
    );
}

#[test]
fn test_bounded_standalone_square_linearization_rewrites_nia_to_lia_9004() {
    let n = ChcVar::new("n", ChcSort::Int);
    let square = ChcExpr::mul(ChcExpr::var(n.clone()), ChcExpr::var(n));
    let mut conjuncts = vec![ChcExpr::or(
        ChcExpr::lt(square.clone(), ChcExpr::int(0)),
        ChcExpr::ge(square, ChcExpr::int(4_294_967_296_i64)),
    )];

    let rewritten =
        BmcSolver::linearize_bounded_square_conjuncts_for_test(&mut conjuncts, &[("n", 0, 100)]);
    let formula = ChcExpr::and_all(conjuncts);

    assert_eq!(rewritten, 1);
    assert!(
        !formula.contains_nonlinear_mul(),
        "standalone bounded square linearization should remove nonlinear multiplication, got {formula:?}"
    );
}

#[test]
fn test_bounded_square_overflow_guard_simplifies_error_branch_9004() {
    let n = ChcVar::new("n", ChcSort::Int);
    let p = ChcVar::new("p", ChcSort::Int);
    let overflow = ChcVar::new("overflow", ChcSort::Bool);
    let square = ChcExpr::mul(ChcExpr::var(n.clone()), ChcExpr::var(n));
    let overflow_guard = ChcExpr::or(
        ChcExpr::lt(square.clone(), ChcExpr::int(0)),
        ChcExpr::ge(square.clone(), ChcExpr::int(4_294_967_296_i64)),
    );
    let mut conjuncts = vec![
        ChcExpr::eq(ChcExpr::var(p), square),
        ChcExpr::eq(ChcExpr::var(overflow.clone()), overflow_guard),
        ChcExpr::var(overflow),
    ];

    let (linearized, simplified) =
        BmcSolver::linearize_and_simplify_bounded_square_conjuncts_for_test(
            &mut conjuncts,
            &[("n", 0, 100)],
        );
    let formula = ChcExpr::and_all(conjuncts);

    assert_eq!(linearized, 1);
    assert!(simplified > 0);
    assert_eq!(formula, ChcExpr::Bool(false));
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_large_bounded_square_acyclic_dag_bmc_proves_safe_9004() {
    let problem = create_large_acyclic_bounded_square_safe_chain_9004();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            verbose: true,
            ..AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10))
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(!features.has_cycles);
    assert!(features.is_linear);
    assert!(AdaptivePortfolio::is_large_acyclic_linear_graph(&features));

    let proof_result = adaptive.try_acyclic_bmc_probe(&features, None);
    assert!(
        matches!(
            proof_result,
            Some((
                PortfolioResult::Safe(_),
                ValidationEvidence::ScalarAcyclicBmcExhaustive { .. }
            ))
        ),
        "bounded square scalar acyclic DAG BMC should be accepted, got {proof_result:?}"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_large_split_square_query_acyclic_dag_bmc_proves_safe_9004() {
    let problem = create_large_acyclic_split_square_query_safe_chain_9004();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            verbose: true,
            ..AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10))
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(!features.has_cycles);
    assert!(features.is_linear);
    assert!(AdaptivePortfolio::is_large_acyclic_linear_graph(&features));

    let proof_result = adaptive.try_acyclic_bmc_probe(&features, None);
    assert!(
        matches!(
            proof_result,
            Some((
                PortfolioResult::Safe(_),
                ValidationEvidence::ScalarAcyclicBmcExhaustive { .. }
            ))
        ),
        "split square scalar acyclic DAG BMC should be accepted, got {proof_result:?}"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_acyclic_bmc_ignores_tautological_terminal_self_loop_9191() {
    let mut problem = create_acyclic_int_safe_chain_9303();
    let p2 = problem
        .lookup_predicate("P2_safe")
        .expect("test predicate exists");
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p2, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(p2, vec![ChcExpr::var(x)]),
    ));

    assert!(
        problem.has_cycles(),
        "raw graph contains the terminal self-edge"
    );
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(!features.has_cycles);

    let proof_result = adaptive.try_acyclic_bmc_probe(&features, None);
    assert!(
        matches!(
            proof_result,
            Some((
                PortfolioResult::Safe(_),
                ValidationEvidence::ScalarAcyclicBmcExhaustive { .. }
            ))
        ),
        "tautological terminal self-loop scalar BMC proof should be accepted, got {proof_result:?}"
    );

    assert!(
        matches!(adaptive.solve(), VerifiedChcResult::Safe(_)),
        "adaptive solver should accept scalar exhaustive acyclic BMC evidence"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_acyclic_int_bmc_probe_without_bv_sorts_8663() {
    let problem = create_acyclic_int_unsafe_chain_8663();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredLinear);
    assert!(features.is_linear);
    assert!(!features.has_cycles);
    assert!(!features.uses_arrays);
    assert!(!adaptive.problem.has_bv_sorts());

    let result = adaptive
        .try_acyclic_bmc_probe(&features, None)
        .map(|(result, _evidence)| result);
    assert!(
        matches!(result, Some(PortfolioResult::Unsafe(_))),
        "acyclic Int BMC probe should find the reachable query without a BV-sort gate, got {result:?}"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_acyclic_complex_bmc_probe_runs_8663() {
    let problem = create_acyclic_int_unsafe_diamond_8663();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    let features = adaptive.features();
    assert_eq!(features.class, ProblemClass::MultiPredComplex);
    assert!(!features.is_linear);
    assert!(!features.has_cycles);
    assert!(!features.uses_arrays);
    assert!(!adaptive.problem.has_bv_sorts());

    let result = adaptive
        .try_acyclic_bmc_probe(&features, None)
        .map(|(result, _evidence)| result);
    assert!(
        matches!(result, Some(PortfolioResult::Unsafe(_))),
        "acyclic complex BMC probe should validate the reachable diamond query, got {result:?}"
    );
}

#[test]
fn test_phase_bounded_fast_path_rejects_empty_model_bmc_safe() {
    let problem = create_phase_bounded_safe_problem(3);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.phase_bounded_depth, Some(4));
    assert!(
        adaptive
            .try_phase_bounded_bmc_fast_path(&features)
            .is_none(),
        "phase-bounded direct BMC fast path must reject empty-model Safe and fall through (#8585)"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_issue_7688_accumulator_unsafe_not_safe() {
    assert_adaptive_benchmark_is_not_safe(
        include_str!(
            "../../../benchmarks/chc-comp/2025/extra-small-lia/accumulator_unsafe_000.smt2"
        ),
        "accumulator_unsafe_000",
    );
}

/// Regression: Kind finds counterexample at k=11 for accumulator_unsafe,
/// but adaptive layer discarded it (returned None). With #7897 fix,
/// Kind Unsafe results flow through to VerifiedChcResult::Unsafe.
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_issue_7897_kind_unsafe_flows_through_adaptive() {
    let problem = parse_benchmark(
        include_str!(
            "../../../benchmarks/chc-comp/2025/extra-small-lia/accumulator_unsafe_000.smt2"
        ),
        "accumulator_unsafe_000",
    );
    // Kind needs k=11 to find the counterexample. In debug mode, each
    // k-induction query is slower, so give the solver enough time for
    // the full simple-loop pipeline (Kind 8s + PDR probe 6s + portfolio).
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(25),
            verbose: false,
            ..AdaptiveConfig::test_default()
        },
    );

    match adaptive.solve() {
        VerifiedChcResult::Unsafe(_) => {} // expected
        VerifiedChcResult::Safe(_) => {
            panic!("accumulator_unsafe_000 must not return Safe (false-SAT)");
        }
        VerifiedChcResult::Unknown(reason) => {
            panic!(
                "accumulator_unsafe_000 should return Unsafe, got Unknown: {:?}.                  Kind finds counterexample at k=11 but adaptive discards it (#7897)",
                reason
            );
        }
    }
}

/// Regression: Simple loop counter reaching 5 should be reported as Unsafe.
/// KIND finds this at k=5 (x starts at 0, increments to 5, query x >= 5).
#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_issue_7897_kind_unsafe_simple_counter() {
    let problem = create_unsafe_simple_loop();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(10),
            verbose: false,
            ..AdaptiveConfig::test_default()
        },
    );

    match adaptive.solve() {
        VerifiedChcResult::Unsafe(_) => {} // expected
        VerifiedChcResult::Safe(_) => {
            panic!("unsafe simple loop must not return Safe");
        }
        VerifiedChcResult::Unknown(reason) => {
            panic!(
                "unsafe simple loop should return Unsafe, got Unknown: {:?}.                  Kind should find counterexample at k=5 (#7897)",
                reason
            );
        }
    }
}

#[test]
#[cfg_attr(debug_assertions, timeout(30_000))]
#[cfg_attr(not(debug_assertions), timeout(20_000))]
fn test_adaptive_issue_7688_two_phase_unsafe_not_safe() {
    assert_adaptive_benchmark_is_not_safe(
        include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/two_phase_unsafe_000.smt2"),
        "two_phase_unsafe_000",
    );
}

#[test]
fn test_validate_adaptive_result_rejects_false_safe_when_validate_disabled() {
    let problem = create_simple_loop();
    let invalid_model = false_model_for_first_predicate(&problem);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let validated = adaptive.validate_adaptive_result(PdrResult::Safe(invalid_model));
    assert!(
        matches!(validated, PdrResult::Unknown),
        "mandatory Safe validation must reject invalid direct-engine models even when validate=false"
    );
}

#[test]
fn test_validate_adaptive_result_rejects_unverified_unsafe_when_validate_disabled() {
    let problem = create_simple_loop();
    let cex = empty_counterexample_for_first_predicate(&problem, 1);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let validated = adaptive.validate_adaptive_result(PdrResult::Unsafe(cex));

    assert!(
        matches!(validated, PdrResult::Unknown),
        "direct adaptive Unsafe results must not be accepted without re-verification"
    );
    // inc-9 (gate g4): the result is now RE-VERIFIED (and rejected on
    // failure) instead of being dropped as a trust-proof fallback, so the
    // fallback counter stays at zero.
    assert_eq!(adaptive.statistics().trust_proof_fallbacks, 0);
}

#[test]
fn test_validate_adaptive_result_rejects_individually_inductive_false_safe() {
    let problem = create_simple_loop();
    let mut invalid_model = false_model_for_first_predicate(&problem);
    invalid_model.individually_inductive = true;
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let validated = adaptive.validate_adaptive_result(PdrResult::Safe(invalid_model));
    assert!(
        matches!(validated, PdrResult::Unknown),
        "individually_inductive Safe models must still pass full validation (#9227)"
    );
}

#[test]
fn test_validate_adaptive_result_rejects_convergence_proven_false_safe() {
    let problem = create_simple_loop();
    let mut invalid_model = false_model_for_first_predicate(&problem);
    invalid_model.convergence_proven = true;
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let validated = adaptive.validate_adaptive_result(PdrResult::Safe(invalid_model));
    assert!(
        matches!(validated, PdrResult::Unknown),
        "convergence_proven Safe models must still pass full validation (#9227)"
    );
}

#[test]
fn test_try_synthesis_returns_validated_safe_model() {
    let adaptive = AdaptivePortfolio::new(create_simple_loop(), AdaptiveConfig::test_default());
    assert!(
        matches!(adaptive.try_synthesis(), Some(PortfolioResult::Safe(_))),
        "structural synthesis should still produce a validated Safe result on the bounded loop canary"
    );
}

#[test]
#[timeout(5000)]
fn test_try_synthesis_accepts_parsed_threshold_ite_multiphase_loop_issue_9692() {
    let input = r#"
(set-logic HORN)

(declare-fun |fail| () Bool)
(declare-fun |inv| (Int Int) Bool)

(assert
  (forall ((A Int) (B Int))
    (=>
      (and (= B 5000) (= A 0))
      (inv A B))))

(assert
  (forall ((A Int) (B Int) (C Int) (D Int))
    (=>
      (and
        (inv A B)
        (= D (ite (>= A 5000) (+ 1 B) B))
        (= C (+ 1 A)))
      (inv C D))))

(assert
  (forall ((A Int) (B Int))
    (=>
      (and
        (inv B A)
        (= B 10000)
        (not (= A B)))
      fail)))

(assert
  (forall ((CHC_COMP_UNUSED Bool))
    (=>
      (and fail true)
      false)))

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("s_split_01-style CHC should parse");
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    assert!(
        matches!(adaptive.try_synthesis(), Some(PortfolioResult::Safe(_))),
        "parsed threshold-ITE synthesis should be accepted after its constructive proof"
    );
}

/// SOUNDNESS POLICY (022c-horn_000 false-SAT fix): structural shape checks
/// are pattern recognizers, not proofs. `try_synthesis` must route every
/// candidate through full model validation against the original clauses and
/// fail closed when validation cannot prove it. The mod-1000 split-triangle
/// candidate is mod-heavy and currently NOT provable by the full validator,
/// so the structurally-recognized candidate must be rejected (None) — it must
/// never be accepted on the structural certificate alone. If the validator
/// later becomes strong enough, Some(Safe) is acceptable IF AND ONLY IF the
/// returned model passes a fresh strict verify_model.
#[test]
#[timeout(60000)]
fn test_try_synthesis_mod1000_split_triangle_requires_full_validation_9692() {
    let input = r#"
(set-logic HORN)

(declare-fun |fail| () Bool)
(declare-fun |inv| (Int Int Int Int) Bool)

(assert
  (forall ((A Int) (B Int) (C Int) (D Int))
    (=>
      (and (= B 0) (= C 0) (= D 500) (= A 0))
      (inv A B C D))))

(assert
  (forall ((A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int))
    (=>
      (and
        (inv C A B D)
        (and (= F (+ 1 A))
             (= G (ite (<= 500 C) (+ (- 1) B) (+ 1 B)))
             (= H (ite (>= C 500) (+ 1 D) (+ (- 1) D)))
             (= E (mod (+ 1 C) 1000))))
      (inv E F G H))))

(assert
  (forall ((A Int) (B Int) (C Int) (D Int))
    (=>
      (and
        (inv A B C D)
        (and (not (= C D)) (= B 2250)))
      fail)))

(assert
  (forall ((CHC_COMP_UNUSED Bool))
    (=>
      (and fail true)
      false)))

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("s_split_53-style CHC should parse");
    let adaptive = AdaptivePortfolio::new(problem.clone(), AdaptiveConfig::test_default());

    match adaptive.try_synthesis() {
        None => {} // fail-closed: full validation could not prove the candidate
        Some(PortfolioResult::Safe(model)) => {
            // Acceptance is only allowed when the model independently passes a
            // fresh strict full verification on the original clauses.
            let mut verifier = crate::pdr::PdrSolver::new(
                problem,
                crate::pdr::PdrConfig {
                    strict_proofs: true,
                    preserve_original_clauses: true,
                    ..crate::pdr::PdrConfig::default()
                },
            );
            assert!(
                verifier.verify_model(&model),
                "try_synthesis returned Safe with a model that fails fresh full verification"
            );
        }
        other => panic!("unexpected try_synthesis result: {other:?}"),
    }
}

/// The assertion here is FUNCTIONAL — these four CHC-COMP benchmarks must be
/// discharged by validated structural synthesis — and the timeout is only a
/// hang guard, so it is sized like its sibling
/// `test_try_synthesis_mod1000_split_triangle_requires_full_validation_9692`
/// rather than tightly.
///
/// It was 10s, which the four solves nearly exhaust on their own (~8.5s
/// isolated). Run in-lib under the default parallel runner alongside 4400+
/// other tests, the remaining 1.5s is scheduler time, not solver time, so the
/// test failed on contention while asserting nothing about it. The repo's usual
/// remedy — a dedicated test binary, as `dillig12_m_deadline_4751` documents —
/// is unavailable here because `try_synthesis` is `pub(crate)` and widening it
/// purely to relocate a test would be the worse trade.
#[test]
#[timeout(60_000)]
fn test_try_synthesis_accepts_chccomp_extra_small_lia_safe_summaries() {
    for (name, input) in [
        (
            "const_mod_3_000",
            include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/const_mod_3_000.smt2"),
        ),
        (
            "dillig02_m_000",
            include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2"),
        ),
        (
            "s_multipl_17_000",
            include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_17_000.smt2"),
        ),
        (
            "s_mutants_16_m_000",
            include_str!(
                "../../../benchmarks/chc-comp/2025/extra-small-lia/s_mutants_16_m_000.smt2"
            ),
        ),
    ] {
        let problem = ChcParser::parse(input).unwrap_or_else(|error| {
            panic!("{name} should parse as a CHC-COMP HORN benchmark: {error}")
        });
        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        assert!(
            matches!(adaptive.try_synthesis(), Some(PortfolioResult::Safe(_))),
            "{name} should be discharged by validated structural synthesis"
        );
    }
}

#[test]
#[timeout(5_000)]
fn test_query_safety_structural_admission_rejects_dillig02_hardened_shapes() {
    let unsafe_fact =
        include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2")
            .replacen("(= E 0)", "(= E 1)", 1);
    assert!(
        !query_safety_structural_admission_accepts(&unsafe_fact),
        "structural query-safety admission must reject facts that violate the synthesized invariant"
    );

    let missing_query_predicate = r#"
(set-logic HORN)

(declare-fun |inv| ( Int Int Int Int Int Int ) Bool)
(declare-fun |inv1| ( Int Int Int Int Int Int ) Bool)
(declare-fun |bad| ( Bool Bool Bool Bool Bool Bool ) Bool)

(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and (= E 0) (= D 0) (= C (+ A (* (- 1) B))) (= B 0) (= A 1) (= F 0))
      (inv A B C D E F))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and (inv A B C D E F) true)
      (inv1 A B C D E F))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) (H Int) (I Int) (J Int) )
    (=>
      (and
        (inv1 E F A C B D)
        (and (= I (+ 1 B)) (= H (ite (= (mod G 2) 1) (+ 1 C) C)) (= G (+ A C B D)) (= J (+ 2 D))))
      (inv1 E F G H I J))))
(assert
  (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) )
    (=>
      (and (inv1 A B C D E F) true)
      (inv A B C D E F))))
(assert
  (forall ( (P Bool) (Q Bool) (R Bool) (S Bool) (T Bool) (U Bool) )
    (=>
      (and (bad P Q R S T U) (not (= S T)))
      false)))

(check-sat)
(exit)
"#;
    assert!(
        !query_safety_structural_admission_accepts(missing_query_predicate),
        "structural query-safety admission must reject queries outside the synthesized predicates"
    );
}

#[test]
#[timeout(5_000)]
fn test_query_safety_structural_admission_accepts_chccomp_safe_summaries_9692() {
    for (name, input) in [
        (
            "const_mod_3_000",
            include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/const_mod_3_000.smt2"),
        ),
        (
            "dillig02_m_000",
            include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2"),
        ),
        (
            "s_multipl_17_000",
            include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_17_000.smt2"),
        ),
        (
            "s_mutants_16_m_000",
            include_str!(
                "../../../benchmarks/chc-comp/2025/extra-small-lia/s_mutants_16_m_000.smt2"
            ),
        ),
    ] {
        assert!(
            query_safety_structural_admission_accepts(input),
            "{name} should be accepted by exact structural summary admission"
        );
    }
}

#[test]
#[timeout(5_000)]
fn test_query_safety_structural_admission_rejects_hardened_safe_summary_shapes_9692() {
    let bad_mod6_query =
        include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_17_000.smt2")
            .replace("(mod A 6)", "(mod A 5)");
    assert!(
        !query_safety_structural_admission_accepts(&bad_mod6_query),
        "mod-6 structural admission must reject queries outside the generated modulus summary"
    );

    let bad_affine_fact =
        include_str!("../../../benchmarks/chc-comp/2025/extra-small-lia/s_mutants_16_m_000.smt2")
            .replacen("(= B (* 3 C))", "(= B (* 4 C))", 1);
    assert!(
        !query_safety_structural_admission_accepts(&bad_affine_fact),
        "bounded affine structural admission must reject facts outside the generated affine summary"
    );
}

fn query_safety_structural_admission_accepts(input: &str) -> bool {
    let problem = ChcParser::parse(input).expect("query-safety fixture should parse");
    let synth = crate::synthesis::StructuralSynthesizer::new(&problem);
    synth
        .try_query_safety_candidates()
        .iter()
        .any(|candidate| synth.structurally_validates_query_safety_candidate(candidate))
}

#[test]
fn test_solidity_array_dt_projection_route_accepts_validated_safe_only() {
    let problem = create_solidity_array_dt_route_problem(false);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.try_solidity_array_dt_projection_route(None);

    assert!(
        matches!(result, Some(PortfolioResult::Safe(_))),
        "SAFE-only Solidity array-DT route must return only a model that validates on the original problem"
    );
}

#[test]
fn test_solidity_array_dt_projection_route_demotes_transformed_unsafe() {
    let problem = create_solidity_array_dt_route_problem(true);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.try_solidity_array_dt_projection_route(None);

    assert!(
        result.is_none(),
        "SAFE-only Solidity array-DT route must fall through instead of accepting transformed Unsafe"
    );
}

#[test]
fn test_solidity_array_dt_projection_route_validation_no_budget_demotes_safe() {
    let problem = create_solidity_array_dt_route_problem(false);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let model = InvariantModel::new();

    let status = adaptive.validate_solidity_array_dt_original_model(&model, Instant::now());

    assert_eq!(
        status,
        SolidityArrayDtValidationStatus::NoBudget,
        "original-model validation must fail closed when the route deadline is already exhausted"
    );
}

#[test]
fn test_solidity_array_dt_projection_route_validation_failure_demotes_safe() {
    let problem = create_simple_loop();
    let invalid_model = true_model_for_first_predicate(&problem);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let status = adaptive.validate_solidity_array_dt_original_model(
        &invalid_model,
        Instant::now() + Duration::from_secs(1),
    );

    assert_eq!(
        status,
        SolidityArrayDtValidationStatus::Failed,
        "invalid original-model validation must be reported as a failed validation verdict"
    );
}

#[test]
#[timeout(20_000)]
fn test_reduced_lia_array_route_replays_unsafe_on_original_chain() {
    let problem = create_reducible_lia_array_chain();
    let original = problem.clone();
    let summary = PreprocessSummary::build(problem.clone(), false);
    assert!(
        summary.transformed_problem.predicates().len() <= REDUCED_LIA_ARRAY_ROUTE_MAX_PREDICATES,
        "fixture must exercise the major-reduction gate"
    );
    assert!(
        summary.transformed_problem.clauses().len() <= REDUCED_LIA_ARRAY_ROUTE_MAX_CLAUSES,
        "fixture must reduce to the bounded early-route clause set"
    );

    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::with_budget(Duration::from_secs(5), false),
    );
    let result = adaptive
        .try_reduced_lia_array_preprocessed_route(Some(Instant::now() + Duration::from_secs(5)));
    let Some((PortfolioResult::Unsafe(counterexample), evidence)) = result else {
        panic!("reduced LIA-array route did not return its replayed Unsafe result: {result:?}");
    };
    assert!(matches!(
        evidence,
        ValidationEvidence::CounterexampleVerification
    ));

    let mut verifier = PdrSolver::new(
        original,
        PdrConfig {
            strict_proofs: true,
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        },
    );
    assert_eq!(
        verifier.verify_counterexample(&counterexample),
        crate::pdr::CexVerificationResult::Valid,
        "route result must replay on the original unreduced clauses"
    );
}

#[test]
fn test_interval_pass_zero_duration_budget_is_identity() {
    let problem = create_simple_loop();
    let result = Box::new(
        IntervalPropagator::new()
            .with_enabled_for_test(true)
            .with_pass_budget(Duration::ZERO),
    )
    .transform(problem.clone());

    assert_eq!(
        format!("{:?}", result.problem.clauses()),
        format!("{:?}", problem.clauses())
    );
    assert_eq!(
        result.back_translator.transform_memory().transform(),
        "identity"
    );
}

#[test]
fn test_interval_pass_mid_analysis_work_exhaustion_is_identity() {
    let problem = create_simple_loop();
    let result = Box::new(
        IntervalPropagator::new()
            .with_enabled_for_test(true)
            .with_work_budget_for_test(8),
    )
    .transform(problem.clone());

    assert_eq!(
        format!("{:?}", result.problem.clauses()),
        format!("{:?}", problem.clauses()),
        "partial interval analysis must be discarded after deterministic fuel exhaustion"
    );
    assert_eq!(
        result.back_translator.transform_memory().transform(),
        "identity"
    );
}

#[test]
#[timeout(10_000)]
fn test_reduced_lia_array_interval_model_is_backtranslated_and_original_validated() {
    let problem = create_reducible_interval_lia_array_problem(false);
    let original = problem.clone();
    let summary = PreprocessSummary::build(problem.clone(), false);
    assert!(
        summary.transformed_problem.predicates().len() <= REDUCED_LIA_ARRAY_ROUTE_MAX_PREDICATES
            && summary.transformed_problem.clauses().len() <= REDUCED_LIA_ARRAY_ROUTE_MAX_CLAUSES,
        "fixture must exercise the bounded reduced route"
    );
    assert!(
        AdaptivePortfolio::try_top_model_query_infeasibility_candidate(
            &summary.transformed_problem,
            Duration::from_millis(500),
        )
        .is_none(),
        "the raw reduced query x >= 7 is feasible under top; interval bounds must be essential"
    );
    let interval_result = Box::new(
        IntervalPropagator::new()
            .with_enabled_for_test(true)
            .with_pass_budget(Duration::from_secs(1)),
    )
    .transform(summary.transformed_problem.clone());
    assert_eq!(
        interval_result
            .back_translator
            .transform_memory()
            .transform(),
        "interval_prop",
        "the x < 6 loop must retain a verified finite post-widening upper bound"
    );
    assert!(
        AdaptivePortfolio::try_top_model_query_infeasibility_candidate(
            &interval_result.problem,
            Duration::from_millis(500),
        )
        .is_some(),
        "verified interval strengthening must make x >= 7 infeasible under top"
    );

    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::with_budget(Duration::from_secs(5), false),
    );
    let result = adaptive
        .try_reduced_lia_array_preprocessed_route(Some(Instant::now() + Duration::from_secs(5)));
    let Some((PortfolioResult::Safe(model), ValidationEvidence::FullVerification)) = result else {
        panic!("verified interval model route did not prove the bounded loop Safe: {result:?}");
    };
    assert!(
        crate::engines::validate_external_invariant_model(
            &original,
            &model,
            &PdrConfig {
                strict_proofs: true,
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        )
        .expect("independent original-clause validation should complete"),
        "the returned interval model must independently satisfy the unreduced original clauses"
    );
}

#[test]
#[timeout(10_000)]
fn test_reduced_lia_array_interval_model_never_flips_reachable_query_safe() {
    let problem = create_reducible_interval_lia_array_problem(true);
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::with_budget(Duration::from_secs(5), false),
    );
    let result = adaptive
        .try_reduced_lia_array_preprocessed_route(Some(Instant::now() + Duration::from_secs(5)));

    assert!(
        !matches!(&result, Some((PortfolioResult::Safe(_), _))),
        "reachable x = 3 must never be accepted as Safe by interval candidate generation: {result:?}"
    );
}

#[test]
fn test_array_const_key_cegar_route_accepts_original_validated_safe() {
    let problem = create_const_key_array_cegar_safe_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.try_array_const_key_cegar_route(None);

    assert!(
        matches!(result, Some(PortfolioResult::Safe(_))),
        "finite-key array CEGAR route should accept only a SAFE model that PDR validated on original clauses"
    );
}

#[test]
fn test_argument_constant_invariant_route_is_quarantined_by_default() {
    let problem = create_array_argument_constant_safe_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.try_argument_constant_invariant_route(None);

    assert!(
        result.is_none(),
        "argument-constant route must stay default-off until array/datatype validation is score-clean"
    );
}

#[test]
fn test_solidity_array_dt_projection_route_attempt_result_table() {
    for (transformed_result, validation_status, expected) in [
        ("safe", SolidityArrayDtValidationStatus::Accepted, "safe"),
        (
            "safe_refined",
            SolidityArrayDtValidationStatus::RefinedAccepted,
            "safe",
        ),
        (
            "safe",
            SolidityArrayDtValidationStatus::Failed,
            "validation_failed",
        ),
        (
            "safe",
            SolidityArrayDtValidationStatus::Error,
            "validation_error",
        ),
        (
            "safe",
            SolidityArrayDtValidationStatus::NoBudget,
            "validation_no_budget",
        ),
        (
            "safe",
            SolidityArrayDtValidationStatus::Timeout,
            "validation_timeout",
        ),
        (
            "unsafe",
            SolidityArrayDtValidationStatus::NotRun,
            "transformed_unsafe",
        ),
        (
            "unknown",
            SolidityArrayDtValidationStatus::NotRun,
            "transformed_unknown",
        ),
        (
            "not_applicable",
            SolidityArrayDtValidationStatus::NotRun,
            "transformed_not_applicable",
        ),
    ] {
        assert_eq!(
            AdaptivePortfolio::solidity_array_dt_attempt_result(
                transformed_result,
                validation_status,
            ),
            expected
        );
    }
}

#[test]
fn test_solidity_array_dt_projection_route_logs_transformed_unsafe_decision() {
    let dir = tempfile::tempdir().expect("temp decision-log dir");
    let log_path = dir.path().join("decisions.jsonl");
    let problem = create_solidity_array_dt_route_problem(true);
    let mut adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);

    let result = adaptive.try_solidity_array_dt_projection_route(None);

    assert!(
        result.is_none(),
        "transformed Unsafe should fall through instead of being accepted"
    );
    let log = std::fs::read_to_string(&log_path).expect("decision log should be written");
    let transformed_unsafe_entry = log
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("valid JSONL row"))
        .find(|entry| entry["result"] == "transformed_unsafe")
        .expect("route should log transformed_unsafe decision");
    assert_eq!(
        transformed_unsafe_entry["stage"],
        "solidity_array_dt_projection"
    );
    let gate_reason = transformed_unsafe_entry["gate_reason"]
        .as_str()
        .expect("gate_reason should be a string");
    assert!(
        gate_reason.contains("transformed_result=unsafe; validation=not_run"),
        "gate_reason should expose raw transformed result and skipped validation, got {gate_reason}"
    );
    assert_eq!(
        transformed_unsafe_entry["transformed_result"], "unsafe",
        "raw transformed result should be a first-class decision-log field"
    );
    assert_eq!(
        transformed_unsafe_entry["validation_status"], "not_run",
        "validation status should be a first-class decision-log field"
    );
    assert_eq!(
        transformed_unsafe_entry["unsafe_backtranslation_complete"], false,
        "transformed UNSAFE must remain fail-closed until original trace backtranslation is complete"
    );
    assert!(
        transformed_unsafe_entry["transform_memory"]
            .as_str()
            .expect("transform_memory should be a string")
            .contains("unsafe-demotion-required"),
        "transform memory should explain why UNSAFE cannot be promoted"
    );
}

#[test]
fn test_solidity_array_dt_projection_route_logs_safe_original_validation_and_memory() {
    let dir = tempfile::tempdir().expect("temp decision-log dir");
    let log_path = dir.path().join("decisions.jsonl");
    let problem = create_solidity_array_dt_route_problem(false);
    let mut adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);

    let result = adaptive.try_solidity_array_dt_projection_route(None);

    assert!(
        matches!(result, Some(PortfolioResult::Safe(_))),
        "route must only accept SAFE after original-clause validation"
    );
    let log = std::fs::read_to_string(&log_path).expect("decision log should be written");
    let entry: serde_json::Value =
        serde_json::from_str(log.lines().next().expect("one JSONL row")).expect("valid JSONL row");
    assert_eq!(entry["stage"], "solidity_array_dt_projection");
    assert_eq!(entry["result"], "safe");
    assert!(
        matches!(
            entry["validation_status"].as_str(),
            Some("accepted" | "refined_accepted")
        ),
        "SAFE route acceptance must record original validation status, got {entry}"
    );
    assert_eq!(
        entry["unsafe_backtranslation_complete"], false,
        "SAFE acceptance must not imply transformed UNSAFE witnesses are replayable"
    );
    let memory = entry["transform_memory"]
        .as_str()
        .expect("transform_memory should be a string");
    assert!(
        memory.contains("original-validation-on-safe"),
        "transform memory should preserve the SAFE validation obligation: {memory}"
    );
    assert!(
        memory.contains("observed-select-store-key-refinement"),
        "transform memory should preserve the array-key refinement obligation: {memory}"
    );
    assert!(
        entry["lemmas_learned"].is_u64() && entry["max_frame"].is_u64(),
        "route log should expose PDR counter fields for gate evidence"
    );
    assert!(
        entry["refinement_performed"].is_boolean(),
        "route log should expose whether observed-key refinement produced the accepted model"
    );
}

#[test]
fn test_solidity_array_dt_projection_route_logs_refined_counters() {
    let dir = tempfile::tempdir().expect("temp decision-log dir");
    let log_path = dir.path().join("decisions.jsonl");
    let mut adaptive = AdaptivePortfolio::new(create_simple_loop(), AdaptiveConfig::test_default());
    adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);

    adaptive.log_solidity_array_dt_attempt(
        Instant::now(),
        Duration::from_secs(2),
        &SolidityArrayDtProjectionStats::default(),
        "safe_refined",
        SolidityArrayDtValidationStatus::RefinedAccepted,
        &crate::transform::TransformMemoryReport::with_original_validation_obligations(
            "solidity_array_dt_projection",
            [crate::transform::TransformObligation::named(
                "observed-select-store-key-refinement",
            )],
        ),
        7,
        3,
    );

    let log = std::fs::read_to_string(&log_path).expect("decision log should be written");
    let entry: serde_json::Value =
        serde_json::from_str(log.lines().next().expect("one JSONL row")).expect("valid JSONL row");
    assert_eq!(entry["stage"], "solidity_array_dt_projection");
    assert_eq!(entry["result"], "safe");
    assert_eq!(entry["transformed_result"], "safe_refined");
    assert_eq!(entry["validation_status"], "refined_accepted");
    assert_eq!(entry["refinement_performed"], true);
    assert_eq!(entry["lemmas_learned"], 7);
    assert_eq!(entry["max_frame"], 3);
}

#[test]
fn test_solidity_array_dt_projection_refines_only_after_original_validation_failure() {
    let src = include_str!("adaptive.rs");
    let fn_start = src
        .find("fn try_solidity_array_dt_projection_route(")
        .expect("adaptive.rs should define the Solidity array-DT route");
    let fn_end = src[fn_start..]
        .find("fn try_array_const_key_cegar_route(")
        .map(|offset| fn_start + offset)
        .expect("Solidity array-DT route should precede array const-key route");
    let route_body = &src[fn_start..fn_end];

    let failed_gate = route_body
        .find("validation_status == SolidityArrayDtValidationStatus::Failed")
        .expect("SAFE validation failure should be a distinct refinement gate");
    let refinement_call = route_body
        .find("self.try_solidity_array_dt_observed_key_refinement(")
        .expect("route should retry with observed array keys after validation failure");
    assert!(
        failed_gate < refinement_call,
        "observed-key refinement must run only after original validation rejects the first SAFE"
    );
    assert!(
        route_body[refinement_call..].contains("SolidityArrayDtValidationStatus::RefinedAccepted"),
        "successful refinement should be recorded as refined_accepted instead of plain SAFE"
    );
    assert!(
        route_body[refinement_call..].contains("lemmas_learned = refined_safe.lemmas_learned")
            && route_body[refinement_call..].contains("max_frame = refined_safe.max_frame"),
        "successful refinement should log the refined PDR solve counters, not stale first-attempt counters"
    );
    assert!(
        route_body.contains("translated_safe.map(PortfolioResult::Safe)"),
        "failed validation with no accepted refinement must fall through as UNKNOWN/None"
    );
}

#[test]
fn test_solidity_array_dt_projection_route_logs_validation_verdicts_as_structured_fields() {
    for (validation_status, expected_result) in [
        (SolidityArrayDtValidationStatus::Failed, "validation_failed"),
        (SolidityArrayDtValidationStatus::Error, "validation_error"),
        (
            SolidityArrayDtValidationStatus::Timeout,
            "validation_timeout",
        ),
        (
            SolidityArrayDtValidationStatus::NoBudget,
            "validation_no_budget",
        ),
    ] {
        let dir = tempfile::tempdir().expect("temp decision-log dir");
        let log_path = dir.path().join("decisions.jsonl");
        let mut adaptive =
            AdaptivePortfolio::new(create_simple_loop(), AdaptiveConfig::test_default());
        adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);

        adaptive.log_solidity_array_dt_attempt(
            Instant::now(),
            Duration::from_secs(2),
            &SolidityArrayDtProjectionStats::default(),
            "safe",
            validation_status,
            &crate::transform::TransformMemoryReport::identity(),
            0,
            0,
        );

        let log = std::fs::read_to_string(&log_path).expect("decision log should be written");
        let entry: serde_json::Value =
            serde_json::from_str(log.lines().next().expect("one JSONL row"))
                .expect("valid JSONL row");
        assert_eq!(entry["result"], expected_result);
        assert_eq!(entry["transformed_result"], "safe");
        assert_eq!(entry["validation_status"], validation_status.as_str());
    }
}

#[test]
fn test_solidity_array_dt_projection_route_logs_no_budget_gate() {
    let dir = tempfile::tempdir().expect("temp decision-log dir");
    let log_path = dir.path().join("decisions.jsonl");
    let problem = create_solidity_array_dt_route_problem(false);
    let mut adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);

    let result = adaptive.try_solidity_array_dt_projection_route(Some(Instant::now()));

    assert!(result.is_none());
    let log = std::fs::read_to_string(&log_path).expect("decision log should be written");
    let entry: serde_json::Value =
        serde_json::from_str(log.lines().next().expect("one JSONL row")).expect("valid JSONL row");
    assert_eq!(entry["stage"], "solidity_array_dt_projection");
    assert_eq!(entry["gate_result"], false);
    assert_eq!(entry["result"], "skipped");
    assert_eq!(entry["gate_reason"], "no remaining budget");
}

#[test]
fn test_solidity_array_dt_route_step_budget_gate_is_preemptive() {
    assert!(
        !AdaptivePortfolio::solidity_array_dt_has_step_budget(
            Instant::now() + SOLIDITY_ARRAY_DT_ROUTE_MIN_STEP_BUDGET / 2
        ),
        "route should skip a new expensive step when less than the minimum step budget remains"
    );
    assert!(
        AdaptivePortfolio::solidity_array_dt_has_step_budget(
            Instant::now() + SOLIDITY_ARRAY_DT_ROUTE_MIN_STEP_BUDGET * 2
        ),
        "route should still run a step when a bounded minimum budget remains"
    );
}

#[test]
fn test_algebraic_prestage_budget_extends_pure_polynomial_but_stays_capped() {
    let input = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int))
  (=> (= y (* x x)) (Inv x y))))
(assert (forall ((x Int) (y Int))
  (=> (and (Inv x y) (> y 10)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("pure polynomial CHC should parse");
    let mut features = ProblemClassifier::classify(&problem);
    assert!(features.has_multiplication);
    assert!(!features.has_mod_div);
    assert!(!features.uses_arrays);
    assert!(!features.uses_real);

    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_secs(10)),
        Duration::from_secs(5),
        "short bounded runs can give polynomial synthesis up to half the budget"
    );
    // Sub-6s budgets used to re-raise to the 3s ALGEBRAIC_PRESTAGE_BUDGET floor and
    // then clamp to the caller budget, i.e. the pre-stage silently took 100% of the
    // wall (63% of a 5s CHC-COMP budget) before any engine ran. The half-budget cap
    // asserted above now applies at every scale.
    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_secs(1)),
        Duration::from_millis(500),
        "algebraic pre-stage must not exceed half a bounded caller budget"
    );
    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_millis(500)),
        Duration::from_millis(250),
        "sub-second bounded runs must not expand to the default algebraic budget"
    );
    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_secs(5000)),
        ALGEBRAIC_POLYNOMIAL_PRESTAGE_BUDGET_CAP,
        "CHC-COMP scale timeouts must not give arbitrary multiplication half the wall clock"
    );

    features.class = ProblemClass::MultiPredLinear;
    features.is_linear = true;
    features.has_cycles = false;
    features.num_predicates = 91;
    features.dag_depth = 89;
    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_secs(5000)),
        ALGEBRAIC_LARGE_ACYCLIC_BUDGET,
        "acyclic compiler DAGs below the old 128-node gate still need the constructive proof budget"
    );
    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_secs(20)),
        Duration::from_secs(10),
        "large acyclic extension must still respect the caller's remaining budget"
    );

    features.class = ProblemClass::Trivial;
    features.is_linear = true;
    features.has_cycles = false;
    features.num_predicates = 1;
    features.dag_depth = 0;
    features.uses_real = true;
    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_secs(5000)),
        ALGEBRAIC_PRESTAGE_BUDGET,
        "Real/LRA validation keeps the strict default pre-stage budget"
    );

    features.uses_real = false;
    features.has_mod_div = true;
    assert_eq!(
        algebraic_prestage_budget(&features, Duration::from_secs(5000)),
        ALGEBRAIC_PRESTAGE_BUDGET,
        "mod/div cases keep the strict default pre-stage budget"
    );
}

#[test]
fn test_finalize_verified_result_rejects_invalid_unsafe_when_validate_disabled() {
    let problem = create_simple_loop();
    let fake_cex = empty_counterexample_for_first_predicate(&problem, 10);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Unsafe(fake_cex),
        ValidationEvidence::FullVerification,
    );
    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "verified adaptive API must reject spurious Unsafe even when validate=false"
    );
}

#[test]
fn test_finalize_verified_result_accepts_algebraic_closed_form_safe_model() {
    let problem = create_simple_loop();
    let model = true_model_for_first_predicate(&problem);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Safe(model),
        ValidationEvidence::AlgebraicClosedForm,
    );

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "algebraic closed-form evidence should be accepted for complete Safe models"
    );
}

#[test]
fn test_finalize_verified_result_demotes_empty_algebraic_closed_form_safe_model() {
    let problem = create_simple_loop();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Safe(InvariantModel::new()),
        ValidationEvidence::AlgebraicClosedForm,
    );

    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "algebraic closed-form evidence must still require predicate interpretations"
    );
}

#[test]
fn test_finalize_verified_result_rejects_safe_with_unsafe_evidence() {
    let problem = create_simple_loop();
    let model = true_model_for_first_predicate(&problem);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Safe(model),
        ValidationEvidence::BmcCounterexample,
    );

    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "Safe results must not pass finalization with counterexample-only evidence"
    );
}

#[test]
fn test_finalize_verified_result_accepts_reachable_unsafe_when_validate_disabled() {
    let problem = create_unsafe_simple_loop();
    let reachable_cex = empty_counterexample_for_first_predicate(&problem, 5);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result(
        PortfolioResult::Unsafe(reachable_cex),
        ValidationEvidence::FullVerification,
    );
    assert!(
        matches!(result, VerifiedChcResult::Unsafe(_)),
        "verified adaptive API must preserve a reachable Unsafe after fresh validation"
    );
}

#[test]
fn test_finalize_verified_result_demotes_reachable_unsafe_when_final_budget_expired() {
    let problem = create_unsafe_simple_loop();
    let reachable_cex = empty_counterexample_for_first_predicate(&problem, 5);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result_with_deadline(
        PortfolioResult::Unsafe(reachable_cex),
        ValidationEvidence::FullVerification,
        Some(Instant::now()),
    );

    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "final Unsafe validation must fail closed when the caller budget is already expired"
    );
}

#[test]
fn test_finalize_verified_result_demotes_bmc_unsafe_when_final_budget_expired() {
    let problem = create_unsafe_simple_loop();
    let reachable_cex = empty_counterexample_for_first_predicate(&problem, 5);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.finalize_verified_result_with_deadline(
        PortfolioResult::Unsafe(reachable_cex),
        ValidationEvidence::BmcCounterexample,
        Some(Instant::now()),
    );

    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "BMC source evidence must still fail closed when original trace replay has no budget"
    );
}

#[test]
fn test_final_validation_demotion_diagnostics_are_bounded_and_preserve_source_evidence() {
    let problem = create_unsafe_simple_loop();
    let cex = empty_counterexample_for_first_predicate(&problem, 5);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let diagnostics = adaptive.format_final_validation_demotion_diagnostics(
        "unsafe_rejected_by_final_verification",
        &ValidationEvidence::BmcCounterexample,
        &cex,
    );

    assert!(
        diagnostics.contains("stage=unsafe_rejected_by_final_verification"),
        "diagnostics should identify the demotion stage: {diagnostics}"
    );
    assert!(
        diagnostics.contains("source_evidence=BmcCounterexample"),
        "diagnostics should preserve the original evidence source: {diagnostics}"
    );
    assert!(
        diagnostics.contains("depth=6"),
        "diagnostics should report the counterexample depth: {diagnostics}"
    );
    assert!(
        diagnostics.contains("head=[0:Inv/vars=0, 1:Inv/vars=0, 2:Inv/vars=0]"),
        "diagnostics should keep a bounded head summary: {diagnostics}"
    );
    assert!(
        diagnostics.contains("tail=5:Inv/vars=0"),
        "diagnostics should include the tail step summary: {diagnostics}"
    );
    assert!(
        diagnostics.contains("omitted_steps=3"),
        "diagnostics should avoid dumping the full trace: {diagnostics}"
    );
}

#[test]
fn test_finalize_verified_result_keeps_final_demotion_diagnostics_hooked_up() {
    let src = include_str!("adaptive.rs");
    let fn_start = src
        .find("fn finalize_verified_result(")
        .expect("adaptive.rs should define finalize_verified_result");
    let fn_end = src[fn_start..]
        .find("/// Returns the remaining time")
        .map(|offset| fn_start + offset)
        .expect("finalize_verified_result should be followed by remaining_budget");
    let fn_body = &src[fn_start..fn_end];

    assert_eq!(
        fn_body
            .matches("emit_final_validation_demotion_diagnostics(")
            .count(),
        1,
        "finalize_verified_result should emit diagnostics when final Unsafe replay fails"
    );
    assert!(
        fn_body.contains("unsafe_rejected_by_final_verification"),
        "fresh-verification demotions should keep their diagnostic stage label"
    );
}

#[test]
fn test_bv_simple_loop_uses_native_direct_route() {
    let problem = create_identity_simple_loop(ChcSort::BitVec(8));
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(adaptive.use_bv_native_direct_route(&features));
}

#[test]
#[timeout(10000)]
fn test_deterministic_bv_bool_transition_route_validates_bmc_witness() {
    let problem = create_deterministic_bv_bool_unsafe_loop();
    let mut adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let dir = tempfile::tempdir().expect("temp decision-log dir");
    let log_path = dir.path().join("decision.jsonl");
    adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    let (result, evidence) = adaptive
        .try_deterministic_bv_bool_transition_route(Duration::from_secs(3))
        .expect("deterministic BV/Bool route should apply");

    let PortfolioResult::Unsafe(cex) = result else {
        panic!("route should accept only the source-validated BMC witness, got {result:?}");
    };
    assert!(
        cex.witness.is_some(),
        "deterministic route must not accept witness-less existential traces"
    );
    assert!(
        matches!(evidence, ValidationEvidence::CounterexampleVerification),
        "unsafe result must carry counterexample-validation evidence"
    );
    let stats = adaptive.statistics();
    assert_eq!(stats.deterministic_bv_bool_transition_attempts, 1);
    assert_eq!(stats.deterministic_bv_bool_transition_recognized, 1);
    assert_eq!(
        stats.deterministic_bv_bool_transition_bmc_unsafe_validated,
        1
    );
    assert_eq!(
        stats.deterministic_bv_bool_transition_validation_rejections,
        0
    );

    let entries = read_decision_log_entries(&log_path);
    let route_entry = entries
        .iter()
        .find(|entry| {
            entry["stage"] == "deterministic_bv_bool_transition"
                && entry["result"] == "bmc_unsafe_validated"
        })
        .expect("deterministic BMC route should log the accepted result");
    assert!(
        route_entry["bmc_checks"].as_u64().unwrap_or(0) > 0,
        "decision log should include BMC check counters, got {route_entry:?}"
    );
}

#[test]
#[timeout(10000)]
fn test_bv_bool_control_reachability_route_validates_safe_invariant() {
    let problem = create_bv_bool_control_safe_loop();
    let mut adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let dir = tempfile::tempdir().expect("temp decision-log dir");
    let log_path = dir.path().join("decision.jsonl");
    adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);

    let (result, evidence) = adaptive
        .try_deterministic_bv_bool_transition_route(Duration::from_secs(3))
        .expect("BV Boolean-control route should prove the disjunctive safe loop");

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "route should accept only the source-validated control invariant, got {result:?}"
    );
    assert!(
        matches!(evidence, ValidationEvidence::FullVerification),
        "safe result must carry full-validation evidence"
    );
    let stats = adaptive.statistics();
    assert_eq!(stats.deterministic_bv_bool_transition_attempts, 1);
    assert_eq!(stats.deterministic_bv_bool_transition_recognized, 1);
    assert_eq!(
        stats.deterministic_bv_bool_transition_bool_control_safe_validated,
        1
    );

    let entries = read_decision_log_entries(&log_path);
    let route_entry = entries
        .iter()
        .find(|entry| {
            entry["stage"] == "deterministic_bv_bool_transition"
                && entry["result"] == "bool_control_safe_validated"
        })
        .expect("deterministic SAFE route should log the validated result");
    let gate_reason = route_entry["gate_reason"]
        .as_str()
        .expect("gate_reason should be a string");
    assert!(
        gate_reason.contains("bool_vars=")
            && gate_reason.contains("state_bits=")
            && gate_reason.contains("assignments="),
        "SAFE route log should expose deterministic route counters, got {gate_reason}"
    );
}

#[test]
#[timeout(10000)]
fn test_lia_farkas_pdr_route_validates_safe_model_on_original() {
    let problem = create_simple_loop();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    let (result, evidence) = adaptive
        .try_lia_farkas_pdr_route(&features, None)
        .expect("LIA/Farkas route should apply to the simple Int loop");

    assert!(
        matches!(result, PortfolioResult::Safe(_)),
        "LIA/Farkas route should return the source-validated invariant, got {result:?}"
    );
    assert!(
        matches!(evidence, ValidationEvidence::FullVerification),
        "safe result must carry full original-clause verification evidence"
    );
}

#[test]
#[timeout(10000)]
fn test_lia_farkas_pdr_route_logs_score_bearing_counters() {
    let dir = tempfile::tempdir().expect("temp decision-log dir");
    let log_path = dir.path().join("decisions.jsonl");
    let problem = create_simple_loop();
    let mut adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    adaptive.decision_log = DecisionLog::from_path_for_test(&log_path);
    let features = adaptive.features();

    let (result, _) = adaptive
        .try_lia_farkas_pdr_route(&features, None)
        .expect("LIA/Farkas route should apply to the simple Int loop");

    assert!(matches!(result, PortfolioResult::Safe(_)));
    let log = std::fs::read_to_string(&log_path).expect("decision log should be written");
    let entry = log
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("valid JSONL row"))
        .find(|entry| entry["stage"] == "lia_farkas_pdr")
        .expect("route should log a LIA/Farkas decision");

    assert_eq!(entry["profile_name"], "lia_farkas");
    assert_eq!(entry["profile_enabled"], true);
    assert!(
        entry["enabled_template_surfaces"]
            .as_u64()
            .is_some_and(|count| count > 0),
        "route should report enabled arithmetic template surfaces, got {entry}"
    );
    assert!(
        entry["template_generation_surfaces"]
            .as_u64()
            .zip(entry["enabled_template_surfaces"].as_u64())
            .is_some_and(|(generated, enabled)| generated <= enabled),
        "generated template surfaces should not exceed enabled surfaces, got {entry}"
    );
    assert!(entry["templates_generated"].as_u64().is_some());
    assert!(entry["template_generation_checks"].as_u64().is_some());
    assert!(entry["farkas_checks"].as_u64().is_some());
    assert!(entry["accepted_lemmas"].as_u64().is_some());
    assert!(entry["rejected_lemmas"].as_u64().is_some());
    assert_eq!(entry["original_validation_required"], true);
    assert_eq!(entry["original_safe_validation"], true);
    assert_eq!(entry["route_result"], "safe");
    assert_eq!(entry["route_validation_failures"], 0);
}

#[test]
fn test_lia_farkas_pdr_route_quarantines_real_lra() {
    let problem = create_identity_simple_loop(ChcSort::Real);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(features.uses_real);
    assert!(
        adaptive
            .try_lia_farkas_pdr_route(&features, None)
            .is_none(),
        "LIA/Farkas PDR promotion must stay quarantined from Real/LRA until wrong=0 evidence exists"
    );
}

#[test]
#[timeout(10000)]
fn test_lia_farkas_pdr_route_validates_unsafe_trace_on_original() {
    let problem = create_unsafe_simple_loop();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    let (result, evidence) = adaptive
        .try_lia_farkas_pdr_route(&features, None)
        .expect("LIA/Farkas route should apply to the unsafe Int loop");

    assert!(
        matches!(result, PortfolioResult::Unsafe(_)),
        "UNSAFE route result must survive original trace replay, got {result:?}"
    );
    assert!(
        matches!(evidence, ValidationEvidence::CounterexampleVerification),
        "UNSAFE route result must carry counterexample-validation evidence"
    );
}

#[test]
fn test_bv_native_direct_route_requires_non_array_non_real_bv_simple_loop() {
    let int_problem = create_identity_simple_loop(ChcSort::Int);
    let int_adaptive = AdaptivePortfolio::new(int_problem, AdaptiveConfig::test_default());
    let int_features = int_adaptive.features();
    assert_eq!(int_features.class, ProblemClass::SimpleLoop);
    assert!(!int_adaptive.use_bv_native_direct_route(&int_features));

    let array_problem = create_identity_simple_loop(ChcSort::Array(
        Box::new(ChcSort::Int),
        Box::new(ChcSort::BitVec(8)),
    ));
    let array_adaptive = AdaptivePortfolio::new(array_problem, AdaptiveConfig::test_default());
    let array_features = array_adaptive.features();
    assert_eq!(array_features.class, ProblemClass::SimpleLoop);
    assert!(array_features.uses_arrays);
    assert!(!array_adaptive.use_bv_native_direct_route(&array_features));

    let real_problem = create_identity_simple_loop(ChcSort::Real);
    let real_adaptive = AdaptivePortfolio::new(real_problem, AdaptiveConfig::test_default());
    let real_features = real_adaptive.features();
    assert_eq!(real_features.class, ProblemClass::SimpleLoop);
    assert!(real_features.uses_real);
    assert!(!real_adaptive.use_bv_native_direct_route(&real_features));
}

#[test]
fn test_real_simple_loop_dispatch_uses_learned_real_route() {
    let src = include_str!("adaptive.rs");
    let dispatch_start = src
        .find("let (result, evidence) = match features.class {")
        .expect("adaptive dispatcher should match on problem class");
    let dispatch = &src[dispatch_start..];
    let simple_loop_start = dispatch
        .find("ProblemClass::SimpleLoop if features.uses_real")
        .expect("real simple loops should have a dedicated dispatch arm");
    let real_simple_loop_arm = &dispatch[simple_loop_start..];
    let arm_end = real_simple_loop_arm
        .find("ProblemClass::SimpleLoop =>")
        .expect("real simple-loop arm should precede the generic simple-loop arm");
    let real_simple_loop_arm = &real_simple_loop_arm[..arm_end];

    assert!(
        real_simple_loop_arm.contains("self.solve_with_learned_selection(deadline)"),
        "real simple loops should use the selector's LRA/mixed arithmetic route"
    );
    assert!(
        real_simple_loop_arm.contains("ValidationEvidence::FullVerification"),
        "selector portfolio results must keep the portfolio validation evidence"
    );
    assert!(
        !real_simple_loop_arm.contains("try_lia_farkas_pdr_route"),
        "Real/LRA simple loops must not enter the quarantined LIA/Farkas route"
    );
    assert!(
        !real_simple_loop_arm.contains("try_dual_cas_lra_phase_invariant"),
        "Real/LRA simple loops must not promote the quarantined dual-CAS route by default"
    );
}

#[test]
fn test_mixed_lia_lra_cruise_route_is_env_quarantined() {
    let src = include_str!("adaptive.rs");
    let call = "self.try_cruise_controller_mixed_phase_invariant(&features, deadline)";
    let call_start = src
        .find(call)
        .expect("adaptive dispatcher should contain the mixed LIA/LRA cruise route call");
    let prefix = &src[..call_start];
    let guard_start = prefix
        .rfind("std::env::var_os(REAL_LRA_PROMOTION_ENV).is_some()")
        .expect("mixed LIA/LRA cruise route should be behind the Real/LRA promotion env gate");
    assert!(
        call_start - guard_start < 160,
        "mixed LIA/LRA cruise route call should stay directly tied to the env quarantine gate"
    );
}

#[test]
fn test_arithmetic_dispatch_tries_lia_farkas_route_before_fallbacks() {
    let src = include_str!("adaptive.rs");
    let dispatch_start = src
        .find("let (result, evidence) = match features.class {")
        .expect("adaptive dispatcher should match on problem class");
    let dispatch = &src[dispatch_start..];

    let simple_loop_start = dispatch
        .find("ProblemClass::SimpleLoop =>")
        .expect("generic simple-loop arm should exist");
    let simple_loop_arm = &dispatch[simple_loop_start..];
    let lia_route = simple_loop_arm
        .find("self.try_lia_farkas_pdr_route(&features, deadline)")
        .expect("simple-loop arm should try the LIA/Farkas route");
    let fallback = simple_loop_arm
        .find("self.solve_simple_loop_with_evidence(&features, deadline)")
        .expect("simple-loop arm should keep the existing fallback");
    assert!(
        lia_route < fallback,
        "LIA/Farkas route should run before generic simple-loop fallback"
    );

    let multi_pred_start = dispatch
        .find("ProblemClass::MultiPredLinear =>")
        .expect("multi-predicate linear arm should exist");
    let multi_pred_arm = &dispatch[multi_pred_start..];
    assert!(
        multi_pred_arm.contains("self.try_lia_farkas_pdr_route(&features, deadline)")
            && multi_pred_arm.contains("self.solve_multi_pred_linear(&features, deadline)"),
        "multi-predicate linear dispatch should try LIA/Farkas before the existing fallback"
    );
}

#[test]
#[timeout(5000)]
fn test_dual_cas_lra_phase_invariant_validates_on_nonatomic_inc_cas_shape() {
    let smt = r#"
(set-logic HORN)
(declare-fun |invariant| ( Bool Bool Real Real Real Real Real Real Real ) Bool)
(assert
  (forall ( (A Bool) (B Bool) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) )
    (=>
      (and (= H 0.0) (= G 0.0) (= F 0.0) (= E 0.0) (= D 0.0)
           (= C 0.0) (not B) (not A) (= I 0.0))
      (invariant A B C D E F G H I))))
(assert
  (forall ( (A Bool) (B Bool) (C Bool) (D Bool) (E Real) (F Real) (G Real)
            (H Real) (I Real) (J Real) (K Real) (L Real) (M Real) (N Real)
            (O Real) (P Real) (Q Real) (R Real) )
    (=>
      (and
        (invariant A C E G I K M O Q)
        (let ((a!1 (= N (to_real (ite (= Q I) 2 3))))
              (a!3 (= P (to_real (ite (= Q K) 2 3)))))
        (let ((a!2 (or (and (= M 0.0) (= N 1.0) (= R Q) (= F (+ 1.0 Q)) (= J Q) (= B A))
                       (and (= M 1.0) a!1 (= R Q) (= F E) (= J I) (= B A))
                       (and B (= M 2.0) (= N 3.0) (= R E) (= F E) (= J I))
                       (and (= M 3.0) (= N M) (= R Q) (= F E) (= J I) (= B A))))
              (a!4 (or (and (= L Q) (= O 0.0) (= P 1.0) (= R Q) (= H (+ 1.0 Q)) (= D C))
                       (and (= L K) (= O 1.0) a!3 (= R Q) (= H G) (= D C))
                       (and D (= L K) (= O 2.0) (= P 3.0) (= R G) (= H G))
                       (and (= L K) (= O 3.0) (= P O) (= R Q) (= H G) (= D C)))))
          (or (and a!2 (= L K) (= P O) (= H G) (= D C))
              (and a!4 (= N M) (= F E) (= J I) (= B A))))))
      (invariant B D F H J L N P R))))
(assert
  (forall ( (A Bool) (B Bool) (C Real) (D Real) (E Real) (F Real) (G Real) (H Real) (I Real) )
    (=>
      (and (invariant A B C D E F G H I) (or A B) (<= I 0.0))
      false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt).expect("dual-CAS LRA fixture parses");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(3),
            ..AdaptiveConfig::test_default()
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(features.uses_real);
    assert!(matches!(
        adaptive.try_dual_cas_lra_phase_invariant(&features),
        Some(PortfolioResult::Safe(_))
    ));
}

#[test]
fn test_adaptive_array_bv_safe_simple_loop_classification_and_portfolio_shape() {
    // Verify that BV-indexed array problems are classified correctly and
    // routed to the array-safe portfolio (PDR + negated-eq PDR + BMC, no
    // TPA/Kind/TRL). Solving BV-indexed arrays requires SMT-level array
    // reasoning that is too slow in debug mode for a solve assertion.
    // Release-mode benchmark tests cover the end-to-end solve.
    let problem = ChcParser::parse(include_str!("../../../benchmarks/chc/array_bv_safe.smt2"))
        .expect("array_bv_safe benchmark should parse");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(10),
            ..AdaptiveConfig::test_default()
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(features.uses_arrays);

    // Verify the portfolio config excludes unsupported engines.
    let config = adaptive.simple_loop_array_portfolio_config(Duration::from_secs(10));
    for engine in &config.engines {
        assert!(
            !matches!(
                engine,
                EngineConfig::Kind(_) | EngineConfig::Tpa(_) | EngineConfig::Trl(_)
            ),
            "array-safe portfolio must not include Kind/TPA/TRL, found: {}",
            engine.name()
        );
    }
    // Must include PDR (array MBP) and BMC. #8734 temporarily excluded BMC
    // from this lane, but the underlying SMT array-model unsoundness (#8745)
    // is fixed on current HEAD and #8822 removed the temporary downgrade.
    let has_pdr = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::Pdr(_)));
    let has_bmc = config
        .engines
        .iter()
        .any(|e| matches!(e, EngineConfig::Bmc(_)));
    assert!(has_pdr, "array-safe portfolio must include PDR");
    assert!(
        has_bmc,
        "array-safe portfolio must include BMC again now that #8734/#8745 are fixed"
    );
}

#[test]
fn test_adaptive_bv_simple_loop_triple_lane_solves_safe_problem() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ((_ BitVec 8)) Bool)

(assert (forall ((x (_ BitVec 8)))
  (=> (= x #x00) (inv x))))

(assert (forall ((x (_ BitVec 8)) (xp (_ BitVec 8)))
  (=> (and (inv x) (bvule x #x03) (= xp (bvadd x #x01)))
      (inv xp))))

(assert (forall ((x (_ BitVec 8)))
  (=> (and (inv x) (bvule #x05 x))
      false)))

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("BV simple-loop benchmark should parse");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(5),
            ..AdaptiveConfig::test_default()
        },
    );
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    // Helper recognizes BV direct-route shape, but the direct route is
    // disabled (see adaptive.rs:548-567). Routing goes through triple-lane
    // (BvToBool + BvToInt + BV-native) which solves more BV benchmarks
    // (9/30 vs 0/30 per W1:3265 A/B test). W1:3285 confirmed direct route
    // cannot solve nested4 either.
    assert!(adaptive.use_bv_native_direct_route(&features));
    assert!(
        matches!(adaptive.solve(), VerifiedChcResult::Safe(_)),
        "BV triple-lane should solve the tiny BV simple-loop benchmark"
    );
}

/// Verify the nested4 benchmark shape selects the BV-native direct route.
/// nested4 is the canonical #5877 regression canary: 1 predicate (3 Bool + 5 BV32),
/// 3 clauses (init, transition, query), classified as SimpleLoop.
#[test]
fn test_bv_native_direct_route_selected_for_nested4_shape() {
    // nested4 shape: 1 predicate with mixed Bool+BV32 args, 3 clauses, SimpleLoop
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate(
        "state",
        vec![
            ChcSort::Bool,
            ChcSort::Bool,
            ChcSort::Bool,
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
        ],
    );
    let args: Vec<ChcExpr> = (0..8)
        .map(|i| {
            ChcExpr::var(ChcVar::new(
                &format!("x{i}"),
                if i < 3 {
                    ChcSort::Bool
                } else {
                    ChcSort::BitVec(32)
                },
            ))
        })
        .collect();

    // Init clause
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, args.clone()),
    ));

    // Transition clause
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, args.clone())], None),
        ClauseHead::Predicate(inv, args.clone()),
    ));

    // Query clause
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, args)], None),
        ClauseHead::False,
    ));

    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(features.is_single_predicate);
    assert_eq!(features.num_transitions, 1);
    assert!(!features.uses_arrays);
    assert!(!features.uses_real);
    assert!(
        adaptive.use_bv_native_direct_route(&features),
        "nested4-shape problem should select the BV-native direct route"
    );
}

#[test]
fn test_skip_classification_uses_default() {
    let problem = create_simple_loop();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        skip_classification: true,
        ..AdaptiveConfig::test_default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);

    // Should still solve correctly, just using default portfolio
    let result = adaptive.solve();
    match result {
        VerifiedChcResult::Safe(_) => {}
        VerifiedChcResult::Unknown(_) => panic!(
            "Adaptive portfolio (skip_classification) returned Unknown on a trivial safe loop."
        ),
        VerifiedChcResult::Unsafe(_) => {
            panic!("Problem is safe");
        }
    }
}

/// Create an entry-exit-only SAFE problem
/// x > 5 /\ x < 3 => false (constraint is UNSAT)
fn create_entry_exit_only_safe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(5)),
            ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(3)),
        )),
        ClauseHead::False,
    ));

    problem
}

/// Create an entry-exit-only UNSAFE problem
/// x > 0 /\ x < 10 => false (constraint is SAT)
fn create_entry_exit_only_unsafe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let x = ChcVar::new("x", ChcSort::Int);

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
fn test_entry_exit_only_classification() {
    let safe = create_entry_exit_only_safe();
    let adaptive = AdaptivePortfolio::new(safe, AdaptiveConfig::test_default());
    assert_eq!(adaptive.features().class, ProblemClass::EntryExitOnly);

    let unsafe_problem = create_entry_exit_only_unsafe();
    let adaptive = AdaptivePortfolio::new(unsafe_problem, AdaptiveConfig::test_default());
    assert_eq!(adaptive.features().class, ProblemClass::EntryExitOnly);
}

#[test]
fn test_entry_exit_only_safe() {
    let problem = create_entry_exit_only_safe();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::test_default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: constraint is UNSAT, so problem is safe
        }
        other => {
            panic!("Expected Safe, got {other:?}");
        }
    }
}

#[test]
fn test_entry_exit_only_unsafe() {
    let problem = create_entry_exit_only_unsafe();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::test_default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    match result {
        VerifiedChcResult::Unsafe(_) => {
            // Expected: constraint is SAT, so problem is unsafe
        }
        other => {
            panic!("Expected Unsafe, got {other:?}");
        }
    }
}

/// Create a multi-predicate problem with two predicates.
///
/// Models: x >= 0, y >= 0, x + y increment, safe if x + y <= 20
/// Predicates: Inv1(x), Inv2(y)
///
/// Init: x = 0 => Inv1(x)
///       y = 0 => Inv2(y)
/// Trans: Inv1(x) /\ x < 10 => Inv1(x + 1)
///        Inv2(y) /\ y < 10 => Inv2(y + 1)
/// Query: Inv1(x) /\ Inv2(y) /\ x + y > 20 => false
fn create_multi_predicate_safe() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let inv1 = problem.declare_predicate("Inv1", vec![ChcSort::Int]);
    let inv2 = problem.declare_predicate("Inv2", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Init: x = 0 => Inv1(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv1, vec![ChcExpr::var(x.clone())]),
    ));

    // Init: y = 0 => Inv2(y)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv2, vec![ChcExpr::var(y.clone())]),
    ));

    // Trans: Inv1(x) /\ x < 10 => Inv1(x + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv1, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv1,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    // Trans: Inv2(y) /\ y < 10 => Inv2(y + 1)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv2, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(10))),
        ),
        ClauseHead::Predicate(
            inv2,
            vec![ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1))],
        ),
    ));

    // Query: Inv1(x) /\ Inv2(y) /\ x + y > 20 => false
    // Safe because max(x) = 10, max(y) = 10, so x + y <= 20
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![
                (inv1, vec![ChcExpr::var(x.clone())]),
                (inv2, vec![ChcExpr::var(y.clone())]),
            ],
            Some(ChcExpr::gt(
                ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y)),
                ChcExpr::int(20),
            )),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_two_predicate_gate_problem(constraint: Option<ChcExpr>) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], constraint),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
        ),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(10))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_four_predicate_gate_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let predicates: Vec<_> = (0..4)
        .map(|i| problem.declare_predicate(&format!("P{i}"), vec![ChcSort::Int]))
        .collect();
    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(predicates[0], vec![ChcExpr::int(0)]),
    ));

    for window in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(window[0], vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(10))),
            ),
            ClauseHead::Predicate(
                window[1],
                vec![ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1))],
            ),
        ));
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(predicates[3], vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(x), ChcExpr::int(20))),
        ),
        ClauseHead::False,
    ));

    problem
}

fn create_four_predicate_array_gate_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::BitVec(8)));
    let predicates: Vec<_> = (0..4)
        .map(|i| problem.declare_predicate(&format!("AP{i}"), vec![array_sort.clone()]))
        .collect();
    let arr = ChcVar::new("arr", array_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(predicates[0], vec![ChcExpr::var(arr.clone())]),
    ));

    for window in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(window[0], vec![ChcExpr::var(arr.clone())])], None),
            ClauseHead::Predicate(window[1], vec![ChcExpr::var(arr.clone())]),
        ));
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(predicates[3], vec![ChcExpr::var(arr)])], None),
        ClauseHead::False,
    ));

    problem
}

fn create_large_bv_array_acyclic_gate_problem(num_predicates: usize) -> ChcProblem {
    assert!(num_predicates >= 2);

    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8)));
    let predicates: Vec<_> = (0..num_predicates)
        .map(|i| problem.declare_predicate(&format!("BAP{i}"), vec![array_sort.clone()]))
        .collect();
    let arr = ChcVar::new("arr", array_sort);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(predicates[0], vec![ChcExpr::var(arr.clone())]),
    ));

    for window in predicates.windows(2) {
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(window[0], vec![ChcExpr::var(arr.clone())])], None),
            ClauseHead::Predicate(window[1], vec![ChcExpr::var(arr.clone())]),
        ));
    }

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                *predicates.last().expect("non-empty"),
                vec![ChcExpr::var(arr)],
            )],
            None,
        ),
        ClauseHead::False,
    ));

    problem
}

#[test]
fn test_multi_pred_classification() {
    let problem = create_multi_predicate_safe();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    // Should be classified as multi-predicate (either Linear or Complex)
    assert!(
        matches!(
            features.class,
            ProblemClass::MultiPredLinear | ProblemClass::MultiPredComplex
        ),
        "Expected multi-predicate class, got {:?}",
        features.class
    );
}

/// Test that multi-predicate paths have failure-guided retry capability.
///
/// Part of #2082 - this test verifies the failure retry code path is reachable.
/// The retry mechanism may or may not trigger depending on whether the portfolio
/// returns Unknown, but the code structure is exercised.
#[test]
fn test_multi_pred_failure_retry_path() {
    let problem = create_multi_predicate_safe();
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(10),
        verbose: false,
        skip_classification: false,
        ..AdaptiveConfig::test_default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    // Multi-predicate benchmark can still return Unknown.
    // VerifiedChcResult maps NotApplicable → Unknown, so no NotApplicable arm needed.
    match result {
        VerifiedChcResult::Safe(_) => {
            // Expected: problem is safe, found invariant
        }
        VerifiedChcResult::Unknown(_) => {
            // Acceptable: conservative while exercising retry logic.
        }
        VerifiedChcResult::Unsafe(_) => {
            panic!("Problem is safe, should not return Unsafe");
        }
    }
}

#[test]
fn test_multi_pred_linear_portfolio_uses_single_pdkind_engine() {
    let problem = create_multi_predicate_safe();
    let features = ProblemClassifier::classify(&problem);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let config = adaptive.multi_pred_linear_portfolio_config(
        PdrConfig::default(),
        PdrConfig::portfolio_variant_with_splits(),
        &features,
    );

    let kind_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Kind(_)))
        .count();
    let pdr_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Pdr(_)))
        .count();
    let tpa_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Tpa(_)))
        .count();
    let dar_count = config
        .engines
        .iter()
        .filter(|engine| matches!(engine, EngineConfig::Dar(_)))
        .count();

    // #6500: Kind via SingleLoop replaced the no-op PDKind for non-DT problems.
    assert_eq!(
        kind_count, 1,
        "multi-pred linear should run one Kind (#6500)"
    );
    assert_eq!(
        pdr_count, 2,
        "multi-pred linear should keep two PDR variants"
    );
    assert_eq!(tpa_count, 1, "multi-pred linear should include one TPA");
    assert_eq!(
        dar_count, 0,
        "multi-pred linear should not schedule single-predicate DAR"
    );
}

#[test]
fn test_multi_pred_linear_capped_roster_preserves_engine_diversity() {
    let problem = create_multi_predicate_safe();
    let features = ProblemClassifier::classify(&problem);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let config = adaptive.multi_pred_linear_portfolio_config(
        PdrConfig::default(),
        PdrConfig::portfolio_variant_with_splits(),
        &features,
    );

    let capped_names: Vec<_> = config
        .engines
        .iter()
        .take(adaptive.config.max_engines.expect("test config has a cap"))
        .map(EngineConfig::name)
        .collect();
    assert_eq!(
        capped_names,
        ["PDR", "TPA", "Kind"],
        "the three-engine test roster must retain complementary MultiPredLinear lanes"
    );
    assert!(
        matches!(config.engines.get(3), Some(EngineConfig::Pdr(_))),
        "the spacer PDR variant must remain available to uncapped production runs"
    );
}

#[test]
fn test_multi_pred_linear_direct_kind_uses_full_verification_evidence_source_regression() {
    let src = include_str!("adaptive_multi_pred.rs");
    let fn_start = src
        .find("pub(super) fn solve_multi_pred_linear(")
        .expect("adaptive_multi_pred.rs should define solve_multi_pred_linear");
    let fn_body = &src[fn_start..];
    let kind_start = fn_body
        .find("if let Some(result) = self.try_kind(kind_budget) {")
        .expect("MultiPredLinear path should try direct Kind before fallback");
    let kind_return = fn_body[kind_start..]
        .find("return (result, evidence);")
        .map(|offset| kind_start + offset + "return (result, evidence);".len())
        .expect("direct Kind branch should return the computed evidence");
    let kind_branch = &fn_body[kind_start..kind_return];

    assert!(
        kind_branch.contains("ValidationEvidence::CounterexampleVerification"),
        "direct Kind branch must preserve explicit counterexample evidence on MultiPredLinear"
    );
    assert!(
        kind_branch.contains("ValidationEvidence::FullVerification"),
        "direct adaptive Kind on MultiPredLinear must report original-clause verification evidence for Safe results"
    );
    assert!(
        !kind_branch.contains("ValidationEvidence::QueryOnly"),
        "direct adaptive Kind branch on MultiPredLinear must not report query-only evidence"
    );
}

#[test]
fn test_direct_kind_probe_uses_budget_cancellation_token() {
    let src = include_str!("adaptive_engines.rs");
    let fn_start = src
        .find("pub(crate) fn try_kind(&self, budget: Duration)")
        .expect("adaptive_engines.rs should define try_kind");
    let fn_body = &src[fn_start..];
    let config_start = fn_body
        .find("let kind_config = KindConfig::with_engine_config(")
        .expect("try_kind should construct KindConfig");
    let config_end = fn_body[config_start..]
        .find(");")
        .map(|offset| config_start + offset)
        .expect("KindConfig construction should terminate");
    let prefix = &fn_body[..config_end];

    assert!(
        prefix.contains("let cancellation = self.cancellation_token.child();"),
        "direct Kind probes should create a lane cancellation token linked to the portfolio handle (item 5)"
    );
    // The cancel timer is extended by KIND_VALIDATION_GRACE so a proof found
    // at the probe-budget edge can still be validated instead of dropped;
    // the SEARCH stays bounded by `budget` via KindConfig::total_timeout.
    assert!(
        prefix
            .contains("let _timeout_guard = cancellation.cancel_after(budget + validation_grace);"),
        "direct Kind probes should cancel at the advertised budget plus validation grace"
    );
    assert!(
        prefix.contains("Some(cancellation)"),
        "direct Kind probes should pass the budget cancellation token into KindConfig"
    );
    assert!(
        fn_body.contains(".with_validation_grace(validation_grace)"),
        "direct Kind probes should grant proof-validation grace to KindConfig"
    );
}

#[test]
fn test_direct_kind_probe_splits_single_pred_lia_ites_before_solver() {
    let src = include_str!("adaptive_engines.rs");
    let fn_start = src
        .find("pub(crate) fn try_kind(&self, budget: Duration)")
        .expect("adaptive_engines.rs should define try_kind");
    let fn_body = &src[fn_start..];
    let solver_start = fn_body
        .find("let mut solver = KindSolver::new(")
        .expect("try_kind should construct KindSolver");
    let prefix = &fn_body[..solver_start];

    assert!(
        prefix.contains("kind_problem.try_split_ites_in_clauses(32, self.config.verbose);"),
        "single-predicate LIA direct Kind should split ITE-heavy clauses before KindSolver::new"
    );
    assert!(
        prefix.contains("kind_problem.predicates().len() <= 1")
            && prefix.contains("!kind_problem.has_bv_sorts()")
            && prefix.contains("!kind_problem.has_array_sorts()")
            && prefix.contains("!kind_problem.has_real_sorts()")
            && prefix.contains("!kind_problem.has_datatype_sorts()"),
        "Kind ITE splitting should stay scoped to single-predicate pure LIA/Bool problems"
    );
}

#[test]
fn test_multi_pred_linear_ite_direct_kind_uses_smoke_budget() {
    let src = include_str!("adaptive_multi_pred.rs");
    let fn_start = src
        .find("pub(super) fn solve_multi_pred_linear(")
        .expect("adaptive_multi_pred.rs should define solve_multi_pred_linear");
    let fn_body = &src[fn_start..];
    let budget_start = fn_body
        .find("let direct_kind_cap = if features.has_ite || features.has_mod_div")
        .expect("direct Kind pre-pass should branch on ITE/mod-div features");
    let budget_slice = &fn_body[budget_start..];
    let budget_end = budget_slice
        .find("let kind_budget = self")
        .expect("direct Kind cap should feed the remaining-budget clamp");
    let budget_block = &budget_slice[..budget_end];

    assert!(
        budget_block.contains("Duration::from_millis(500)"),
        "ITE/mod-div multi-predicate direct Kind should use only a smoke-test budget"
    );
    assert!(
        budget_block.contains("Duration::from_secs(3)"),
        "non-ITE/mod-div direct Kind should retain the existing 3s cap"
    );
}

#[test]
fn test_complex_loop_pdr_probe_logs_actual_probe_budget() {
    let src = include_str!("adaptive_multi_pred_complex.rs");
    let fn_start = src
        .find("pub(super) fn solve_complex_loop(")
        .expect("adaptive_multi_pred_complex.rs should define solve_complex_loop");
    let fn_body = &src[fn_start..];
    let probe_start = fn_body
        .find("let pdr_probe_timeout_ms: u64 = 500;")
        .expect("ComplexLoop PDR probe should define a 500ms cap");
    let probe_slice = &fn_body[probe_start..];
    let probe_end = probe_slice
        .find("// Cross-engine lemma transfer pool")
        .expect("ComplexLoop PDR probe block should precede lemma transfer");
    let probe_block = &probe_slice[..probe_end];

    assert_eq!(
        probe_block
            .matches("budget_secs: pdr_probe_dur.as_secs_f64()")
            .count(),
        2,
        "ComplexLoop PDR probe decision rows should report the actual 500ms probe budget"
    );
    assert!(
        !probe_block.contains("budget_secs: 2.0"),
        "ComplexLoop PDR probe should not claim a stale 2s budget"
    );
}

#[test]
fn test_trivial_pdr_routes_have_adaptive_deadline_solve_timeout_cap() {
    let src = include_str!("adaptive_engines.rs");
    let fn_start = src
        .find("pub(crate) fn solve_trivial(")
        .expect("adaptive_engines.rs should define solve_trivial");
    let fn_body = &src[fn_start..];
    let fn_end = fn_body
        .find("pub(crate) fn cap_pdr_solve_timeout_to_budget(")
        .expect("solve_trivial should be followed by the PDR timeout helper");
    let fn_body = &fn_body[..fn_end];

    assert_eq!(
        fn_body
            .matches("Self::cap_pdr_solve_timeout_to_budget")
            .count(),
        2,
        "solve_trivial should cap both initial PDR and guided retry PDR"
    );

    let initial_cap = fn_body
        .find("Self::cap_pdr_solve_timeout_to_budget(&mut config")
        .expect("initial trivial PDR config should be capped");
    let initial_run = fn_body
        .find("PdrSolver::solve_problem_with_stats(&self.problem, config.clone())")
        .expect("solve_trivial should run the initial PDR solver");
    assert!(
        initial_cap < initial_run,
        "initial trivial PDR solve_timeout must be capped before solving"
    );

    let retry_config = fn_body
        .find("let mut retry_config = guide.apply_to_config(config);")
        .expect("solve_trivial should build a guided retry PDR config");
    let retry_cap = fn_body[retry_config..]
        .find("Self::cap_pdr_solve_timeout_to_budget")
        .map(|offset| retry_config + offset)
        .expect("guided retry PDR config should be capped");
    let retry_run = fn_body
        .find("PdrSolver::solve_problem_with_stats(&self.problem, retry_config)")
        .expect("solve_trivial should run guided retry PDR");
    assert!(
        retry_config < retry_cap && retry_cap < retry_run,
        "guided retry PDR solve_timeout must be capped after adjustment and before solving"
    );
}

#[test]
fn test_cap_pdr_solve_timeout_to_budget_is_fail_closed() {
    let mut config = PdrConfig::default();
    assert!(AdaptivePortfolio::cap_pdr_solve_timeout_to_budget(
        &mut config,
        Some(Duration::from_secs(3)),
    ));
    assert_eq!(config.solve_timeout, Some(Duration::from_secs(3)));

    assert!(AdaptivePortfolio::cap_pdr_solve_timeout_to_budget(
        &mut config,
        Some(Duration::from_secs(5)),
    ));
    assert_eq!(
        config.solve_timeout,
        Some(Duration::from_secs(3)),
        "an existing shorter PDR timeout should remain in force"
    );

    assert!(!AdaptivePortfolio::cap_pdr_solve_timeout_to_budget(
        &mut config,
        Some(Duration::ZERO),
    ));
    assert!(AdaptivePortfolio::cap_pdr_solve_timeout_to_budget(
        &mut config,
        None,
    ));
}

#[test]
fn test_simple_loop_direct_kind_lia_budget_keeps_mul_headroom() {
    let src = include_str!("adaptive_bv_strategy.rs");
    let budget_start = src
        .find("fn simple_loop_kind_budget_nominal(&self, features: &ProblemFeatures)")
        .expect("simple-loop strategy should compute a nominal Kind budget");
    let budget_slice = &src[budget_start..];
    let budget_end = budget_slice
        .find("/// Solve simple loop problems with validation evidence tracking.")
        .expect("simple-loop strategy should clamp the nominal Kind budget");
    let budget_block = &budget_slice[..budget_end];

    assert!(
        budget_block.contains("simple_loop_needs_dillig_style_kind_headroom"),
        "Dillig-style LIA simple loops should keep a distinct Kind headroom path"
    );
    assert!(
        budget_block.contains("simple_loop_needs_deep_lia_unsafe_kind_budget"),
        "deep accumulator-style unsafe LIA loops should keep enough Kind budget for counterexample discovery"
    );
    assert!(
        !budget_block.contains("features.has_multiplication"),
        "raw multiplication is too broad for the 3s Kind headroom trigger"
    );
    assert!(
        budget_block.contains("Duration::from_secs(3)"),
        "Dillig-style LIA simple loops should keep enough Kind budget for dillig32-style proofs"
    );
    assert!(
        budget_block.contains("Duration::from_secs(8)"),
        "deep accumulator-style unsafe LIA loops should get enough Kind budget to reach double-digit depths"
    );
    assert!(
        budget_block.contains("Duration::from_millis(1500)"),
        "ordinary non-BV simple loops should keep Kind to the 1.5s pre-pass budget"
    );
    assert!(
        budget_block.contains("Duration::from_secs(1)"),
        "BV simple loops should retain the tighter 1s Kind budget"
    );
}

#[test]
fn test_accumulator_unsafe_prepass_runs_before_lia_farkas_route() {
    let src = include_str!("adaptive.rs");
    let simple_loop_start = src
        .find("ProblemClass::SimpleLoop => {")
        .expect("generic SimpleLoop dispatch arm should be present");
    let simple_loop_slice = &src[simple_loop_start..];
    let simple_loop_end = simple_loop_slice
        .find("ProblemClass::ComplexLoop")
        .expect("generic SimpleLoop arm should precede ComplexLoop arm");
    let simple_loop_arm = &simple_loop_slice[..simple_loop_end];

    let accumulator_pos = simple_loop_arm
        .find("try_accumulator_lia_unsafe_counterexample")
        .expect("SimpleLoop dispatch should include accumulator unsafe prepass");
    let farkas_pos = simple_loop_arm
        .find("try_lia_farkas_pdr_route")
        .expect("SimpleLoop dispatch should include LIA Farkas route");

    assert!(
        accumulator_pos < farkas_pos,
        "accumulator unsafe prepass must run before generic LIA Farkas/PDR can consume the budget"
    );
}

#[test]
fn test_triangle_bv_diff_bounds_route_skips_generic_multi_pred_staging_9698() {
    let src = include_str!("adaptive.rs");
    let guard_pos = src
        .find("should_route_triangle_bv_diff_bounds_to_bv_lane")
        .expect("triangle BV diff-bound direct-route guard should be present");
    let algebraic_pos = src
        .find("use crate::algebraic_invariant::AlgebraicResult")
        .expect("algebraic pre-stage should still be present");

    assert!(
        guard_pos < algebraic_pos,
        "triangle BV diff-bound routing decision must be computed before generic algebraic staging"
    );

    let multi_pred_start = src
        .find("ProblemClass::MultiPredLinear => {")
        .expect("MultiPredLinear dispatch arm should be present");
    let multi_pred_slice = &src[multi_pred_start..];
    let multi_pred_end = multi_pred_slice
        .find("ProblemClass::MultiPredComplex")
        .expect("MultiPredLinear arm should precede MultiPredComplex arm");
    let multi_pred_arm = &multi_pred_slice[..multi_pred_end];

    let triangle_route = multi_pred_arm
        .find("triangle_bv_diff_bound_direct_route")
        .expect("MultiPredLinear dispatch should check triangle BV route");
    let original_bmc = multi_pred_arm
        .find("try_triangle_bv_diff_bound_original_bmc_route(route_budget)")
        .expect("triangle BV route should use the validated original-BMC specialist");
    let generic_multi_pred = multi_pred_arm
        .find("self.solve_multi_pred_linear(&features, deadline)")
        .expect("generic multi-predicate fallback should remain present");

    assert!(
        triangle_route < original_bmc && original_bmc < generic_multi_pred,
        "triangle BV diff-bound samples must use BV lanes before generic multi-predicate staging"
    );
}

#[test]
fn test_simple_loop_focused_bmc_probe_enforces_budget_issue_9690() {
    // The focused BMC probe moved to the FRONT of the SimpleLoop and
    // MultiPredLinear dispatch arms (try_front_bmc_probe in
    // adaptive_engines.rs) so shallow counterexamples no longer wait behind
    // the LIA/Farkas and Kind routes (lustre/svcomp-class latency). The
    // budget contract is unchanged.
    let src = include_str!("adaptive_engines.rs");
    let probe_start = src
        .find("pub(crate) fn try_front_bmc_probe(")
        .expect("front BMC probe should be implemented in adaptive_engines.rs");
    let probe_slice = &src[probe_start..];
    let probe_end = probe_slice
        .find("/// Solve entry-exit-only problems")
        .expect("front BMC probe should end before solve_entry_exit_only");
    let probe_block = &probe_slice[..probe_end];

    assert!(
        probe_block.contains("per_depth_timeout: Some(bmc_probe_budget)"),
        "focused BMC must pass its advertised budget to per-depth executor deadlines"
    );
    assert!(
        probe_block.contains("time_budget: Some(bmc_probe_budget)"),
        "focused BMC must pass its advertised budget to the overall BMC budget"
    );
    assert!(
        probe_block.contains("cancel.cancel_after(bmc_probe_budget)"),
        "focused BMC should keep its cancellation guard as a secondary budget check"
    );
    assert!(
        probe_block.contains("ScopedSmtDeadline::install(bmc_probe_budget)"),
        "focused BMC should install the thread-local SMT deadline as the hard budget"
    );

    // Dispatch ordering: the probe must run before the LIA/Farkas route in
    // both the SimpleLoop and MultiPredLinear arms.
    let adaptive_src = include_str!("adaptive.rs");
    for arm in [
        "ProblemClass::SimpleLoop => {",
        "ProblemClass::MultiPredLinear => {",
    ] {
        let arm_start = adaptive_src
            .find(arm)
            .unwrap_or_else(|| panic!("{arm} dispatch arm should be present"));
        let arm_slice = &adaptive_src[arm_start..];
        let probe_pos = arm_slice
            .find("try_front_bmc_probe")
            .unwrap_or_else(|| panic!("{arm} should call the front BMC probe"));
        let farkas_pos = arm_slice
            .find("try_lia_farkas_pdr_route")
            .unwrap_or_else(|| panic!("{arm} should include LIA Farkas route"));
        assert!(
            probe_pos < farkas_pos,
            "front BMC probe must run before the LIA Farkas/PDR route in {arm}"
        );
    }
}

// `#chc25-array-unsafe` (investigated, NOT adopted): the front BMC probe keeps
// EXCLUDING array-sorted problems. An empirical isolation sweep of the 2025
// LIA-Lin-Arrays unsafe misses showed BMC can find a few shallow array
// counterexamples uncontended (O0_array 10s, O3_ludcmp 1.6s, strcspn_3 15.3s),
// but admitting arrays to the sequential front probe was a MEASURED net
// regression (39 -> 37): the array-theory per-depth SMT checks do NOT honor the
// probe's `per_depth_timeout`/cancellation, so a single check overran the
// budget by tens of seconds and pushed three near-edge SAFE instances
// (heap__clearstr, heap__cocome2, O3 OpenSER) over the 90s wall. This test pins
// the exclusion so the array path is not re-enabled without first fixing
// array-SMT deadline enforcement.
#[test]
fn test_front_bmc_probe_still_excludes_arrays() {
    let src = include_str!("adaptive_engines.rs");
    let probe_start = src
        .find("pub(crate) fn try_front_bmc_probe(")
        .expect("front BMC probe should be implemented in adaptive_engines.rs");
    let probe_slice = &src[probe_start..];
    let probe_end = probe_slice
        .find("/// Solve entry-exit-only problems")
        .expect("front BMC probe should end before solve_entry_exit_only");
    let probe_block = &probe_slice[..probe_end];

    assert!(
        probe_block.contains("|| features.uses_arrays"),
        "front BMC probe must keep excluding array-sorted problems (array-SMT \
         per-depth timeouts are unenforced; a sequential array probe overruns \
         its budget and regresses near-edge SAFE instances — see #chc25-array-unsafe)"
    );
}

#[test]
fn test_simple_loop_bv_dispatch_tries_deterministic_transition_before_dual_lane() {
    let src = include_str!("adaptive_bv_strategy.rs");
    let simple_loop_start = src
        .find("pub(super) fn solve_simple_loop_with_evidence(")
        .expect("simple-loop strategy should be implemented");
    let simple_loop = &src[simple_loop_start..];
    let deterministic_route = simple_loop
        .find("self.try_deterministic_bv_bool_transition_route(deterministic_budget)")
        .expect("BV simple-loop dispatch should try the deterministic transition route");
    let direct_kind = simple_loop
        .find("// Stage 1: Try K-Induction")
        .expect("simple-loop strategy should keep the generic Kind stage");
    let dual_lane = simple_loop
        .find("self.solve_bv_dual_lane(full_budget)")
        .expect("BV simple-loop dispatch should keep the generic BV dual-lane fallback");

    assert!(
        deterministic_route < direct_kind && direct_kind < dual_lane,
        "deterministic BV/Bool transition route should run before generic Kind and BV dual-lane fallback"
    );

    let route_start = src
        .find("pub(crate) fn try_deterministic_bv_bool_transition_route(")
        .expect("deterministic BV/Bool route should be implemented");
    let route_body = &src[route_start..];
    assert!(
        route_body.contains("recognize_deterministic_bv_bool()"),
        "route must be gated by deterministic Bool/BV transition recognition"
    );
    assert!(
        route_body.contains("validate_original_counterexample_with_budget")
            && route_body.contains("validate_translated_safe_model_on_original"),
        "route must validate Unsafe traces and Safe invariants on the original CHC"
    );
    assert!(
        route_body.contains("cex.witness.is_none()"),
        "route must reject witness-less Unsafe traces instead of relying on existential validation"
    );
    assert!(
        route_body.contains("ValidationEvidence::CounterexampleVerification"),
        "validated unsafe results must carry counterexample-validation evidence"
    );
    assert!(
        !route_body.contains("ValidationEvidence::BmcCounterexample"),
        "deterministic route must not promote UNSAFE with source-only BMC evidence"
    );
    for rejected_result in [
        "bmc_unsafe_validation_rejected",
        "kind_unsafe_validation_rejected",
        "kind_safe_validation_rejected",
    ] {
        assert!(
            route_body.contains(rejected_result),
            "route must expose fail-closed validation demotion {rejected_result}"
        );
    }
}

const DILLIG_STYLE_KIND_FIXTURE: &str = r#"
(set-logic HORN)

(declare-fun P (Int Int Int) Bool)

(assert
  (forall ((X Int) (Y Int) (M Int))
    (=>
      (and (= X 0) (= Y 0) (= M 0))
      (P X Y M))))

(assert
  (forall ((X Int) (Y Int) (M Int) (NX Int) (NY Int) (NM Int))
    (=>
      (and
        (P X Y M)
        (= NX (+ X 1))
        (= NM (+ M 1))
        (= NY (ite (= M 0) (* 2 NX) Y)))
      (P NX NY NM))))

(assert
  (forall ((X Int) (Y Int) (M Int))
    (=>
      (and (P X Y M) (not (= Y (* 2 X))))
      false)))

(check-sat)
(exit)
"#;

const NON_DILLIG_VAR_MUL_FIXTURE: &str = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)

(assert
  (forall ((X Int) (Y Int))
    (=>
      (and (= X 1) (= Y 1))
      (P X Y))))

(assert
  (forall ((X Int) (Y Int) (NX Int) (NY Int))
    (=>
      (and
        (P X Y)
        (= NX (+ X 1))
        (= NY (ite (= X 1) (* X X) Y)))
      (P NX NY))))

(assert
  (forall ((X Int) (Y Int))
    (=>
      (and (P X Y) (not (= Y (* X X))))
      false)))

(check-sat)
(exit)
"#;

const NON_DILLIG_NO_ITE_FIXTURE: &str = r#"
(set-logic HORN)

(declare-fun P (Int Int) Bool)

(assert
  (forall ((X Int) (Y Int))
    (=>
      (and (= X 0) (= Y 0))
      (P X Y))))

(assert
  (forall ((X Int) (Y Int) (NX Int) (NY Int))
    (=>
      (and
        (P X Y)
        (= NX (+ X 1))
        (= NY (* 2 NX)))
      (P NX NY))))

(assert
  (forall ((X Int) (Y Int))
    (=>
      (and (P X Y) (not (= Y (* 2 X))))
      false)))

(check-sat)
(exit)
"#;

const NON_DILLIG_MOD_DIV_FIXTURE: &str = r#"
(set-logic HORN)

(declare-fun P (Int Int Int) Bool)

(assert
  (forall ((X Int) (Y Int) (M Int))
    (=>
      (and (= X 0) (= Y 0) (= M 0))
      (P X Y M))))

(assert
  (forall ((X Int) (Y Int) (M Int) (NX Int) (NY Int) (NM Int) (R Int))
    (=>
      (and
        (P X Y M)
        (= NX (+ X 1))
        (= NM (+ M 1))
        (= R (mod NX 2))
        (= NY (ite (= R 0) (* 2 NX) Y)))
      (P NX NY NM))))

(assert
  (forall ((X Int) (Y Int) (M Int))
    (=>
      (and (P X Y M) (not (= Y (* 2 X))))
      false)))

(check-sat)
(exit)
"#;

fn fallback_extra_small_lia_benchmark(name: &str) -> Option<&'static str> {
    match name {
        "dillig32_000" | "s_mutants_20_000" => Some(DILLIG_STYLE_KIND_FIXTURE),
        "three_dots_moving_2_000" => Some(NON_DILLIG_NO_ITE_FIXTURE),
        "menlo_park_term_simpl_2_000" => Some(NON_DILLIG_VAR_MUL_FIXTURE),
        "s_mutants_16_000" => Some(NON_DILLIG_MOD_DIV_FIXTURE),
        _ => None,
    }
}

fn adaptive_for_extra_small_lia_benchmark(name: &str) -> AdaptivePortfolio {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .join(format!(
            "benchmarks/chc-comp/2025/extra-small-lia/{name}.smt2"
        ));
    let input = match std::fs::read_to_string(&path) {
        Ok(input) => input,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            fallback_extra_small_lia_benchmark(name)
                .unwrap_or_else(|| {
                    panic!("benchmark should be present at {}: {error}", path.display())
                })
                .to_owned()
        }
        Err(error) => panic!(
            "benchmark should be readable at {}: {error}",
            path.display()
        ),
    };
    let problem = ChcParser::parse(&input).expect("benchmark should parse");
    AdaptivePortfolio::new(problem, AdaptiveConfig::test_default())
}

#[test]
fn test_dillig_style_kind_headroom_targets_dillig32_family() {
    for name in ["dillig32_000", "s_mutants_20_000"] {
        let adaptive = adaptive_for_extra_small_lia_benchmark(name);
        let features = adaptive.features();
        assert!(
            adaptive.simple_loop_needs_dillig_style_kind_headroom(&features),
            "{name} should receive the 3s Dillig-style direct-Kind budget"
        );
    }
}

#[test]
fn test_dillig_style_kind_headroom_rejects_broad_multiplication_cases() {
    for name in [
        "three_dots_moving_2_000",
        "menlo_park_term_simpl_2_000",
        "s_mutants_16_000",
    ] {
        let adaptive = adaptive_for_extra_small_lia_benchmark(name);
        let features = adaptive.features();
        assert!(
            !adaptive.simple_loop_needs_dillig_style_kind_headroom(&features),
            "{name} should not receive the 3s Dillig-style direct-Kind budget"
        );
    }
}

#[test]
fn test_multi_pred_portfolio_timeout_reserves_retry_budget() {
    assert_eq!(
        AdaptivePortfolio::multi_pred_portfolio_timeout(Duration::from_secs(15)),
        Duration::from_millis(10_500)
    );
}

#[test]
fn test_multi_pred_portfolio_timeout_clamps_small_remaining_budget() {
    assert_eq!(
        AdaptivePortfolio::multi_pred_portfolio_timeout(Duration::from_secs(2)),
        Duration::ZERO
    );
    assert_eq!(
        AdaptivePortfolio::multi_pred_portfolio_timeout(Duration::from_secs(4)),
        Duration::from_secs(2),
        "the nested portfolio's two-second cancellation grace must fit inside the global deadline"
    );
}

#[test]
fn test_multi_pred_case_split_budget_scales_from_actual_remaining_time() {
    assert_eq!(
        AdaptivePortfolio::multi_pred_case_split_budget(None),
        Duration::from_secs(8),
        "an unbounded adaptive solve retains the established case-split budget"
    );

    let cases = [
        (Duration::ZERO, Duration::ZERO),
        (Duration::from_nanos(1), Duration::from_nanos(1)),
        (Duration::from_nanos(3), Duration::from_nanos(2)),
        (Duration::from_secs(6), Duration::from_secs(4)),
        (Duration::from_secs(12), Duration::from_secs(8)),
        (Duration::from_secs(20), Duration::from_secs(8)),
        (Duration::from_secs(40), Duration::from_secs(10)),
        (Duration::from_secs(65), Duration::from_secs(16)),
        (Duration::from_mins(2), Duration::from_secs(16)),
    ];
    for (remaining, expected) in cases {
        let budget = AdaptivePortfolio::multi_pred_case_split_budget(Some(remaining));
        assert_eq!(budget, expected, "unexpected budget for {remaining:?}");
        assert!(
            budget <= remaining.saturating_sub(remaining / 3),
            "case-split must preserve its downstream share for {remaining:?}"
        );
        assert!(
            budget <= Duration::from_secs(16),
            "case-split must retain its hard stage cap"
        );
    }
}

#[test]
fn test_multi_pred_pdr_config_disables_entry_cegar_discharge() {
    let config = AdaptivePortfolio::multi_pred_pdr_config(PdrConfig::default());
    assert!(
        !config.use_entry_cegar_discharge,
        "multi-predicate adaptive PDR runs should skip entry-CEGAR discharge"
    );
}

#[test]
fn test_non_inlined_pdr_gate_skips_zero_predicate_problems() {
    let problem = ChcProblem::new();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 0);
    assert!(
        !adaptive.should_try_non_inlined_pdr(&features),
        "problems without predicates should never run non-inlined PDR"
    );
}

#[test]
fn test_non_inlined_pdr_gate_skips_single_predicate_problems() {
    let problem = create_simple_loop();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert!(features.is_single_predicate);
    assert!(
        !adaptive.should_try_non_inlined_pdr(&features),
        "single-predicate problems should stay on the normal path"
    );
}

#[test]
fn test_non_inlined_pdr_gate_always_tries_two_predicate_problems() {
    // #7934: The wide gate (all 2+ predicate problems) is required to
    // preserve per-predicate structure that clause inlining would destroy.
    // Narrowing to mod/div/ITE-only caused the s_multipl_* regression.
    let x = ChcVar::new("x", ChcSort::Int);
    let problem =
        create_two_predicate_gate_problem(Some(ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(10))));
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 2);
    assert!(
        adaptive.should_try_non_inlined_pdr(&features),
        "all 2+ predicate problems should try non-inlined PDR (#7934 wide gate)"
    );
}

#[test]
fn test_non_inlined_pdr_gate_keeps_trying_mod_constraints_for_two_predicates() {
    let x = ChcVar::new("x", ChcSort::Int);
    let problem = create_two_predicate_gate_problem(Some(ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
        ChcExpr::int(0),
    )));
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 2);
    assert!(
        adaptive.should_try_non_inlined_pdr(&features),
        "mod/div-triggered problems should still try the non-inlined PDR stage"
    );
}

#[test]
fn test_non_inlined_pdr_gate_always_tries_long_predicate_chains() {
    let problem = create_four_predicate_gate_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 4);
    assert!(
        adaptive.should_try_non_inlined_pdr(&features),
        "4+ predicate problems should always try the non-inlined PDR stage"
    );
}

#[test]
fn test_non_inlined_pdr_budget_preserves_standard_long_chain_budget_without_arrays() {
    let problem = create_four_predicate_gate_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert!(!features.uses_arrays);
    assert_eq!(
        adaptive.non_inlined_pdr_stage_budget(&features, None),
        Duration::from_millis(3500)
    );
}

#[test]
fn test_non_inlined_pdr_budget_caps_array_heavy_long_chains_7897() {
    let problem = create_four_predicate_array_gate_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();

    assert_eq!(features.num_predicates, 4);
    assert!(features.uses_arrays);
    assert_eq!(
        adaptive.non_inlined_pdr_stage_budget(&features, None),
        Duration::from_millis(1750)
    );
}

#[test]
fn test_non_inlined_pdr_budget_promotes_large_bv_array_acyclic_chains_9191() {
    let problem = create_large_bv_array_acyclic_gate_problem(129);
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();
    let deadline = Instant::now() + Duration::from_secs(30);

    assert_eq!(features.num_predicates, 129);
    assert!(features.uses_arrays);
    assert!(adaptive.problem.has_bv_sorts());
    assert!(
        !features.has_cycles,
        "large generated basic-block chain should stay acyclic"
    );
    let budget = adaptive.non_inlined_pdr_stage_budget(&features, Some(deadline));
    assert!(
        budget >= Duration::from_secs(25) && budget <= Duration::from_secs(30),
        "large BV+array acyclic chains should get a first-class native PDR slice, got {budget:?}"
    );
}

/// Regression test for #6847: stack overflow on multi-predicate problems
/// with many arguments per predicate. The adaptive solver must run on a
/// thread with a large stack so that deep ChcExpr trees from SingleLoop
/// encoding don't overflow during recursive Arc<ChcExpr> Drop.
/// Note: the 5s internal time_budget is not a hard wall — the adaptive
/// solver can overrun significantly (20s debug, 90s+ release). The
/// time_budget enforcement gap is tracked by a separate issue.
#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(180_000))]
fn test_adaptive_multi_pred_many_args_no_stack_overflow_6847() {
    // Create a multi-predicate problem with many arguments (similar to
    // model-checker-consumer's merge_deps harness: 12 relations, 32 args per predicate).
    // Use a simpler variant (4 relations, 16 args) that exercises the
    // same SingleLoop encoding path without taking too long.
    let num_preds = 4;
    let args_per_pred = 16;
    let mut problem = ChcProblem::new();

    let mut pred_ids = Vec::new();
    for i in 0..num_preds {
        let sorts = vec![ChcSort::Int; args_per_pred];
        let id = problem.declare_predicate(&format!("P{i}"), sorts);
        pred_ids.push(id);
    }

    // Init clause: true => P0(0, 0, ..., 0)
    let zeros: Vec<ChcExpr> = (0..args_per_pred).map(|_| ChcExpr::int(0)).collect();
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(pred_ids[0], zeros),
    ));

    // Transition clauses: Pi(x0..xN) => P(i+1)(x0+1..xN+1)
    for i in 0..num_preds - 1 {
        let vars: Vec<ChcVar> = (0..args_per_pred)
            .map(|j| ChcVar::new(format!("x{j}"), ChcSort::Int))
            .collect();
        let args: Vec<ChcExpr> = vars.iter().map(|v| ChcExpr::var(v.clone())).collect();
        let next_args: Vec<ChcExpr> = vars
            .iter()
            .map(|v| ChcExpr::add(ChcExpr::var(v.clone()), ChcExpr::int(1)))
            .collect();
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(pred_ids[i], args)], None),
            ClauseHead::Predicate(pred_ids[i + 1], next_args),
        ));
    }

    // Query clause: P(N-1)(x0..xN) /\ x0 > 1000 => false
    let vars: Vec<ChcVar> = (0..args_per_pred)
        .map(|j| ChcVar::new(format!("x{j}"), ChcSort::Int))
        .collect();
    let args: Vec<ChcExpr> = vars.iter().map(|v| ChcExpr::var(v.clone())).collect();
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pred_ids[num_preds - 1], args)],
            Some(ChcExpr::gt(
                ChcExpr::var(vars[0].clone()),
                ChcExpr::int(1000),
            )),
        ),
        ClauseHead::False,
    ));

    // Solve with a short budget — we only care about not crashing.
    let config = AdaptiveConfig {
        time_budget: Duration::from_secs(5),
        verbose: false,
        ..AdaptiveConfig::test_default()
    };
    let adaptive = AdaptivePortfolio::new(problem, config);
    let result = adaptive.solve();

    // Any result is acceptable — the key is that we didn't stack overflow.
    match result {
        VerifiedChcResult::Safe(_)
        | VerifiedChcResult::Unsafe(_)
        | VerifiedChcResult::Unknown(_) => {}
    }
}

#[test]
fn test_adaptive_portfolio_drop_deep_problem_small_stack_6847() {
    fn build_deep_problem(depth: usize) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("P", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let arg = ChcExpr::var(x);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(pred, vec![ChcExpr::int(0)]),
        ));

        let mut deep = ChcExpr::Int(0);
        for _ in 0..depth {
            deep = ChcExpr::add(arg.clone(), deep);
        }

        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(pred, vec![arg])], Some(deep)),
            ClauseHead::False,
        ));
        problem
    }

    let problem = build_deep_problem(20_000);
    let handle = std::thread::Builder::new()
        .name("adaptive-drop-small-stack".to_string())
        .stack_size(2 * 1024 * 1024)
        .spawn(move || {
            let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
            drop(adaptive);
        })
        .expect("small-stack regression thread should spawn");

    handle
        .join()
        .expect("AdaptivePortfolio drop should not overflow the caller stack");
}

/// BV MBP Packet 4 integration test: verify BV-native PDR converges on a
/// BV counting loop using the BV MBP interval projection path.
///
/// Problem: x starts at 0, increments by 1 while bvule(x, 3), asserts
/// bvule(5, x) is unreachable. Invariant: not(bvule(5, x)).
///
/// Uses PdrSolver directly (not PortfolioSolver) because the portfolio's
/// #6789 tautological guard rejects invariants that are exactly ¬query.
/// The invariant IS correct and 1-inductive; the guard is conservative.
/// The test verifies the full BV MBP integration: BV-native preprocessing,
/// MBP interval projection in project_bitvec_var, and PDR fixed-point.
///
/// Part of #7015 (BV MBP design, Packet 4).
#[test]
#[timeout(10_000)]
fn test_bv_native_pdr_interval_lemma_convergence() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ((_ BitVec 8)) Bool)

(assert (forall ((x (_ BitVec 8)))
  (=> (= x #x00) (inv x))))

(assert (forall ((x (_ BitVec 8)) (xp (_ BitVec 8)))
  (=> (and (inv x) (bvule x #x03) (= xp (bvadd x #x01)))
      (inv xp))))

(assert (forall ((x (_ BitVec 8)))
  (=> (and (inv x) (bvule #x05 x))
      false)))

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("BV counting loop should parse");

    // Run BV-native PDR directly (bypasses portfolio #6789 guard)
    let summary = PreprocessSummary::build_bv_native(problem, false);
    let pdr_config = PdrConfig {
        use_must_summaries: true,
        use_lemma_hints: true,
        max_frames: 50,
        ..PdrConfig::default()
    };
    let mut pdr = PdrSolver::new(summary.transformed_problem, pdr_config);
    let result = pdr.solve();
    assert!(
        matches!(result, PdrResult::Safe(_)),
        "BV-native PDR with interval MBP should prove the counting loop safe. Got: {result:?}"
    );
}

/// Regression test for #7897/#7931: adaptive solver must solve the accumulator
/// pattern via algebraic invariant synthesis. The loop computes sum = 0+1+...+(n-1)
/// = n*(n-1)/2, which requires a polynomial invariant that PDR alone cannot discover.
/// Algebraic synthesis detects the quadratic closed form and emits the invariant.
#[test]
#[timeout(30_000)]
fn test_adaptive_accumulator_algebraic_synthesis_7897() {
    let input = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (<= 0 n) (<= n 100) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Inv n i sum)
           (> sum (* n n)))
      false)))

(check-sat)
"#;
    let problem = ChcParser::parse(input).expect("accumulator should parse");
    let config = AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10));
    let solver = AdaptivePortfolio::new(problem, config);
    let deadline = solver.solve_deadline();
    let (portfolio_result, evidence) = solver.solve_internal(deadline);
    assert!(
        matches!(evidence, ValidationEvidence::AlgebraicClosedForm),
        "Adaptive solver should use algebraic closed-form evidence for accumulator, got {evidence:?}"
    );
    let result =
        solver.finalize_verified_result_with_deadline(portfolio_result, evidence, deadline);
    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "Adaptive solver should prove accumulator safe via algebraic synthesis (#7897). Got: {result:?}"
    );
}

// Integration test for #8578 removed: the acyclic LIA problem is too
// expensive for the full adaptive portfolio (even with a 2s budget, the
// portfolio infrastructure takes >20s to time out in both debug and release).
// The unit tests in inductiveness/tests.rs directly verify the fix:
//   - test_strictly_self_inductive_returns_false_for_no_self_loop_predicate_8578
//   - test_self_inductive_returns_false_for_no_self_loop_predicate_8578

// ---------------------------------------------------------------------------
// #8739 regression: BV-indexed array ROW expansion
// ---------------------------------------------------------------------------
//
// Before this fix, BV+array simple-loop problems hit destructive preprocessing
// (BvToBool + BvToIntAbstractor) that stripped BV index structure and
// spuriously scalarized away the array, leaving PDR unable to reason about
// `select`/`store` with symbolic BV indices. The fix adds a BV+array dispatch
// branch that races a BV-native lane (PreprocessSummary::build_bv_native) in
// parallel with the original array-safe lane; the BV-native lane preserves
// `Array(BV, BV)` sorts so `expand_select_store_symbolic` can run correctly.
//
// Design: the development design notes

/// Verify BV-indexed array simple loops are classified as SimpleLoop and
/// exercise both lanes of the #8739 BV+array dispatch. The test problem is
/// `test_array_int_pred.smt2`-shaped but uses BV indices, ensuring the
/// BV-native lane's PreprocessSummary preserves the `Array(BV, BV)` sort.
#[test]
fn test_adaptive_bv_indexed_array_classification_8739() {
    let input = r"
(set-logic HORN)
(declare-fun inv ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32)) Bool)
(assert (forall ((arr (Array (_ BitVec 32) (_ BitVec 32))) (i (_ BitVec 32)))
  (=> (and (= (select arr (_ bv0 32)) (_ bv42 32)) (= i (_ bv0 32)))
      (inv arr i))))
(assert (forall ((arr (Array (_ BitVec 32) (_ BitVec 32))) (i (_ BitVec 32))
                 (arr2 (Array (_ BitVec 32) (_ BitVec 32))) (i2 (_ BitVec 32)))
  (=> (and (inv arr i)
           (bvult i (_ bv10 32))
           (= arr2 (store arr i (bvadd (select arr i) (_ bv1 32))))
           (= i2 (bvadd i (_ bv1 32))))
      (inv arr2 i2))))
(assert (forall ((arr (Array (_ BitVec 32) (_ BitVec 32))) (i (_ BitVec 32)))
  (=> (inv arr i)
      (not (bvult (select arr (_ bv0 32)) (_ bv42 32))))))
(check-sat)
";
    let problem = ChcParser::parse(input).expect("BV-indexed array benchmark should parse");
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(5),
            ..AdaptiveConfig::test_default()
        },
    );
    let features = adaptive.features();

    // The fix hinges on classification and routing: SimpleLoop + uses_arrays +
    // problem.has_bv_sorts() must all hold so the new BV+array dispatch branch
    // fires.
    assert_eq!(features.class, ProblemClass::SimpleLoop);
    assert!(
        features.uses_arrays,
        "BV-indexed array problem must set uses_arrays"
    );
    assert!(
        adaptive.problem.has_bv_sorts(),
        "BV-indexed array problem must report has_bv_sorts()"
    );
    assert!(
        !features.uses_real,
        "BV+array problem must not claim uses_real"
    );

    // Lane N (BV-native) config shape: preprocessing disabled because
    // PreprocessSummary::build_bv_native has already been applied, and PDR
    // is present so BV-sorted predicates can be solved natively.
    let native_config = adaptive.bv_native_portfolio_config(Duration::from_secs(5));
    assert!(
        !native_config.enable_preprocessing,
        "Lane N must have enable_preprocessing=false — BV-native preprocessing \
         is done via PreprocessSummary::build_bv_native before the portfolio runs"
    );
    assert!(
        native_config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Pdr(_))),
        "Lane N must include PDR for BV-native array reasoning"
    );
    // PDKIND must be absent from Lane N: #8675 soundness guard rejects
    // array-sorted problems in PdkindSolver::solve_raw. Including PDKIND
    // wastes a thread and produces an immediate Unknown.
    assert!(
        !native_config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Pdkind(_))),
        "Lane N must NOT include PDKIND: #8675 array soundness guard short-circuits"
    );

    // Lane S (array-safe) config shape: preprocessing enabled because
    // PortfolioSolver::new runs BvToBool + BvToIntAbstractor internally on the
    // original problem. Lane S is the fallback that solves pure-LIA-indexed
    // arrays without the BV-native code path.
    let safe_config = adaptive.simple_loop_array_portfolio_config(Duration::from_secs(5));
    assert!(
        safe_config.enable_preprocessing,
        "Lane S must have enable_preprocessing=true — PortfolioSolver::new \
         runs internal preprocessing"
    );
    assert!(
        safe_config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Pdr(_))),
        "Lane S must include PDR for array reasoning"
    );
    assert!(
        safe_config
            .engines
            .iter()
            .any(|e| matches!(e, EngineConfig::Bmc(_))),
        "Lane S must include BMC again now that #8734/#8745 are fixed"
    );
}

#[test]
fn test_budget_report_solves_model_checker_consumer_nested_array_9185() {
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
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig {
            time_budget: Duration::from_secs(65),
            ..AdaptiveConfig::test_default()
        },
    );
    let (result, _report) = adaptive.solve_with_budget_report();

    assert!(
        matches!(result, VerifiedChcResult::Safe(_)),
        "expected budget-report API to prove preserved model-checker-consumer nested-array CHC, got {result:?}"
    );

    let mut expanded_problem =
        ChcParser::parse(input).expect("model-checker-consumer nested-array CHC should parse");
    assert!(
        expanded_problem.expand_nullary_fail_queries(false),
        "test fixture should match model-checker-consumer's nullary error expansion path"
    );
    let mut expanded_config = AdaptiveConfig::with_budget(Duration::from_secs(65), false);
    expanded_config.strict_proofs = true;
    let expanded_adaptive = AdaptivePortfolio::new(expanded_problem, expanded_config);
    let (expanded_result, _report) = expanded_adaptive.solve_with_budget_report();

    assert!(
        matches!(expanded_result, VerifiedChcResult::Safe(_)),
        "expected model-checker-consumer-expanded budget-report API to prove nested-array CHC, got {expanded_result:?}"
    );
}

/// Unit discriminator for the finite-vs-recursive datatype guard that gates
/// acyclic-BMC Safe admission. FINITE (non-recursive) ADTs — a struct of
/// scalars, an `Option`-like enum, a nested-finite struct — have a bounded
/// value space and must NOT be flagged; a self-recursive list and a pair of
/// mutually recursive datatypes MUST be flagged (their unbounded value space
/// makes bounded acyclic unrolling incomplete).
#[test]
fn test_has_recursive_datatype_sorts_discriminates_finite_from_recursive() {
    // Self-recursive: Lst = nil | cons(Int, Lst).
    let recursive = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-fun P (Lst) Bool)\n\
         (assert (forall ((l Lst)) (=> (= l nil) (P l))))\n\
         (assert (forall ((l Lst)) (=> (P l) false)))\n\
         (check-sat)\n",
    )
    .expect("self-recursive list fixture parses");
    assert!(
        recursive.has_datatype_sorts(),
        "Lst is a datatype-sorted predicate argument"
    );
    assert!(
        recursive.has_recursive_datatype_sorts(),
        "self-referential Lst must be detected as recursive"
    );

    // Finite struct of two scalars.
    let finite_struct = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))\n\
         (declare-fun P (Pair) Bool)\n\
         (assert (forall ((p Pair)) (=> (= p (mk 0 0)) (P p))))\n\
         (assert (forall ((p Pair)) (=> (P p) false)))\n\
         (check-sat)\n",
    )
    .expect("finite struct fixture parses");
    assert!(finite_struct.has_datatype_sorts());
    assert!(
        !finite_struct.has_recursive_datatype_sorts(),
        "a struct of scalars is finite; must NOT be flagged recursive"
    );

    // Finite enum of nullary + scalar variants (Option-like).
    let finite_enum = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((Opt 0)) (((none) (some (val Int)))))\n\
         (declare-fun P (Opt) Bool)\n\
         (assert (forall ((o Opt)) (=> (= o none) (P o))))\n\
         (assert (forall ((o Opt)) (=> (P o) false)))\n\
         (check-sat)\n",
    )
    .expect("finite enum fixture parses");
    assert!(
        !finite_enum.has_recursive_datatype_sorts(),
        "an Option-like enum is finite; must NOT be flagged recursive"
    );

    // Finite nested struct (a struct whose field is another finite struct).
    let finite_nested = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((Inner 0)) (((mki (a Int)))))\n\
         (declare-datatypes ((Outer 0)) (((mko (i Inner) (b Int)))))\n\
         (declare-fun P (Outer) Bool)\n\
         (assert (forall ((o Outer)) (=> (P o) false)))\n\
         (check-sat)\n",
    )
    .expect("finite nested struct fixture parses");
    assert!(
        !finite_nested.has_recursive_datatype_sorts(),
        "a struct nesting another finite struct is finite; must NOT be flagged recursive"
    );

    // Mutually recursive: A references B, B references A.
    let mutual = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((A 0) (B 0)) (((mkA (get_b B))) ((nilB) (mkB (get_a A)))))\n\
         (declare-fun P (A) Bool)\n\
         (assert (forall ((a A)) (=> (P a) false)))\n\
         (check-sat)\n",
    )
    .expect("mutually recursive fixture parses");
    assert!(
        mutual.has_recursive_datatype_sorts(),
        "mutually recursive A/B must be detected as recursive"
    );
}

/// Soundness + completeness for the loosened acyclic-BMC admission gate
/// (`adaptive.rs` `ScalarAcyclicBmcExhaustive` arm). Both fixtures are the same
/// shape — a loop-free P -> Q -> false DAG whose single predicate argument is a
/// datatype — differing ONLY in whether that datatype is finite or recursive.
///
/// - FINITE datatype: an empty-model exhaustive acyclic BMC Safe is a complete
///   proof (finite value space), so it is admitted as `Safe` (the completeness
///   win this change delivers).
/// - RECURSIVE datatype: bounded acyclic unrolling is NOT complete (unbounded
///   value space), so the identical empty-model Safe evidence is demoted to
///   `Unknown` — never a false Safe. This is the mandatory soundness guard.
#[test]
fn test_acyclic_bmc_admission_demotes_recursive_datatype_but_admits_finite() {
    let finite = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((Opt 0)) (((none) (some (val Int)))))\n\
         (declare-fun P (Opt) Bool)\n\
         (declare-fun Q (Opt) Bool)\n\
         (assert (forall ((o Opt)) (=> (= o none) (P o))))\n\
         (assert (forall ((o Opt)) (=> (P o) (Q o))))\n\
         (assert (forall ((o Opt)) (=> (and (Q o) (= o none)) false)))\n\
         (check-sat)\n",
    )
    .expect("finite-datatype acyclic fixture parses");
    assert!(!finite.has_recursive_datatype_sorts());
    let finite_adaptive = AdaptivePortfolio::new(finite, AdaptiveConfig::test_default());
    let finite_result = finite_adaptive.finalize_verified_result(
        PortfolioResult::Safe(InvariantModel::default()),
        ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: 3 },
    );
    assert!(
        matches!(finite_result, VerifiedChcResult::Safe(_)),
        "finite-datatype empty-model exhaustive acyclic BMC Safe must be admitted, got {finite_result:?}"
    );

    let recursive = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))\n\
         (declare-fun P (Lst) Bool)\n\
         (declare-fun Q (Lst) Bool)\n\
         (assert (forall ((l Lst)) (=> (= l nil) (P l))))\n\
         (assert (forall ((l Lst)) (=> (P l) (Q l))))\n\
         (assert (forall ((l Lst)) (=> (and (Q l) (= l nil)) false)))\n\
         (check-sat)\n",
    )
    .expect("recursive-datatype acyclic fixture parses");
    assert!(recursive.has_recursive_datatype_sorts());
    let recursive_adaptive = AdaptivePortfolio::new(recursive, AdaptiveConfig::test_default());
    let recursive_result = recursive_adaptive.finalize_verified_result(
        PortfolioResult::Safe(InvariantModel::default()),
        ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: 3 },
    );
    assert!(
        matches!(recursive_result, VerifiedChcResult::Unknown(_)),
        "recursive-datatype empty-model acyclic BMC Safe must be DEMOTED to Unknown (no false proof), got {recursive_result:?}"
    );
}

/// A scalar evidence label is not itself a proof. The finalizer may consume
/// solver-internal evidence, but it must not turn that label into a
/// process-global cache entry: doing so lets a fabricated Safe label poison
/// later external empty-model validation for the same unsafe problem.
#[test]
fn test_fabricated_scalar_evidence_cannot_poison_acyclic_bmc_cache() {
    let problem = ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-datatypes ((CachePoisonFlag 0)) (((cache_poison_a) (cache_poison_b))))\n\
         (declare-fun CachePoisonP (CachePoisonFlag) Bool)\n\
         (declare-fun CachePoisonQ (CachePoisonFlag) Bool)\n\
         (assert (CachePoisonP cache_poison_a))\n\
         (assert (forall ((f CachePoisonFlag))\n\
           (=> (CachePoisonP f) (CachePoisonQ f))))\n\
         (assert (forall ((f CachePoisonFlag))\n\
           (=> (CachePoisonQ f) false)))\n\
         (check-sat)\n",
    )
    .expect("unique finite-datatype cache-poison fixture parses");
    assert!(!problem.has_cycles());
    assert!(problem.has_datatype_sorts());
    assert!(!problem.has_recursive_datatype_sorts());

    let validation_problem = problem.clone();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
    let features = adaptive.features();
    let depth = features.dag_depth.max(features.num_predicates).max(1);
    assert!(
        crate::acyclic_cert_cache::lookup_acyclic_bmc_safe(&adaptive.problem).is_none(),
        "the unique unsafe fixture must begin without a cached proof"
    );

    let fabricated = adaptive.finalize_verified_result(
        PortfolioResult::Safe(InvariantModel::default()),
        ValidationEvidence::ScalarAcyclicBmcExhaustive { max_depth: depth },
    );
    assert!(
        matches!(fabricated, VerifiedChcResult::Safe(_)),
        "the regression must exercise the generic scalar-evidence admission arm"
    );
    assert!(
        crate::acyclic_cert_cache::lookup_acyclic_bmc_safe(&adaptive.problem).is_none(),
        "generic finalization must not cache a merely labelled Safe"
    );

    assert!(
        !crate::engines::validate_external_invariant_model(
            &validation_problem,
            &InvariantModel::new(),
            &PdrConfig::default(),
        )
        .expect("unsafe finite-DT validation should fail closed, not error"),
        "independent exact BMC must reject the reachable query"
    );

    let shallow_depth = depth.saturating_sub(1);
    crate::acyclic_cert_cache::record_acyclic_bmc_safe(&adaptive.problem, shallow_depth);
    assert_eq!(
        crate::acyclic_cert_cache::lookup_acyclic_bmc_safe(&adaptive.problem),
        Some(shallow_depth)
    );
    assert!(
        !crate::engines::validate_external_invariant_model(
            &validation_problem,
            &InvariantModel::new(),
            &PdrConfig::default(),
        )
        .expect("shallow-cache validation should fail closed, not error"),
        "a cached proof shallower than the recomputed exhaustive depth must not validate an unsafe empty model"
    );
}

#[test]
#[timeout(20_000)]
fn test_reduced_lia_array_route_backtranslates_queryless_safe_model() {
    let problem = create_reducible_queryless_lia_array_chain();
    let original = problem.clone();
    let summary = PreprocessSummary::build(problem.clone(), false);
    assert!(
        !summary
            .transformed_problem
            .clauses()
            .iter()
            .any(HornClause::is_query),
        "unreachable query must disappear in the certified reduced problem"
    );

    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::with_budget(Duration::from_secs(5), false),
    );
    let result = adaptive
        .try_reduced_lia_array_preprocessed_route(Some(Instant::now() + Duration::from_secs(5)));
    let Some((PortfolioResult::Safe(model), ValidationEvidence::FullVerification)) = result else {
        panic!("queryless reduced route did not return a fully verified Safe model: {result:?}");
    };
    assert!(
        crate::engines::validate_external_invariant_model(
            &original,
            &model,
            &PdrConfig::default(),
        )
        .expect("original validation must complete"),
        "backtranslated queryless model must satisfy the original unreachable query"
    );
}

// ============================================================================
// All-predicates-top query-infeasibility certificate
// ============================================================================

fn create_top_model_array_candidate(
    query_constraint: impl FnOnce(ChcExpr) -> ChcExpr,
) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let inv = problem.declare_predicate("TopInv", vec![array_sort.clone(), ChcSort::Int]);
    let array = ChcVar::new("array", array_sort);
    let index = ChcVar::new("index", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(array.clone()), ChcExpr::int(0)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![ChcExpr::var(array.clone()), ChcExpr::var(index.clone())],
            )],
            Some(ChcExpr::ge(ChcExpr::var(index.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::store(
                    ChcExpr::var(array.clone()),
                    ChcExpr::var(index.clone()),
                    ChcExpr::int(7),
                ),
                ChcExpr::add(ChcExpr::var(index.clone()), ChcExpr::int(1)),
            ],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(array), ChcExpr::var(index.clone())])],
            Some(query_constraint(ChcExpr::var(index))),
        ),
        ClauseHead::False,
    ));
    problem
}

#[test]
#[timeout(5_000)]
fn test_top_model_query_infeasibility_accepts_only_after_original_validation() {
    let problem = create_top_model_array_candidate(|index| {
        ChcExpr::and(
            ChcExpr::lt(index.clone(), ChcExpr::int(0)),
            ChcExpr::ge(index, ChcExpr::int(0)),
        )
    });
    let original = problem.clone();
    let Some(model) = AdaptivePortfolio::try_top_model_query_infeasibility_candidate(
        &problem,
        Duration::from_millis(500),
    ) else {
        panic!("contradictory original query constraint should admit the top model");
    };

    assert!(
        crate::engines::validate_external_invariant_model(
            &original,
            &model,
            &PdrConfig {
                strict_proofs: true,
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        )
        .expect("fresh unchanged-original validation should complete"),
        "the returned top model must independently satisfy every original clause"
    );
}

#[test]
#[timeout(5_000)]
fn test_top_model_query_infeasibility_rejects_satisfiable_query_constraint() {
    let problem = create_top_model_array_candidate(|index| ChcExpr::eq(index, ChcExpr::int(0)));

    assert!(
        AdaptivePortfolio::try_top_model_query_infeasibility_candidate(
            &problem,
            Duration::from_millis(500),
        )
        .is_none(),
        "a SAT query under the top interpretation must fail closed"
    );
}

#[test]
#[timeout(60_000)]
fn test_top_model_query_infeasibility_solves_hcai_targets() {
    // Wall-clock-deadline route test. Green in ISOLATION on every measured
    // host since the 2026-08-17 wave (the Farkas byte/hole phantom charges
    // and the 750ms validation reserve were the real defects); under a FULL
    // 16-way parallel debug suite on a Grace box every 5s attempt window is
    // still scheduler-starved — the env lock and bounded retries below help
    // at moderate load but cannot beat sustained full-suite contention, and
    // the route budget cap deliberately refuses to let a test grant more
    // wall. Treat a full-suite-only failure here as load, not regression:
    // `cargo test -p ay-chc --lib test_top_model_query_infeasibility` is the
    // authoritative check.
    let _env_guard = lock_env();
    let corpus_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/chc/chc-comp25-benchmarks/hcai-bench/svcomp/O0");
    for (name, file_name) in [
        (
            "trex02",
            "O0_trex02_true-unreach-call_true-termination_000.smt2",
        ),
        (
            "OpenSER stripFullBoth_arr",
            "O0_veris.c_OpenSER__cases1_stripFullBoth_arr_true-unreach-call_true-termination_000.smt2",
        ),
    ] {
        let path = corpus_root.join(file_name);
        let input = match std::fs::read_to_string(&path) {
            Ok(input) => input,
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                eprintln!(
                    "skipping HCAI corpus regression: download benchmarks first ({})",
                    path.display()
                );
                return;
            }
            Err(error) => panic!("failed to read {}: {error}", path.display()),
        };
        let problem =
            ChcParser::parse(&input).unwrap_or_else(|error| panic!("{name} should parse: {error}"));
        assert!(
            AdaptivePortfolio::try_top_model_query_infeasibility_candidate(
                &problem,
                Duration::from_millis(500),
            )
            .is_none(),
            "{name} raw nullary-error encoding must not admit the top model"
        );
        let summary = PreprocessSummary::build(problem.clone(), false);
        assert!(
            summary.transformed_problem.queries().next().is_some(),
            "{name} must retain an explicit transformed query"
        );
        assert!(
            AdaptivePortfolio::try_top_model_query_infeasibility_candidate(
                &summary.transformed_problem,
                Duration::from_millis(500),
            )
            .is_some(),
            "{name} transformed query constraint must admit the top candidate"
        );
        let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());
        // Wall-clock route under a full parallel suite: one attempt's 5s
        // deadline is scheduler-load-sensitive (measured ~4.2s in isolation
        // on a Grace debug build once validation really checks the AUFLIA
        // Farkas lemmas). Retry a bounded number of times so contention flake
        // cannot masquerade as a route regression; a deterministic failure
        // still fails every attempt.
        let mut result = None;
        for _ in 0..3 {
            result = adaptive.try_reduced_lia_array_preprocessed_route(Some(
                Instant::now() + Duration::from_secs(5),
            ));
            if result.is_some() {
                break;
            }
        }
        let Some((PortfolioResult::Safe(_), ValidationEvidence::FullVerification)) = result else {
            panic!(
                "{name} should be discharged by the reduced, back-translated, \
                 original-validated top certificate; got {result:?}"
            );
        };
    }
}

// ============================================================================
// FORALL-ARR ghost-pair lane (agenda #16)
// ============================================================================

/// Safe problem whose invariant is necessarily quantified:
/// `forall i. a[i] = 0` (init const-0 array, transition re-writes 0).
fn create_array_ghost_pair_safe_problem() -> ChcProblem {
    ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-fun P ((Array Int Int) Int) Bool)\n\
         (assert (forall ((a (Array Int Int)))\n\
           (=> (= a ((as const (Array Int Int)) 0)) (P a 0))))\n\
         (assert (forall ((a (Array Int Int)) (a2 (Array Int Int)) (n Int))\n\
           (=> (and (P a n) (= a2 (store a n 0))) (P a2 (+ n 1)))))\n\
         (assert (forall ((a (Array Int Int)) (n Int) (q Int))\n\
           (=> (and (P a n) (<= 0 q) (not (= (select a q) 0))) false)))\n\
         (check-sat)\n",
    )
    .expect("ghost-pair safe fixture parses")
}

/// Unsafe variant: the initial array is unconstrained, so the query is
/// reachable.
fn create_array_ghost_pair_unsafe_problem() -> ChcProblem {
    ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-fun P ((Array Int Int) Int) Bool)\n\
         (assert (forall ((a (Array Int Int))) (P a 0)))\n\
         (assert (forall ((a (Array Int Int)) (a2 (Array Int Int)) (n Int))\n\
           (=> (and (P a n) (= a2 (store a n 0))) (P a2 (+ n 1)))))\n\
         (assert (forall ((a (Array Int Int)) (n Int) (q Int))\n\
           (=> (and (P a n) (not (= (select a q) 0))) false)))\n\
         (check-sat)\n",
    )
    .expect("ghost-pair unsafe fixture parses")
}

/// Safe quantified-array loop hidden behind inlineable entry/exit wrappers.
///
/// After ghost instrumentation, clause inlining removes A/Q/R and predicate
/// compaction remaps the surviving recursive P.  This exercises the exact
/// vocabulary reconstruction required before the original-problem quantified
/// certificate can be sealed.
fn create_array_ghost_pair_compaction_safe_problem() -> ChcProblem {
    ChcParser::parse(
        "(set-logic HORN)\n\
         (declare-fun A ((Array Int Int) Int) Bool)\n\
         (declare-fun P ((Array Int Int) Int) Bool)\n\
         (declare-fun Q ((Array Int Int) Int) Bool)\n\
         (declare-fun R ((Array Int Int) Int) Bool)\n\
         (assert (forall ((a (Array Int Int)))\n\
           (=> (= a ((as const (Array Int Int)) 0)) (A a 0))))\n\
         (assert (forall ((a (Array Int Int)) (n Int))\n\
           (=> (A a n) (P a n))))\n\
         (assert (forall ((a (Array Int Int)) (a2 (Array Int Int)) (n Int))\n\
           (=> (and (P a n) (= a2 (store a n 0))) (P a2 (+ n 1)))))\n\
         (assert (forall ((a (Array Int Int)) (n Int))\n\
           (=> (P a n) (Q a n))))\n\
         (assert (forall ((a (Array Int Int)) (n Int))\n\
           (=> (Q a n) (R a n))))\n\
         (assert (forall ((a (Array Int Int)) (n Int) (q Int))\n\
           (=> (and (R a n) (not (= (select a q) 0))) false)))\n\
         (check-sat)\n",
    )
    .expect("ghost-pair compaction fixture parses")
}

#[test]
#[timeout(120000)]
fn test_array_ghost_pair_route_kill_switch_returns_none() {
    let _env_guard = lock_env();
    let problem = create_array_ghost_pair_safe_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let ghost_pair_disable = ScopedEnvVar::set(ARRAY_GHOST_PAIR_DISABLE_ENV, "1");
    let result = adaptive.try_array_ghost_pair_route(None);
    drop(ghost_pair_disable);

    assert!(
        result.is_none(),
        "AY_CHC_DISABLE_ARRAY_GHOST_PAIRS must disable the ghost-pair lane"
    );
}

#[test]
#[timeout(300000)]
fn test_array_ghost_pair_route_never_reports_safe_on_unsafe_problem() {
    let _env_guard = lock_env();
    let problem = create_array_ghost_pair_unsafe_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    let result = adaptive.try_array_ghost_pair_route(None);

    assert!(
        !matches!(result, Some((PortfolioResult::Safe(_), _))),
        "ghost-pair lane must never certify Safe on an unsafe array problem"
    );
}

/// POSITIVE end-to-end lane pin: on the safe fixture (whose invariant is
/// necessarily quantified — `forall i. a[i] = 0`) the route must discover the
/// ghost invariant with PDR, seal the quantified certificate on the ORIGINAL
/// clauses, and survive the finalize re-check. Guards against regressions that
/// silently degrade the lane to always-unknown (e.g. a nonlinear transformed
/// encoding stalling the PDR core at frame 1).
#[test]
#[timeout(300000)]
fn test_array_ghost_pair_route_certifies_safe_quantified_fixture() {
    let _env_guard = lock_env();
    let problem = create_array_ghost_pair_safe_problem();
    let adaptive = AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

    // A HANG GUARD's worth of budget, deliberately NOT a contention probe.
    //
    // Passing `None` means "unbounded run", which pins the route to its 8s
    // NOMINAL; that nominal splits down to a 4.2s wall-clock PDR sub-budget
    // (70% lane share, less the 25% certify reserve) for a solve that takes
    // ~1.0s in isolation. Measured under a default-parallelism `cargo test`
    // (16-way on this machine) the very same solve inflates ~3.7x to 3.67s --
    // already 87% of the sub-budget, with no code change involved. Any
    // additional suite-wide load pushes it to exactly 4.2s, PDR returns
    // Unknown, the route returns None, and this test fails having measured
    // nothing but scheduler contention.
    //
    // Production never takes the `None` path here: the portfolio calls this
    // route with `solve_deadline()`, so supplying a deadline is also the more
    // representative shape. It yields the route's 45s `BUDGET_CAP` and a
    // ~23.6s PDR sub-budget, ~24x the isolated solve, which the measured 3.7x
    // contention factor cannot reach.
    //
    // The `#[timeout(300000)]` above remains the real hang guard. The
    // regression this test exists to catch -- the lane silently degrading to
    // always-unknown, e.g. a nonlinear transformed encoding stalling the PDR
    // core at frame 1 -- fails the assertions below at ANY budget, so a
    // generous one costs nothing in coverage.
    let deadline = Instant::now() + Duration::from_mins(4);
    let result = adaptive.try_array_ghost_pair_route(Some(deadline));

    let Some((PortfolioResult::Safe(model), evidence)) = result else {
        panic!("ghost-pair route must certify the safe quantified fixture, got {result:?}");
    };
    assert!(
        matches!(
            evidence,
            ValidationEvidence::QuantifiedArrayInvariantCertificate
        ),
        "route Safe must carry the quantified-certificate evidence, got {evidence:?}"
    );
    assert!(
        model.has_quantified_array_certificate(),
        "route Safe model must carry the sealed certificate"
    );
    assert!(
        model.is_empty(),
        "quantifier-free interpretations must stay empty (the certificate is the witness)"
    );

    // The certified result survives the finalize boundary as Safe.
    let finalized = adaptive.finalize_verified_result(PortfolioResult::Safe(model), evidence);
    assert!(
        matches!(finalized, VerifiedChcResult::Safe(_)),
        "finalize must accept the sealed certificate on its own problem, got {finalized:?}"
    );
}

/// Regression for the preprocessed ghost lane's most important trust
/// boundary: PDR solves in compacted predicate space, preprocessing rebuilds
/// every inlined RAW-ghost interpretation, and only that reconstructed model
/// is allowed into original-clause quantified certification.
#[test]
#[timeout(300000)]
fn test_array_ghost_pair_preprocess_reconstructs_compacted_model_before_certificate() {
    use crate::transform::{
        recheck_ghost_pair_certificate, ArrayGhostPairTransformer, GhostPairCertificate,
        GhostPairSpec, Transformer,
    };

    let _env_guard = lock_env();
    // Keep the regression specifically on ClauseInliner's compaction/model
    // reconstruction rather than letting the earlier condense superpass
    // remove the wrappers first.
    let condense_disable =
        crate::ab_switches::TestOverride::set(crate::ab_switches::ChcAbSwitches {
            condense: false,
            ..Default::default()
        });

    let original = create_array_ghost_pair_compaction_safe_problem();
    let spec = GhostPairSpec::analyze(&original, 1);
    let raw_transform = Box::new(ArrayGhostPairTransformer::new(1)).transform(original.clone());
    let raw_ghost_problem = raw_transform.problem;
    let raw_p = raw_ghost_problem
        .lookup_predicate("P")
        .expect("raw ghost P declared");
    assert_ne!(
        raw_p.index(),
        0,
        "P must begin after an inlineable predicate so compaction remaps it"
    );

    let summary =
        PreprocessSummary::build_with_graph_collapse(raw_ghost_problem.clone(), false, false);
    drop(condense_disable);
    assert_eq!(
        summary.transformed_problem.predicates().len(),
        1,
        "A/Q/R must inline, leaving only recursive P"
    );
    let compact_p = summary
        .transformed_problem
        .lookup_predicate("P")
        .expect("recursive P survives preprocessing");
    assert_ne!(
        compact_p, raw_p,
        "surviving P must be renumbered so the test covers predicate compaction"
    );
    assert!(
        raw_ghost_problem.predicates().len()
            >= summary
                .transformed_problem
                .predicates()
                .len()
                .saturating_mul(ARRAY_GHOST_PAIR_PREPROCESS_REDUCTION_FACTOR),
        "fixture must cross the adaptive lane's major-reduction gate"
    );

    // Supply the known compact invariant directly.  This regression targets
    // the acceptance boundary, not PDR's search completeness: for this
    // const-zero loop the final ghost value parameter is always zero.
    let compact_predicate = summary
        .transformed_problem
        .predicates()
        .first()
        .expect("recursive compact predicate exists");
    assert_eq!(compact_predicate.id, compact_p);
    assert_eq!(
        compact_predicate.arg_sorts.last(),
        Some(&ChcSort::Int),
        "the final compact argument must be the ghost value"
    );
    let compact_params: Vec<_> = compact_predicate
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(index, sort)| {
            ChcVar::new(format!("__p{}_a{index}", compact_p.index()), sort.clone())
        })
        .collect();
    let ghost_value = ChcExpr::var(
        compact_params
            .last()
            .expect("instrumented predicate has a ghost value")
            .clone(),
    );
    let mut compact_model = InvariantModel::new();
    compact_model.set(
        compact_p,
        PredicateInterpretation::new(compact_params, ChcExpr::eq(ghost_value, ChcExpr::int(0))),
    );
    let raw_ghost_model = summary.back_translator.translate_validity(compact_model);
    for predicate in raw_ghost_problem.predicates() {
        let interpretation = raw_ghost_model.get(&predicate.id).unwrap_or_else(|| {
            panic!(
                "preprocess validity backtranslation did not reconstruct '{}'",
                predicate.name
            )
        });
        assert_eq!(
            interpretation.vars.len(),
            predicate.arity(),
            "reconstructed '{}' interpretation has the wrong raw-ghost arity",
            predicate.name
        );
    }

    let certificate = GhostPairCertificate::certify_and_seal(
        &original,
        spec,
        raw_ghost_model,
        Some(Duration::from_mins(1)),
    )
    .expect("reconstructed raw-ghost model must seal on the original clauses");
    assert!(
        recheck_ghost_pair_certificate(
            &original,
            certificate.as_ref(),
            Some(Duration::from_mins(1)),
            false,
        ),
        "sealed certificate must survive a full original-clause recheck"
    );
}

/// SOUNDNESS PIN at the finalize boundary: a sealed ghost-pair certificate is
/// only valid for the problem it was sealed against. Presenting it to a
/// portfolio solving a DIFFERENT (unsafe) problem must demote to Unknown —
/// this is exactly the wrong-verdict a naive lane (trusting the transformed
/// verdict, or trusting the certificate without re-checking) would emit.
#[test]
#[timeout(120000)]
fn test_finalize_demotes_ghost_pair_certificate_from_wrong_problem() {
    use crate::transform::{GhostPairCertificate, GhostPairSpec};

    let safe_problem = create_array_ghost_pair_safe_problem();
    let p = safe_problem.predicates()[0].id;
    let spec = GhostPairSpec::analyze(&safe_problem, 1);

    // Ghost model `I'(a, n, idx, val) := val = 0` — the quantified invariant
    // `forall i. a[i] = 0` — genuinely certifies on the SAFE problem.
    let vars = vec![
        ChcVar::new(
            format!("__p{}_a0", p.index()),
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
        ),
        ChcVar::new(format!("__p{}_a1", p.index()), ChcSort::Int),
        ChcVar::new(format!("__p{}_a2", p.index()), ChcSort::Int),
        ChcVar::new(format!("__p{}_a3", p.index()), ChcSort::Int),
    ];
    let val_var = ChcExpr::var(vars[3].clone());
    let mut ghost_model = InvariantModel::new();
    ghost_model.set(
        p,
        PredicateInterpretation::new(vars, ChcExpr::eq(val_var, ChcExpr::int(0))),
    );
    let certificate = GhostPairCertificate::certify_and_seal(
        &safe_problem,
        spec,
        ghost_model,
        Some(Duration::from_secs(30)),
    )
    .expect("val=0 ghost model must seal on the safe fixture");

    let mut certified_model = InvariantModel::new();
    certified_model.set_ghost_pair_certificate(certificate);

    // Accepted on the problem it was sealed against.
    let safe_adaptive = AdaptivePortfolio::new(
        create_array_ghost_pair_safe_problem(),
        AdaptiveConfig::test_default(),
    );
    let accepted = safe_adaptive.finalize_verified_result(
        PortfolioResult::Safe(certified_model.clone()),
        ValidationEvidence::QuantifiedArrayInvariantCertificate,
    );
    assert!(
        matches!(accepted, VerifiedChcResult::Safe(_)),
        "sealed certificate must be accepted on its own problem, got {accepted:?}"
    );

    // Demoted on a different (unsafe) problem: the finalize re-check re-runs
    // the quantified per-rule discharge against THIS portfolio's clauses.
    let unsafe_adaptive = AdaptivePortfolio::new(
        create_array_ghost_pair_unsafe_problem(),
        AdaptiveConfig::test_default(),
    );
    let demoted = unsafe_adaptive.finalize_verified_result(
        PortfolioResult::Safe(certified_model),
        ValidationEvidence::QuantifiedArrayInvariantCertificate,
    );
    assert!(
        matches!(demoted, VerifiedChcResult::Unknown(_)),
        "certificate for a different problem must demote to Unknown, got {demoted:?}"
    );
}

// ---------------------------------------------------------------------------
// Cancellation handle (wishlist item 5) — bounded timeout and cancellation
// ---------------------------------------------------------------------------

/// Nonlinear orbit whose error state is off-orbit at a huge magnitude: no
/// engine proves Safe (needs the exact nonlinear orbit) and no bounded search
/// reaches the target, so the solve deterministically grinds its budget.
fn guard_timeout_class_problem() -> ChcProblem {
    let input = r#"
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 2) (= y 3)) (inv x y))))
(assert (forall ((x Int) (y Int) (x2 Int) (y2 Int))
    (=> (and (inv x y) (= x2 (+ (* x x) y)) (= y2 (+ (* y y) x))) (inv x2 y2))))
(assert (forall ((x Int) (y Int)) (=> (and (inv x y) (= x 1234567891)) false)))
(check-sat)
"#;
    ChcParser::parse(input).expect("guard-timeout-class fixture parses")
}

#[test]
#[timeout(15000)]
fn guard_timeout_class_respects_small_budget() {
    let problem = guard_timeout_class_problem();
    let budget = Duration::from_millis(500);
    let config = AdaptiveConfig::with_budget(budget, false);
    let solver = AdaptivePortfolio::new(problem, config);
    let start = std::time::Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();
    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "bounded hard solve must fail closed to Unknown, got {result}"
    );
    assert!(
        elapsed < Duration::from_secs(10),
        "500ms solver budget was not enforced: elapsed={elapsed:?}"
    );
}

#[test]
#[timeout(120000)]
fn cancellation_handle_cancels_solve_from_another_thread() {
    // Item 5: an embedding driver (the model-checker-consumer guard) cancels a hard solve
    // mid-flight from another thread; the solve must wind down promptly with
    // Unknown instead of burning its whole 10-minute budget on a thread the
    // driver would previously have had to orphan (KNOWN-UNCANCELLABLE).
    let problem = guard_timeout_class_problem();
    // Budget far beyond the wall-clock assertion bound below, so only the
    // external cancel can explain a prompt return (the bounded test above
    // establishes that this fixture otherwise consumes its allotted budget).
    let config = AdaptiveConfig::with_budget(Duration::from_mins(10), false);
    let solver = AdaptivePortfolio::new(problem, config);
    let handle = solver.cancellation_handle();

    let canceller = std::thread::spawn(move || {
        std::thread::sleep(Duration::from_millis(300));
        handle.cancel();
    });

    let start = std::time::Instant::now();
    let result = solver.solve();
    let elapsed = start.elapsed();
    canceller.join().expect("canceller thread");

    assert!(
        matches!(result, VerifiedChcResult::Unknown(_)),
        "externally cancelled solve must degrade to Unknown, got {result}"
    );
    // Generous bound (vs. the ~0.3s cancel point) to avoid contention flakes;
    // the point is that it returns nowhere near the 600s budget.
    assert!(
        elapsed < Duration::from_mins(1),
        "cancelled solve took {:.1}s — cancellation did not propagate promptly",
        elapsed.as_secs_f64()
    );
}

// ===========================================================================
// Item 4 Stage 0 acceptance fixes: double-run query-only discharge +
// #9227 equisat re-keyed empty-model acyclic exhaustion.
// ===========================================================================

/// Small acyclic scalar-safe DAG: P0(x) with x=1, error requires x=9.
fn stage0_scalar_acyclic_safe_problem() -> ChcProblem {
    parse_benchmark(
        r#"
(set-logic HORN)
(declare-var x Int)
(declare-rel P0 (Int))
(declare-rel error ())
(rule (=> (= x 1) (P0 x)))
(rule (=> (and (P0 x) (= x 9)) error))
(query error)
"#,
        "stage0-scalar-acyclic-safe",
    )
}

/// Same DAG threaded through an array table (still safe).
fn stage0_array_acyclic_safe_problem() -> ChcProblem {
    parse_benchmark(
        r#"
(set-logic HORN)
(declare-var A (Array Int Int))
(declare-var x Int)
(declare-rel P0 ((Array Int Int) Int))
(declare-rel error ())
(rule (=> (and (= (select A 1) 5) (= x 1)) (P0 A x)))
(rule (=> (and (P0 A x) (= x 9)) error))
(query error)
"#,
        "stage0-array-acyclic-safe",
    )
}

fn equisat_grade_memory() -> crate::transform::TransformMemoryReport {
    crate::transform::TransformMemoryReport::with_original_validation_obligations(
        "test-equisat-chain",
        [
            crate::transform::TransformObligation::named("clause-local-store-forwarding"),
            crate::transform::TransformObligation::named("original-validation-on-safe"),
            crate::transform::TransformObligation::named("original-replay-on-unsafe"),
        ],
    )
}

fn non_equisat_memory() -> crate::transform::TransformMemoryReport {
    crate::transform::TransformMemoryReport::with_original_validation_obligations(
        "test-abstraction-chain",
        [
            crate::transform::TransformObligation::named("array-scalarization-map"),
            crate::transform::TransformObligation::named("original-validation-on-safe"),
        ],
    )
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(30_000))]
fn test_9227_rekey_rejects_array_carrying_transformed_problem() {
    let problem = stage0_array_acyclic_safe_problem();
    let adaptive = AdaptivePortfolio::new(
        problem.clone(),
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    // Transformed problem STILL carries arrays -> promotion must refuse even
    // under an equisat-grade chain.
    assert!(
        adaptive
            .try_promote_equisat_acyclic_exhaustion(
                &problem,
                &equisat_grade_memory(),
                4,
                Duration::from_secs(5),
            )
            .is_none(),
        "array-carrying transformed problem must never be promoted (#9227)"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(30_000))]
fn test_9227_rekey_rejects_non_equisat_chain() {
    // The REGRESSION the plan mandates: an empty-model array Safe whose
    // transform chain is NOT equisat-grade stays rejected even though the
    // transformed problem itself is array-free and provably safe.
    let array_original = stage0_array_acyclic_safe_problem();
    let scalar_transformed = stage0_scalar_acyclic_safe_problem();
    let adaptive = AdaptivePortfolio::new(
        array_original,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    assert!(
        adaptive
            .try_promote_equisat_acyclic_exhaustion(
                &scalar_transformed,
                &non_equisat_memory(),
                4,
                Duration::from_secs(5),
            )
            .is_none(),
        "non-equisat transform chain must keep the #9227 fail-closed rejection"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(120_000))]
#[cfg_attr(not(debug_assertions), timeout(60_000))]
fn test_9227_rekey_promotes_equisat_array_free_chain_with_fresh_rerun() {
    let array_original = stage0_array_acyclic_safe_problem();
    let scalar_transformed = stage0_scalar_acyclic_safe_problem();
    let adaptive = AdaptivePortfolio::new(
        array_original,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(20)),
    );
    let promoted = adaptive.try_promote_equisat_acyclic_exhaustion(
        &scalar_transformed,
        &equisat_grade_memory(),
        4,
        Duration::from_secs(10),
    );
    assert!(
        matches!(
            promoted,
            Some(ValidationEvidence::EquisatAcyclicBmcExhaustive { .. })
        ),
        "equisat array-free chain + confirming fresh re-run must promote, got {promoted:?}"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(30_000))]
fn test_checked_query_only_discharge_finalize_accepts_acyclic() {
    let problem = stage0_scalar_acyclic_safe_problem();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    let verified = adaptive.finalize_verified_result(
        PortfolioResult::Safe(InvariantModel::default()),
        ValidationEvidence::CheckedQueryOnlyDischarge { query_count: 1 },
    );
    assert!(
        matches!(verified, VerifiedChcResult::Safe(_)),
        "acyclic double-run discharge Safe must be accepted at finalize, got {verified}"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(30_000))]
fn test_checked_query_only_discharge_finalize_demotes_cyclic() {
    // Defense in depth: the evidence is complete only for acyclic problems.
    let problem = create_simple_loop();
    let adaptive = AdaptivePortfolio::new(
        problem,
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );
    let verified = adaptive.finalize_verified_result(
        PortfolioResult::Safe(InvariantModel::default()),
        ValidationEvidence::CheckedQueryOnlyDischarge { query_count: 1 },
    );
    assert!(
        matches!(verified, VerifiedChcResult::Unknown(_)),
        "cyclic problem carrying acyclic double-run evidence must demote, got {verified}"
    );
}

#[test]
#[cfg_attr(debug_assertions, timeout(60_000))]
#[cfg_attr(not(debug_assertions), timeout(30_000))]
fn test_recheck_query_only_discharge_confirms_unsat_bodies_and_rejects_sat() {
    let adaptive = AdaptivePortfolio::new(
        stage0_scalar_acyclic_safe_problem(),
        AdaptiveConfig::test_default().with_time_budget(Duration::from_secs(10)),
    );

    // Predicate-free query-only problem with an UNSAT body -> recheck
    // confirms. (Mirrors the shape exact preprocessing produces: zero
    // predicates, every clause a bodyless-predicate query.)
    let x = ChcVar::new("x", ChcSort::Int);
    let mut unsat_query_only = ChcProblem::new();
    unsat_query_only.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        )),
        ClauseHead::False,
    ));
    assert!(
        adaptive.recheck_query_only_discharge(&unsat_query_only, Duration::from_secs(5)),
        "UNSAT query bodies must re-confirm on a fresh executor"
    );

    // Predicate-free query-only problem with a SAT body -> recheck fails
    // closed.
    let mut sat_query_only = ChcProblem::new();
    sat_query_only.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))),
        ClauseHead::False,
    ));
    assert!(
        !adaptive.recheck_query_only_discharge(&sat_query_only, Duration::from_secs(5)),
        "a satisfiable query body must fail the recheck"
    );
}

/// Build the BV wide-hub archetype analogue for the BMC-only scalarized
/// ground-witness landing regression (model-checker-consumer item 4 mirror).
///
/// Shape (mirrors what makes `Coroutines/iterator-count` convert, scaled
/// down; sized SMALL — 2 layers of 3 lanes — so the converting solve has a
/// multiple-x wall-clock margin inside the test budget even on a heavily
/// loaded machine):
/// - a short unique-definition front chain the CondenseSuperpass contracts
///   (making the condense-first round non-identity),
/// - two layers of three hub lanes with full 3x3 coupling whose defining
///   clauses use three DISTINCT head-argument equality patterns, so
///   MultiEdgeMerger can never fold them and golem's
///   `|in|*|out| <= |in|+|out|` rule blocks node contraction (no multi-def
///   expansion anywhere — the ClauseInliner ground back-translation stays
///   1:1/composite),
/// - two unmergeable queries per last-layer lane (distinct body-argument
///   patterns) so every lane keeps out-degree 2 and the query side cannot be
///   contracted either,
/// - a long PAD chain that is backward-unreachable from every query: it
///   lifts the ORIGINAL problem past the >128-predicate BMC-only lane gate
///   and is then dropped by condense's reachability pruning.
///
/// `reachable` picks the error guard: `n = S_min` is hit by the all-lane-0
/// path (UNSAFE), `n > S_max` is above the true maximum (SAFE).
fn bmc_only_hub_analogue_smt(reachable: bool) -> String {
    let front = 6usize;
    let layers = 2usize;
    let width = 3usize;
    let pads = 120usize;
    let bv = |v: usize| format!("(_ bv{v} 8)");
    let mut smt = String::from("(set-logic HORN)\n");
    let decl = |smt: &mut String, name: &str| {
        smt.push_str(&format!(
            "(declare-fun {name} ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) Bool)\n"
        ));
    };
    for k in 0..front {
        decl(&mut smt, &format!("C{k}"));
    }
    for j in 0..layers {
        for l in 0..width {
            decl(&mut smt, &format!("H{j}_{l}"));
        }
    }
    for p in 0..pads {
        decl(&mut smt, &format!("PAD{p}"));
    }
    let s_min = (front - 1) + 1 + (layers - 1);
    let s_max = (front - 1) + width * layers;
    let head_args = |ls: usize| match ls {
        0 => "m m m",
        1 => "m m n",
        _ => "m n m",
    };
    smt.push_str(&format!("(assert (C0 {} {} {}))\n", bv(0), bv(0), bv(0)));
    let vars = "((n (_ BitVec 8)) (a (_ BitVec 8)) (b (_ BitVec 8)) (m (_ BitVec 8)))";
    for k in 0..front - 1 {
        smt.push_str(&format!(
            "(assert (forall {vars} (=> (and (C{k} n a b) (= m (bvadd n {}))) (C{} m m m))))\n",
            bv(1),
            k + 1
        ));
    }
    let hub_edge = |smt: &mut String, src: &str, dst: &str, ls: usize| {
        smt.push_str(&format!(
            "(assert (forall {vars} (=> (and ({src} n a b) (= m (bvadd n {}))) ({dst} {}))))\n",
            bv(1 + ls),
            head_args(ls)
        ));
    };
    for l in 0..width {
        for ls in 0..width {
            hub_edge(&mut smt, &format!("C{}", front - 1), &format!("H0_{l}"), ls);
        }
    }
    for j in 0..layers - 1 {
        for ls in 0..width {
            for ld in 0..width {
                hub_edge(
                    &mut smt,
                    &format!("H{j}_{ls}"),
                    &format!("H{}_{ld}", j + 1),
                    ls,
                );
            }
        }
    }
    smt.push_str(&format!(
        "(assert (forall {vars} (=> (and (H{}_0 n a b) (= m (bvadd n {}))) (PAD0 m m m))))\n",
        layers - 1,
        bv(1)
    ));
    for p in 0..pads - 1 {
        smt.push_str(&format!(
            "(assert (forall {vars} (=> (and (PAD{p} n a b) (= m (bvadd n {}))) (PAD{} m m m))))\n",
            bv(1),
            p + 1
        ));
    }
    let g_hit = format!("(= n {})", bv(s_min));
    let g_miss = format!("(bvugt n {})", bv(s_max));
    let qvars = "((n (_ BitVec 8)) (a (_ BitVec 8)) (b (_ BitVec 8)))";
    for l in 0..width {
        let g1 = if reachable { &g_hit } else { &g_miss };
        smt.push_str(&format!(
            "(assert (forall {qvars} (=> (and (H{}_{l} n a b) {g1} (bvuge a n) (bvuge b a)) false)))\n",
            layers - 1
        ));
        smt.push_str(&format!(
            "(assert (forall {qvars} (=> (and (H{}_{l} n a a) {g_miss} (bvuge a n)) false)))\n",
            layers - 1
        ));
    }
    smt.push_str("(check-sat)\n");
    smt
}

/// BMC-only config mirroring the model-checker-consumer native acyclic-BMC shortcut
/// (`tools` driver: max_depth = predicate count, acyclic_safe, per-depth
/// timeout `min(budget/4, 10s)`).
fn bmc_only_lane_config(problem: &ChcProblem, budget: Duration) -> crate::BmcConfig {
    crate::BmcConfig::default()
        .with_max_depth(problem.predicates().len().max(1))
        .with_acyclic_safe(true)
        .with_time_budget(budget)
        .with_per_depth_timeout((budget / 4).min(Duration::from_secs(10)))
}

/// Item-4 BMC-only mirror regression: the >128-predicate, condense-scalarizable
/// UNSAFE analogue must convert THROUGH `engines::solve_bmc_only`, and the
/// verdict must be carried by a ground derivation that validates against the
/// ORIGINAL clauses (the ground-witness back-translation landing). Without the
/// landing this instance is a fail-closed Unknown (its transform chain does not
/// admit plain witness back-translation), so this test pins the landing itself,
/// not merely the verdict.
#[test]
#[timeout(360_000)]
#[serial_test::serial(bmc_only_hub_analogue)]
fn bmc_only_lane_lands_ground_backtranslated_unsafe_on_hub_analogue() {
    let smt = bmc_only_hub_analogue_smt(true);
    let problem = ChcParser::parse(&smt).unwrap_or_else(|err| panic!("parse failed: {err}"));
    assert!(
        AdaptivePortfolio::is_large_acyclic_linear_graph(&ProblemClassifier::classify(&problem)),
        "analogue must be in the BMC-only condense-first class"
    );
    let original = problem.clone();
    // Generous budget: the probe's level-BMC split (min(remaining/2, 90s))
    // runs first and cannot decide this instance (multi-lane queries — see
    // the upstream note in the response doc), so the converting follow-on
    // must still get a heavily-loaded-machine-sized slice behind it.
    let config = bmc_only_lane_config(&problem, Duration::from_secs(210));
    let result = crate::engines::solve_bmc_only(problem, config);
    let VerifiedChcResult::Unsafe(verified) = result else {
        panic!("UNSAFE hub analogue did not convert through the BMC-only lane: {result}");
    };
    let cex = verified.counterexample();
    assert!(
        cex.has_ground_derivation(),
        "BMC-only Unsafe verdict must be carried by the ground-witness landing"
    );
    let derivation = cex
        .ground_derivation
        .as_ref()
        .expect("has_ground_derivation checked above");
    crate::ground_derivation::validate_ground_derivation(&original, derivation)
        .expect("promoted derivation must ground-validate against the ORIGINAL clauses");
}

include!("adaptive_tests/final_validation_budget.rs");
