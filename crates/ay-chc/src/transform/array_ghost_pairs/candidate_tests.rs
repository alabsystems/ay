// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{ChcParser, ClauseBody, ClauseHead, HornClause};

const MODEL_CHECKER_CONSUMER_HARDER: &str =
    include_str!("../../../../../benchmarks/smt/chc_dt_array_model_checker_consumer_harder.smt2");
const MODEL_CHECKER_CONSUMER_MULTI: &str =
    include_str!("../../../../../benchmarks/smt/chc_loop_alloc_multi_pred.smt2");

fn int_array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int))
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn one_array_problem(constraint: impl FnOnce(ChcExpr) -> ChcExpr) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![int_array()]);
    let array = var("array", int_array());
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(p, vec![ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0))]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![array.clone()])],
        Some(constraint(array)),
    )));
    problem
}

fn assert_scalar_candidate(candidate: &QueryAnchoredGhostCandidate) {
    assert_eq!(candidate.formula.sort(), ChcSort::Bool);
    let allowed: FxHashSet<ChcVar> = candidate.vars.iter().cloned().collect();
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    assert!(exact_scalar_walk(&candidate.formula, &allowed, 0, &mut remaining).is_some());
}

#[test]
fn derives_exact_bv32_bv64_candidate_for_model_checker_consumer_harder() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_HARDER)
        .expect("parse MODEL_CHECKER_CONSUMER harder canary");
    let spec = GhostPairSpec::analyze(&problem, 1);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("MODEL_CHECKER_CONSUMER harder query should yield a candidate");
    assert_eq!(candidates.len(), 1);
    let candidate = &candidates[0];
    assert_eq!(candidate.predicate, candidate.source_query_predicate);
    assert_eq!(candidate.vars.len(), 10);
    assert_scalar_candidate(candidate);

    let used = candidate.formula.vars();
    for position in [4usize, 5, 8, 9] {
        assert!(
            used.contains(&candidate.vars[position]),
            "candidate must use typed ghost parameter {position}: {}",
            candidate.formula
        );
    }
    assert_eq!(candidate.vars[4].sort, ChcSort::BitVec(32));
    assert_eq!(candidate.vars[5].sort, ChcSort::Bool);
    assert_eq!(candidate.vars[8].sort, ChcSort::BitVec(64));
    assert_eq!(candidate.vars[9].sort, ChcSort::BitVec(8));
    assert!(!used.contains(&candidate.vars[6]));
    assert!(!used.contains(&candidate.vars[7]));
}

#[test]
fn propagates_model_checker_consumer_multi_query_to_all_compatible_predicates() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_MULTI)
        .expect("parse MODEL_CHECKER_CONSUMER multi canary");
    let source = problem
        .get_predicate_by_name("loop_inv")
        .expect("loop_inv declaration")
        .id;
    let spec = GhostPairSpec::analyze(&problem, 1);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("MODEL_CHECKER_CONSUMER multi query should yield propagated candidates");
    assert_eq!(candidates.len(), 3);

    let mut predicates: Vec<_> = candidates
        .iter()
        .map(|candidate| candidate.predicate)
        .collect();
    predicates.sort_by_key(|predicate| predicate.index());
    predicates.dedup();
    assert_eq!(predicates.len(), 3);
    for candidate in &candidates {
        assert_eq!(candidate.source_query_predicate, source);
        assert_scalar_candidate(candidate);
        let layout = spec.preds.get(&candidate.predicate).expect("ghost layout");
        for array_index in 0..3 {
            let index_position = layout.original_arity + 2 * array_index;
            let value_position = index_position + 1;
            let used = candidate.formula.vars();
            assert!(used.contains(&candidate.vars[index_position]));
            assert!(used.contains(&candidate.vars[value_position]));
        }
    }
}

#[test]
fn rejects_query_with_multiple_body_predicates() {
    let mut problem = one_array_problem(|array| {
        ChcExpr::ne(ChcExpr::select(array, ChcExpr::Int(0)), ChcExpr::Int(0))
    });
    let query = problem.clauses().last().expect("query").clone();
    let (predicate, args) = query.body.predicates[0].clone();
    problem
        .clauses_mut()
        .last_mut()
        .expect("query")
        .body
        .predicates
        .push((predicate, args));
    let spec = GhostPairSpec::analyze(&problem, 1);
    assert!(query_anchored_ghost_candidates(&problem, &spec).is_none());
}

#[test]
fn rejects_leftover_array_term_after_select_rewrite() {
    let problem = one_array_problem(|array| {
        ChcExpr::and(
            ChcExpr::ne(
                ChcExpr::select(array.clone(), ChcExpr::Int(0)),
                ChcExpr::Int(0),
            ),
            ChcExpr::eq(array, ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0))),
        )
    });
    let spec = GhostPairSpec::analyze(&problem, 1);
    assert!(query_anchored_ghost_candidates(&problem, &spec).is_none());
}

#[test]
fn rejects_free_query_index() {
    let problem = one_array_problem(|array| {
        ChcExpr::ne(
            ChcExpr::select(array, var("free_index", ChcSort::Int)),
            ChcExpr::Int(0),
        )
    });
    let spec = GhostPairSpec::analyze(&problem, 1);
    assert!(query_anchored_ghost_candidates(&problem, &spec).is_none());
}

#[test]
fn rejects_more_distinct_accesses_than_ghost_slots() {
    let problem = one_array_problem(|array| {
        ChcExpr::or(
            ChcExpr::ne(
                ChcExpr::select(array.clone(), ChcExpr::Int(0)),
                ChcExpr::Int(0),
            ),
            ChcExpr::ne(ChcExpr::select(array, ChcExpr::Int(1)), ChcExpr::Int(0)),
        )
    });
    let spec = GhostPairSpec::analyze(&problem, 1);
    assert!(query_anchored_ghost_candidates(&problem, &spec).is_none());

    let spec = GhostPairSpec::analyze(&problem, 2);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("two ghost slots should cover two distinct accesses");
    assert_eq!(candidates.len(), 1);
    let candidate = &candidates[0];
    assert_scalar_candidate(candidate);
    assert_eq!(candidate.vars.len(), 5);
    let used = candidate.formula.vars();
    for position in 1..5 {
        assert!(used.contains(&candidate.vars[position]));
    }
}

#[test]
fn rejects_non_variable_body_argument_and_non_plain_array_base() {
    let mut non_variable = one_array_problem(|array| {
        ChcExpr::ne(ChcExpr::select(array, ChcExpr::Int(0)), ChcExpr::Int(0))
    });
    non_variable
        .clauses_mut()
        .last_mut()
        .expect("query")
        .body
        .predicates[0]
        .1[0] = ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0));
    let spec = GhostPairSpec::analyze(&non_variable, 1);
    assert!(query_anchored_ghost_candidates(&non_variable, &spec).is_none());

    let stored_base = one_array_problem(|array| {
        ChcExpr::ne(
            ChcExpr::select(
                ChcExpr::store(array, ChcExpr::Int(0), ChcExpr::Int(1)),
                ChcExpr::Int(0),
            ),
            ChcExpr::Int(0),
        )
    });
    let spec = GhostPairSpec::analyze(&stored_base, 1);
    assert!(query_anchored_ghost_candidates(&stored_base, &spec).is_none());
}

#[test]
fn rewrite_budget_is_shared_across_compatible_targets() {
    let one_target = one_array_problem(|array| {
        ChcExpr::ne(ChcExpr::select(array, ChcExpr::Int(0)), ChcExpr::Int(0))
    });
    let one_spec = GhostPairSpec::analyze(&one_target, 1);
    let one = query_anchored_ghost_candidates_with_budget(&one_target, &one_spec, 5)
        .expect("five rewrite nodes exactly cover one simple query candidate");
    assert_eq!(one.len(), 1);

    let mut two_targets = one_target;
    let q = two_targets.declare_predicate("Q", vec![int_array()]);
    two_targets.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(q, vec![ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0))]),
    ));
    let two_spec = GhostPairSpec::analyze(&two_targets, 1);
    assert!(
        query_anchored_ghost_candidates_with_budget(&two_targets, &two_spec, 5).is_none(),
        "the second target must exhaust the same meter and reject all candidates"
    );
    let two = query_anchored_ghost_candidates_with_budget(&two_targets, &two_spec, 10)
        .expect("ten rewrite nodes cover both simple target candidates");
    assert_eq!(two.len(), 2);
}

#[test]
fn exact_scalar_boundary_rejects_functions_and_datatype_terms() {
    let function = ChcExpr::FuncApp("opaque".to_string(), ChcSort::Int, Vec::new());
    let mut remaining = 4;
    assert!(
        exact_scalar_walk(&function, &FxHashSet::default(), 0, &mut remaining).is_none(),
        "even scalar-returning function applications are outside this candidate boundary"
    );

    let datatype_sort = ChcSort::Datatype {
        name: "Cell".to_string(),
        constructors: Arc::new(Vec::new()),
    };
    let datatype_var = ChcVar::new("cell", datatype_sort);
    let datatype_expr = ChcExpr::eq(
        ChcExpr::var(datatype_var.clone()),
        ChcExpr::var(datatype_var.clone()),
    );
    let allowed = [datatype_var].into_iter().collect();
    let mut remaining = 4;
    assert!(
        exact_scalar_walk(&datatype_expr, &allowed, 0, &mut remaining).is_none(),
        "a nested datatype-returning term must reject the whole candidate"
    );
}
