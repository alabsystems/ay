// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::{CancellationToken, ChcParser, ClauseBody, HornClause};

use super::super::candidate::query_anchored_ghost_candidates;

const MODEL_CHECKER_CONSUMER_HARDER: &str =
    include_str!("../../../../../benchmarks/smt/chc_dt_array_model_checker_consumer_harder.smt2");
const MODEL_CHECKER_CONSUMER_MULTI: &str =
    include_str!("../../../../../benchmarks/smt/chc_loop_alloc_multi_pred.smt2");

fn supports(problem: &ChcProblem) -> Vec<(PredicateId, usize, u32)> {
    let spec = GhostPairSpec::analyze(problem, 1);
    let candidates =
        query_anchored_ghost_candidates(problem, &spec).expect("query-anchored candidates");
    demanded_nonzero_supports(problem, &spec, &candidates, None).expect("support analysis")
}

#[test]
fn harder_demands_only_the_symbolic_store_counter() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_HARDER)
        .expect("parse harder MODEL_CHECKER_CONSUMER canary");
    let invariant = problem
        .get_predicate_by_name("inv")
        .expect("inv predicate")
        .id;

    assert_eq!(supports(&problem), vec![(invariant, 3, 32)]);
}

#[test]
fn multi_cycle_closes_old_and_new_counter_columns() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_MULTI)
        .expect("parse multi MODEL_CHECKER_CONSUMER canary");
    let loop_inv = problem
        .get_predicate_by_name("loop_inv")
        .expect("loop_inv predicate")
        .id;
    let post_alloc = problem
        .get_predicate_by_name("post_alloc")
        .expect("post_alloc predicate")
        .id;
    let post_write = problem
        .get_predicate_by_name("post_write")
        .expect("post_write predicate")
        .id;
    let found: FxHashSet<_> = supports(&problem).into_iter().collect();
    let expected = FxHashSet::from_iter([
        (loop_inv, 3, 32),
        (post_alloc, 3, 32),
        (post_alloc, 4, 32),
        (post_write, 3, 32),
    ]);

    assert_eq!(found, expected);
}

#[test]
fn nonprefix_cfg_permutation_preserves_exact_support_column_identity() {
    let key = ChcSort::BitVec(32);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value.clone()));
    let mut problem = ChcProblem::new();
    let source =
        problem.declare_predicate("source", vec![array.clone(), key.clone(), value.clone()]);
    let target =
        problem.declare_predicate("target", vec![value.clone(), array.clone(), key.clone()]);

    let memory = ChcVar::new("store_memory", array.clone());
    let index = ChcVar::new("store_index", key.clone());
    let byte = ChcVar::new("store_byte", value.clone());
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            source,
            vec![
                ChcExpr::var(memory.clone()),
                ChcExpr::var(index.clone()),
                ChcExpr::var(byte.clone()),
            ],
        )]),
        ClauseHead::Predicate(
            source,
            vec![
                ChcExpr::store(
                    ChcExpr::var(memory),
                    ChcExpr::var(index.clone()),
                    ChcExpr::BitVec(0x2a, 8),
                ),
                ChcExpr::var(index),
                ChcExpr::var(byte),
            ],
        ),
    ));

    let memory = ChcVar::new("edge_memory", array.clone());
    let index = ChcVar::new("edge_index", key.clone());
    let byte = ChcVar::new("edge_byte", value.clone());
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            source,
            vec![
                ChcExpr::var(memory.clone()),
                ChcExpr::var(index.clone()),
                ChcExpr::var(byte.clone()),
            ],
        )]),
        ClauseHead::Predicate(
            target,
            vec![
                ChcExpr::var(byte),
                ChcExpr::var(memory),
                ChcExpr::var(index),
            ],
        ),
    ));

    let query_memory = ChcVar::new("query_memory", array);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            target,
            vec![
                ChcExpr::var(ChcVar::new("query_byte", value)),
                ChcExpr::var(query_memory.clone()),
                ChcExpr::var(ChcVar::new("query_index", key)),
            ],
        )],
        Some(ChcExpr::ne(
            ChcExpr::select(ChcExpr::var(query_memory), ChcExpr::BitVec(0, 32)),
            ChcExpr::BitVec(0x2a, 8),
        )),
    )));

    assert_eq!(supports(&problem), vec![(source, 1, 32), (target, 2, 32)]);
}

#[test]
fn admitted_wide_cfg_omits_more_than_the_global_candidate_cap_of_noise() {
    const NOISE_COLUMNS: usize = 90;

    let key = ChcSort::BitVec(32);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value));
    let mut sorts = vec![array.clone(), key.clone()];
    sorts.extend((0..NOISE_COLUMNS).map(|_| key.clone()));

    let mut problem = ChcProblem::new();
    let predicates: Vec<_> = (0..3)
        .map(|number| problem.declare_predicate(format!("P{number}"), sorts.clone()))
        .collect();
    let arguments = |prefix: &str| {
        let array_var = ChcVar::new(format!("{prefix}_a"), array.clone());
        let index_var = ChcVar::new(format!("{prefix}_idx"), key.clone());
        let noise: Vec<_> = (0..NOISE_COLUMNS)
            .map(|column| ChcVar::new(format!("{prefix}_noise_{column}"), key.clone()))
            .collect();
        let mut args = vec![
            ChcExpr::var(array_var.clone()),
            ChcExpr::var(index_var.clone()),
        ];
        args.extend(noise.iter().cloned().map(ChcExpr::var));
        (array_var, index_var, noise, args)
    };

    let (array_var, index_var, noise, body_args) = arguments("store");
    let mut head_args = vec![
        ChcExpr::store(
            ChcExpr::var(array_var),
            ChcExpr::var(index_var.clone()),
            ChcExpr::BitVec(0x2a, 8),
        ),
        ChcExpr::var(index_var),
    ];
    head_args.extend(noise.into_iter().map(ChcExpr::var));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(predicates[0], body_args)]),
        ClauseHead::Predicate(predicates[0], head_args),
    ));
    for (edge, pair) in predicates.windows(2).enumerate() {
        let (_, _, _, args) = arguments(&format!("edge_{edge}"));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(pair[0], args.clone())]),
            ClauseHead::Predicate(pair[1], args),
        ));
    }

    let (query_array, _, _, query_args) = arguments("query");
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicates[2], query_args)],
        Some(ChcExpr::ne(
            ChcExpr::select(ChcExpr::var(query_array), ChcExpr::BitVec(0, 32)),
            ChcExpr::BitVec(0x2a, 8),
        )),
    )));

    assert_eq!(
        supports(&problem),
        predicates
            .into_iter()
            .map(|predicate| (predicate, 1, 32))
            .collect::<Vec<_>>()
    );
}

#[test]
fn cancelled_support_analysis_fails_closed() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_HARDER)
        .expect("parse harder MODEL_CHECKER_CONSUMER canary");
    let spec = GhostPairSpec::analyze(&problem, 1);
    let candidates =
        query_anchored_ghost_candidates(&problem, &spec).expect("query-anchored candidates");
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let control = CandidateControl {
        cancellation: &cancellation,
        deadline: ay_core::time::Instant::now() + std::time::Duration::from_secs(30),
    };

    assert!(demanded_nonzero_supports(&problem, &spec, &candidates, Some(control)).is_none());
}
