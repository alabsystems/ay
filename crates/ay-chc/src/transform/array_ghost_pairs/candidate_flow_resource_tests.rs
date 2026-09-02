// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Resource-bound regressions for reverse CFG candidate transport.

use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn nth_permutation(mut ordinal: usize, width: usize) -> Vec<usize> {
    let mut pool: Vec<usize> = (0..width).collect();
    let mut permutation = Vec::with_capacity(width);
    while !pool.is_empty() {
        let choice = ordinal % pool.len();
        ordinal /= pool.len();
        permutation.push(pool.remove(choice));
    }
    permutation
}

#[test]
fn paths_that_differ_only_on_unused_columns_share_one_state() {
    const UNUSED_COLUMNS: usize = 9;
    const DISTINCT_EDGES: usize = 256;

    let array = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)));
    let mut sorts = vec![ChcSort::BitVec(32), array];
    sorts.extend((0..UNUSED_COLUMNS).map(|_| ChcSort::BitVec(32)));

    let mut problem = ChcProblem::new();
    let predecessor = problem.declare_predicate("predecessor", sorts.clone());
    let source = problem.declare_predicate("source", sorts.clone());
    let body_args: Vec<ChcExpr> = sorts
        .iter()
        .enumerate()
        .map(|(position, sort)| var(&format!("v{position}"), sort.clone()))
        .collect();

    for ordinal in 0..DISTINCT_EDGES {
        let mut head_args = body_args[..2].to_vec();
        head_args.extend(
            nth_permutation(ordinal, UNUSED_COLUMNS)
                .into_iter()
                .map(|position| body_args[position + 2].clone()),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(predecessor, body_args.clone())]),
            ClauseHead::Predicate(source, head_args),
        ));
    }

    let required: FxHashSet<usize> = [0, 1].into_iter().collect();
    let transports = super::bounded_reverse_transports(&problem, source, &required, None)
        .expect("irrelevant permutations must not exhaust the flow-state cap");
    assert_eq!(transports.len(), 2, "identity plus one predecessor state");
}
