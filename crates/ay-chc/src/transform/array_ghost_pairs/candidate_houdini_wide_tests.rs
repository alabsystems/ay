// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use ntest::timeout;

use super::*;
use crate::transform::{recheck_ghost_pair_certificate, ArrayGhostPairTransformer, Transformer};
use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

const NOISE_COLUMNS: usize = 90;

fn admitted_aggregate_wide_problem() -> ChcProblem {
    let key = ChcSort::BitVec(32);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value));
    let mut state_sorts = vec![array.clone()];
    state_sorts.extend((0..NOISE_COLUMNS).map(|_| key.clone()));

    let mut problem = ChcProblem::new();
    let states: Vec<_> = (0..3)
        .map(|number| problem.declare_predicate(format!("state_{number}"), state_sorts.clone()))
        .collect();
    let error_leaf = problem.declare_predicate("error_p4", Vec::new());
    let error = problem.declare_predicate("error", Vec::new());

    let initial_index = ChcExpr::var(ChcVar::new("initial_index", key.clone()));
    let initial_memory = ChcExpr::store(
        ChcExpr::const_array(key.clone(), ChcExpr::BitVec(0x2a, 8)),
        initial_index,
        ChcExpr::BitVec(0x2a, 8),
    );
    let mut initial = vec![initial_memory];
    initial.extend((0..NOISE_COLUMNS).map(|_| ChcExpr::BitVec(0, 32)));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(states[0], initial),
    ));

    let arguments = |prefix: &str| {
        let memory = ChcVar::new(format!("{prefix}_memory"), array.clone());
        let mut args = vec![ChcExpr::var(memory.clone())];
        args.extend((0..NOISE_COLUMNS).map(|column| {
            ChcExpr::var(ChcVar::new(format!("{prefix}_noise_{column}"), key.clone()))
        }));
        (memory, args)
    };
    for (edge, pair) in states.windows(2).enumerate() {
        let (_, args) = arguments(&format!("edge_{edge}"));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(pair[0], args.clone())]),
            ClauseHead::Predicate(pair[1], args),
        ));
    }

    let (query_memory, query_args) = arguments("query");
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(states[2], query_args)],
            Some(ChcExpr::ne(
                ChcExpr::select(ChcExpr::var(query_memory), ChcExpr::BitVec(0, 32)),
                ChcExpr::BitVec(0x2a, 8),
            )),
        ),
        ClauseHead::Predicate(error_leaf, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error_leaf, Vec::new())]),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        Vec::new(),
    )])));
    problem
}

#[test]
#[timeout(120000)]
fn aggregate_wide_state_keeps_mandatory_pool_below_global_cap() {
    let problem = admitted_aggregate_wide_problem();
    assert!(
        problem
            .clauses()
            .iter()
            .any(super::super::clause_has_symbolic_index),
        "fixture must pass the adaptive route's symbolic-index gate"
    );
    assert!(
        problem
            .predicates()
            .iter()
            .all(|predicate| predicate.arity() <= 256),
        "every predicate must remain inside production route admission"
    );
    let spec = GhostPairSpec::analyze(&problem, 1);
    let raw = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem.clone())
        .problem;
    assert!(
        raw.predicates()
            .iter()
            .all(|predicate| predicate.arity() <= 272),
        "every transformed predicate must remain inside production route admission"
    );
    let now = Instant::now();
    let sealed = try_query_anchored_and_seal(
        &problem,
        &raw,
        &spec,
        now + Duration::from_secs(40),
        now + Duration::from_secs(80),
        &CancellationToken::new(),
        None,
    )
    .expect("three anchors and two false sinks must fit without 270 irrelevant BV supports");

    assert_eq!(sealed.candidates, 5);
    assert_eq!(sealed.survivors, 5);
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(10)),
        false,
    ));
    for state_name in ["state_0", "state_1", "state_2"] {
        let predicate = problem
            .get_predicate_by_name(state_name)
            .expect("state declaration");
        let interpretation = sealed
            .certificate
            .ghost_interpretation(predicate.id)
            .expect("state interpretation");
        assert_eq!(interpretation.vars.len(), NOISE_COLUMNS + 3);
        let used = interpretation.formula.vars();
        assert_eq!(used.len(), 2);
        assert!(used.contains(&interpretation.vars[NOISE_COLUMNS + 1]));
        assert!(used.contains(&interpretation.vars[NOISE_COLUMNS + 2]));
        assert!(
            interpretation.vars[..=NOISE_COLUMNS]
                .iter()
                .all(|variable| !used.contains(variable)),
            "irrelevant original BV columns must not enter the model"
        );
    }
    for sink_name in ["error_p4", "error"] {
        let predicate = problem
            .get_predicate_by_name(sink_name)
            .expect("sink declaration");
        let interpretation = sealed
            .certificate
            .ghost_interpretation(predicate.id)
            .expect("sink interpretation");
        assert!(interpretation.vars.is_empty());
        assert_eq!(interpretation.formula, ChcExpr::Bool(false));
    }
}
