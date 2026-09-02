// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression coverage for reverse CFG transport of query-anchored candidates.
//!
//! This file is intended to be included as a child test module of the
//! candidate transport implementation, so its direct calls can pin bounded
//! fail-closed behavior without widening the production API.

use std::time::Duration;

use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::time::Instant;
use ntest::timeout;

use crate::transform::array_ghost_pairs::candidate::{
    query_anchored_ghost_candidates, query_anchored_ghost_candidates_controlled,
    QueryAnchoredGhostCandidate, MAX_PROPAGATED_CANDIDATES,
};
use crate::transform::array_ghost_pairs::{
    recheck_ghost_pair_certificate, try_query_anchored_and_seal, GhostPairSpec, QueryAnchoredSeal,
};
use crate::transform::{ArrayGhostPairTransformer, Transformer};
use crate::{
    CancellationToken, ChcExpr, ChcParser, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, PredicateId,
};

const NONPREFIX_FLOW: &str =
    include_str!("../../../../../benchmarks/smt/chc_model_checker_consumer_nonprefix_flow.smt2");

fn byte_array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, sort))
}

fn bad_query(count: ChcExpr, memory: ChcExpr) -> ChcExpr {
    ChcExpr::or(
        ChcExpr::eq(count, ChcExpr::BitVec(0, 32)),
        ChcExpr::ne(
            ChcExpr::select(memory, ChcExpr::BitVec(0, 64)),
            ChcExpr::BitVec(0x2a, 8),
        ),
    )
}

fn initialized_memory(value: u128) -> ChcExpr {
    ChcExpr::store(
        ChcExpr::const_array(ChcSort::BitVec(64), ChcExpr::BitVec(0, 8)),
        ChcExpr::BitVec(0, 64),
        ChcExpr::BitVec(value, 8),
    )
}

fn target_set(candidates: &[QueryAnchoredGhostCandidate]) -> FxHashSet<PredicateId> {
    candidates
        .iter()
        .map(|candidate| candidate.predicate)
        .collect()
}

#[test]
fn transports_used_columns_through_permutation_and_projection() {
    let problem = ChcParser::parse(NONPREFIX_FLOW).expect("parse non-prefix flow canary");
    let spec = GhostPairSpec::analyze(&problem, 1);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("query anchor should flow to every predecessor");

    let loop_id = problem.lookup_predicate("loop").expect("loop declaration");
    let stage_id = problem
        .lookup_predicate("stage")
        .expect("stage declaration");
    let check_id = problem
        .lookup_predicate("check")
        .expect("check declaration");
    assert_eq!(
        target_set(&candidates),
        [loop_id, stage_id, check_id].into_iter().collect()
    );

    for (predicate, count_position) in [(loop_id, 1), (stage_id, 2), (check_id, 0)] {
        let candidate = candidates
            .iter()
            .find(|candidate| candidate.predicate == predicate)
            .expect("one transported candidate per predicate");
        let layout = spec.preds.get(&predicate).expect("instrumented predicate");
        let used = candidate.formula.vars();
        assert!(
            used.contains(&candidate.vars[count_position]),
            "the used count column must follow its clause variable"
        );
        assert!(
            used.contains(&candidate.vars[layout.original_arity]),
            "ghost index must be recomputed from the target layout"
        );
        assert!(
            used.contains(&candidate.vars[layout.original_arity + 1]),
            "ghost value must be recomputed from the target layout"
        );
    }
}

#[test]
fn two_array_two_pair_transport_preserves_array_ordinal_and_pair_number() {
    let array = byte_array();
    let mut problem = ChcProblem::new();
    let predecessor = problem.declare_predicate(
        "predecessor",
        vec![array.clone(), ChcSort::BitVec(32), array.clone()],
    );
    let check = problem.declare_predicate(
        "check",
        vec![array.clone(), array.clone(), ChcSort::BitVec(32)],
    );
    let left = var("left", array.clone());
    let right = var("right", array.clone());
    let count = var("count", ChcSort::BitVec(32));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            predecessor,
            vec![right.clone(), count.clone(), left.clone()],
        )]),
        ClauseHead::Predicate(check, vec![left, right, count]),
    ));
    let query_left = var("query_left", array.clone());
    let query_right = var("query_right", array);
    let query_count = var("query_count", ChcSort::BitVec(32));
    let bad = ChcExpr::or(
        ChcExpr::ne(
            ChcExpr::select(query_right.clone(), ChcExpr::BitVec(0, 64)),
            ChcExpr::BitVec(0x2a, 8),
        ),
        ChcExpr::ne(
            ChcExpr::select(query_right.clone(), ChcExpr::BitVec(1, 64)),
            ChcExpr::BitVec(0x2b, 8),
        ),
    );
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(check, vec![query_left, query_right, query_count])],
        Some(bad),
    )));

    let spec = GhostPairSpec::analyze(&problem, 2);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("the second source array must transport to the first target array");
    let transported = candidates
        .iter()
        .filter(|candidate| candidate.predicate == predecessor)
        .find(|candidate| {
            let used = candidate.formula.vars();
            (3..7).all(|position| used.contains(&candidate.vars[position]))
        })
        .expect("both pairs of target array ordinal zero must be used");
    let used = transported.formula.vars();
    assert!(
        (7..11).all(|position| !used.contains(&transported.vars[position])),
        "the source array's old ordinal must not leak into target ghost positions"
    );
}

#[test]
fn raw_transform_aligns_reordered_and_projected_ghost_indices() {
    let problem = ChcParser::parse(NONPREFIX_FLOW).expect("parse non-prefix flow canary");
    let transformed = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem)
        .problem;

    // loop(mem,count,tag) -> stage(tag,mem,count): both appended index
    // fields must be the very same fresh head variable despite the permutation.
    let loop_to_stage = &transformed.clauses()[1];
    let (_, loop_args) = &loop_to_stage.body.predicates[0];
    let ClauseHead::Predicate(_, stage_args) = &loop_to_stage.head else {
        panic!("stage head");
    };
    assert_eq!(loop_args[3], stage_args[3]);

    // stage(tag,mem,count) -> check(count,mem): projection changes arity,
    // but the body array's ghost index must still follow check's array slot.
    let stage_to_check = &transformed.clauses()[2];
    let (_, stage_body_args) = &stage_to_check.body.predicates[0];
    let ClauseHead::Predicate(_, check_args) = &stage_to_check.head else {
        panic!("check head");
    };
    assert_eq!(stage_body_args[3], check_args[2]);
}

#[derive(Clone, Copy)]
enum EdgeShape {
    Plain,
    RepeatedBodyVariable,
    NonVariableHeadArgument,
    Nonlinear,
}

fn edge_shape_problem(shape: EdgeShape) -> (ChcProblem, PredicateId, PredicateId) {
    let array = byte_array();
    let mut problem = ChcProblem::new();
    let predecessor = problem.declare_predicate(
        "predecessor",
        vec![array.clone(), ChcSort::BitVec(32), ChcSort::BitVec(32)],
    );
    let query_predicate =
        problem.declare_predicate("check", vec![ChcSort::BitVec(32), array.clone()]);
    let side = problem.declare_predicate("side", Vec::new());

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            predecessor,
            vec![
                initialized_memory(0x2a),
                ChcExpr::BitVec(1, 32),
                ChcExpr::BitVec(7, 32),
            ],
        ),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(side, Vec::new()),
    ));

    let memory = var("memory", array.clone());
    let count = var("count", ChcSort::BitVec(32));
    let tag = var("tag", ChcSort::BitVec(32));
    let body_args = match shape {
        EdgeShape::RepeatedBodyVariable => {
            vec![memory.clone(), count.clone(), count.clone()]
        }
        _ => vec![memory.clone(), count.clone(), tag],
    };
    let mut body_predicates = vec![(predecessor, body_args)];
    if matches!(shape, EdgeShape::Nonlinear) {
        body_predicates.push((side, Vec::new()));
    }
    let head_memory = if matches!(shape, EdgeShape::NonVariableHeadArgument) {
        ChcExpr::store(
            memory.clone(),
            ChcExpr::BitVec(1, 64),
            ChcExpr::BitVec(0xff, 8),
        )
    } else {
        memory.clone()
    };
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(body_predicates),
        ClauseHead::Predicate(query_predicate, vec![count, head_memory]),
    ));

    let query_count = var("query_count", ChcSort::BitVec(32));
    let query_memory = var("query_memory", array);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            query_predicate,
            vec![query_count.clone(), query_memory.clone()],
        )],
        Some(bad_query(query_count, query_memory)),
    )));
    (problem, predecessor, query_predicate)
}

#[test]
fn skips_ambiguous_nonvariable_and_nonlinear_edges() {
    for shape in [
        EdgeShape::RepeatedBodyVariable,
        EdgeShape::NonVariableHeadArgument,
        EdgeShape::Nonlinear,
    ] {
        let (problem, predecessor, query_predicate) = edge_shape_problem(shape);
        let spec = GhostPairSpec::analyze(&problem, 1);
        let candidates = query_anchored_ghost_candidates(&problem, &spec)
            .expect("a malformed edge must not discard the local query anchor");
        let targets = target_set(&candidates);
        assert!(targets.contains(&query_predicate));
        assert!(
            !targets.contains(&predecessor),
            "unsupported edge must not invent a predecessor mapping"
        );
    }

    let (problem, predecessor, query_predicate) = edge_shape_problem(EdgeShape::Plain);
    let spec = GhostPairSpec::analyze(&problem, 1);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("the plain variable permutation/projection is transportable");
    assert_eq!(
        target_set(&candidates),
        [predecessor, query_predicate].into_iter().collect()
    );
}

#[test]
fn repeated_unrelated_body_column_does_not_block_required_transport() {
    let array = byte_array();
    let mut problem = ChcProblem::new();
    let predecessor = problem.declare_predicate(
        "predecessor",
        vec![
            array.clone(),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
            ChcSort::BitVec(32),
        ],
    );
    let check = problem.declare_predicate("check", vec![ChcSort::BitVec(32), array.clone()]);
    let memory = var("memory", array.clone());
    let count = var("count", ChcSort::BitVec(32));
    let unrelated = var("unrelated", ChcSort::BitVec(32));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            predecessor,
            vec![memory.clone(), count.clone(), unrelated.clone(), unrelated],
        )]),
        ClauseHead::Predicate(check, vec![count.clone(), memory.clone()]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(check, vec![count.clone(), memory.clone()])],
        Some(bad_query(count, memory)),
    )));

    let spec = GhostPairSpec::analyze(&problem, 1);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("ambiguity confined to an unused column is harmless");
    assert!(target_set(&candidates).contains(&predecessor));
}

fn cycle_problem() -> ChcProblem {
    let array = byte_array();
    let mut problem = ChcProblem::new();
    let left = problem.declare_predicate("left", vec![array.clone(), ChcSort::BitVec(32)]);
    let right = problem.declare_predicate("right", vec![ChcSort::BitVec(32), array.clone()]);
    let memory = var("memory", array.clone());
    let count = var("count", ChcSort::BitVec(32));

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(left, vec![initialized_memory(0x2a), ChcExpr::BitVec(1, 32)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(left, vec![memory.clone(), count.clone()])]),
        ClauseHead::Predicate(right, vec![count.clone(), memory.clone()]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(right, vec![count.clone(), memory.clone()])]),
        ClauseHead::Predicate(left, vec![memory.clone(), count.clone()]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(right, vec![count.clone(), memory.clone()])],
        Some(bad_query(count, memory)),
    )));
    problem
}

#[test]
fn cycle_deduplicates_and_control_stops_fail_closed() {
    let problem = cycle_problem();
    let spec = GhostPairSpec::analyze(&problem, 1);
    let candidates = query_anchored_ghost_candidates(&problem, &spec)
        .expect("the two-node cycle should reach a bounded fixpoint");
    assert_eq!(
        candidates.len(),
        2,
        "identity must deduplicate on the cycle"
    );

    let cancellation = CancellationToken::new();
    cancellation.cancel();
    assert!(query_anchored_ghost_candidates_controlled(
        &problem,
        &spec,
        &cancellation,
        Instant::now() + Duration::from_secs(30),
    )
    .is_none());
    assert!(query_anchored_ghost_candidates_controlled(
        &problem,
        &spec,
        &CancellationToken::new(),
        Instant::now(),
    )
    .is_none());
}

fn fan_in_problem(predecessors: usize) -> ChcProblem {
    let array = byte_array();
    let mut problem = ChcProblem::new();
    let query_predicate =
        problem.declare_predicate("check", vec![ChcSort::BitVec(32), array.clone()]);
    for index in 0..predecessors {
        let predecessor = problem.declare_predicate(
            format!("predecessor_{index}"),
            vec![array.clone(), ChcSort::BitVec(32)],
        );
        let memory = var("memory", array.clone());
        let count = var("count", ChcSort::BitVec(32));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(predecessor, vec![memory.clone(), count.clone()])]),
            ClauseHead::Predicate(query_predicate, vec![count, memory]),
        ));
    }
    let memory = var("query_memory", array);
    let count = var("query_count", ChcSort::BitVec(32));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(query_predicate, vec![count.clone(), memory.clone()])],
        Some(bad_query(count, memory)),
    )));
    problem
}

#[test]
fn flow_state_cap_accepts_boundary_and_rejects_one_more() {
    let at_cap = fan_in_problem(MAX_PROPAGATED_CANDIDATES - 1);
    let spec = GhostPairSpec::analyze(&at_cap, 1);
    let candidates = query_anchored_ghost_candidates(&at_cap, &spec)
        .expect("identity plus predecessors exactly at the cap must fit");
    assert_eq!(candidates.len(), MAX_PROPAGATED_CANDIDATES);

    let over_cap = fan_in_problem(MAX_PROPAGATED_CANDIDATES);
    let spec = GhostPairSpec::analyze(&over_cap, 1);
    assert!(
        query_anchored_ghost_candidates(&over_cap, &spec).is_none(),
        "one state over the hard cap must reject the entire heuristic pass"
    );
}

fn synthesize(problem: &ChcProblem) -> Option<QueryAnchoredSeal> {
    let spec = GhostPairSpec::analyze(problem, 1);
    let raw = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem.clone())
        .problem;
    let now = Instant::now();
    try_query_anchored_and_seal(
        problem,
        &raw,
        &spec,
        now + Duration::from_secs(40),
        now + Duration::from_secs(80),
        &CancellationToken::new(),
        None,
    )
}

#[test]
#[timeout(120000)]
fn nonprefix_model_checker_consumer_canary_seals_against_original_clauses() {
    let problem = ChcParser::parse(NONPREFIX_FLOW).expect("parse non-prefix flow canary");
    let sealed = synthesize(&problem).expect("transported joint model must seal");
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(20)),
        false,
    ));
    for name in ["loop", "stage", "check"] {
        let predicate = problem.lookup_predicate(name).expect("named predicate");
        assert!(sealed.certificate.ghost_interpretation(predicate).is_some());
    }
}

#[test]
#[timeout(120000)]
fn poisoned_nonprefix_model_checker_consumer_canary_cannot_seal() {
    let poisoned = NONPREFIX_FLOW.replacen("#x2A", "#x2B", 1);
    let problem = ChcParser::parse(&poisoned).expect("parse poisoned non-prefix flow canary");
    assert!(
        synthesize(&problem).is_none(),
        "changing only the reachable initializer must withhold Safe evidence"
    );
}
