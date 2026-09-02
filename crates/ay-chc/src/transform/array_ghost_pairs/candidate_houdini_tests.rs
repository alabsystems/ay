// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::time::Duration;

use ntest::timeout;

use super::*;
use crate::transform::{recheck_ghost_pair_certificate, ArrayGhostPairTransformer, Transformer};
use crate::{ChcParser, ChcSort, ClauseBody, ClauseHead, HornClause};

const MODEL_CHECKER_CONSUMER_HARDER: &str =
    include_str!("../../../../../benchmarks/smt/chc_dt_array_model_checker_consumer_harder.smt2");
const MODEL_CHECKER_CONSUMER_MULTI: &str =
    include_str!("../../../../../benchmarks/smt/chc_loop_alloc_multi_pred.smt2");

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

fn wrapped_error_problem(initial: u128) -> ChcProblem {
    let key = ChcSort::BitVec(32);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value));
    let mut problem = ChcProblem::new();
    let state = problem.declare_predicate("state", vec![array.clone()]);
    let error_leaf = problem.declare_predicate("error_p4", Vec::new());
    let undefined_leaf = problem.declare_predicate("error_unused", Vec::new());
    let error = problem.declare_predicate("error", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            state,
            vec![ChcExpr::const_array(key, ChcExpr::BitVec(initial, 8))],
        ),
    ));
    let memory = ChcExpr::var(ChcVar::new("memory", array));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(state, vec![memory.clone()])],
            Some(ChcExpr::ne(
                ChcExpr::select(memory, ChcExpr::BitVec(0, 32)),
                ChcExpr::BitVec(0x2a, 8),
            )),
        ),
        ClauseHead::Predicate(error_leaf, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error_leaf, Vec::new())]),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(undefined_leaf, Vec::new())]),
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
fn nullary_error_wrapper_candidates_seal_and_fail_closed() {
    let safe = wrapped_error_problem(0x2a);
    let sealed = synthesize(&safe).expect("guarded anchor plus false sink closure must seal");
    assert_eq!(sealed.candidates, 4, "anchor plus three false sinks");
    assert_eq!(sealed.survivors, 4);
    assert!(recheck_ghost_pair_certificate(
        &safe,
        &sealed.certificate,
        Some(Duration::from_secs(10)),
        false,
    ));
    for name in ["error_p4", "error_unused", "error"] {
        let predicate = safe
            .get_predicate_by_name(name)
            .expect("sink declaration")
            .id;
        let interpretation = sealed
            .certificate
            .ghost_interpretation(predicate)
            .expect("complete sink interpretation");
        assert!(interpretation.vars.is_empty());
        assert_eq!(interpretation.formula, ChcExpr::Bool(false));
    }

    let unsafe_problem = wrapped_error_problem(0x2b);
    assert!(
        synthesize(&unsafe_problem).is_none(),
        "a reachable error leaf must drop the sink closure and withhold Safe"
    );
}

#[test]
#[timeout(120000)]
fn one_unproved_error_branch_prevents_partial_sink_sealing() {
    let mut problem = wrapped_error_problem(0x2a);
    let error = problem
        .get_predicate_by_name("error")
        .expect("error declaration")
        .id;
    let rogue = problem.declare_predicate("rogue", vec![ChcSort::BitVec(8)]);
    let bad_leaf = problem.declare_predicate("error_bad", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(rogue, vec![ChcExpr::BitVec(0, 8)]),
    ));
    let value = ChcExpr::var(ChcVar::new("rogue_value", ChcSort::BitVec(8)));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(rogue, vec![value])]),
        ClauseHead::Predicate(bad_leaf, Vec::new()),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(bad_leaf, Vec::new())]),
        ClauseHead::Predicate(error, Vec::new()),
    ));

    assert!(
        synthesize(&problem).is_none(),
        "a reachable unsupported branch must drop the root false candidate"
    );
}

#[test]
#[timeout(120000)]
fn vacuous_sink_closure_can_seal_without_a_rewritten_anchor() {
    let array = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::BitVec(8)));
    let mut problem = ChcProblem::new();
    problem.declare_predicate("unused_array_state", vec![array]);
    let leaf = problem.declare_predicate("undefined_error", Vec::new());
    let error = problem.declare_predicate("error", Vec::new());
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(leaf, Vec::new())]),
        ClauseHead::Predicate(error, Vec::new()),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        Vec::new(),
    )])));

    let sealed = synthesize(&problem).expect("the false sink closure is sufficient");
    assert_eq!(sealed.candidates, 2);
    assert_eq!(sealed.survivors, 2);
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(10)),
        false,
    ));
}

#[test]
#[timeout(120000)]
fn joint_anchor_and_bv_nonzero_seal_model_checker_consumer_harder() {
    let mut problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_HARDER)
        .expect("parse harder MODEL_CHECKER_CONSUMER canary");
    let unused = problem.declare_predicate("unused_scalar_wrapper", vec![ChcSort::Bool]);
    let invariant = problem
        .get_predicate_by_name("inv")
        .expect("inv predicate")
        .id;

    let sealed = synthesize(&problem).expect("joint candidate model must seal harder canary");
    assert_eq!(sealed.candidates, 2, "anchor plus cnt != 0 support");
    assert_eq!(sealed.survivors, 2);
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(30)),
        false,
    ));

    let invariant_interp = sealed
        .certificate
        .ghost_interpretation(invariant)
        .expect("complete model contains inv");
    assert_eq!(invariant_interp.vars.len(), 10);
    assert!(invariant_interp
        .formula
        .vars()
        .contains(&invariant_interp.vars[3]));
    let unused_interp = sealed
        .certificate
        .ghost_interpretation(unused)
        .expect("complete model contains an uncandidate predicate");
    assert_eq!(unused_interp.formula, ChcExpr::Bool(true));
}

#[test]
#[timeout(120000)]
fn multi_predicate_houdini_closes_model_checker_consumer_loop_cycle_jointly() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_MULTI)
        .expect("parse multi MODEL_CHECKER_CONSUMER canary");
    let sealed = synthesize(&problem).expect("joint candidate model must seal multi canary");
    assert_eq!(sealed.candidates, 7, "three anchors plus four BV supports");
    assert_eq!(sealed.survivors, 7);
    assert!(sealed.rounds >= 1);
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(30)),
        false,
    ));

    for name in ["loop_inv", "post_alloc", "post_write"] {
        let predicate = problem
            .get_predicate_by_name(name)
            .expect("named cycle predicate");
        assert!(sealed
            .certificate
            .ghost_interpretation(predicate.id)
            .is_some());
    }
    let post_alloc = problem
        .get_predicate_by_name("post_alloc")
        .expect("post_alloc predicate");
    let interp = sealed
        .certificate
        .ghost_interpretation(post_alloc.id)
        .expect("post_alloc interpretation");
    let used = interp.formula.vars();
    assert!(
        used.contains(&interp.vars[3]),
        "old count support must survive"
    );
    assert!(
        used.contains(&interp.vars[4]),
        "new count support must survive"
    );
}

#[test]
#[timeout(120000)]
fn houdini_drops_noninductive_bv_support_and_seals_anchor() {
    let key = ChcSort::BitVec(32);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value.clone()));
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", vec![array.clone(), key.clone()]);

    // The array anchor is valid, while the symbolic store index demands a
    // `noise != 0` support proposal. Initialization at zero forces Houdini to
    // drop only that support candidate and retry the whole system.
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            predicate,
            vec![
                ChcExpr::const_array(key.clone(), ChcExpr::BitVec(0x2a, 8)),
                ChcExpr::BitVec(0, 32),
            ],
        ),
    ));
    let transition_array = ChcExpr::var(ChcVar::new("transition_array", array.clone()));
    let transition_noise = ChcExpr::var(ChcVar::new("transition_noise", key.clone()));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(
            predicate,
            vec![transition_array.clone(), transition_noise.clone()],
        )]),
        ClauseHead::Predicate(
            predicate,
            vec![
                ChcExpr::store(
                    transition_array,
                    transition_noise.clone(),
                    ChcExpr::BitVec(0x2a, 8),
                ),
                transition_noise,
            ],
        ),
    ));
    let source_array = ChcExpr::var(ChcVar::new("a", array));
    let noise = ChcExpr::var(ChcVar::new("noise", key));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicate, vec![source_array.clone(), noise])],
        Some(ChcExpr::ne(
            ChcExpr::select(source_array, ChcExpr::BitVec(0, 32)),
            ChcExpr::BitVec(0x2a, 8),
        )),
    )));

    let sealed = synthesize(&problem).expect("the surviving array anchor must seal");
    assert_eq!(sealed.candidates, 2, "anchor plus noise != 0 support");
    assert_eq!(sealed.survivors, 1, "Houdini must drop noise != 0");
    assert!(sealed.rounds > 1, "dropping must require another round");
    assert!(recheck_ghost_pair_certificate(
        &problem,
        &sealed.certificate,
        Some(Duration::from_secs(10)),
        false,
    ));

    let interp = sealed
        .certificate
        .ghost_interpretation(predicate)
        .expect("sealed model contains P");
    let used = interp.formula.vars();
    assert!(
        !used.contains(&interp.vars[1]),
        "the non-inductive noise support must be absent"
    );
    assert!(
        used.contains(&interp.vars[2]) && used.contains(&interp.vars[3]),
        "the guarded ghost index/value anchor must survive"
    );
}

#[test]
#[timeout(120000)]
fn unsafe_zero_count_mutation_cannot_seal() {
    let poisoned =
        MODEL_CHECKER_CONSUMER_HARDER.replacen("(= cnt #x00000001)", "(= cnt #x00000000)", 1);
    let problem =
        ChcParser::parse(&poisoned).expect("parse poisoned MODEL_CHECKER_CONSUMER canary");
    assert!(
        synthesize(&problem).is_none(),
        "a reachable write to address zero must never produce sealed Safe evidence"
    );
}

#[test]
fn cancelled_and_expired_candidate_attempts_fail_closed() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_HARDER)
        .expect("parse harder MODEL_CHECKER_CONSUMER canary");
    let spec = GhostPairSpec::analyze(&problem, 1);
    let raw = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem.clone())
        .problem;
    let cancellation = CancellationToken::new();
    cancellation.cancel();
    let future = Instant::now() + Duration::from_secs(30);
    assert!(try_query_anchored_and_seal(
        &problem,
        &raw,
        &spec,
        future,
        future,
        &cancellation,
        None,
    )
    .is_none());

    assert!(try_query_anchored_and_seal(
        &problem,
        &raw,
        &spec,
        future + Duration::from_secs(1),
        future,
        &CancellationToken::new(),
        None,
    )
    .is_none());

    let past = Instant::now();
    assert!(try_query_anchored_and_seal(
        &problem,
        &raw,
        &spec,
        past,
        past,
        &CancellationToken::new(),
        None,
    )
    .is_none());
}

#[test]
fn canonical_binders_avoid_source_variable_capture() {
    let key = ChcSort::BitVec(32);
    let value = ChcSort::BitVec(8);
    let array = ChcSort::Array(Box::new(key.clone()), Box::new(value.clone()));
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", vec![array.clone(), key.clone()]);
    let source_array = ChcExpr::var(ChcVar::new("__ay_gqh_p0_a0", array.clone()));
    let count = ChcExpr::var(ChcVar::new("count", key.clone()));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(
            predicate,
            vec![
                ChcExpr::const_array(key.clone(), ChcExpr::BitVec(0x2a, 8)),
                ChcExpr::BitVec(1, 32),
            ],
        ),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(predicate, vec![source_array.clone(), count])],
        Some(ChcExpr::ne(
            ChcExpr::select(source_array, ChcExpr::BitVec(0, 32)),
            ChcExpr::BitVec(0x2a, 8),
        )),
    )));
    let spec = GhostPairSpec::analyze(&problem, 1);
    let raw = Box::new(ArrayGhostPairTransformer::new(1))
        .transform(problem.clone())
        .problem;
    let canonical = canonical_raw_variables(
        &problem,
        &raw,
        &spec,
        &CancellationToken::new(),
        Instant::now() + Duration::from_secs(5),
    )
    .expect("canonical binders");
    let vars = canonical.get(&predicate).expect("P binders");
    assert_ne!(vars[0].name, "__ay_gqh_p0_a0");
    assert_eq!(
        vars.iter().map(|var| &var.sort).collect::<Vec<_>>(),
        raw.predicates()[0].arg_sorts.iter().collect::<Vec<_>>()
    );
}
