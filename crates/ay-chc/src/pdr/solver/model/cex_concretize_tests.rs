// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lock L-C (`DESIGN` §4.1.5 / §6 S11): a free-variable counterexample chain
//! that `verify_counterexample_premise_head_alignment` marks `Spurious` is
//! re-concretised by `concretize_cex_chain` and replays `Valid`; a genuinely
//! spurious chain stays `Spurious`; an already-aligned (pinned) chain is a
//! no-op; a hyperedge incoming clause stops the walk.
//!
//! The chains are built by hand (the R1 constructor still pins every cube, so
//! a solve cannot produce a free-variable chain before R2); the integration
//! test `tests/group_pdr/spacer_cex_concretize.rs` runs the same transition
//! system end to end through the lane.

use super::super::super::{
    ChcExpr, ChcSort, ChcVar, FxHashMap, PdrSolver, ProofObligation, SmtValue,
};
use super::ConcretizeFail;
use crate::pdr::config::PdrConfig;
use crate::pdr::verification::CexVerificationResult;
use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause, PredicateId};

fn v(n: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(n, ChcSort::Int))
}

/// `x = 0 → P(x, y)` (y free); `P(x, y) ∧ x1 = x + 1 ∧ y1 = y → P(x1, y1)`;
/// `P(x, y) ∧ x ≥ 3 → false`. Unsafe at depth 3; MBP leaves `y` free.
fn free_y_problem() -> (ChcProblem, PredicateId) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(v("x"), ChcExpr::Int(0)))),
        ClauseHead::Predicate(p, vec![v("x"), v("y")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x"), v("y")])],
            Some(ChcExpr::and(
                ChcExpr::eq(v("x1"), ChcExpr::add(v("x"), ChcExpr::Int(1))),
                ChcExpr::eq(v("y1"), v("y")),
            )),
        ),
        ClauseHead::Predicate(p, vec![v("x1"), v("y1")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x"), v("y")])],
            Some(ChcExpr::ge(v("x"), ChcExpr::Int(3))),
        ),
        ClauseHead::False,
    ));
    (problem, p)
}

fn solver(problem: ChcProblem) -> PdrSolver {
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.spacer_core = true;
    solver
}

fn model(pairs: &[(&str, i128)]) -> FxHashMap<String, SmtValue> {
    pairs
        .iter()
        .map(|(n, val)| ((*n).to_owned(), SmtValue::Int(*val)))
        .collect()
}

/// Leaf → root chain: `nodes[0]` is the level-0 leaf; each entry is
/// `(state, level, incoming_clause, model)`. The root gets the query clause.
fn chain(
    pred: PredicateId,
    nodes: &[(ChcExpr, usize, usize, FxHashMap<String, SmtValue>)],
    query_clause: usize,
) -> ProofObligation {
    let mut iter = nodes.iter().rev();
    let (state, level, clause, m) = iter.next().expect("non-empty chain");
    let mut acc = ProofObligation::new(pred, state.clone(), *level)
        .with_query_clause(query_clause)
        .with_incoming_clause(*clause)
        .with_smt_model(m.clone());
    for (state, level, clause, m) in iter {
        acc = ProofObligation::new(pred, state.clone(), *level)
            .with_incoming_clause(*clause)
            .with_smt_model(m.clone())
            .with_parent(acc);
    }
    acc
}

fn collect(leaf: &ProofObligation) -> Vec<&ProofObligation> {
    let mut out = Vec::new();
    let mut cur = Some(leaf);
    while let Some(p) = cur {
        out.push(p);
        cur = p.parent.as_deref();
    }
    out
}

fn int(m: &FxHashMap<String, SmtValue>, n: &str) -> i128 {
    match m.get(n) {
        Some(SmtValue::Int(v)) => *v,
        other => panic!("model value {n}: {other:?}"),
    }
}

/// The free-variable chain of the `free_y_problem`: states `x ≥ k` at level
/// `k`; every recorded model picks a DIFFERENT `y`, exactly what independent
/// Q1 solves do once `y` is no longer pinned.
fn free_chain(solver: &PdrSolver, p: PredicateId) -> ProofObligation {
    let canon = solver.canonical_vars(p).unwrap().to_vec();
    let xc = ChcExpr::var(canon[0].clone());
    let ge = |k: i128| ChcExpr::ge(xc.clone(), ChcExpr::Int(k));
    chain(
        p,
        &[
            (ge(0), 0, 0, model(&[("x", 0), ("y", 13)])),
            (
                ge(1),
                1,
                1,
                model(&[("x", 0), ("y", 9), ("x1", 1), ("y1", 9)]),
            ),
            (
                ge(2),
                2,
                1,
                model(&[("x", 1), ("y", -4), ("x1", 2), ("y1", -4)]),
            ),
            (
                ge(3),
                3,
                1,
                model(&[("x", 2), ("y", 7), ("x1", 3), ("y1", 7)]),
            ),
        ],
        2,
    )
}

#[test]
fn free_variable_chain_is_reconcretised_and_replays_valid() {
    let (problem, p) = free_y_problem();
    let mut solver = solver(problem);
    let leaf = free_chain(&solver, p);

    // Today's chain: the alignment check sees premise head (x, y) = (0, 13)
    // against body (0, 9) and marks the witness Spurious.
    let before = solver.build_cex(&leaf);
    assert_eq!(
        solver.verify_counterexample(&before),
        CexVerificationResult::Spurious,
        "the un-concretised free-variable chain must be the Spurious case D3 fixes"
    );

    let original: Vec<(ChcExpr, usize, Option<usize>)> = collect(&leaf)
        .iter()
        .map(|n| (n.state.clone(), n.level, n.incoming_clause))
        .collect();
    let leaf = match solver.concretize_cex_chain(leaf) {
        Ok(leaf) => leaf,
        Err((_, fail)) => panic!("concretisation must succeed on a genuine chain: {fail:?}"),
    };
    let nodes = collect(&leaf);
    assert_eq!(nodes.len(), 4, "chain length preserved");
    for (node, (state, level, clause)) in nodes.iter().zip(original.iter()) {
        assert_eq!(&node.state, state, "state preserved");
        assert_eq!(node.level, *level, "level preserved");
        assert_eq!(node.incoming_clause, *clause, "incoming clause preserved");
    }
    assert_eq!(
        nodes[3].query_clause,
        Some(2),
        "root keeps its query clause"
    );
    // Forward alignment: y is carried from the leaf's fact model.
    let m0 = nodes[0].smt_model.as_ref().unwrap();
    assert_eq!((int(m0, "x"), int(m0, "y")), (0, 13));
    for (i, node) in nodes.iter().enumerate().skip(1) {
        let m = node.smt_model.as_ref().unwrap();
        assert_eq!(int(m, "x"), i as i128 - 1, "step {i} body x");
        assert_eq!(int(m, "x1"), i as i128, "step {i} head x");
        assert_eq!(
            int(m, "y"),
            13,
            "step {i} body y pinned to the previous head"
        );
        assert_eq!(int(m, "y1"), 13, "step {i} head y");
    }

    let after = solver.build_cex(&leaf);
    assert_eq!(
        solver.verify_counterexample(&after),
        CexVerificationResult::Valid,
        "the re-concretised chain must replay Valid"
    );
}

#[test]
fn genuinely_spurious_chain_stays_spurious_and_keeps_its_models() {
    let (problem, p) = free_y_problem();
    let mut solver = solver(problem);
    let canon = solver.canonical_vars(p).unwrap().to_vec();
    let xc = ChcExpr::var(canon[0].clone());
    // Root `x ≥ 3` claimed ONE step from the leaf `x ≥ 0`: no model of
    // `x1 = x + 1 ∧ x = 0 ∧ x1 ≥ 3` exists.
    let leaf = chain(
        p,
        &[
            (
                ChcExpr::ge(xc.clone(), ChcExpr::Int(0)),
                0,
                0,
                model(&[("x", 0), ("y", 0)]),
            ),
            (
                ChcExpr::ge(xc, ChcExpr::Int(3)),
                1,
                1,
                model(&[("x", 2), ("y", 0), ("x1", 3), ("y1", 0)]),
            ),
        ],
        2,
    );
    let before = solver.build_cex(&leaf);
    assert_eq!(
        solver.verify_counterexample(&before),
        CexVerificationResult::Spurious
    );

    let (leaf, fail) = match solver.concretize_cex_chain(leaf) {
        Ok(_) => panic!("an impossible step must not concretise"),
        Err(e) => e,
    };
    assert_eq!(fail, ConcretizeFail::Unsat { step: 1 });
    // The original chain comes back untouched (models included).
    let nodes = collect(&leaf);
    assert_eq!(nodes.len(), 2);
    assert_eq!(int(nodes[1].smt_model.as_ref().unwrap(), "x"), 2);
    let after = solver.build_cex(&leaf);
    assert_eq!(
        solver.verify_counterexample(&after),
        CexVerificationResult::Spurious,
        "a genuinely spurious chain stays Spurious"
    );
}

#[test]
fn aligned_pinned_chain_is_a_no_op_without_a_solve() {
    let (problem, p) = free_y_problem();
    let mut solver = solver(problem);
    let canon = solver.canonical_vars(p).unwrap().to_vec();
    let xc = ChcExpr::var(canon[0].clone());
    let yc = ChcExpr::var(canon[1].clone());
    let point = |k: i128| {
        ChcExpr::and(
            ChcExpr::eq(xc.clone(), ChcExpr::Int(k)),
            ChcExpr::eq(yc.clone(), ChcExpr::Int(5)),
        )
    };
    // Point cubes (R1 constructor): every model already aligns.
    let leaf = chain(
        p,
        &[
            (point(0), 0, 0, model(&[("x", 0), ("y", 5)])),
            (
                point(1),
                1,
                1,
                model(&[("x", 0), ("y", 5), ("x1", 1), ("y1", 5)]),
            ),
            (
                point(2),
                2,
                1,
                model(&[("x", 1), ("y", 5), ("x1", 2), ("y1", 5)]),
            ),
            (
                point(3),
                3,
                1,
                model(&[("x", 2), ("y", 5), ("x1", 3), ("y1", 5)]),
            ),
        ],
        2,
    );
    let originals: Vec<FxHashMap<String, SmtValue>> = collect(&leaf)
        .iter()
        .map(|n| n.smt_model.clone().unwrap())
        .collect();
    let solves_before = solver.spacer_stats.smt_solves_total;
    let leaf = solver
        .concretize_cex_chain(leaf)
        .unwrap_or_else(|(_, f)| panic!("aligned chain must concretise: {f:?}"));
    assert_eq!(
        solver.spacer_stats.smt_solves_total, solves_before,
        "an aligned chain needs no SMT solve"
    );
    for (node, original) in collect(&leaf).iter().zip(originals.iter()) {
        assert_eq!(
            node.smt_model.as_ref().unwrap(),
            original,
            "models kept verbatim"
        );
    }
    let cex = solver.build_cex(&leaf);
    assert_eq!(
        solver.verify_counterexample(&cex),
        CexVerificationResult::Valid
    );
}

#[test]
fn hyperedge_incoming_clause_stops_the_walk() {
    // `x = 0 → P(x)`; `P(x) ∧ P(y) ∧ z = x + y → P(z)`; `P(x) ∧ x ≥ 1 → false`.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    problem.add_clause(HornClause::new(
        ClauseBody::new(Vec::new(), Some(ChcExpr::eq(v("x"), ChcExpr::Int(0)))),
        ClauseHead::Predicate(p, vec![v("x")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")]), (p, vec![v("y")])],
            Some(ChcExpr::eq(v("z"), ChcExpr::add(v("x"), v("y")))),
        ),
        ClauseHead::Predicate(p, vec![v("z")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![v("x")])],
            Some(ChcExpr::ge(v("x"), ChcExpr::Int(1))),
        ),
        ClauseHead::False,
    ));
    let mut solver = solver(problem);
    let canon = solver.canonical_vars(p).unwrap().to_vec();
    let xc = ChcExpr::var(canon[0].clone());
    let leaf = chain(
        p,
        &[
            (
                ChcExpr::eq(xc.clone(), ChcExpr::Int(0)),
                0,
                0,
                model(&[("x", 0)]),
            ),
            (
                ChcExpr::ge(xc, ChcExpr::Int(1)),
                1,
                1,
                model(&[("x", 0), ("y", 1), ("z", 1)]),
            ),
        ],
        2,
    );
    let (leaf, fail) = match solver.concretize_cex_chain(leaf) {
        Ok(_) => panic!("a hyperedge incoming clause must stop the walk"),
        Err(e) => e,
    };
    assert_eq!(fail, ConcretizeFail::Hyperedge { step: 1 });
    let nodes = collect(&leaf);
    assert_eq!(nodes.len(), 2, "chain returned intact");
    assert_eq!(
        int(nodes[1].smt_model.as_ref().unwrap(), "y"),
        1,
        "models kept"
    );
}
