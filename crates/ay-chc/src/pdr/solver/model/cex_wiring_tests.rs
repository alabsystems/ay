// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `build_cex` premise wiring on a chain that went through a POB push.
//!
//! A POB push re-queues a blocked obligation at `level + 1` and keeps its
//! parent, so the chain can hold a node ABOVE its parent's level and repeat
//! `(predicate, level)` pairs. The witness premises follow the chain itself;
//! the `(predicate, level - 1)` lookup used to wire the root of such a chain to
//! a deeper node with the same key, which the verifier's premise/head
//! alignment check rejects as spurious (`contradiction_hints::
//! pdr_poisoned_relative_induction_hint_cannot_force_false_safe` returned
//! Unknown after 500 identical spurious rebuilds).

#![allow(clippy::unwrap_used)]

use super::PdrSolver;
use crate::pdr::config::PdrConfig;
use crate::pdr::obligation::ProofObligation;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcParser, ClauseHead, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

const DECREMENT_LOOP: &str = r#"
(set-logic HORN)
(declare-fun head (Int) Bool)
(declare-fun body (Int) Bool)
(assert (forall ((x Int)) (=> (= x 2) (head x))))
(assert (forall ((x Int)) (=> (and (head x) (> x (- 10))) (body x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (body x) (= x2 (- x 1))) (head x2))))
(assert (forall ((x Int)) (=> (and (head x) (< x 0)) false)))
(check-sat)
"#;

fn model(x: i128) -> FxHashMap<String, SmtValue> {
    let mut m = FxHashMap::default();
    m.insert("x".to_string(), SmtValue::Int(x));
    m
}

fn point(solver: &PdrSolver, pred: PredicateId, v: i64) -> ChcExpr {
    let c = solver.canonical_vars(pred).unwrap()[0].clone();
    ChcExpr::eq(ChcExpr::var(c), ChcExpr::int(v))
}

#[test]
fn build_cex_wires_a_pushed_pob_chain_by_position() {
    let solver = PdrSolver::new(
        ChcParser::parse(DECREMENT_LOOP).unwrap(),
        PdrConfig::default(),
    );
    let head = solver.problem.get_predicate_by_name("head").unwrap().id;
    let body = solver.problem.get_predicate_by_name("body").unwrap().id;
    let clauses = solver.problem.clauses();
    let find = |f: &dyn Fn(&crate::HornClause) -> bool| clauses.iter().position(|c| f(c)).unwrap();
    let fact = find(&|c| c.body.predicates.is_empty());
    let to_body = find(&|c| matches!(c.head, ClauseHead::Predicate(p, _) if p == body));
    let to_head = find(&|c| {
        matches!(c.head, ClauseHead::Predicate(p, _) if p == head) && !c.body.predicates.is_empty()
    });
    let query = find(&|c| matches!(c.head, ClauseHead::False));

    // The run's chain (root first): head(-1)@4 <- body(0)@3 <- head(0)@4 (the
    // pushed POB: blocked at 2 and 3, pushed to 4) <- body(1)@3 <- head(1)@2
    // <- body(2)@1 <- head(2)@0. `(head, 4)` and `(body, 3)` occur twice.
    let root = ProofObligation::new(head, point(&solver, head, -1), 4)
        .with_query_clause(query)
        .with_incoming_clause(to_head)
        .with_smt_model(model(0));
    let n1 = ProofObligation::new(body, point(&solver, body, 0), 3)
        .with_parent(root)
        .with_incoming_clause(to_body)
        .with_smt_model(model(0));
    let pushed = ProofObligation::new(head, point(&solver, head, 0), 4)
        .with_parent(n1)
        .with_incoming_clause(to_head)
        .with_smt_model(model(1));
    let n3 = ProofObligation::new(body, point(&solver, body, 1), 3)
        .with_parent(pushed)
        .with_incoming_clause(to_body)
        .with_smt_model(model(1));
    let n4 = ProofObligation::new(head, point(&solver, head, 1), 2)
        .with_parent(n3)
        .with_incoming_clause(to_head)
        .with_smt_model(model(2));
    let n5 = ProofObligation::new(body, point(&solver, body, 2), 1)
        .with_parent(n4)
        .with_incoming_clause(to_body)
        .with_smt_model(model(2));
    let leaf = ProofObligation::new(head, point(&solver, head, 2), 0)
        .with_parent(n5)
        .with_incoming_clause(fact)
        .with_smt_model(model(2));

    let cex = solver.build_cex(&leaf);
    let witness = cex.witness.expect("witness");
    assert_eq!(witness.entries.len(), 7);
    let levels: Vec<usize> = witness.entries.iter().map(|e| e.level).collect();
    assert_eq!(levels, vec![4, 3, 4, 3, 2, 1, 0], "chain order, root first");
    for i in 0..6 {
        assert_eq!(
            witness.entries[i].premises,
            vec![i + 1],
            "entry {i} must premise its chain child, not a deeper node with the same (predicate, level)"
        );
    }
    assert!(
        witness.entries[6].premises.is_empty(),
        "the fact entry has no premise"
    );
}

/// The same system solved without hints (the default PDR configuration). Its
/// counterexample chain crosses a pushed POB AND a non-point child cube
/// (`body: x - 1 < 0` under a root whose query chose `x = -1`, expanded later
/// at `x = 0`), so the witness needs both the positional premise wiring and
/// the forward re-concretisation (`cex_concretize.rs`); without them PDR
/// returned Unknown after 511 identical spurious rebuilds, on either
/// push-guard reading.
#[test]
fn pdr_decrement_loop_without_hints_is_unsafe() {
    let mut solver = PdrSolver::new(
        ChcParser::parse(DECREMENT_LOOP).unwrap(),
        PdrConfig::default(),
    );
    let result = solver.solve();
    assert!(
        matches!(result, crate::pdr::PdrResult::Unsafe(_)),
        "the decrement loop reaches x = -1 in seven clause steps, got {result:?}"
    );
}
