// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

pub(super) fn graph(nodes: usize, edges: &[(usize, Vec<usize>)], roots: &[usize]) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let predicates: Vec<_> = (0..nodes)
        .map(|index| problem.declare_predicate(format!("N{index}"), Vec::new()))
        .collect();
    for (head, body) in edges {
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(
                body.iter()
                    .map(|index| (predicates[*index], Vec::new()))
                    .collect(),
            ),
            ClauseHead::Predicate(predicates[*head], Vec::new()),
        ));
    }
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(
            roots
                .iter()
                .map(|index| (predicates[*index], Vec::new()))
                .collect(),
        ),
        ClauseHead::False,
    ));
    problem
}

pub(super) fn scalar_diamond(second_fact: i128) -> ChcProblem {
    crate::parser::ChcParser::parse(&format!(
        r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(declare-fun R (Int) Bool)
(assert (P 0))
(assert (P {second_fact}))
(assert (forall ((x Int)) (=> (P x) (Q x))))
(assert (forall ((y Int)) (=> (P y) (R y))))
(assert (forall ((x Int) (y Int)) (=> (and (Q x) (R y) (not (= x y))) false)))
(check-sat)
"#
    ))
    .unwrap()
}

pub(super) fn wide_array_diamond() -> ChcProblem {
    let high = num_bigint::BigUint::from(1u8) << 128usize;
    let next = &high + 1u8;
    crate::parser::ChcParser::parse(&format!(r#"
(set-logic HORN)
(declare-fun P ((Array (_ BitVec 8) (_ BitVec 129)) (_ BitVec 129)) Bool)
(declare-fun Q ((Array (_ BitVec 8) (_ BitVec 129)) (_ BitVec 129)) Bool)
(declare-fun R ((Array (_ BitVec 8) (_ BitVec 129)) (_ BitVec 129)) Bool)
(assert (P (store ((as const (Array (_ BitVec 8) (_ BitVec 129))) (_ bv0 129)) (_ bv7 8) (_ bv{high} 129)) (_ bv{high} 129)))
(assert (P (store ((as const (Array (_ BitVec 8) (_ BitVec 129))) (_ bv0 129)) (_ bv7 8) (_ bv{next} 129)) (_ bv{next} 129)))
(assert (forall ((a (Array (_ BitVec 8) (_ BitVec 129))) (x (_ BitVec 129))) (=> (P a x) (Q a x))))
(assert (forall ((a (Array (_ BitVec 8) (_ BitVec 129))) (x (_ BitVec 129))) (=> (P a x) (R a x))))
(assert (forall ((a (Array (_ BitVec 8) (_ BitVec 129))) (b (Array (_ BitVec 8) (_ BitVec 129))) (x (_ BitVec 129)) (y (_ BitVec 129)))
  (=> (and (Q a x) (R b y) (not (= x y)) (= (select a (_ bv7 8)) x) (= (select b (_ bv7 8)) y)) false)))
(check-sat)
"#)).unwrap()
}

pub(super) fn solver(problem: ChcProblem) -> BmcSolver {
    BmcSolver::new(
        problem,
        BmcConfig {
            max_depth: 3,
            acyclic_safe: true,
            prefer_exact_acyclic_first: false,
            per_depth_timeout: Some(std::time::Duration::from_secs(10)),
            time_budget: Some(std::time::Duration::from_secs(10)),
            enable_k_induction: false,
            enable_adaptive_stepping: false,
            ..BmcConfig::default()
        },
    )
}
