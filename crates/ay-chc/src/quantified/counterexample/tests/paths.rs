// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

fn premise(x: &ChcExpr, expected: u128) -> UniversalPremise {
    let i = ChcVar::new("i", ChcSort::BitVec(64));
    let j = ChcVar::new("j", ChcSort::BitVec(64));
    let guard = op(
        ChcOp::And,
        vec![
            op(
                ChcOp::BvULt,
                vec![ChcExpr::Var(i.clone()), ChcExpr::BitVec(1, 64)],
            ),
            op(
                ChcOp::BvULt,
                vec![ChcExpr::Var(j.clone()), ChcExpr::BitVec(1, 64)],
            ),
        ],
    );
    UniversalPremise::with_binders(
        vec![i, j],
        op(
            ChcOp::Implies,
            vec![
                guard,
                op(ChcOp::Eq, vec![x.clone(), ChcExpr::BitVec(expected, 8)]),
            ],
        ),
    )
    .unwrap()
}

fn chain() -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let sort = ChcSort::BitVec(8);
    let p = declarations.declare_predicate("P", vec![sort.clone()]);
    let q = declarations.declare_predicate("Q", vec![sort.clone()]);
    let r = declarations.declare_predicate("R", vec![sort.clone()]);
    // Reuse the identical variable name and sort in all four raw clauses.
    // The values differ across clauses: 0, then 0, then 1, then 2.
    let x = ChcExpr::Var(ChcVar::new("x", sort));
    let next = op(ChcOp::BvAdd, vec![x.clone(), ChcExpr::BitVec(1, 8)]);
    let fact = HornClause::new(
        ClauseBody::constraint(op(ChcOp::Eq, vec![x.clone(), ChcExpr::BitVec(0, 8)])),
        ClauseHead::Predicate(p, vec![x.clone()]),
    );
    let first = HornClause::new(
        ClauseBody::new(vec![(p, vec![x.clone()])], None),
        ClauseHead::Predicate(q, vec![next.clone()]),
    );
    let second = HornClause::new(
        ClauseBody::new(vec![(q, vec![x.clone()])], None),
        ClauseHead::Predicate(r, vec![next]),
    );
    let query = HornClause::query(ClauseBody::new(
        vec![(r, vec![x.clone()])],
        Some(op(ChcOp::Eq, vec![x.clone(), ChcExpr::BitVec(2, 8)])),
    ));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(fact, vec![]),
            QuantifiedHornClause::new(first, vec![premise(&x, 0)]),
            QuantifiedHornClause::new(second, vec![premise(&x, 1)]),
            QuantifiedHornClause::new(query, vec![]),
        ],
    )
    .unwrap()
}

#[test]
fn multistep_fixture_keeps_local_scopes_and_every_grouped_transition_premise() {
    let source = chain();
    assert_eq!(source.source_problem().clauses().len(), 4);
    for (index, expected) in [(1, 0), (2, 1)] {
        let clause = &source.source_problem().clauses()[index];
        assert_eq!(fixtures::variable(&clause.body.predicates[0].1[0]), "x");
        let universal = &source.premises()[index][0];
        assert_eq!(universal.binder_count(), 2);
        let model = [
            ("x".to_owned(), SmtValue::BitVec(expected, 8)),
            ("i".to_owned(), SmtValue::BitVec(0, 64)),
            ("j".to_owned(), SmtValue::BitVec(0, 64)),
        ]
        .into_iter()
        .collect();
        assert_eq!(
            crate::expr::evaluate_expr(universal.matrix(), &model),
            Some(SmtValue::Bool(true))
        );
    }
}

#[test]
#[timeout(180000)]
fn multistep_original_path_counterexample_renames_clause_local_values() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(90);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = chain();
    let evidence = require_unsafe(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 1, 2, 3]);
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    assert_eq!(
        evidence.replay_obligation().matches("(forall ((").count(),
        2
    );
    assert!(evidence.replay_obligation().contains("bvadd"));
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn bodyless_original_query_has_a_one_clause_counterexample_only_when_reachable() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = fixtures::bodyless(true, false);
    let evidence = require_unsafe(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0]);
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    let unreachable = fixtures::bodyless(false, false);
    assert!(!matches!(
        unreachable.solve(remaining(deadline), Some(TERM_BUDGET), &token),
        QuantifiedChcResult::Unsafe(_)
    ));
}
