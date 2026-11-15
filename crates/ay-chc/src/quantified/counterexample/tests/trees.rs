// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;
use ay_core::kani_compat::DetHashMap;

mod fixtures;
use fixtures::{Cells, Comparison, Join};

fn source() -> QuantifiedChcProblem {
    fixtures::source(Cells::Filled, Join::Query, Comparison::Different)
}

#[test]
fn same_summary_fixture_needs_two_distinct_fills_and_full_last_cell_premises() {
    for cells in [Cells::Filled, Cells::CorruptLast] {
        let source = fixtures::source(cells, Join::Query, Comparison::Different);
        let fact = &source.source_problem().clauses()[0];
        let ClauseHead::Predicate(predicate, arguments) = &fact.head else {
            panic!("source fact")
        };
        let query = &source.source_problem().clauses()[1];
        assert_eq!(query.body.predicates.len(), 2);
        assert!(query.body.predicates.iter().all(|(id, _)| id == predicate));
        assert_eq!(query.body.predicates[0].1[1], ChcExpr::BitVec(7, 8));
        assert_eq!(query.body.predicates[1].1[1], ChcExpr::BitVec(9, 8));
        let constraint = fact.body.constraint.as_ref().unwrap();
        let premise = &source.premises()[0][0];
        assert_eq!(premise.binder_count(), 1);
        let mut worlds = Vec::new();
        for fill in [7, 9] {
            let mut model = DetHashMap::default();
            model.insert(
                super::fixtures::variable(&arguments[1]).to_owned(),
                SmtValue::BitVec(fill, 8),
            );
            let value = crate::expr::evaluate_expr(super::fixtures::operand(constraint, 1), &model)
                .unwrap();
            worlds.push(value.clone());
            model.insert(super::fixtures::variable(&arguments[0]).to_owned(), value);
            assert_eq!(
                crate::expr::evaluate_expr(constraint, &model),
                Some(SmtValue::Bool(true))
            );
            let mut false_indices = Vec::new();
            for index in 0..67 {
                model.insert(premise.binder().name.clone(), SmtValue::BitVec(index, 64));
                let result = crate::expr::evaluate_expr(premise.matrix(), &model);
                assert!(matches!(result, Some(SmtValue::Bool(_))));
                if result == Some(SmtValue::Bool(false)) {
                    false_indices.push(index);
                }
            }
            assert_eq!(
                false_indices,
                match cells {
                    Cells::Filled => vec![],
                    Cells::CorruptLast => vec![64],
                }
            );
            // Every remaining BV64 index is >=65, making the guard false.
        }
        assert_ne!(worlds[0], worlds[1]);
    }
}

#[test]
#[timeout(180000)]
fn repeated_source_fact_has_independent_tree_instances_and_fresh_original_replay() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(90);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = source();
    let mut evidence = require_unsafe(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 0, 1]);
    assert_eq!(evidence.premise_steps(), &[vec![], vec![], vec![0, 1]]);
    assert_eq!(evidence.source_smtlib(), source.source_smtlib());
    assert_eq!(
        evidence.replay_obligation().matches("(forall ((").count(),
        2
    );
    assert!(evidence.replay_obligation().contains("(_ bv64 64)"));
    assert!(evidence.replay_obligation().contains("(declare-datatype"));
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    token.cancel();
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    token.reset();
    assert!(!evidence.recheck(&source, Duration::ZERO, &token));
    let retained_memory = evidence.memory_budget;
    evidence.memory_budget = Some(0);
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    evidence.memory_budget = retained_memory;
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn internal_join_tree_replay_rejects_edge_and_occurrence_mutations() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(90);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let source = fixtures::source(Cells::Filled, Join::Internal, Comparison::Different);
    let mut evidence = require_unsafe(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 0, 1, 2]);
    assert_eq!(
        evidence.premise_steps(),
        &[vec![], vec![], vec![0, 1], vec![2]]
    );
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    let original_edges = evidence.premise_steps.clone();
    for invalid in [
        vec![vec![], vec![], vec![1, 0], vec![2]], // changed edge order
        vec![vec![], vec![], vec![0, 0], vec![2]], // aliases both source instances
        vec![vec![], vec![], vec![0], vec![2]],    // missing body premise
        vec![vec![], vec![], vec![0, 2], vec![2]], // self-cycle
        vec![vec![], vec![], vec![0, usize::MAX], vec![2]], // foreign step
        vec![vec![], vec![], vec![0, 1]],          // missing final edge row
    ] {
        evidence.premise_steps = invalid;
        assert!(!evidence.recheck(&source, remaining(deadline), &token));
    }
    evidence.premise_steps = original_edges;
    let original_clauses = evidence.clause_indices.clone();
    evidence.clause_indices[0] = usize::MAX;
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    evidence.clause_indices = original_clauses;
    let foreign = fixtures::source(Cells::Filled, Join::Internal, Comparison::Equal);
    assert!(!evidence.recheck(&foreign, remaining(deadline), &token));
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}

#[test]
#[timeout(180000)]
fn false_full_premise_or_false_join_query_never_mints_tree_evidence() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    for source in [
        fixtures::source(Cells::CorruptLast, Join::Query, Comparison::Different),
        fixtures::source(Cells::Filled, Join::Query, Comparison::Equal),
    ] {
        assert!(!matches!(
            source.solve(
                remaining(deadline).min(Duration::from_secs(30)),
                Some(TERM_BUDGET),
                &CancellationToken::new(),
            ),
            QuantifiedChcResult::Unsafe(_)
        ));
    }
}

#[test]
#[timeout(180000)]
fn topology_binding_rejects_valid_reordered_edges_even_when_scripts_are_identical() {
    let _memory = SmtContext::scoped_thread_term_memory_budget(Some(TERM_BUDGET));
    let deadline = Instant::now() + Duration::from_secs(60);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let token = CancellationToken::new();
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(HornClause::fact(ChcExpr::Bool(true), p, vec![]), vec![]),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::predicates_only(vec![(p, vec![]), (p, vec![])])),
                vec![],
            ),
        ],
    )
    .unwrap();
    let mut evidence = require_unsafe(&source, deadline, &token);
    assert_eq!(evidence.clause_indices(), &[0, 0, 1]);
    let original = evidence.premise_steps.clone();
    assert_eq!(original, vec![vec![], vec![], vec![0, 1]]);
    evidence.premise_steps[2].swap(0, 1);
    let control = super::super::SourceControl::new(deadline, &token);
    let reordered = super::super::render::render_derivation(
        &source,
        evidence.clause_indices(),
        evidence.premise_steps(),
        &control,
    )
    .expect("reordered edges still form a structurally valid occurrence tree");
    // Nullary arguments generate no edge-equality text. Script comparison
    // alone therefore cannot authenticate the retained ordered topology.
    assert_eq!(reordered, evidence.replay_obligation());
    assert!(!evidence.recheck(&source, remaining(deadline), &token));
    evidence.premise_steps = original;
    assert!(evidence.recheck(&source, remaining(deadline), &token));
    assert!(Instant::now() < deadline);
}
