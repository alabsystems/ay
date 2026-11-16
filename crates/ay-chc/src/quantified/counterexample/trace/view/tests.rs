// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Private, deliberately unsealed fixtures test only joins and accessors.
//! No test here runs a solver or establishes a counterexample verdict.

use super::*;
use crate::quantified::{QuantifiedHornClause, UniversalPremise};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ClauseBody, HornClause};

mod fixtures;
mod functions;
mod refusal;
use fixtures::{control, source, unchecked_trace, Change};

#[test]
fn repeated_occurrences_join_complete_clauses_and_contiguous_borrowed_values() {
    let source = source(Change::None);
    let token = CancellationToken::new();
    let trace = unchecked_trace(&source, &token);
    let view = trace
        .view_for(&source, Duration::from_secs(30), &token)
        .unwrap();
    let steps: Vec<_> = view.steps().collect();
    assert_eq!(steps.len(), 3);
    assert_eq!(
        steps
            .iter()
            .map(|step| step.clause_index())
            .collect::<Vec<_>>(),
        [0, 0, 1]
    );
    assert_eq!(
        view.steps()
            .rev()
            .map(|step| step.occurrence())
            .collect::<Vec<_>>(),
        [2, 1, 0]
    );
    assert!(view.step(3).is_none());
    assert!(view.step(usize::MAX).is_none());
    assert_eq!(steps[2].premise_steps(), &[0, 1]);
    assert_eq!(steps[0].premise_steps(), &[] as &[usize]);
    assert_eq!(steps[0].bindings().len(), 3);
    assert_eq!(steps[1].bindings().len(), 3);
    assert_eq!(steps[2].bindings().len(), 4);
    assert!(std::ptr::eq(
        steps[0].bindings(),
        &raw const trace.bindings()[..3]
    ));
    assert!(std::ptr::eq(
        steps[1].bindings(),
        &raw const trace.bindings()[3..6]
    ));
    assert!(std::ptr::eq(
        steps[2].bindings(),
        &raw const trace.bindings()[6..]
    ));
    assert!(std::ptr::eq(
        steps[0].clause().head(),
        steps[1].clause().head()
    ));
    assert!(matches!(
        steps[0].source_binding("x"),
        Some(SmtValue::BitVec(0, 2))
    ));
    assert!(matches!(
        steps[1].source_binding("x"),
        Some(SmtValue::BitVec(1, 2))
    ));
    assert!(std::ptr::eq(
        steps[0].source_binding("x").unwrap(),
        trace.bindings()[2].value()
    ));
    assert!(steps[0].source_binding("missing").is_none());
    assert!(steps[0].source_binding("\0private").is_none());
}

#[test]
fn matrix_only_locals_and_shadowed_groups_remain_distinct_and_complete() {
    let source = source(Change::None);
    let token = CancellationToken::new();
    let trace = unchecked_trace(&source, &token);
    let view = trace
        .view_for(&source, Duration::from_secs(30), &token)
        .unwrap();
    for step in view.steps() {
        let clause = step.clause();
        let original = source.source_view().clause(step.clause_index()).unwrap();
        assert!(std::ptr::eq(clause.premises(), original.premises()));
        assert_eq!(clause.premises().len(), 1);
        let premise = &clause.premises()[0];
        assert_eq!(premise.binder_count(), 2);
        assert_eq!(
            premise
                .binders()
                .map(|binder| binder.name.as_str())
                .collect::<Vec<_>>(),
            ["i", "j"]
        );
        assert!(premise
            .binders()
            .all(|binder| binder.sort == ChcSort::BitVec(2)));
        // The free Bool i is not the premise's BV2 i. Matrix-only `matrix`
        // remains a local; the exclusively bound `j` never becomes one.
        assert!(matches!(
            step.source_binding("i"),
            Some(SmtValue::Bool(true))
        ));
        assert!(matches!(
            step.source_binding("matrix"),
            Some(SmtValue::Bool(true))
        ));
        assert!(step.source_binding("j").is_none());
        assert_eq!(step.bindings()[0].variable().sort, ChcSort::Bool);
    }
    // Unused declarations and the unselected literal-false query remain in
    // the joined source, not merely the selected derivation's backward cone.
    assert_eq!(view.source().predicates().len(), 2);
    assert_eq!(view.source().datatype_declarations().len(), 1);
    assert_eq!(view.source().clauses().len(), 3);
    assert!(matches!(
        view.source().clause(2).unwrap().constraint(),
        Some(ChcExpr::Bool(false))
    ));
    assert_eq!(view.function_models(), []);
}

#[test]
fn returned_payloads_borrow_owners_not_temporary_view_wrappers() {
    let source = source(Change::None);
    let token = CancellationToken::new();
    let trace = unchecked_trace(&source, &token);
    let (clause, bindings, value, predecessors) = {
        let view = trace
            .view_for(&source, Duration::from_secs(30), &token)
            .unwrap();
        let step = view.step(2).unwrap();
        (
            step.clause(),
            step.bindings(),
            step.source_binding("y").unwrap(),
            step.premise_steps(),
        )
    };
    assert_eq!(clause.index(), 1);
    assert_eq!(bindings.len(), 4);
    assert!(matches!(value, SmtValue::BitVec(1, 2)));
    assert_eq!(predecessors, &[0, 1]);
}

#[test]
fn bodyless_query_has_one_complete_step_and_an_empty_assignment() {
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![QuantifiedHornClause::new(
            HornClause::query(ClauseBody::constraint(ChcExpr::Bool(true))),
            vec![],
        )],
    )
    .unwrap();
    let token = CancellationToken::new();
    let trace = fixtures::unchecked_tree(&source, vec![0], vec![vec![]], &token);
    let view = trace
        .view_for(&source, Duration::from_secs(30), &token)
        .unwrap();
    let step = view.step(0).unwrap();
    assert_eq!(view.steps().count(), 1);
    assert!(step.bindings().is_empty());
    assert_eq!(step.premise_steps(), &[] as &[usize]);
    assert!(step.source_binding("i").is_none());
    assert_eq!(step.clause().source_query_ordinal(), Some(0));
}
