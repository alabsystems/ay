// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn with_identity_metadata(
    source: &QuantifiedChcProblem,
    reverse_binders: bool,
    field_width: u32,
) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    for predicate in source.source_problem().predicates() {
        assert_eq!(
            declarations.declare_predicate(&predicate.name, predicate.arg_sorts.clone()),
            predicate.id
        );
    }
    // Even a declaration that never occurs in a clause belongs to source identity.
    declarations.add_datatype_def(
        "Unused Record".into(),
        vec![(
            "make unused".into(),
            vec![("unused field".into(), ChcSort::BitVec(field_width))],
        )],
    );
    let clauses = source
        .source_problem()
        .clauses()
        .iter()
        .zip(source.premises())
        .map(|(clause, premises)| {
            let premises = premises
                .iter()
                .map(|premise| {
                    let mut binders: Vec<_> = premise.binders().cloned().collect();
                    if reverse_binders {
                        binders.reverse();
                    }
                    UniversalPremise::with_binders(binders, premise.matrix().clone()).unwrap()
                })
                .collect();
            let raw = HornClause::new(clause.body.clone(), clause.head.clone());
            QuantifiedHornClause::new(raw, premises)
        })
        .collect();
    QuantifiedChcProblem::new(declarations, clauses).unwrap()
}

#[test]
fn complete_unused_datatype_and_ordered_binder_identity_bind_the_replay_model() {
    let base = source("fill");
    let source = with_identity_metadata(&base, false, 8);
    let token = CancellationToken::new();
    let live = control(&token);
    let model = model(&source, &live);
    validate(&source, &model, &live).unwrap();
    let prepared = prepare(&source, &model, 0, &live).unwrap();
    let text = &prepared.obligation.smtlib;
    assert!(text.contains("|Unused Record|"));
    assert!(text.contains("|make unused|"));
    assert!(text.contains("(|unused field| (_ BitVec 8))"));
    for changed in [
        with_identity_metadata(&base, false, 16),
        with_identity_metadata(&base, true, 8),
    ] {
        assert_ne!(source.source_smtlib(), changed.source_smtlib());
        assert!(!model.layout.matches_source(&changed, &live));
        assert!(validate(&changed, &model, &live).is_none());
        assert!(prepare(&changed, &model, 0, &live).is_none());
    }
    // Repeating the exact source remains acceptable after ordinary mismatches.
    assert!(prepare(&source, &model, 0, &live).is_some());
}
