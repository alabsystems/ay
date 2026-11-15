// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::super::super::tests::{deadline, fixture, interpretation};
use super::*;
use crate::quantified::QuantifiedHornClause;
use crate::{ChcOp, ClauseBody, PredicateInterpretation};

fn repeated_formal_source() -> (QuantifiedChcProblem, GhostPairModel) {
    let array = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::Bool));
    let mut declarations = ChcProblem::new();
    let predicate = declarations.declare_predicate("P", vec![array.clone(), ChcSort::Bool]);
    let args = vec![
        ChcExpr::var(ChcVar::new("a", array)),
        ChcExpr::var(ChcVar::new("x".repeat(8192), ChcSort::Bool)),
    ];
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::empty(),
                    ClauseHead::Predicate(predicate, args.clone()),
                ),
                vec![],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(vec![(predicate, args)], None)),
                vec![],
            ),
        ],
    )
    .unwrap();
    let spec = GhostPairSpec::analyze(source.source_problem(), 1);
    let vars: Vec<_> = spec
        .extended_sorts(
            predicate,
            &source.source_problem().predicates()[0].arg_sorts,
        )
        .unwrap()
        .into_iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("f{i}"), sort))
        .collect();
    // Raw shared input is small. Substitution nevertheless copies the large
    // actual name once per occurrence, so unique-DAG counting is insufficient.
    let repeated = Arc::new(ChcExpr::var(vars[1].clone()));
    let formula = ChcExpr::Op(ChcOp::And, vec![repeated; 8193]);
    let mut model = InvariantModel::new();
    model.set(predicate, PredicateInterpretation::new(vars, formula));
    (
        source,
        GhostPairModel {
            spec,
            model,
            executor_term_memory_limit: None,
        },
    )
}

#[test]
fn repeated_formal_large_actual_name_is_refused_before_head_or_body_instantiation() {
    let (source, model) = repeated_formal_source();
    let token = CancellationToken::new();
    let admission = SourceControl::new(deadline(), &token);
    for clause in source.source_problem().clauses() {
        source_premises::preflight_clause(clause, &admission).unwrap();
    }
    for (_, interpretation) in model.model.iter() {
        assert!(expression_bytes(&interpretation.formula, &admission).is_some());
    }
    // The independent source/formula admission succeeds; their cross-product
    // is what fails. Each real prepare call reaches this precharge first.
    for (index, clause) in source.source_problem().clauses().iter().enumerate() {
        let control = SourceControl::new(deadline(), &token);
        assert!(precharge(&model, clause, &control).is_none());
        assert!(control.poll().is_none(), "copy-ledger refusal is sticky");
        let fresh = SourceControl::new(deadline(), &token);
        assert!(super::super::prepare(&source, &model, index, &fresh, None).is_none());
        assert!(fresh.poll().is_none());
    }
}

#[test]
fn symbolic_resize_replay_still_fits_with_all_model_expansions_precharged() {
    let source = fixture(true, "i");
    let model = interpretation(&source);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    for index in 0..source.source_problem().clauses().len() {
        let prepared = super::super::prepare(&source, &model, index, &control, None).unwrap();
        assert_eq!(prepared.obligation.clause_index, index);
        assert!(prepared.obligation.smtlib.ends_with("(check-sat)\n"));
    }
    assert!(control.poll().is_some());
}
