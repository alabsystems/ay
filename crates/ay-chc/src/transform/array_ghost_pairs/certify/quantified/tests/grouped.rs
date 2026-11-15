// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

// Deliberately unsealed candidates: these tests check replay construction,
// never turn an arbitrary model into a safety certificate or call SMT.
fn model(problem: &ChcProblem) -> GhostPairModel {
    let spec = GhostPairSpec::analyze(problem, 1);
    let mut model = InvariantModel::new();
    for predicate in problem.predicates() {
        let vars = spec
            .extended_sorts(predicate.id, &predicate.arg_sorts)
            .unwrap()
            .into_iter()
            .enumerate()
            .map(|(index, sort)| ChcVar::new(format!("m{index}"), sort))
            .collect();
        model.set(
            predicate.id,
            PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
        );
    }
    GhostPairModel {
        spec,
        model,
        executor_term_memory_limit: Some(64 * 1024 * 1024),
    }
}

fn assert_group(source: &QuantifiedChcProblem, prepared: &replay::Prepared<'_>) {
    let premise = &source.premises()[0][0];
    let binders: Vec<_> = premise.binders().collect();
    assert_eq!(binders.len(), 2);
    let expected = format!(
        "(assert (forall (({} (_ BitVec 8)) ({} (_ BitVec 8))) {}))",
        binders[0].name,
        binders[1].name,
        InvariantModel::expr_to_smtlib(premise.matrix())
    );
    assert!(prepared.obligation.smtlib.contains(&expected));
    for binder in binders {
        assert!(!prepared
            .obligation
            .smtlib
            .contains(&format!("(declare-const {} ", binder.name)));
    }
    assert!(prepared.obligation.smtlib.ends_with("(check-sat)\n"));
    assert_eq!(prepared.obligation.clause_index, 0);
}

#[test]
fn scalar_array_original_replay_keeps_both_lexical_binders() {
    let source = QuantifiedChcProblem::parse_smtlib(
        "(declare-var a (Array (_ BitVec 8) Bool))(declare-var b (Array (_ BitVec 8) Bool))
         (declare-rel P ((Array (_ BitVec 8) Bool) (Array (_ BitVec 8) Bool)))
         (declare-rel error ())
         (rule (=> (forall ((i (_ BitVec 8)) (j (_ BitVec 8)))
           (= (select a i) (select b j))) (P a b)))(query error)",
    )
    .unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let model = model(source.source_problem());
    let prepared = replay::prepare(&source, &model, 0, &control, None).unwrap();
    assert_group(&source, &prepared);
    assert!(prepared
        .obligation
        .smtlib
        .contains("(declare-const a (Array (_ BitVec 8) Bool))"));
    assert!(prepared
        .obligation
        .smtlib
        .contains("(declare-const b (Array (_ BitVec 8) Bool))"));
}

#[test]
fn record_projection_replay_keeps_original_group_not_search_alpha_names() {
    let source = QuantifiedChcProblem::parse_smtlib(
        "(declare-datatype R ((mkR (flag Bool) (data (Array (_ BitVec 8) Bool)))))
         (declare-var r R)(declare-rel P (R))(declare-rel error ())
         (rule (=> (forall ((i (_ BitVec 8)) (j (_ BitVec 8)))
           (= (select (data r) i) (select (data r) j))) (P r)))(query error)",
    )
    .unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&source, &control).unwrap();
    let projected = projection.project(&source, &control).unwrap();
    let model = model(projected.source_problem());
    let prepared = replay::prepare(&source, &model, 0, &control, Some(&projection)).unwrap();
    assert_group(&source, &prepared);
    assert!(prepared.obligation.smtlib.contains("(declare-datatypes"));
    assert!(prepared.obligation.smtlib.contains("(select (data r)"));
    for binder in projected.premises()[0][0].binders() {
        assert!(!prepared.obligation.smtlib.contains(&binder.name));
    }
}
