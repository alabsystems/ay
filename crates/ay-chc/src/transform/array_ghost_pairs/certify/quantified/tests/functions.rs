// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Authored array/Vec sources, not a compiler export or a proof of the
//! summarized function's implementation. Candidate formulas contain no UFs.

use super::*;
use fixtures::{Calls, Query, Shape};

mod fixtures;
mod native;
mod oracle;

fn complete_declarations(source: &QuantifiedChcProblem, text: &str) {
    let mut previous = 0;
    for function in source.function_declarations() {
        let head = format!("(declare-fun {} ", ay_core::quote_symbol(function.name()));
        assert_eq!(text.matches(&head).count(), 1, "{}", function.name());
        let position = text.find(&head).unwrap();
        assert!(position >= previous, "original declaration order");
        previous = position;
    }
    assert!(
        !text.contains("(define-fun "),
        "Safe must not choose a UF model"
    );
}

fn full_premise(source: &QuantifiedChcProblem, text: &str) {
    let premise = &source.premises()[0][0];
    assert_eq!(premise.binder_count(), 2);
    assert!(text.contains(&InvariantModel::expr_to_smtlib(premise.matrix())));
    let binders = premise
        .binders()
        .map(|v| format!("({} (_ BitVec 64))", ay_core::quote_symbol(&v.name)))
        .collect::<Vec<_>>()
        .join(" ");
    assert!(text.contains(&format!("(forall ({binders}) ")));
}

#[test]
fn authored_total_function_witnesses_distinguish_same_call_from_independent_call() {
    for shape in [Shape::Array, Shape::Vec, Shape::Nested] {
        let good = fixtures::source(shape, Calls::Same, Query::Same);
        assert!(!oracle::bad_state(&good, shape, Calls::Same));
        let independent = fixtures::source(shape, Calls::Independent, Query::Same);
        assert!(oracle::bad_state(&independent, shape, Calls::Independent));
        let shifted = fixtures::source(shape, Calls::Same, Query::Shifted);
        assert!(oracle::bad_state(&shifted, shape, Calls::Same));
        assert_ne!(good.source_smtlib(), independent.source_smtlib());
        assert_eq!(
            good.function_declarations(),
            independent.function_declarations()
        );
    }
}

#[test]
fn flat_original_replay_declares_matrix_only_unused_and_nullary_global_functions() {
    let source = fixtures::source(Shape::Array, Calls::Same, Query::Same);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let candidate = fixtures::ghost_candidate(&source, Shape::Array, &control);
    let obligations = candidate
        .replay_obligations(&source, deadline(), &token)
        .unwrap();
    assert_eq!(obligations.len(), 3);
    for obligation in &obligations {
        complete_declarations(&source, &obligation.smtlib);
        assert!(!obligation.smtlib.contains("(declare-const __gpc0 "));
        assert!(obligation.smtlib.ends_with("(check-sat)\n"));
    }
    full_premise(&source, &obligations[0].smtlib);
    assert!(obligations[0].smtlib.contains("(matrix_only "));
    assert!(obligations[0].smtlib.contains("(_ BitVec 136)"));
}

#[test]
fn record_projection_retains_complete_functions_and_original_record_replay() {
    let source = fixtures::source(Shape::Vec, Calls::Same, Query::Same);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let candidate = fixtures::ghost_candidate(&source, Shape::Vec, &control);
    let projected = &candidate.records.as_ref().unwrap().projected;
    assert_eq!(
        projected.function_declarations(),
        source.function_declarations()
    );
    assert!(projected.source_problem().datatype_defs().is_empty());
    assert_eq!(
        projected.source_problem().predicates()[0].arg_sorts.len(),
        5
    );
    assert_eq!(projected.premises()[0][0].binder_count(), 2);
    assert!(projected.source_smtlib().contains("(matrix_only "));
    let obligations = candidate
        .replay_obligations(&source, deadline(), &token)
        .unwrap();
    for obligation in &obligations {
        complete_declarations(&source, &obligation.smtlib);
        assert!(obligation.smtlib.contains("(declare-datatypes"));
        assert!(!obligation.smtlib.contains("(declare-fun fld_data "));
    }
    full_premise(&source, &obligations[0].smtlib);
    assert!(obligations[0].smtlib.contains("((as mkVec Vec)"));
    assert!(obligations[1].smtlib.contains("(select (fld_data v) k)"));
}

#[test]
fn nested_observation_replay_keeps_both_axes_functions_and_full_original_matrix() {
    let source = fixtures::source(Shape::Nested, Calls::Same, Query::Same);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let model = fixtures::observation_candidate(&source, &control);
    source_observations::replay::validate(&source, &model, &control).unwrap();
    let predicate = source.source_problem().predicates()[0].id;
    assert_eq!(
        model.layout.axes(predicate).unwrap(),
        &[ChcSort::BitVec(64), ChcSort::BitVec(64)]
    );
    assert!(model
        .layout
        .canonical(predicate)
        .unwrap()
        .iter()
        .all(|var| {
            !source
                .function_declarations()
                .iter()
                .any(|f| f.name() == var.name)
        }));
    for index in 0..3 {
        let prepared =
            source_observations::replay::prepare(&source, &model, index, &control).unwrap();
        let text = &prepared.obligation.smtlib;
        complete_declarations(&source, text);
        assert!(text.contains("Inner") && text.contains("Outer"));
        assert!(!text.contains("(declare-fun fld_data "));
        if index == 0 {
            full_premise(&source, text);
        }
        if index == 1 {
            assert!(text.contains("(select (fld_data (select (fld_data outer) row)) col)"));
        }
    }
}

#[test]
fn source_registry_mutations_and_observed_cancellation_cannot_reuse_a_candidate() {
    let source = fixtures::source(Shape::Vec, Calls::Same, Query::Same);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let candidate = fixtures::ghost_candidate(&source, Shape::Vec, &control);
    let text = fixtures::script(Shape::Vec, Calls::Same, Query::Same);
    let changed =
        QuantifiedChcProblem::parse_smtlib(&text.replace("(_ BitVec 136)", "(_ BitVec 128)"))
            .unwrap();
    let reordered = QuantifiedChcProblem::parse_smtlib(&text.replace(
        "(declare-fun __gpi0 () (_ BitVec 1))\n(declare-fun __gpc0 () (_ BitVec 1))",
        "(declare-fun __gpc0 () (_ BitVec 1))\n(declare-fun __gpi0 () (_ BitVec 1))",
    ))
    .unwrap();
    for different in [&changed, &reordered] {
        assert_ne!(different.source_smtlib(), source.source_smtlib());
        for (left, right) in different
            .source_problem()
            .clauses()
            .iter()
            .zip(source.source_problem().clauses())
        {
            assert_eq!(left.body.predicates, right.body.predicates);
            assert_eq!(left.body.constraint, right.body.constraint);
            assert_eq!(format!("{:?}", left.head), format!("{:?}", right.head));
        }
        assert!(candidate
            .replay_obligations(different, deadline(), &token)
            .is_err());
        assert!(!candidate.recheck(different, deadline(), &token));
    }
    let stopped = SourceControl::new(deadline(), &token);
    token.cancel();
    assert!(stopped.poll().is_none());
    token.reset();
    assert!(replay::prepare(
        &source,
        &candidate.interpretation,
        0,
        &stopped,
        Some(&candidate.records.as_ref().unwrap().projection),
    )
    .is_none());
    assert!(candidate
        .replay_obligations(&source, deadline(), &token)
        .is_ok());
}
