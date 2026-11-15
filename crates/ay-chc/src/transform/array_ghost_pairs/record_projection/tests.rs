// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

mod fixtures;
mod functions;
mod grouped;
mod nested;
mod semantics;

use super::*;
use crate::{CancellationToken, ChcDtConstructor, ChcDtSelector, ChcOp, ChcVar};
use fixtures::*;

#[test]
fn every_field_is_retained_and_raw_clause_premise_query_order_is_unchanged() {
    let original = source("r", "i", "n");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let projected = projection.project(&original, &control).unwrap();
    assert_eq!(
        projected.source_problem().predicates()[0].arg_sorts,
        vec![
            ChcSort::Bool,
            ChcSort::BitVec(2),
            array(),
            ChcSort::BitVec(2)
        ]
    );
    assert!(projected.source_problem().datatype_defs().is_empty());
    assert_eq!(projected.source_problem().clauses().len(), 3);
    assert_eq!(
        projected
            .premises()
            .iter()
            .map(Vec::len)
            .collect::<Vec<_>>(),
        vec![1, 0, 0]
    );
    assert_eq!(
        projected
            .source_problem()
            .clauses()
            .iter()
            .map(|clause| clause.source_query_ordinal)
            .collect::<Vec<_>>(),
        vec![None, Some(0), Some(1)]
    );
    for clause in &projected.source_problem().clauses()[1..] {
        assert_eq!(clause.body.constraint, Some(ChcExpr::Bool(false)));
    }
    assert_eq!(projected.source_problem().pruned_false_query_count(), 0);
    assert!(projected.source_problem().is_fixedpoint_format());
    assert_ne!(projected.source_smtlib(), original.source_smtlib());
}

#[test]
fn one_variable_map_covers_arguments_constraints_and_matrices_without_capture() {
    let original = source("r", "ay!record!0", "ay!record!1");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let projected = projection.project(&original, &control).unwrap();
    let clause = &projected.source_problem().clauses()[0];
    let fields = &clause.body.predicates[0].1;
    assert_eq!(fields.len(), 4);
    for (field, expected) in fields[..3]
        .iter()
        .zip(["ay!record!2", "ay!record!3", "ay!record!4"])
    {
        assert!(matches!(field, ChcExpr::Var(var) if var.name == expected));
    }
    let ClauseHead::Predicate(_, head) = &clause.head else {
        panic!("missing head")
    };
    assert_eq!(head, fields);
    let ChcExpr::Op(ChcOp::Eq, equality) = clause.body.constraint.as_ref().unwrap() else {
        panic!("missing equality")
    };
    assert_eq!(equality[0].as_ref(), &fields[1]);
    assert_eq!(equality[1].as_ref(), &fields[3]);
    let premise = &projected.premises()[0][0];
    assert_eq!(premise.binder().name, "ay!record!0");
    let ChcExpr::Op(ChcOp::Select, read) = premise.matrix() else {
        panic!("missing matrix read")
    };
    assert_eq!(read[0].as_ref(), &fields[2]);
    assert!(matches!(read[1].as_ref(), ChcExpr::Var(var) if var == premise.binder()));
}

#[test]
fn original_replay_uses_all_authenticated_selectors_and_original_scalar_args() {
    let original = source("r", "i", "n");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let source_args = &original.source_problem().clauses()[0].body.predicates[0].1;
    let args = projection
        .project_arguments(PredicateId::new(0), source_args, &control)
        .unwrap();
    for ((name, sort), expr) in fields().into_iter().zip(&args) {
        let ChcExpr::FuncApp(actual, result, children) = expr else {
            panic!("fresh variable is not original replay")
        };
        assert_eq!(*actual, name);
        assert_eq!(*result, sort);
        assert_eq!(children.len(), 1);
        assert_eq!(children[0].as_ref(), &source_args[0]);
    }
    assert_eq!(args[3], source_args[1]);
    assert!(!args
        .iter()
        .any(|expr| matches!(expr, ChcExpr::Var(var) if var.name.starts_with("ay!record!"))));
}

#[test]
fn identity_rejects_source_or_declaration_changes_and_projection_is_deterministic() {
    let original = source("r", "i", "n");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let first = projection.project(&original, &control).unwrap();
    let second = projection.project(&original, &control).unwrap();
    assert_eq!(first.source_smtlib(), second.source_smtlib());
    let renamed = source("s", "i", "n");
    assert!(!projection.matches_source(&renamed, &control));
    assert!(projection.project(&renamed, &control).is_none());
    let changed = with_unused_record();
    assert!(!projection.matches_source(&changed, &control));
    assert!(projection.project(&changed, &control).is_none());
    assert!(projection.matches_source(&original, &control));
}

#[test]
fn stopped_controls_never_publish_a_partial_projection_or_resume_after_reset() {
    let original = source("r", "i", "n");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    assert!(control.bytes(usize::MAX).is_none());
    assert!(projection.project(&original, &control).is_none());
    assert!(projection
        .project_arguments(PredicateId::new(0), &[], &control)
        .is_none());
    let cancelled = SourceControl::new(deadline(), &token);
    token.cancel();
    assert!(RecordProjection::new(&original, &cancelled).is_none());
    token.reset();
    assert!(projection.project(&original, &cancelled).is_none());
    let expired = SourceControl::new(ay_core::time::Instant::now(), &token);
    assert!(projection.project(&original, &expired).is_none());
    let fresh = SourceControl::new(deadline(), &token);
    assert!(projection.project(&original, &fresh).is_some());
}

#[test]
fn replay_arguments_reject_wrong_arity_types_and_untrusted_record_metadata() {
    let original = source("r", "i", "n");
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let args = &original.source_problem().clauses()[0].body.predicates[0].1;
    assert!(projection
        .project_arguments(PredicateId::new(99), args, &control)
        .is_none());
    assert!(projection
        .project_arguments(PredicateId::new(0), &args[..1], &control)
        .is_none());
    let mut altered = args.clone();
    altered[0] = ChcExpr::Bool(true);
    assert!(projection
        .project_arguments(PredicateId::new(0), &altered, &control)
        .is_none());
    let bad_sort = ChcSort::Datatype {
        name: "R".into(),
        constructors: crate::ChcDtConstructors::new(vec![ChcDtConstructor {
            name: "make-r".into(),
            selectors: vec![ChcDtSelector {
                name: "flag".into(),
                sort: ChcSort::Bool,
            }],
        }]),
    };
    altered[0] = var("r", bad_sort);
    assert!(projection
        .project_arguments(PredicateId::new(0), &altered, &control)
        .is_none());
    altered[0] = ChcExpr::FuncApp(
        "make-r".into(),
        record(),
        vec![Arc::new(ChcExpr::Bool(true))],
    );
    assert!(projection
        .project_arguments(PredicateId::new(0), &altered, &control)
        .is_none());
    altered[0] = ChcExpr::FuncApp("not-a-constructor".into(), record(), vec![]);
    assert!(projection
        .project_arguments(PredicateId::new(0), &altered, &control)
        .is_none());
}
