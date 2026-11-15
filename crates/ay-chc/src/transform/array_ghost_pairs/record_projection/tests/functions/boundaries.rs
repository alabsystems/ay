// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

#[test]
fn wide_scalar_calls_and_exact_128_bit_leaves_survive_projection_and_original_actuals() {
    for width in [72, 128, 136, 256] {
        let sort = ChcSort::BitVec(width);
        let mut declarations = ChcProblem::new();
        let p = declarations.declare_predicate("P", vec![sort.clone()]);
        let functions = vec![QuantifiedChcFunction::new(
            "wide".into(),
            vec![sort.clone()],
            sort.clone(),
        )];
        let literal = if width < 128 {
            (1_u128 << (width - 1)) + 1
        } else {
            u128::MAX
        };
        let literal = if width > 128 {
            op(
                ChcOp::BvConcat,
                vec![
                    ChcExpr::BitVec(1, width - 128),
                    ChcExpr::BitVec(literal, 128),
                ],
            )
        } else {
            ChcExpr::BitVec(literal, width)
        };
        let actual = app("wide", sort.clone(), vec![literal]);
        let clause = QuantifiedHornClause::new(
            HornClause::new(
                ClauseBody::new(vec![], None),
                ClauseHead::Predicate(p, vec![actual.clone()]),
            ),
            vec![],
        );
        // A rule-only clause list is rejected as `NoQuery` by source::preflight
        // before the projection under test is built, so this fixture never
        // reached its assertions. The added query has an empty body and carries
        // no function and no record, leaving every assertion below unchanged.
        let mut clauses = vec![clause];
        clauses.extend(fixtures::empty_query());
        let source =
            QuantifiedChcProblem::new_with_functions(declarations, functions, clauses).unwrap();
        let token = CancellationToken::new();
        let control = SourceControl::new(deadline(), &token);
        let projection = RecordProjection::new(&source, &control).unwrap();
        let projected = projection.project(&source, &control).unwrap();
        assert_eq!(projected.source_smtlib(), source.source_smtlib());
        assert_eq!(
            projection
                .project_arguments(p, &[actual.clone()], &control)
                .unwrap(),
            vec![actual]
        );
        let wrong = app("wide", sort.clone(), vec![ChcExpr::BitVec(0, width - 1)]);
        assert!(projection
            .project_arguments(p, &[wrong], &control)
            .is_none());
    }
}

#[test]
fn complete_uf_signatures_and_every_record_child_are_checked_before_rewrite_or_replay() {
    let source = source_with_functions();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&source, &control).unwrap();
    let record_sort = source.source_problem().predicates()[0].arg_sorts[0].clone();
    let original_record = var("actual", record_sort.clone());
    let scalar = ChcSort::BitVec(8);
    let call = app(
        "F",
        scalar.clone(),
        vec![ChcExpr::Bool(true), app("G", scalar.clone(), vec![])],
    );
    assert!(projection
        .project_arguments(
            PredicateId::new(0),
            &[original_record.clone(), call],
            &control
        )
        .is_some());
    let malformed = [
        var("G", scalar.clone()),
        app("missing", scalar.clone(), vec![]),
        app("G", ChcSort::BitVec(7), vec![]),
        app("G", scalar.clone(), vec![ChcExpr::Bool(true)]),
        app("F", scalar.clone(), vec![ChcExpr::Bool(true)]),
        app(
            "F",
            scalar.clone(),
            vec![ChcExpr::Bool(true), ChcExpr::BitVec(0, 7)],
        ),
        app(
            "F",
            scalar.clone(),
            vec![ChcExpr::BitVec(1, 1), ChcExpr::BitVec(0, 8)],
        ),
        app(
            "F",
            scalar.clone(),
            vec![ChcExpr::Bool(true), ChcExpr::BitVec(256, 8)],
        ),
        app(
            "F",
            scalar.clone(),
            vec![ChcExpr::Bool(true), original_record.clone()],
        ),
        app(
            "F",
            record_sort.clone(),
            vec![ChcExpr::Bool(true), ChcExpr::BitVec(0, 8)],
        ),
        app(
            "payload",
            scalar.clone(),
            vec![app("G", scalar.clone(), vec![])],
        ),
    ];
    let reserved = BTreeSet::new();
    let mut context = Context::new(
        &projection.registry,
        &projection.functions,
        &projection.layouts,
        &reserved,
        &control,
    );
    for bad in malformed {
        assert!(context.rewrite(&bad, 0).is_none(), "{bad:?}");
        assert!(projection
            .project_arguments(
                PredicateId::new(0),
                &[original_record.clone(), bad],
                &control
            )
            .is_none());
    }
    let malformed_record = app(
        "mkR",
        record_sort.clone(),
        vec![
            ChcExpr::Bool(true),
            ChcExpr::BitVec(0, 8),
            ChcExpr::ConstArray(
                ChcSort::BitVec(136),
                Arc::new(app("G", ChcSort::BitVec(7), vec![])),
            ),
        ],
    );
    let selected = app("payload", scalar, vec![malformed_record]);
    assert!(context.rewrite(&selected, 0).is_none());
    assert!(projection
        .project_arguments(PredicateId::new(0), &[original_record, selected], &control)
        .is_none());
    assert!(
        control.poll().is_some(),
        "shape refusal does not pretend exhaustion"
    );
}

#[test]
fn nullary_globals_in_record_fields_and_wide_constant_arrays_remain_applications() {
    let source = source_with_functions();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&source, &control).unwrap();
    let sort = source.source_problem().predicates()[0].arg_sorts[0].clone();
    let g = app("G", ChcSort::BitVec(8), vec![]);
    let array = ChcExpr::ConstArray(ChcSort::BitVec(136), Arc::new(g.clone()));
    let actual = app(
        "mkR",
        sort,
        vec![ChcExpr::Bool(false), g.clone(), array.clone()],
    );
    let reserved = BTreeSet::new();
    let mut context = Context::new(
        &projection.registry,
        &projection.functions,
        &projection.layouts,
        &reserved,
        &control,
    );
    let flat = projection
        .arguments(
            PredicateId::new(0),
            &[actual.clone(), g.clone()],
            &mut context,
        )
        .unwrap();
    assert_eq!(
        flat,
        vec![ChcExpr::Bool(false), g.clone(), array, g.clone()]
    );
    let replay = projection
        .project_arguments(PredicateId::new(0), &[actual, g.clone()], &control)
        .unwrap();
    assert_eq!(replay[3], g);
    assert!(matches!(&replay[3], ChcExpr::FuncApp(_, _, args) if args.is_empty()));
}

#[test]
fn unused_wide_registry_cost_is_shared_and_refusal_does_not_publish_partial_source() {
    let wide = ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH);
    let declarations = vec![QuantifiedChcFunction::new(
        "unused".into(),
        vec![wide.clone()],
        wide,
    )];
    let source = QuantifiedChcProblem::new_with_functions(
        ChcProblem::new(),
        declarations,
        fixtures::empty_query(),
    )
    .unwrap();
    let empty = QuantifiedChcProblem::new(ChcProblem::new(), fixtures::empty_query()).unwrap();
    let token = CancellationToken::new();
    let limited = SourceControl::new(deadline(), &token);
    limited.bytes(64 * 1024 * 1024 - 128 * 1024).unwrap();
    assert!(RecordProjection::new(&empty, &limited).is_some());
    assert!(RecordProjection::new(&source, &limited).is_none());
    assert!(limited.poll().is_none());
    assert!(RecordProjection::new(&empty, &limited).is_none());
    let fresh = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&source, &fresh).unwrap();
    let projected = projection.project(&source, &fresh).unwrap();
    assert_eq!(projected.source_smtlib(), source.source_smtlib());
    assert_eq!(
        projected.function_declarations(),
        source.function_declarations()
    );
    let cancelled = SourceControl::new(deadline(), &token);
    token.cancel();
    assert!(projection.project(&source, &cancelled).is_none());
    token.reset();
    assert!(projection.project(&source, &cancelled).is_none());
    let retry = SourceControl::new(deadline(), &token);
    assert!(projection.project(&source, &retry).is_some());
}
