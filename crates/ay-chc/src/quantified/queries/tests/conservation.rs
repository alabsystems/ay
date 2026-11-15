// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]
#![allow(clippy::unwrap_used)]

use crate::quantified::{QuantifiedChcProblem, QuantifiedHornClause, UniversalPremise};
use crate::{
    CancellationToken, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead,
    HornClause, PredicateId,
};
use std::sync::Arc;
use std::time::Duration;

fn op(operator: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(operator, args.into_iter().map(Arc::new).collect())
}

fn var(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn premise(name: &str, width: u32, matrix: ChcExpr) -> UniversalPremise {
    UniversalPremise::new(ChcVar::new(name, ChcSort::BitVec(width)), matrix)
}

fn row(
    inputs: &[PredicateId],
    head: Option<PredicateId>,
    constraint: Option<ChcExpr>,
    premises: Vec<UniversalPremise>,
) -> QuantifiedHornClause {
    let body = ClauseBody::new(inputs.iter().map(|id| (*id, vec![])).collect(), constraint);
    let head = head.map_or(ClauseHead::False, |id| ClauseHead::Predicate(id, vec![]));
    QuantifiedHornClause::new(HornClause::new(body, head), premises)
}

fn obligations(source: &QuantifiedChcProblem) -> Vec<super::super::QuantifiedChcQueryObligation> {
    source
        .query_obligations(Duration::from_secs(10), &CancellationToken::new())
        .unwrap()
}

fn assert_premises(actual: &[UniversalPremise], expected: &[UniversalPremise]) {
    assert_eq!(actual.len(), expected.len());
    for (actual, expected) in actual.iter().zip(expected) {
        assert_eq!(
            actual.binders().collect::<Vec<_>>(),
            expected.binders().collect::<Vec<_>>()
        );
        assert_eq!(actual.matrix(), expected.matrix());
    }
}

fn assert_body(actual: &HornClause, expected: &HornClause) {
    assert_eq!(actual.body.predicates, expected.body.predicates);
    assert_eq!(actual.body.constraint, expected.body.constraint);
    assert_eq!(actual.action_id, expected.action_id);
}

fn assert_slice(
    source: &QuantifiedChcProblem,
    slice: &QuantifiedChcProblem,
    retained: &[usize],
    query_body: usize,
) {
    let original = source.source_problem();
    let actual = slice.source_problem();
    assert_eq!(actual.predicates().len(), original.predicates().len());
    for (actual, expected) in actual.predicates().iter().zip(original.predicates()) {
        assert_eq!(actual.id, expected.id);
        assert_eq!(actual.name, expected.name);
        assert_eq!(actual.arg_sorts, expected.arg_sorts);
    }
    assert_eq!(actual.datatype_defs(), original.datatype_defs());
    assert_eq!(actual.clauses().len(), retained.len() + 1);
    assert_eq!(slice.premises().len(), actual.clauses().len());
    assert_eq!(actual.pruned_false_query_count(), 0);
    assert!(!actual.has_stripped_body_forall());
    for (new_index, old_index) in retained.iter().copied().enumerate() {
        let clause = &actual.clauses()[new_index];
        let expected = &original.clauses()[old_index];
        assert_body(clause, expected);
        match (&clause.head, &expected.head) {
            (ClauseHead::Predicate(p, args), ClauseHead::Predicate(q, expected_args)) => {
                assert_eq!((p, args), (q, expected_args));
            }
            _ => panic!("retained rows must be original definitions"),
        }
        assert_eq!(clause.source_query_ordinal, None);
        assert_premises(&slice.premises()[new_index], &source.premises()[old_index]);
    }
    let query = actual.clauses().last().unwrap();
    assert!(query.is_query());
    assert_eq!(query.source_query_ordinal, Some(0));
    assert_body(query, &original.clauses()[query_body]);
    assert_premises(
        slice.premises().last().unwrap(),
        &source.premises()[query_body],
    );
}

#[test]
fn producer_error_wrappers_split_without_losing_quantified_definitions() {
    // Source-shaped, not a retained whole harness: MC 22278991c4d8e731,
    // model-checker-consumer-compiler/src/codegen_ay/chc/error_property.rs::register_error_head
    // emits precisely error_p{id} -> error and keeps error as the sole query.
    let source = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN)
         (declare-var a (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-var b (Array (_ BitVec 64) (_ BitVec 8)))
         (declare-var old (_ BitVec 64)) (declare-var new (_ BitVec 64))
         (declare-var fill (_ BitVec 8))
         (declare-rel R ()) (declare-rel error_p0 ())
         (declare-rel error_p1 ()) (declare-rel error ())
         (declare-rel unrelated ())
         (rule (=> (forall ((i (_ BitVec 64)))
           (and (=> (bvult i old) (= (select b i) (select a i)))
                (=> (and (bvuge i old) (bvult i new)) (= (select b i) fill)))) R))
         (rule (=> R error_p0)) (rule (=> (and R false) error_p1))
         (rule (=> error_p0 error)) (rule unrelated)
         (rule (=> error_p1 error)) (query error)",
    )
    .unwrap();
    let slices = obligations(&source);
    assert_eq!(slices.len(), 2);
    assert_eq!(source.source_problem().clauses().len(), 7);
    assert_eq!(source.premises()[0].len(), 1);
    for (slice, definition, label, retained) in [
        (&slices[0], 3, "error_p0", [0, 1]),
        (&slices[1], 5, "error_p1", [0, 2]),
    ] {
        let id = slice.id();
        assert_eq!(id.source_query_ordinal(), 0);
        assert_eq!(id.query_clause_index(), 6);
        assert_eq!(id.defining_clause_index(), Some(definition));
        assert_eq!(id.label(), label);
        assert_slice(&source, slice.problem(), &retained, definition);
    }
    let matrix = source.premises()[0][0].matrix();
    assert_eq!(matrix, slices[0].problem().premises()[0][0].matrix());
    assert_eq!(matrix, slices[1].problem().premises()[0][0].matrix());
    assert_ne!(
        slices[0].id().content_sha256(),
        slices[1].id().content_sha256()
    );
    assert_eq!(
        slices[0].id().aggregate_source_sha256(),
        slices[1].id().aggregate_source_sha256()
    );
}

#[test]
fn unfolding_moves_definition_premises_with_their_original_lexical_scope() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(
                &[],
                Some(error),
                Some(var("x", ChcSort::Bool)),
                vec![
                    premise(
                        "x",
                        1,
                        op(
                            ChcOp::Eq,
                            vec![var("x", ChcSort::BitVec(1)), ChcExpr::BitVec(0, 1)],
                        ),
                    ),
                    premise(
                        "x",
                        8,
                        op(
                            ChcOp::Eq,
                            vec![var("x", ChcSort::BitVec(8)), ChcExpr::BitVec(1, 8)],
                        ),
                    ),
                ],
            ),
            row(&[error], None, None, vec![]),
        ],
    )
    .unwrap();
    let slices = obligations(&source);
    assert_eq!(slices.len(), 1);
    assert_slice(&source, slices[0].problem(), &[], 0);
    assert_eq!(slices[0].id().defining_clause_index(), Some(0));
    assert_eq!(slices[0].id().label(), "error_definition_0");
    let text = slices[0].problem().source_smtlib();
    assert!(text.contains("(forall ((x Bool))"));
    assert!(text.contains("(forall ((x (_ BitVec 1)))"));
    assert!(text.contains("(forall ((x (_ BitVec 8)))"));
}

#[test]
fn constrained_or_quantified_query_scope_is_never_merged_with_a_definition() {
    let query_cases = [
        (Some(var("x", ChcSort::Bool)), vec![]),
        (Some(ChcExpr::Bool(true)), vec![]),
        (
            None,
            vec![premise(
                "j",
                1,
                op(
                    ChcOp::Eq,
                    vec![var("j", ChcSort::BitVec(1)), var("x", ChcSort::BitVec(1))],
                ),
            )],
        ),
    ];
    for (constraint, premises) in query_cases {
        let mut declarations = ChcProblem::new();
        let error = declarations.declare_predicate("error", vec![]);
        let definition = op(
            ChcOp::Eq,
            vec![var("x", ChcSort::BitVec(8)), ChcExpr::BitVec(0, 8)],
        );
        let source = QuantifiedChcProblem::new(
            declarations,
            vec![
                row(&[], Some(error), Some(definition), vec![]),
                row(&[error], None, constraint, premises),
            ],
        )
        .unwrap();
        let slices = obligations(&source);
        assert_eq!(slices.len(), 1);
        assert_eq!(slices[0].id().defining_clause_index(), None);
        assert_eq!(slices[0].id().label(), "error");
        assert_slice(&source, slices[0].problem(), &[0], 1);
    }
}

#[test]
fn recursive_dependency_cone_keeps_all_ordered_definitions_and_raw_duplicates() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let q = declarations.declare_predicate("Q", vec![]);
    let u = declarations.declare_predicate("U", vec![]);
    let v = declarations.declare_predicate("V", vec![]);
    let marker = declarations.declare_predicate("error_p0", vec![]);
    let error = declarations.declare_predicate("error", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[], Some(p), Some(ChcExpr::Bool(false)), vec![]),
            row(
                &[p],
                Some(q),
                None,
                vec![premise("i", 1, ChcExpr::Bool(true))],
            ),
            row(&[q], Some(p), None, vec![]),
            row(
                &[p],
                Some(q),
                None,
                vec![premise("i", 1, ChcExpr::Bool(true))],
            ),
            row(&[u], Some(v), None, vec![]),
            row(&[v], Some(u), None, vec![]),
            row(&[q], Some(marker), None, vec![]),
            row(&[marker], Some(error), None, vec![]),
            row(&[error], None, None, vec![]),
        ],
    )
    .unwrap();
    let slices = obligations(&source);
    assert_eq!(slices.len(), 1);
    assert_slice(&source, slices[0].problem(), &[0, 1, 2, 3, 6], 7);
    assert_eq!(slices[0].id().query_clause_index(), 8);
    assert_eq!(slices[0].id().defining_clause_index(), Some(7));
    assert_eq!(source.source_problem().clauses().len(), 9);
}

#[test]
fn marker_recursion_retains_the_marker_definitions_needed_by_each_slice() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let error = declarations.declare_predicate("error", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[error], Some(p), None, vec![]),
            row(&[p], Some(error), None, vec![]),
            row(&[], Some(error), Some(ChcExpr::Bool(false)), vec![]),
            row(&[error], None, None, vec![]),
        ],
    )
    .unwrap();
    let slices = obligations(&source);
    assert_eq!(slices.len(), 2);
    assert_slice(&source, slices[0].problem(), &[0, 1, 2], 1);
    assert_slice(&source, slices[1].problem(), &[], 2);
    assert_eq!(slices[0].id().defining_clause_index(), Some(1));
    assert_eq!(slices[1].id().defining_clause_index(), Some(2));
}

#[test]
fn a_query_before_its_definitions_keeps_source_order_and_local_query_ordinal() {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let q = declarations.declare_predicate("Q", vec![]);
    let unrelated = declarations.declare_predicate("unrelated", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[p], None, None, vec![]),
            row(&[], Some(unrelated), None, vec![]),
            row(
                &[q],
                Some(p),
                None,
                vec![premise("i", 1, ChcExpr::Bool(true))],
            ),
            row(
                &[],
                Some(q),
                Some(ChcExpr::Bool(false)),
                vec![premise("j", 8, ChcExpr::Bool(false))],
            ),
        ],
    )
    .unwrap();
    let slices = obligations(&source);
    assert_eq!(slices.len(), 1);
    let slice = slices[0].problem();
    let rows = slice.source_problem().clauses();
    assert_eq!(rows.len(), 2);
    assert!(rows[0].is_query());
    assert_eq!(rows[0].source_query_ordinal, Some(0));
    assert_body(&rows[0], &source.source_problem().clauses()[2]);
    assert_eq!(rows[1].head.predicate_id(), Some(q));
    assert_eq!(rows[1].source_query_ordinal, None);
    assert_body(&rows[1], &source.source_problem().clauses()[3]);
    assert_premises(&slice.premises()[0], &source.premises()[2]);
    assert_premises(&slice.premises()[1], &source.premises()[3]);
    assert_eq!(slices[0].id().query_clause_index(), 0);
    assert_eq!(slices[0].id().defining_clause_index(), Some(2));
    assert_eq!(slices[0].id().label(), "Q");
}

#[test]
fn duplicate_vacuous_queries_and_duplicate_marker_definitions_keep_distinct_ids() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error", vec![]);
    let undefined = declarations.declare_predicate("undefined", vec![]);
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[], None, Some(ChcExpr::Bool(false)), vec![]),
            row(&[], Some(error), Some(ChcExpr::Bool(false)), vec![]),
            row(&[], None, Some(ChcExpr::Bool(false)), vec![]),
            row(&[], Some(error), Some(ChcExpr::Bool(false)), vec![]),
            row(&[error], None, None, vec![]),
            row(&[undefined], None, None, vec![]),
        ],
    )
    .unwrap();
    let slices = obligations(&source);
    let expected = [
        (0, 0, None, "query_0"),
        (1, 2, None, "query_2"),
        (2, 4, Some(1), "error_definition_1"),
        (2, 4, Some(3), "error_definition_3"),
        (3, 5, None, "undefined"),
    ];
    assert_eq!(slices.len(), expected.len());
    for (slice, (ordinal, query, definition, label)) in slices.iter().zip(expected) {
        let id = slice.id();
        assert_eq!(id.source_query_ordinal(), ordinal);
        assert_eq!(id.query_clause_index(), query);
        assert_eq!(id.defining_clause_index(), definition);
        assert_eq!(id.label(), label);
        assert_slice(&source, slice.problem(), &[], definition.unwrap_or(query));
    }
    for slice in &slices[..4] {
        assert_eq!(slice.id().content_sha256(), slices[0].id().content_sha256());
    }
    let retry = obligations(&source);
    for (left, right) in slices.iter().zip(&retry) {
        assert_eq!(left.id(), right.id());
        assert_eq!(
            left.problem().source_smtlib(),
            right.problem().source_smtlib()
        );
    }
    for pair in slices.windows(2) {
        assert_ne!(pair[0].id(), pair[1].id());
    }
}

fn identity_source(unrelated_value: bool, unused_width: u32) -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![]);
    let unrelated = declarations.declare_predicate("unrelated", vec![]);
    declarations.add_datatype_def(
        "Unused".into(),
        vec![(
            "mk_unused".into(),
            vec![("unused_cell".into(), ChcSort::BitVec(unused_width))],
        )],
    );
    QuantifiedChcProblem::new(
        declarations,
        vec![
            row(&[], Some(p), Some(ChcExpr::Bool(false)), vec![]),
            row(
                &[],
                Some(unrelated),
                Some(ChcExpr::Bool(unrelated_value)),
                vec![],
            ),
            // A present constraint intentionally prevents one-level unfolding.
            row(&[p], None, Some(ChcExpr::Bool(true)), vec![]),
        ],
    )
    .unwrap()
}

#[test]
fn aggregate_identity_distinguishes_original_sources_with_the_same_exact_slice() {
    let left = identity_source(false, 8);
    let right = identity_source(true, 8);
    let left_slices = obligations(&left);
    let right_slices = obligations(&right);
    assert_slice(&left, left_slices[0].problem(), &[0], 2);
    assert_slice(&right, right_slices[0].problem(), &[0], 2);
    assert_ne!(left.source_smtlib(), right.source_smtlib());
    assert_eq!(
        left_slices[0].problem().source_smtlib(),
        right_slices[0].problem().source_smtlib()
    );
    assert_eq!(
        left_slices[0].id().content_sha256(),
        right_slices[0].id().content_sha256()
    );
    assert_ne!(
        left_slices[0].id().aggregate_source_sha256(),
        right_slices[0].id().aggregate_source_sha256()
    );
    assert_ne!(left_slices[0].id(), right_slices[0].id());
}

#[test]
fn unused_datatype_declarations_remain_in_every_slice_and_both_identities() {
    let left = identity_source(false, 8);
    let right = identity_source(false, 16);
    let left_slices = obligations(&left);
    let right_slices = obligations(&right);
    assert_slice(&left, left_slices[0].problem(), &[0], 2);
    assert_slice(&right, right_slices[0].problem(), &[0], 2);
    assert_eq!(
        left_slices[0]
            .problem()
            .source_problem()
            .datatype_defs()
            .len(),
        1
    );
    assert!(left_slices[0].problem().source_smtlib().contains("Unused"));
    assert!(left_slices[0]
        .problem()
        .source_smtlib()
        .contains("unused_cell"));
    assert_ne!(
        left_slices[0].id().content_sha256(),
        right_slices[0].id().content_sha256()
    );
    assert_ne!(
        left_slices[0].id().aggregate_source_sha256(),
        right_slices[0].id().aggregate_source_sha256()
    );
}
