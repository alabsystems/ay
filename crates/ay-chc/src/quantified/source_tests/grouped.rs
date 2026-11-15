// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::{CancellationToken, ChcError, ClauseHead};
use std::time::Duration;

fn group(names: &[(&str, u32)], matrix: ChcExpr) -> UniversalPremise {
    UniversalPremise::with_binders(
        names
            .iter()
            .map(|(name, width)| ChcVar::new(*name, bv(*width)))
            .collect(),
        matrix,
    )
    .unwrap()
}

#[test]
fn singleton_constructor_and_legacy_accessor_preserve_exact_source() {
    let matrix = op(ChcOp::Eq, vec![var("i", bv(2)), ChcExpr::BitVec(0, 2)]);
    let old = premise("i", 2, matrix.clone());
    let grouped = group(&[("i", 2)], matrix);
    assert_eq!(grouped.binder_count(), 1);
    assert_eq!(grouped.binder(), old.binder());
    let iterator = grouped.binders();
    assert_eq!(iterator.clone().collect::<Vec<_>>(), vec![old.binder()]);
    assert_eq!(iterator.count(), 1);
    assert_eq!(
        standalone(vec![old]).unwrap().source_smtlib(),
        standalone(vec![grouped]).unwrap().source_smtlib()
    );
    assert!(matches!(
        UniversalPremise::with_binders(vec![], ChcExpr::Bool(true)),
        Err(ChcError::Verification(_))
    ));
}

#[test]
fn ordered_same_sort_binders_remain_one_joint_quantifier() {
    let matrix = op(ChcOp::Eq, vec![var("r", bv(1)), var("c", bv(1))]);
    let source = standalone(vec![group(&[("r", 1), ("c", 1)], matrix.clone())]).unwrap();
    let retained = &source.premises()[0][0];
    assert_eq!(
        retained
            .binders()
            .map(|b| b.name.as_str())
            .collect::<Vec<_>>(),
        vec!["r", "c"]
    );
    assert_eq!(retained.matrix(), &matrix);
    assert_eq!(source.source_smtlib().matches("(forall").count(), 1);
    assert!(source
        .source_smtlib()
        .contains("(forall ((r (_ BitVec 1)) (c (_ BitVec 1))) (= r c))"));
    // Distinct variables of identical sort are not a diagonal-only premise.
    let truth: Vec<bool> = (0..2).flat_map(|r| (0..2).map(move |c| r == c)).collect();
    assert_eq!(truth, vec![true, false, false, true]);
    let reversed = standalone(vec![group(&[("c", 1), ("r", 1)], matrix)]).unwrap();
    assert_ne!(source.source_smtlib(), reversed.source_smtlib());
}

#[test]
fn all_group_binders_shadow_only_their_matrix_not_outer_or_siblings() {
    let first = group(
        &[("x", 1), ("y", 2)],
        op(
            ChcOp::And,
            vec![
                op(ChcOp::Eq, vec![var("x", bv(1)), ChcExpr::BitVec(0, 1)]),
                op(ChcOp::Eq, vec![var("y", bv(2)), var("free", bv(2))]),
            ],
        ),
    );
    let second = group(
        &[("y", 1), ("x", 2)],
        op(
            ChcOp::And,
            vec![
                op(ChcOp::Eq, vec![var("y", bv(1)), ChcExpr::BitVec(1, 1)]),
                op(ChcOp::Eq, vec![var("x", bv(2)), var("free", bv(2))]),
            ],
        ),
    );
    let source = QuantifiedChcProblem::new(
        ChcProblem::new(),
        vec![query(
            op(
                ChcOp::And,
                vec![var("x", ChcSort::Bool), var("y", ChcSort::Bool)],
            ),
            vec![first, second],
        )],
    )
    .unwrap();
    let text = source.source_smtlib();
    assert!(text.contains("(forall ((free (_ BitVec 2)) (x Bool) (y Bool))"));
    assert!(text.contains("(forall ((x (_ BitVec 1)) (y (_ BitVec 2)))"));
    assert!(text.contains("(forall ((y (_ BitVec 1)) (x (_ BitVec 2)))"));
    assert_eq!(text.matches("(forall").count(), 3);
}

#[test]
fn duplicate_names_and_late_bound_reference_metadata_refuse() {
    for names in [vec![("i", 1), ("i", 1)], vec![("i", 1), ("i", 2)]] {
        // Recording does not authenticate; the immutable problem must refuse.
        let record = group(&names, ChcExpr::Bool(true));
        assert!(standalone(vec![record]).is_err());
    }
    let bad = group(
        &[("i", 1), ("j", 2)],
        op(ChcOp::Eq, vec![var("j", bv(1)), ChcExpr::BitVec(0, 1)]),
    );
    assert!(
        matches!(standalone(vec![bad]), Err(ChcError::Verification(message))
        if message.contains("binder reference sort mismatch"))
    );
    for sort in [ChcSort::Bool, bv(0), bv(65), array()] {
        let record = UniversalPremise::with_binders(
            vec![ChcVar::new("i", bv(1)), ChcVar::new("late", sort)],
            ChcExpr::Bool(true),
        )
        .unwrap();
        assert!(standalone(vec![record]).is_err());
    }
}

#[test]
fn full_group_limit_includes_unused_binders_and_fresh_retry() {
    let vars: Vec<_> = (0..8)
        .map(|i| ChcVar::new(format!("i{i}"), bv(64)))
        .collect();
    let record = UniversalPremise::with_binders(vars.clone(), ChcExpr::Bool(true)).unwrap();
    let valid = standalone(vec![record.clone()]).unwrap();
    assert_eq!(valid.premises()[0][0].binder_count(), 8);
    let mut excessive = vars;
    excessive.push(ChcVar::new("ninth", bv(64)));
    assert!(standalone(vec![UniversalPremise::with_binders(
        excessive,
        ChcExpr::Bool(true)
    )
    .unwrap()])
    .is_err());
    for bad_name in ["", "and", "select", "bad|name"] {
        assert!(standalone(vec![group(&[("i", 1), (bad_name, 1)], ChcExpr::Bool(true))]).is_err());
    }
    assert_eq!(
        standalone(vec![record]).unwrap().source_smtlib(),
        valid.source_smtlib()
    );
}

#[test]
fn sibling_free_variable_conflicts_and_matrix_identity_remain_complete() {
    let first = group(
        &[("i", 1), ("j", 1)],
        op(ChcOp::Eq, vec![var("free", bv(1)), var("i", bv(1))]),
    );
    let conflicting = group(
        &[("free", 1), ("j", 1)],
        op(ChcOp::Eq, vec![var("i", bv(2)), ChcExpr::BitVec(0, 2)]),
    );
    // The first matrix's i is bound, so the second matrix's free i is legal.
    assert!(standalone(vec![first.clone(), conflicting]).is_ok());
    let conflicting = group(
        &[("i", 1), ("j", 1)],
        op(ChcOp::Eq, vec![var("free", bv(2)), ChcExpr::BitVec(0, 2)]),
    );
    assert!(standalone(vec![first, conflicting]).is_err());
    let source = standalone(vec![group(&[("i", 1), ("j", 1)], ChcExpr::Bool(true))]).unwrap();
    let changed = standalone(vec![group(&[("i", 1), ("j", 1)], ChcExpr::Bool(false))]).unwrap();
    assert_ne!(source.source_sha256(), changed.source_sha256());
    let renamed = standalone(vec![group(&[("i", 1), ("last", 1)], ChcExpr::Bool(true))]).unwrap();
    assert_ne!(source.source_sha256(), renamed.source_sha256());
}

#[test]
fn marker_unfolding_copies_the_complete_group_without_combining_scopes() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error_p7", vec![]);
    let group = group(
        &[("r", 1), ("c", 2)],
        op(ChcOp::Eq, vec![var("c", bv(2)), ChcExpr::BitVec(0, 2)]),
    );
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::new(
                    ClauseBody::new(vec![], Some(var("r", ChcSort::Bool))),
                    ClauseHead::Predicate(error, vec![]),
                ),
                vec![group.clone()],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(vec![(error, vec![])], None)),
                vec![],
            ),
        ],
    )
    .unwrap();
    let rows = source
        .query_obligations(Duration::from_secs(60), &CancellationToken::new())
        .unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].id().defining_clause_index(), Some(0));
    let slice = rows[0].problem();
    let retained = &slice.premises()[0][0];
    assert_eq!(
        retained.binders().collect::<Vec<_>>(),
        group.binders().collect::<Vec<_>>()
    );
    assert_eq!(retained.matrix(), group.matrix());
    assert!(slice.source_smtlib().contains("(forall ((r Bool))"));
    assert!(slice
        .source_smtlib()
        .contains("(forall ((r (_ BitVec 1)) (c (_ BitVec 2)))"));
    assert_eq!(
        slice.source_problem().clauses()[0].source_query_ordinal,
        Some(0)
    );
}

#[test]
fn a_grouped_marker_query_is_unsplit_and_every_binder_is_source_bound() {
    let mut declarations = ChcProblem::new();
    let error = declarations.declare_predicate("error_p3", vec![]);
    let group = group(&[("r", 1), ("c", 2)], ChcExpr::Bool(false));
    let source = QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(HornClause::fact(ChcExpr::Bool(true), error, vec![]), vec![]),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(vec![(error, vec![])], None)),
                vec![group.clone()],
            ),
        ],
    )
    .unwrap();
    let rows = source
        .query_obligations(Duration::from_secs(60), &CancellationToken::new())
        .unwrap();
    assert_eq!(rows.len(), 1);
    assert_eq!(rows[0].id().defining_clause_index(), None);
    assert_eq!(rows[0].problem().source_smtlib(), source.source_smtlib());
    let copied = &rows[0].problem().premises()[1][0];
    assert_eq!(
        copied.binders().collect::<Vec<_>>(),
        group.binders().collect::<Vec<_>>()
    );
    assert_eq!(copied.matrix(), group.matrix());
    assert_eq!(rows[0].id().content_sha256(), source.source_sha256());
}
