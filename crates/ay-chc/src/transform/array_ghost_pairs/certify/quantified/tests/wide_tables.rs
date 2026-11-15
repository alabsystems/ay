// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtValue;
use crate::PredicateId;
use ay_core::kani_compat::DetHashMap;
use fixtures::{Change, Table};
use num_bigint::BigUint;

mod fixtures;
mod native;
mod oracle;

#[test]
fn wide_table_and_resize_axes_remain_distinct_through_reordered_successor() {
    for table in [Table::Float32, Table::Float64] {
        let source = fixtures::source(table, Change::None);
        let token = CancellationToken::new();
        let control = SourceControl::new(deadline(), &token);
        assert_eq!(
            source_observations::requires_observations(&source, &control),
            Some(true)
        );
        let (raw, candidate) = fixtures::candidate(&source, &control);
        let p = PredicateId::new(0);
        let q = PredicateId::new(1);
        assert_eq!(
            candidate.layout.axes(p).unwrap(),
            &[ChcSort::BitVec(table.key_width()), ChcSort::BitVec(64)]
        );
        assert_eq!(
            candidate.layout.axes(q).unwrap(),
            &[ChcSort::BitVec(64), ChcSort::BitVec(table.key_width())]
        );
        assert_eq!(candidate.layout.canonical(p).unwrap().len(), 11);
        assert_eq!(candidate.layout.canonical(q).unwrap().len(), 11);
        let ClauseHead::Predicate(_, head) = &raw.clauses()[1].head else {
            panic!("reordered successor")
        };
        let body = &raw.clauses()[1].body.predicates[0].1;
        assert_eq!(body[7], head[8], "same table owner, changed ordinal");
        assert_eq!(body[8], head[7], "same resize owner, changed ordinal");
        assert_ne!(body[7].sort(), body[8].sort());
        assert_eq!(body[9], head[10]);
        assert_eq!(body[10], head[9]);
        let query_actuals = &raw.clauses()[2].body.predicates[0].1;
        assert_eq!(query_actuals[7], variable("j", &ChcSort::BitVec(64)));
        assert_eq!(
            query_actuals[8],
            table.key(4),
            "nullary error heads still observe the real wide key"
        );
        let original = &source.source_problem().clauses()[1].body.predicates[0].1;
        let actuals = candidate
            .layout
            .actuals(
                p,
                original,
                &[table.key(4), ChcExpr::BitVec(64, 64)],
                &control,
            )
            .unwrap();
        assert_eq!(&actuals[..7], original);
        assert_eq!(
            actuals[9],
            ChcExpr::select(original[0].clone(), table.key(4))
        );
        assert_eq!(
            actuals[10],
            ChcExpr::select(original[4].clone(), ChcExpr::BitVec(64, 64))
        );
    }
}

#[test]
fn real_wide_candidates_preserve_high_key_bits_and_both_scalar_observations() {
    for table in [Table::Float32, Table::Float64] {
        let source = fixtures::source(table, Change::None);
        let token = CancellationToken::new();
        let control = SourceControl::new(deadline(), &token);
        let (_, candidate) = fixtures::candidate(&source, &control);
        for id in [PredicateId::new(0), PredicateId::new(1)] {
            let interpretation = candidate.model.get(&id).unwrap();
            for (tag, index, table_cell, byte, expected) in [
                (4, 64, 7, 7, true),
                (4, 64, 9, 7, false),
                (4, 64, 7, 9, false),
                (0, 64, 9, 9, true),
                (4, 31, 7, 9, true),
            ] {
                let env = oracle::candidate_environment(
                    table,
                    id,
                    &interpretation.vars,
                    tag,
                    index,
                    table_cell,
                    byte,
                );
                assert_eq!(
                    crate::expr::evaluate_expr(&interpretation.formula, &env),
                    Some(SmtValue::Bool(expected))
                );
            }
        }
        let high = oracle::key(table, 4);
        let low = oracle::key(table, 0);
        assert_ne!(high, low);
        let mask = (BigUint::from(1u8) << (2 * table.cell_width()) as usize) - BigUint::from(1u8);
        assert_eq!(&high & &mask, &low & &mask);
        assert_eq!(
            &high - &low,
            BigUint::from(4u8) << (2 * table.cell_width()) as usize
        );
    }
}

#[test]
fn original_replay_preserves_full_bv64_premise_and_wide_generated_quantification() {
    for table in [Table::Float32, Table::Float64] {
        let source = fixtures::source(table, Change::None);
        let token = CancellationToken::new();
        let control = SourceControl::new(deadline(), &token);
        let (raw, candidate) = fixtures::candidate(&source, &control);
        source_observations::replay::validate(&source, &candidate, &control).unwrap();
        let premise = &source.premises()[0][0];
        assert_eq!(premise.binder_count(), 1);
        assert_eq!(premise.binder().sort, ChcSort::BitVec(64));
        let ClauseHead::Predicate(_, args) = &raw.clauses()[0].head else {
            panic!("fact")
        };
        assert!(source_premises::simultaneous(
            premise.matrix(),
            &[(premise.binder(), &args[7])],
            &control
        )
        .is_none());
        let instance = source_premises::simultaneous(
            premise.matrix(),
            &[(premise.binder(), &args[8])],
            &control,
        )
        .unwrap();
        let fact_text =
            InvariantModel::expr_to_smtlib(raw.clauses()[0].body.constraint.as_ref().unwrap());
        for conjunct in instance.collect_conjuncts() {
            assert!(fact_text.contains(&InvariantModel::expr_to_smtlib(&conjunct)));
        }
        for index in 0..4 {
            let prepared =
                source_observations::replay::prepare(&source, &candidate, index, &control).unwrap();
            let text = &prepared.obligation.smtlib;
            if index < 3 {
                assert!(text.contains(&format!(
                    "(Array (_ BitVec {}) (_ BitVec {}))",
                    table.key_width(),
                    table.cell_width()
                )));
            }
            if index == 0 {
                assert!(text.contains(&InvariantModel::expr_to_smtlib(premise.matrix())));
                assert!(text.contains(&format!(
                    "(forall (({} (_ BitVec 64)))",
                    premise.binder().name
                )));
            }
            if index == 1 {
                assert!(
                    text.contains("(forall (")
                        && text.contains(&format!("(_ BitVec {})", table.key_width()))
                );
            }
            assert!(text.ends_with("(check-sat)\n"));
        }
    }
}

#[test]
fn independent_tables_changed_tags_and_missing_suffix_have_exact_source_witnesses() {
    for table in [Table::Float32, Table::Float64] {
        assert!(!oracle::bad_state(
            &fixtures::source(table, Change::None),
            table,
            Change::None
        ));
        for change in [
            Change::IndependentTable,
            Change::OtherTag,
            Change::MissingSuffix,
        ] {
            assert!(oracle::bad_state(
                &fixtures::source(table, change),
                table,
                change
            ));
        }
    }
}

#[test]
fn wide_layout_cannot_replay_changed_unused_declarations_or_after_observed_stop() {
    let table = Table::Float64;
    let source = fixtures::source(table, Change::None);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let (_, candidate) = fixtures::candidate(&source, &control);
    let changed =
        QuantifiedChcProblem::parse_smtlib(&fixtures::script(table, Change::None).replace(
            "(declare-rel unused ((_ BitVec 64)))",
            "(declare-rel unused ((_ BitVec 136)))",
        ))
        .unwrap();
    assert_ne!(changed.source_smtlib(), source.source_smtlib());
    assert!(!candidate.layout.matches_source(&changed, &control));
    assert!(source_observations::replay::prepare(&changed, &candidate, 0, &control).is_none());
    let stopped = SourceControl::new(deadline(), &token);
    token.cancel();
    assert!(stopped.poll().is_none());
    token.reset();
    assert!(source_observations::replay::prepare(&source, &candidate, 0, &stopped).is_none());
    let fresh = SourceControl::new(deadline(), &token);
    assert!(source_observations::replay::prepare(&source, &candidate, 0, &fresh).is_some());
}
