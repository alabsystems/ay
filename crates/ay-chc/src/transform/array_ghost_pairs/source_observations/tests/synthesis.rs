// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::smt::SmtValue;
use ay_core::kani_compat::DetHashMap;

#[test]
fn raw_rewrite_keeps_off_diagonal_source_instances_and_query_indices() {
    let source = fixture("a", false);
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    let raw = rewrite::problem(&source, &layout, &control).unwrap();
    let fact = &raw.clauses()[0];
    let ClauseHead::Predicate(_, actuals) = &fact.head else {
        panic!("fact")
    };
    assert_ne!(actuals[2], actuals[3]);
    let premise = &source.premises()[0][0];
    let binders: Vec<_> = premise.binders().collect();
    for (left, right) in [(2, 3), (3, 2)] {
        let instance = source_premises::simultaneous(
            premise.matrix(),
            &[(binders[0], &actuals[left]), (binders[1], &actuals[right])],
            &control,
        )
        .unwrap();
        assert!(fact
            .body
            .constraint
            .as_ref()
            .unwrap()
            .collect_conjuncts()
            .contains(&instance));
    }
    let query = raw.clauses().last().unwrap();
    assert_eq!(query.body.predicates[0].1[2], variable("r", bv(64)));
    assert_eq!(query.body.predicates[0].1[3], variable("c", bv(64)));
    assert_eq!(raw.datatype_defs(), source.source_problem().datatype_defs());
}

#[test]
fn scalar_candidates_keep_joint_guards_and_transport_reordered_cfg_columns() {
    let source = fixture("a", true);
    let token = CancellationToken::new();
    let control = control(&token);
    let layout = Layout::analyze(&source, &control).unwrap();
    let raw = rewrite::problem(&source, &layout, &control).unwrap();
    let pools = candidate::pools(&source, &raw, &layout, &control).unwrap();
    assert_eq!(pools.len(), 2);
    for (id, candidates) in pools {
        assert!(!candidates.is_empty());
        let vars = layout.canonical(id).unwrap();
        let fill = if id.index() == 0 { 1 } else { 0 };
        for (row, column, length, cell, expected) in [
            (33, 65, 66, 7, true),
            (33, 65, 66, 9, false),
            (33, 65, 65, 9, true),
            (31, 65, 66, 9, true),
            (33, 31, 66, 9, true),
        ] {
            let mut env = DetHashMap::default();
            for (position, value, width) in [
                (fill, 7, 8),
                (2, row, 64),
                (3, column, 64),
                (4, length, 64),
                (5, cell, 8),
            ] {
                env.insert(vars[position].name.clone(), SmtValue::BitVec(value, width));
            }
            for candidate in &candidates {
                assert_eq!(
                    crate::expr::evaluate_expr(&candidate.formula, &env),
                    Some(SmtValue::Bool(expected))
                );
            }
        }
    }
}

#[test]
fn observed_cancellation_refuses_all_later_candidate_and_rewrite_phases() {
    let source = fixture("a", false);
    let token = CancellationToken::new();
    let layout = Layout::analyze(&source, &control(&token)).unwrap();
    let stopped = control(&token);
    token.cancel();
    assert!(rewrite::problem(&source, &layout, &stopped).is_none());
    token.reset();
    assert!(rewrite::problem(&source, &layout, &stopped).is_none());
    assert!(rewrite::problem(&source, &layout, &control(&token)).is_some());
}

#[test]
fn scalar_validation_precharges_unused_datatype_signature_reconstruction() {
    let mut raw = crate::ChcProblem::new();
    raw.declare_predicate("P", vec![]);
    raw.add_datatype_def(
        "Unused".into(),
        vec![(
            "make_unused".into(),
            (0..64)
                .map(|index| (format!("field_{index}_{}", "x".repeat(512)), bv(8)))
                .collect(),
        )],
    );
    let bytes = crate::quantified::records::registry_bytes(&raw).unwrap()
        * (crate::quantified::records::MAX_FIELDS + 4);
    assert!(bytes > 0 && bytes < 64 * 1024 * 1024);
    let token = CancellationToken::new();
    let limited = control(&token);
    limited.bytes(64 * 1024 * 1024 - (bytes - 1)).unwrap();
    assert!(budget::scalar_validation(&raw, &limited).is_none());
    assert!(limited.poll().is_none());
    assert!(budget::scalar_validation(&raw, &control(&token)).is_some());
}
