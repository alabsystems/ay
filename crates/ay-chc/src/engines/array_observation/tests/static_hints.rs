// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! UNRUN typed bridge/admission controls. No solver or consumer proof credit.

use super::super::hints::{Admitted, MAX_HINTS};
use super::static_hints_support::{
    collision_source, hint_snapshot, rebase, scalar_family, scalar_hint, shifted_source,
    typed_shape,
};
use super::*;
use crate::problem::ArrayScalarizedArg;
use crate::LemmaHint;

fn rejected(formula: ChcExpr) {
    let original = source(9, false);
    let before = original.clone();
    let id = original.lookup_predicate("H").unwrap();
    let hints = [LemmaHint::new(id, formula, 37, "rejected-fixture")];
    let snapshot = hint_snapshot(&hints);
    assert!(rebase(&project(&original), &hints).is_none());
    assert_eq!(hint_snapshot(&hints), snapshot);
    same_source(&before, &original);
}

fn deeply_shared(levels: usize) -> ChcExpr {
    let mut result = ChcExpr::Bool(true);
    for _ in 0..levels {
        let shared = Arc::new(result);
        result = ChcExpr::Op(ChcOp::And, vec![shared.clone(), shared]);
    }
    result
}

#[test]
fn static_counter_hint_rebases_after_two_observed_array_cells() {
    let original = typed_shape(9);
    let projected = project(&original);
    let hint = scalar_hint(&original, "H", 1);
    let rebased = rebase(&projected, std::slice::from_ref(&hint)).unwrap();
    let expected = operation(
        ChcOp::BvULe,
        variable(
            &crate::canonical_var_name(hint.predicate, 2),
            ChcSort::BitVec(64),
        ),
        bv(4, 64),
    );
    assert_eq!(projected.reduced.predicates()[0].arg_sorts.len(), 3);
    assert_eq!(rebased[0].formula, expected);
    assert_eq!(rebased[0].predicate, hint.predicate);
    assert_eq!(rebased[0].priority, hint.priority);
    assert_eq!(rebased[0].source, hint.source);
}

#[test]
fn scalar_hints_before_between_and_after_arrays_keep_typed_positions() {
    let original = shifted_source();
    let id = original.lookup_predicate("H").unwrap();
    let predicate = original.get_predicate(id).unwrap();
    let old = |position| {
        variable(
            &crate::canonical_var_name(id, position),
            predicate.arg_sorts[position].clone(),
        )
    };
    let hints = [LemmaHint::new(
        id,
        ChcExpr::and_all([
            ChcExpr::eq(old(0), bv(3, 8)),
            operation(ChcOp::BvULe, old(2), bv(4, 64)),
            old(4),
        ]),
        17,
        "mixed-scalar-positions",
    )];
    let projected = project(&original);
    let reduced = |position| {
        variable(
            &crate::canonical_var_name(id, position),
            projected.reduced.predicates()[0].arg_sorts[position].clone(),
        )
    };
    let actual = rebase(&projected, &hints).unwrap();
    assert_eq!(
        actual[0].formula,
        ChcExpr::and_all([
            ChcExpr::eq(reduced(0), bv(3, 8)),
            operation(ChcOp::BvULe, reduced(3), bv(4, 64)),
            reduced(6),
        ])
    );
}

#[test]
fn retained_int_real_and_bool_hints_preserve_exact_scalar_sorts() {
    let original = scalar_family();
    let id = original.predicates()[0].id;
    let old = |position| {
        variable(
            &crate::canonical_var_name(id, position),
            original.predicates()[0].arg_sorts[position].clone(),
        )
    };
    let hint = LemmaHint::new(
        id,
        ChcExpr::and_all([
            ChcExpr::eq(old(1), ChcExpr::Int(0)),
            ChcExpr::eq(old(2), ChcExpr::Real(1, 2)),
            old(3),
        ]),
        23,
        "all-scalar-sorts",
    );
    let projected = project(&original);
    let new = |position| {
        variable(
            &crate::canonical_var_name(id, position),
            projected.reduced.predicates()[0].arg_sorts[position].clone(),
        )
    };
    assert_eq!(
        rebase(&projected, &[hint]).unwrap()[0].formula,
        ChcExpr::and_all([
            ChcExpr::eq(new(2), ChcExpr::Int(0)),
            ChcExpr::eq(new(3), ChcExpr::Real(1, 2)),
            new(4),
        ])
    );
}

#[test]
fn simultaneous_rebasing_never_captures_another_original_canonical_position() {
    let original = collision_source();
    let id = original.predicates()[0].id;
    let var = |position| {
        variable(
            &crate::canonical_var_name(id, position),
            ChcSort::BitVec(64),
        )
    };
    let hint = LemmaHint::new(id, operation(ChcOp::BvULt, var(1), var(2)), 9, "no-capture");
    let projected = project(&original);
    assert_eq!(
        rebase(&projected, &[hint]).unwrap()[0].formula,
        operation(ChcOp::BvULt, var(2), var(3))
    );
}

#[test]
fn each_predicate_hint_and_original_input_remain_distinct() {
    let original = source(9, false);
    let before = original.clone();
    let hints = [
        scalar_hint(&original, "H", 1),
        scalar_hint(&original, "B", 1),
    ];
    let snapshot = hint_snapshot(&hints);
    let actual = rebase(&project(&original), &hints).unwrap();
    assert_eq!(hint_snapshot(&actual), snapshot);
    assert_eq!(hint_snapshot(&hints), snapshot);
    same_source(&before, &original);
}

#[test]
fn boolean_constants_and_empty_hint_batches_are_supported_without_new_authority() {
    let original = source(9, false);
    let id = original.lookup_predicate("H").unwrap();
    let projected = project(&original);
    assert!(rebase(&projected, &[]).unwrap().is_empty());
    for value in [false, true] {
        let hints = [LemmaHint::new(
            id,
            ChcExpr::Bool(value),
            99,
            "candidate-not-trusted",
        )];
        assert_eq!(
            rebase(&projected, &hints).unwrap()[0].formula,
            ChcExpr::Bool(value)
        );
    }
}

#[test]
fn unknown_predicate_and_foreign_canonical_prefix_decline_the_whole_batch() {
    let original = source(9, false);
    let mut hints = vec![scalar_hint(&original, "H", 1)];
    hints.push(LemmaHint::new(
        PredicateId::new(u32::MAX),
        ChcExpr::Bool(true),
        0,
        "unknown-id",
    ));
    let snapshot = hint_snapshot(&hints);
    assert!(rebase(&project(&original), &hints).is_none());
    assert_eq!(hint_snapshot(&hints), snapshot);
    rejected(ChcExpr::eq(
        variable("__p999_a1", ChcSort::BitVec(64)),
        bv(4, 64),
    ));
}

#[test]
fn free_and_wrong_sort_canonical_variables_are_not_reinterpreted() {
    let original = source(9, false);
    let id = original.lookup_predicate("H").unwrap();
    rejected(ChcExpr::eq(
        variable("fresh_counter", ChcSort::BitVec(64)),
        bv(4, 64),
    ));
    rejected(ChcExpr::eq(
        variable(&crate::canonical_var_name(id, 1), ChcSort::BitVec(32)),
        bv(4, 32),
    ));
    rejected(variable(&crate::canonical_var_name(id, 1), ChcSort::Bool));
}

#[test]
fn array_variables_and_literal_or_symbolic_select_hints_decline() {
    let original = source(9, false);
    let id = original.lookup_predicate("H").unwrap();
    let array = variable(
        &crate::canonical_var_name(id, 0),
        original.predicates()[0].arg_sorts[0].clone(),
    );
    rejected(ChcExpr::eq(array.clone(), array.clone()));
    rejected(ChcExpr::eq(
        ChcExpr::select(array.clone(), bv(1, 64)),
        bv(9, 32),
    ));
    let key = variable(&crate::canonical_var_name(id, 1), ChcSort::BitVec(64));
    rejected(ChcExpr::eq(ChcExpr::select(array, key), bv(9, 32)));
}

#[test]
fn constant_array_store_and_opaque_function_hints_decline() {
    let array = ChcExpr::const_array(ChcSort::BitVec(64), bv(5, 32));
    rejected(ChcExpr::eq(
        array.clone(),
        ChcExpr::store(array, bv(1, 64), bv(9, 32)),
    ));
    rejected(ChcExpr::FuncApp(
        "unbound_boolean".into(),
        ChcSort::Bool,
        vec![],
    ));
}

#[test]
fn non_boolean_roots_bad_operation_arity_and_mixed_widths_decline() {
    rejected(ChcExpr::Int(4));
    rejected(ChcExpr::Op(ChcOp::Not, vec![]));
    rejected(ChcExpr::eq(bv(4, 64), bv(4, 32)));
    rejected(ChcExpr::eq(ChcExpr::Real(1, 0), ChcExpr::Real(1, 1)));
    rejected(ChcExpr::eq(bv(256, 8), bv(0, 8)));
}

#[test]
fn inconsistent_map_record_signature_and_scalar_correspondence_decline() {
    let original = typed_shape(9);
    let hint = scalar_hint(&original, "H", 1);
    for case in 0..3 {
        let mut projected = project(&original);
        match case {
            0 => projected.map.original_predicates[0]
                .name
                .push_str("_foreign"),
            1 => projected.map.original_predicates[0].arg_sorts[1] = ChcSort::BitVec(32),
            _ => {
                let mappings = projected.map.pred_args.get_mut(&hint.predicate).unwrap();
                *mappings.last_mut().unwrap() = ArrayScalarizedArg::Original(0);
            }
        }
        assert!(rebase(&projected, std::slice::from_ref(&hint)).is_none());
    }
}

#[test]
fn full_batch_count_and_text_caps_decline_before_formula_copy() {
    let original = source(9, false);
    let hint = scalar_hint(&original, "H", 1);
    let hints = vec![hint.clone(); MAX_HINTS + 1];
    let mut polls = 0;
    assert!(Admitted::new(&hints, &mut || {
        polls += 1;
        true
    })
    .is_none());
    assert_eq!(polls, 1);
    let hint = LemmaHint::new(
        hint.predicate,
        variable(&"x".repeat(1025), ChcSort::Bool),
        0,
        "long-name",
    );
    assert!(Admitted::new(&[hint], &mut || true).is_none());
}

#[test]
fn full_batch_occurrence_pricing_rejects_shared_dag_expansion_and_combined_roots() {
    let original = source(9, false);
    let id = original.lookup_predicate("H").unwrap();
    let big = LemmaHint::new(id, deeply_shared(13), 0, "dag-expansion");
    assert!(Admitted::new(&[big], &mut || true).is_none());
    let smaller = LemmaHint::new(id, deeply_shared(12), 0, "whole-batch");
    assert!(Admitted::new(std::slice::from_ref(&smaller), &mut || true).is_some());
    assert!(Admitted::new(&[smaller.clone(), smaller], &mut || true).is_none());
}

#[test]
fn depth_and_fanout_caps_decline_before_recursive_work_or_rewrite() {
    let original = source(9, false);
    let id = original.lookup_predicate("H").unwrap();
    let mut formula = ChcExpr::Bool(true);
    for _ in 0..32 {
        formula = ChcExpr::Op(ChcOp::Not, vec![Arc::new(formula)]);
    }
    let hint = LemmaHint::new(id, formula, 0, "depth-cap");
    assert!(Admitted::new(&[hint], &mut || true).is_none());
    #[expect(
        clippy::rc_clone_in_vec_init,
        reason = "the fanout fixture intentionally shares one immutable boolean node across every edge"
    )]
    let formula = ChcExpr::Op(ChcOp::And, vec![Arc::new(ChcExpr::Bool(true)); 65]);
    assert!(
        Admitted::new(&[LemmaHint::new(id, formula, 0, "fanout-cap")], &mut || {
            true
        })
        .is_none()
    );
}

#[test]
fn every_hint_admission_and_rebase_poll_can_refuse_without_mutating_inputs() {
    let original = typed_shape(9);
    let before = original.clone();
    let hints = [scalar_hint(&original, "H", 1)];
    let snapshot = hint_snapshot(&hints);
    let projected = project(&original);
    let mut total = 0;
    Admitted::new(&hints, &mut || {
        total += 1;
        true
    })
    .unwrap();
    for stop in 1..=total {
        let mut calls = 0;
        assert!(Admitted::new(&hints, &mut || {
            calls += 1;
            calls < stop
        })
        .is_none());
        assert_eq!(calls, stop);
    }
    let mut total = 0;
    Admitted::new(&hints, &mut || true)
        .unwrap()
        .rebase(&projected, &mut || {
            total += 1;
            true
        })
        .unwrap();
    for stop in 1..=total {
        let mut calls = 0;
        assert!(Admitted::new(&hints, &mut || true)
            .unwrap()
            .rebase(&projected, &mut || {
                calls += 1;
                calls < stop
            })
            .is_none());
        assert_eq!(calls, stop);
    }
    assert_eq!(hint_snapshot(&hints), snapshot);
    same_source(&before, &original);
}
