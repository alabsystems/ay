// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn controlled_native_proof_retains_raw_quantified_shape_and_trigger_identity() {
    let mut store = TermStore::new();
    let x = store.mk_var("exact_bound", Sort::Int);
    let marker = store.mk_app(
        crate::Symbol::named("actual_declared_predicate"),
        [x],
        Sort::Bool,
    );
    let body = store.mk_not_raw(marker);
    let data = TermData::Exists(
        vec![("exact_bound".into(), Sort::Int)],
        body,
        vec![vec![marker]],
    );
    assert_eq!(
        store.try_intern_with_progress(&data, &Sort::Bool, &mut |_, _| true),
        Err(ControlledTermInternError::UnsupportedFragment)
    );
    let q = store
        .try_intern_native_proof_with_progress(&data, &Sort::Bool, &mut |_, _| true)
        .unwrap();
    assert_eq!(store.get(q), &data);
    let (copied, sort) = store
        .try_copy_native_proof_node_with_progress(q, &mut |_, _| true)
        .unwrap();
    assert_eq!(copied, data);
    assert_eq!(sort, Sort::Bool);
    let not_not = store
        .try_intern_native_proof_with_progress(&TermData::Not(body), &Sort::Bool, &mut |_, _| true)
        .unwrap();
    assert!(
        matches!(store.get(not_not), TermData::Not(id) if *id == body),
        "raw proof nodes cannot simplify substitution structure"
    );
}

#[test]
fn controlled_native_proof_preserves_nested_array_and_nominal_operand_sorts() {
    let mut store = TermStore::new();
    let nominal = Sort::Uninterpreted("OwnedOpaqueCarrier".into());
    let array_sort = Sort::array(Sort::Int, Sort::array(nominal.clone(), Sort::Bool));
    let array = store.mk_var("array", array_sort.clone());
    let i = store.mk_int(3.into());
    let data = TermData::App(crate::Symbol::named("select"), vec![array, i]);
    let result_sort = Sort::array(nominal, Sort::Bool);
    let selected = store
        .try_intern_native_proof_with_progress(&data, &result_sort, &mut |_, _| true)
        .unwrap();
    assert_eq!(store.get(selected), &data);
    assert_eq!(store.sort(selected), &result_sort);
}

#[test]
fn controlled_native_proof_rejects_dead_ids_bad_boolean_shapes_and_binders() {
    let mut store = TermStore::new();
    let truth = store.true_term();
    let zero = store.mk_int(0.into());
    for data in [
        TermData::Not(TermId(u32::MAX)),
        TermData::Not(zero),
        TermData::App(crate::Symbol::named("and"), vec![truth, zero]),
        TermData::App(crate::Symbol::named("="), vec![truth, zero]),
        TermData::Forall(
            vec![("x".into(), Sort::Int), ("x".into(), Sort::Int)],
            truth,
            vec![],
        ),
        TermData::Forall(vec![("x".into(), Sort::Int)], zero, vec![]),
        TermData::Forall(
            vec![("x".into(), Sort::Int)],
            truth,
            vec![vec![TermId(u32::MAX)]],
        ),
    ] {
        let before = store.len();
        assert!(store
            .try_intern_native_proof_with_progress(&data, &Sort::Bool, &mut |_, _| true)
            .is_err());
        assert_eq!(store.len(), before);
    }
}

#[test]
fn controlled_native_proof_meter_admits_large_physical_payload_before_copy_and_stays_sticky() {
    let mut store = TermStore::new();
    let truth = store.true_term();
    let data = TermData::Forall(
        vec![("n".repeat(4096), Sort::Bool)],
        truth,
        vec![vec![truth; 4096]],
    );
    let mut cost = (0usize, 0usize);
    store
        .try_intern_native_proof_with_progress(&data, &Sort::Bool, &mut |w, b| {
            cost.0 += w;
            cost.1 += b;
            true
        })
        .unwrap();
    assert!(cost.0 >= 4096 && cost.1 >= 4096 * size_of::<TermId>());
    let mut fresh = TermStore::new();
    let mut stopped = false;
    let mut calls_after_stop = 0;
    let result =
        fresh.try_intern_native_proof_with_progress(&data, &Sort::Bool, &mut |_, bytes| {
            if stopped {
                calls_after_stop += 1;
            }
            if bytes > 4096 {
                stopped = true;
                false
            } else {
                true
            }
        });
    assert_eq!(result, Err(ControlledTermInternError::ResourceLimit));
    assert!(stopped);
    assert_eq!(calls_after_stop, 0);
    assert_eq!(
        fresh.len(),
        2,
        "only the genuine preexisting Bool constants remain"
    );
}

#[test]
fn controlled_native_proof_field_free_receipt_preserves_wide_binder_metadata_without_legacy_census()
{
    fn wide(depth: usize) -> Sort {
        if depth == 0 {
            Sort::Int
        } else {
            Sort::array(wide(depth - 1), wide(depth - 1))
        }
    }
    // 2047 physical sort nodes, depth10: admitted by the owned-sort grammar,
    // but beyond the unrelated legacy metadata census's 1024-node scratch walk.
    let binder = wide(10);
    let mut ordinary = TermStore::new();
    let legacy = ordinary.mk_forall(
        vec![("wide_bound".into(), binder.clone())],
        ordinary.true_term(),
    );
    assert_eq!(ordinary.finite_field_presence(legacy), None);
    let mut controlled = TermStore::new();
    let data = TermData::Forall(
        vec![("wide_bound".into(), binder)],
        controlled.true_term(),
        vec![],
    );
    let mut work = 0;
    let result = controlled
        .try_intern_native_proof_with_progress(&data, &Sort::Bool, &mut |w, _| {
            work += w;
            true
        })
        .unwrap();
    assert!(
        work >= 2047,
        "the real producer still pays every physical sort node"
    );
    assert_eq!(controlled.finite_field_presence(result), Some(false));
}

#[test]
fn controlled_native_proof_field_free_receipt_keeps_body_and_trigger_true_or_unknown_flags() {
    for trigger_only in [false, true] {
        for unknown in [false, true] {
            let mut store = TermStore::new();
            let field = crate::FiniteFieldSort::new(7).unwrap();
            let variable = store.mk_var("actual_field_value", Sort::FiniteField(field));
            let constant = store.mk_finite_field(1, field);
            let equality =
                store.mk_app(crate::Symbol::named("="), [variable, constant], Sort::Bool);
            assert_eq!(store.finite_field_presence(equality), Some(true));
            if unknown {
                // Positional snapshots can retain an unknown child flag. The
                // controlled parent must not turn that into a field-free claim.
                store.terms[equality.index()].field_presence = None;
            }
            let expected = if unknown { None } else { Some(true) };
            let (body, triggers) = if trigger_only {
                (store.true_term(), vec![vec![equality]])
            } else {
                (equality, vec![])
            };
            let data = TermData::Forall(
                vec![("field_free_bound".into(), Sort::Bool)],
                body,
                triggers,
            );
            let result = store
                .try_intern_native_proof_with_progress(&data, &Sort::Bool, &mut |_, _| true)
                .unwrap();
            assert_eq!(
                store.finite_field_presence(result),
                expected,
                "only admitted binder SORTS are skipped, never child syntax"
            );
        }
    }
}

#[test]
fn controlled_native_proof_field_free_receipt_rejects_direct_and_nested_field_binder_sorts() {
    let field = crate::FiniteFieldSort::new(7).unwrap();
    for binder in [
        Sort::FiniteField(field),
        Sort::array(Sort::Int, Sort::FiniteField(field)),
        Sort::Seq(Box::new(Sort::FiniteField(field))),
    ] {
        let mut store = TermStore::new();
        let data = TermData::Forall(
            vec![("forbidden_field_bound".into(), binder)],
            store.true_term(),
            vec![],
        );
        let before = store.len();
        assert_eq!(
            store.try_intern_native_proof_with_progress(&data, &Sort::Bool, &mut |_, _| true),
            Err(ControlledTermInternError::UnsupportedFragment)
        );
        assert_eq!(store.len(), before);
    }
}
