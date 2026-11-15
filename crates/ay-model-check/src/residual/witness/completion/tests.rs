// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod fixtures;
use fixtures::*;

#[test]
fn ordinary_complete_refuted_and_unsupported_verdicts_never_attach_data() {
    let mut terms = TermStore::new();
    let yes = terms.mk_bool(true);
    let no = terms.mk_bool(false);
    let absent = terms.mk_var("absent", Sort::Bool);
    let model = Model::default();
    for (term, expected) in [(yes, 0), (no, 1), (absent, 2)] {
        let roots = [term];
        let (verdict, completion) =
            crate::confirm_model_with_array_completion(&terms, &model, &roots).into_parts();
        assert!(completion.is_none());
        let tag = match verdict {
            GateVerdict::ConfirmedSat => 0,
            GateVerdict::ModelViolates { .. } => 1,
            GateVerdict::CannotConfirm { .. } => 2,
        };
        assert_eq!(tag, expected);
        assert_eq!(
            std::mem::discriminant(&verdict),
            std::mem::discriminant(&crate::confirm_model(&terms, &model, &roots)),
        );
    }
}

#[test]
fn nested_alias_extension_moves_exact_shared_arrays_and_replays_all_roots() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let unrelated = terms.mk_var("unrelated", Sort::bitvec(64));
    let mut model = Model::default();
    let unrelated_value = Arc::new(ModelValue::bitvec(BigInt::from(99), 64));
    model.leaves.insert(unrelated, Arc::clone(&unrelated_value));
    assert!(matches!(
        confirm_completed_model(&terms, &model, &f.roots),
        GateVerdict::CannotConfirm { .. }
    ));
    let assignments = completion(&terms, &model, &f.roots)
        .into_assignments()
        .unwrap();
    assert_eq!(assignments.len(), 2);
    assert_eq!(assignments[0].term(), f.a);
    assert_eq!(assignments[1].term(), f.b);
    assert!(Arc::ptr_eq(assignments[0].value(), assignments[1].value()));
    assert_eq!(Some(assignments[0].stamp()), terms.entry_stamp(f.a));
    assert!(model.leaf_value(f.a).is_none());
    let ModelValue::Array(array) = assignments[0].value().as_ref() else {
        panic!("complete array required");
    };
    assert_eq!(array.store.len(), 1);
    let ModelValue::Datatype { ctor, args } = &array.store[0].1 else {
        panic!("real PbTerm required");
    };
    assert_eq!(ctor, "mkPbTerm");
    assert_eq!(args.len(), 2);
    let ModelValue::Datatype { ctor, args } = &args[1] else {
        panic!("real nested Vec required");
    };
    assert_eq!(ctor, "mkVec_bv8");
    assert!(matches!(&args[3], ModelValue::Array(inner) if inner.store.is_empty()));
    assert!(matches!(array.default, ModelValue::Datatype { .. }));
    model.install(&terms, assignments);
    assert!(Arc::ptr_eq(&model.leaves[&f.a], &model.leaves[&f.b]));
    assert!(Arc::ptr_eq(&model.leaves[&unrelated], &unrelated_value));
    assert!(matches!(
        confirm_completed_model(&terms, &model, &f.roots),
        GateVerdict::ConfirmedSat
    ));
    assert_value(&terms, &model, f.length, 65, 64);
    assert_value(&terms, &model, f.capacity, 66, 64);
    assert_value(&terms, &model, f.coefficient, 7, 128);
}

#[test]
fn committed_nested_pin_is_preserved_and_conflicting_alias_never_exports() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let conflicting = eq_bv(&mut terms, f.b_length, 66, 64);
    let mut model = Model::default();
    model
        .applications
        .insert(f.length, ModelValue::bitvec(BigInt::from(65), 64));
    let data = completion(&terms, &model, &f.roots)
        .into_assignments()
        .unwrap();
    let mut bad = f.roots.clone();
    bad.push(conflicting);
    let (verdict, rejected) =
        crate::confirm_model_with_array_completion(&terms, &model, &bad).into_parts();
    assert!(!matches!(verdict, GateVerdict::ConfirmedSat));
    assert!(rejected.is_none());
    drop(rejected);
    assert!(model.leaf_value(f.a).is_none());
    model.install(&terms, data);
    assert!(model.applications.contains_key(&f.length));
    assert!(matches!(
        confirm_completed_model(&terms, &model, &f.roots),
        GateVerdict::ConfirmedSat
    ));
    assert!(matches!(
        confirm_completed_model(&terms, &model, &bad),
        GateVerdict::ModelViolates { .. }
    ));
}

#[test]
fn later_definitive_refutation_outranks_an_earlier_residual_gap() {
    let mut terms = TermStore::new();
    let mut f = Fixture::new(&mut terms);
    f.roots.push(terms.mk_bool(false));
    let model = Model::default();
    let (verdict, completion) =
        crate::confirm_model_with_array_completion(&terms, &model, &f.roots).into_parts();
    assert!(matches!(verdict, GateVerdict::ModelViolates { .. }));
    assert!(completion.is_none());
}

#[test]
fn exported_data_does_not_justify_omitting_a_quantified_original_root() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let mut model = Model::default();
    let data = completion(&terms, &model, &f.roots)
        .into_assignments()
        .unwrap();
    model.install(&terms, data);
    let false_body = eq_bv(&mut terms, f.length, 66, 64);
    let quantified = terms.mk_forall(vec![("i".into(), Sort::bitvec(2))], false_body);
    let mut full_roots = f.roots.clone();
    full_roots.push(quantified);
    assert!(matches!(
        confirm_completed_model(&terms, &model, &f.roots),
        GateVerdict::ConfirmedSat
    ));
    assert!(matches!(
        confirm_completed_model(&terms, &model, &full_roots),
        GateVerdict::ModelViolates { .. }
    ));
}

#[test]
fn extraction_uses_the_remaining_shared_allocation_and_comparison_allowances() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let model = Model::default();
    let bytes = extraction_bytes(2, 1).unwrap();
    let comparisons = 2 * (2 + 1);
    assert!(bytes < MAX_WITNESS_VALUE_WORK);
    for (short_bytes, short_work) in [(0, 0), (1, 0), (0, 1)] {
        let mut retained = completion(&terms, &model, &f.roots);
        retained.budget.value_work = MAX_WITNESS_VALUE_WORK - bytes + short_bytes;
        retained.budget.index_comparisons = MAX_INDEX_COMPARISONS - comparisons + short_work;
        let data = retained.into_assignments();
        assert_eq!(data.is_some(), short_bytes == 0 && short_work == 0);
    }
    assert!(completion(&terms, &model, &f.roots)
        .into_assignments()
        .is_some());
    assert!(matches!(
        crate::confirm_model(&terms, &model, &f.roots),
        GateVerdict::ConfirmedSat
    ));
}

#[test]
fn numeric_term_indices_from_another_store_do_not_authenticate_data() {
    let mut original = TermStore::new();
    let first = Fixture::new(&mut original);
    let model = Model::default();
    let data = completion(&original, &model, &first.roots)
        .into_assignments()
        .unwrap();
    let mut other = TermStore::new();
    let second = Fixture::new(&mut other);
    assert_eq!(first.a, second.a);
    assert_eq!(first.b, second.b);
    for assignment in data {
        let (term, stamp, _) = assignment.into_parts();
        assert_eq!(Some(stamp), original.entry_stamp(term));
        assert_ne!(Some(stamp), other.entry_stamp(term));
    }
}
