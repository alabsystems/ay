// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact read-over-store misses; all positives recheck the original store AST.

use super::*;

fn store(terms: &mut TermStore, base: TermId, key: TermId, value: TermId) -> TermId {
    let sort = terms.sort(base).clone();
    app(terms, "store", &[base, key, value], sort)
}

fn select(terms: &mut TermStore, array: TermId, key: TermId) -> TermId {
    app(terms, "select", &[array, key], Sort::bitvec(40))
}

#[test]
fn inner_store_miss_completes_the_base_and_replays_unchanged_source() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data, base_read] = f.read(&mut terms, f.a, f.outer, f.inner);
    let written = terms.mk_bitvec(BigInt::from(42), 64);
    let value = terms.mk_bitvec(BigInt::from(9), 40);
    let stored = store(&mut terms, data, written, value);
    let read = select(&mut terms, stored, f.inner);
    let assertion = eq_bv(&mut terms, read, 5, 40);
    assert!(matches!(terms.get(read), ay_core::term::TermData::App(_, args) if args[0] == stored));
    let mut model = Model::default();
    assert_cannot(&confirm_completed_model(&terms, &model, &[assertion]));
    let assignments = complete(&terms, &model, &[assertion]);
    model.install(&terms, assignments);
    assert_confirmed(&confirm_completed_model(&terms, &model, &[assertion]));
    assert_bv(&terms, &model, base_read, 5, 40);
    assert_bv(&terms, &model, read, 5, 40);
    let hit = select(&mut terms, stored, written);
    assert_bv(&terms, &model, hit, 9, 40);
}

#[test]
fn a_known_miss_does_not_require_an_unpinned_stored_value() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data, _] = f.read(&mut terms, f.a, f.outer, f.inner);
    let written = terms.mk_bitvec(BigInt::from(42), 64);
    let missing = terms.mk_var("unobserved_write", Sort::bitvec(40));
    let stored = store(&mut terms, data, written, missing);
    let read = select(&mut terms, stored, f.inner);
    let root = eq_bv(&mut terms, read, 5, 40);
    let mut model = Model::default();
    let assignments = complete(&terms, &model, &[root]);
    model.install(&terms, assignments);
    assert!(model.leaf_value(missing).is_none());
    assert_confirmed(&confirm_completed_model(&terms, &model, &[root]));
    assert_bv(&terms, &model, read, 5, 40);
}

#[test]
fn a_skipped_write_value_dag_still_conserves_its_hidden_committed_read() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data, pinned] = f.read(&mut terms, f.a, f.outer, f.inner);
    let written = terms.mk_bitvec(BigInt::from(42), 64);
    let nine = terms.mk_bitvec(BigInt::from(9), 40);
    let yes = terms.mk_bool(true);
    let hidden = terms.mk_ite_raw(yes, nine, pinned);
    let stored = store(&mut terms, data, written, hidden);
    let read = select(&mut terms, stored, f.inner);
    let good = eq_bv(&mut terms, read, 5, 40);
    let bad = eq_bv(&mut terms, read, 6, 40);
    let mut model = Model::default();
    model.selects.insert(pinned, bv(5, 40));
    assert_bv(&terms, &model, hidden, 9, 40);
    refused(&terms, &model, &[bad]);
    let assignments = complete(&terms, &model, &[good]);
    model.install(&terms, assignments);
    assert_confirmed(&confirm_completed_model(&terms, &model, &[good]));
    assert_bv(&terms, &model, pinned, 5, 40);
}

#[test]
fn outer_and_inner_misses_preserve_aliases_and_both_stored_values() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let outer_write = terms.mk_bitvec(BigInt::from(10), 64);
    let replacement = terms.mk_var("replacement", f.element.clone());
    let outer_stored = store(&mut terms, f.a, outer_write, replacement);
    let [_, _, data, _] = f.read(&mut terms, outer_stored, f.outer, f.inner);
    let inner_write = terms.mk_bitvec(BigInt::from(42), 64);
    let value = terms.mk_bitvec(BigInt::from(9), 40);
    let inner_stored = store(&mut terms, data, inner_write, value);
    let read = select(&mut terms, inner_stored, f.inner);
    let [_, _, _, alias_read] = f.read(&mut terms, f.b, f.outer, f.inner);
    let roots = [
        eq(&mut terms, f.a, f.b),
        eq_bv(&mut terms, read, 5, 40),
        eq_bv(&mut terms, alias_read, 5, 40),
    ];
    let mut model = Model::default();
    model
        .leaves
        .insert(replacement, Arc::new(element(fixtures::data(7, &[]))));
    let assignments = complete(&terms, &model, &roots);
    assert_eq!(assignments.len(), 2);
    assert!(Arc::ptr_eq(assignments[0].value(), assignments[1].value()));
    model.install(&terms, assignments);
    assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
    assert_bv(&terms, &model, read, 5, 40);
    let [_, _, _, outer_hit] = f.read(&mut terms, outer_stored, outer_write, f.inner);
    assert_bv(&terms, &model, outer_hit, 7, 40);
    let inner_hit = select(&mut terms, inner_stored, inner_write);
    assert_bv(&terms, &model, inner_hit, 9, 40);
}

#[test]
fn newest_matching_store_wins_without_inventing_a_completion_for_hits() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data, _] = f.read(&mut terms, f.a, f.outer, f.inner);
    let four = terms.mk_bitvec(BigInt::from(4), 40);
    let five = terms.mk_bitvec(BigInt::from(5), 40);
    let older = store(&mut terms, data, f.inner, four);
    let newer = store(&mut terms, older, f.inner, five);
    let read = select(&mut terms, newer, f.inner);
    let good = eq_bv(&mut terms, read, 5, 40);
    let bad = eq_bv(&mut terms, read, 4, 40);
    let model = Model::default();
    let roots = [good];
    let (verdict, completion) =
        confirm_model_with_array_completion(&terms, &model, &roots).into_parts();
    assert_confirmed(&verdict);
    assert!(
        completion.is_none(),
        "ordinary read-over-store evaluates this hit"
    );
    refused(&terms, &model, &[bad]);
    let missing = terms.mk_var("missing_stored_value", Sort::bitvec(40));
    let unknown = store(&mut terms, data, f.inner, missing);
    let read = select(&mut terms, unknown, f.inner);
    let root = eq_bv(&mut terms, read, 5, 40);
    refused(&terms, &model, &[root]);
}

#[test]
fn committed_miss_read_in_an_unselected_boolean_arm_constrains_the_base() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data, base_read] = f.read(&mut terms, f.a, f.outer, f.inner);
    let written = terms.mk_bitvec(BigInt::from(42), 64);
    let value = terms.mk_bitvec(BigInt::from(9), 40);
    let stored = store(&mut terms, data, written, value);
    let pinned = select(&mut terms, stored, f.inner);
    let pin_clause = eq_bv(&mut terms, pinned, 6, 40);
    let yes = terms.mk_bool(true);
    let already_true = app(&mut terms, "or", &[yes, pin_clause], Sort::Bool);
    let same = eq_bv(&mut terms, base_read, 5, 40);
    let conflict = eq_bv(&mut terms, base_read, 6, 40);
    let mut model = Model::default();
    model.selects.insert(pinned, bv(5, 40));
    assert_bv(&terms, &model, pinned, 5, 40);
    assert_confirmed(&confirm_completed_model(&terms, &model, &[already_true]));
    refused(&terms, &model, &[already_true, conflict]);
    let roots = [already_true, same];
    let assignments = complete(&terms, &model, &roots);
    model.install(&terms, assignments);
    assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
    assert_bv(&terms, &model, pinned, 5, 40);
}

#[test]
fn committed_base_read_and_miss_read_cannot_disagree() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data, base_read] = f.read(&mut terms, f.a, f.outer, f.inner);
    let [_, _, _, other] = f.read(&mut terms, f.b, f.outer, f.inner);
    let written = terms.mk_bitvec(BigInt::from(42), 64);
    let value = terms.mk_bitvec(BigInt::from(9), 40);
    let stored = store(&mut terms, data, written, value);
    let miss = select(&mut terms, stored, f.inner);
    let yes = terms.mk_bool(true);
    let pinned = eq_bv(&mut terms, miss, 5, 40);
    let hidden = app(&mut terms, "or", &[yes, pinned], Sort::Bool);
    let base_pin = eq_bv(&mut terms, base_read, 5, 40);
    let hidden_base = app(&mut terms, "or", &[yes, base_pin], Sort::Bool);
    let alias = eq(&mut terms, f.a, f.b);
    let other_five = eq_bv(&mut terms, other, 5, 40);
    for base_value in [5, 6] {
        let mut model = Model::default();
        model.selects.insert(base_read, bv(base_value, 40));
        model.selects.insert(miss, bv(5, 40));
        let roots = [hidden, hidden_base, alias, other_five];
        if base_value == 5 {
            let assignments = complete(&terms, &model, &roots);
            model.install(&terms, assignments);
            assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
        } else {
            refused(&terms, &model, &roots);
        }
    }
}

#[test]
fn unknown_or_wrong_sort_store_keys_and_malformed_store_metadata_refuse() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, data, _] = f.read(&mut terms, f.a, f.outer, f.inner);
    let unknown = terms.mk_var("unknown_store_key", Sort::bitvec(64));
    let wrong_key = terms.mk_bitvec(BigInt::from(42), 32);
    let key = terms.mk_bitvec(BigInt::from(42), 64);
    let value = terms.mk_bitvec(BigInt::from(9), 40);
    let wrong_value = terms.mk_bool(true);
    let malformed = [
        store(&mut terms, data, unknown, value),
        store(&mut terms, data, wrong_key, value),
        store(&mut terms, data, key, wrong_value),
        app(
            &mut terms,
            "store",
            &[data, key, value],
            Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        ),
    ];
    for array in malformed {
        let read = select(&mut terms, array, f.inner);
        let root = eq_bv(&mut terms, read, 5, 40);
        refused(&terms, &Model::default(), &[root]);
    }
    let stored = store(&mut terms, data, key, value);
    let missing_read_key = terms.mk_var("unknown_read_key", Sort::bitvec(64));
    let read = select(&mut terms, stored, missing_read_key);
    let root = eq_bv(&mut terms, read, 5, 40);
    refused(&terms, &Model::default(), &[root]);
    let stored = store(&mut terms, data, unknown, value);
    let read = select(&mut terms, stored, f.inner);
    let root = eq_bv(&mut terms, read, 5, 40);
    for value in [
        bv(42, 32),
        ModelValue::BitVec {
            value: BigInt::from(-1),
            width: 64,
        },
        ModelValue::BitVec {
            value: BigInt::from(1) << (residual::MAX_WITNESS_VALUE_WORK * 8),
            width: 64,
        },
    ] {
        let mut model = Model::default();
        model.leaves.insert(unknown, Arc::new(value));
        refused(&terms, &model, &[root]);
    }
}

#[test]
fn arbitrary_store_equations_remain_outside_local_read_miss_recovery() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let replacement = terms.mk_var("replacement", f.element.clone());
    let written = terms.mk_bitvec(BigInt::from(10), 64);
    let stored = store(&mut terms, f.a, written, replacement);
    let equation = eq(&mut terms, f.b, stored);
    let [_, _, _, read] = f.read(&mut terms, stored, f.outer, f.inner);
    let requirement = eq_bv(&mut terms, read, 5, 40);
    let mut model = Model::default();
    model
        .leaves
        .insert(replacement, Arc::new(element(data(0, &[]))));
    refused(&terms, &model, &[equation, requirement]);
    refused(&terms, &model, &[requirement, equation]);
    let tautology = eq(&mut terms, stored, stored);
    let wrapper = app(&mut terms, "opaque_wrapper", &[stored], Sort::Bool);
    let wrapped_tautology = eq(&mut terms, wrapper, wrapper);
    let yes = terms.mk_bool(true);
    let conditional = terms.mk_ite_raw(yes, stored, stored);
    let conditional_tautology = eq(&mut terms, conditional, conditional);
    for already_true in [tautology, wrapped_tautology, conditional_tautology] {
        assert_confirmed(&confirm_completed_model(&terms, &model, &[already_true]));
        refused(&terms, &model, &[already_true, requirement]);
        refused(&terms, &model, &[requirement, already_true]);
    }
}

#[test]
fn miss_chain_bounds_refuse_without_partial_retention_and_fresh_retry_succeeds() {
    for count in [2, residual::MAX_CLASSIFY_DEPTH + 1] {
        let mut terms = TermStore::new();
        let f = Fixture::new(&mut terms);
        let [_, _, data, _] = f.read(&mut terms, f.a, f.outer, f.inner);
        let value = terms.mk_bitvec(BigInt::from(9), 40);
        let mut array = data;
        for index in 0..count {
            let key = terms.mk_bitvec(BigInt::from(index + 100), 64);
            array = store(&mut terms, array, key, value);
        }
        let read = select(&mut terms, array, f.inner);
        let root = eq_bv(&mut terms, read, 5, 40);
        let mut model = Model::default();
        if count == 2 {
            let assignments = complete(&terms, &model, &[root]);
            model.install(&terms, assignments);
            assert_confirmed(&confirm_completed_model(&terms, &model, &[root]));
        } else {
            refused(&terms, &model, &[root]);
            assert!(model.leaf_value(f.a).is_none());
            let base = select(&mut terms, data, f.inner);
            let simple = eq_bv(&mut terms, base, 5, 40);
            assert_eq!(complete(&terms, &model, &[simple]).len(), 1);
        }
    }
}
