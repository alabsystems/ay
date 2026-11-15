// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Genuine public residual completion and residual-disabled replay; no SAT solver.

use super::*;
use std::sync::Arc;

#[path = "residual_nested_arrays/fixtures.rs"]
mod fixtures;
#[path = "residual_nested_arrays/pins.rs"]
mod pins;
#[path = "residual_nested_arrays/refusal.rs"]
mod refusal;
#[path = "residual_nested_arrays/stores.rs"]
mod stores;
use fixtures::*;

#[test]
fn packed_pblit_reads_complete_shared_pbterm_arrays_and_replay_every_original() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let outer_alias = terms.mk_var("outer_alias", Sort::bitvec(64));
    let inner_alias = terms.mk_var("inner_alias", Sort::bitvec(64));
    let [element, vector, _, first] = f.read(&mut terms, f.a, f.outer, f.inner);
    let [_, _, _, same] = f.read(&mut terms, f.b, outer_alias, inner_alias);
    let coefficient = app(&mut terms, "fld_coeff", &[element], Sort::bitvec(128));
    let length = app(&mut terms, "fld_len", &[vector], Sort::bitvec(64));
    let roots = [
        eq(&mut terms, f.a, f.b),
        eq_bv(&mut terms, first, 0x80_0000_0001, 40),
        eq_bv(&mut terms, same, 0x80_0000_0001, 40),
        eq_bv(&mut terms, coefficient, 7, 128),
        eq_bv(&mut terms, length, 65, 64),
    ];
    let mut model = Model::default();
    model
        .leaves
        .insert(outer_alias, Arc::new(bv(0x8000_0000_0000_0001, 64)));
    model.leaves.insert(inner_alias, Arc::new(bv(33, 64)));
    assert_cannot(&confirm_completed_model(&terms, &model, &roots));
    let assignments = complete(&terms, &model, &roots);
    assert_eq!(assignments.len(), 2);
    assert!(Arc::ptr_eq(assignments[0].value(), assignments[1].value()));
    assert!(model.leaf_value(f.a).is_none());
    model.install(&terms, assignments);
    assert!(Arc::ptr_eq(&model.leaves[&f.a], &model.leaves[&f.b]));
    assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
    assert_bv(&terms, &model, same, 0x80_0000_0001, 40);
    assert_bv(&terms, &model, coefficient, 7, 128);
    assert_bv(&terms, &model, length, 65, 64);
}

#[test]
fn semantic_inner_keys_merge_aliases_but_distinct_high_keys_stay_distinct() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let alias = terms.mk_var("key_alias", Sort::bitvec(64));
    let high = terms.mk_bitvec(BigInt::from(0x8000_0000_0000_0021u64), 64);
    let [_, _, _, low_read] = f.read(&mut terms, f.a, f.outer, f.inner);
    let [_, _, _, alias_read] = f.read(&mut terms, f.a, f.outer, alias);
    let [_, _, _, high_read] = f.read(&mut terms, f.a, f.outer, high);
    let low = eq_bv(&mut terms, low_read, 5, 40);
    let same = eq_bv(&mut terms, alias_read, 5, 40);
    let conflict = eq_bv(&mut terms, alias_read, 6, 40);
    let high = eq_bv(&mut terms, high_read, 7, 40);
    let mut model = Model::default();
    model.leaves.insert(alias, Arc::new(bv(33, 64)));
    refused(&terms, &model, &[low, conflict]);
    let roots = [low, same, high];
    let assignments = complete(&terms, &model, &roots);
    model.install(&terms, assignments);
    assert_confirmed(&confirm_completed_model(&terms, &model, &roots));
    assert_bv(&terms, &model, low_read, 5, 40);
    assert_bv(&terms, &model, high_read, 7, 40);
}

#[test]
fn completion_data_cannot_hide_a_false_original_or_a_later_quantified_root() {
    let mut terms = TermStore::new();
    let f = Fixture::new(&mut terms);
    let [_, _, _, cell] = f.read(&mut terms, f.a, f.outer, f.inner);
    let root = eq_bv(&mut terms, cell, 5, 40);
    let no = terms.mk_bool(false);
    let mut model = Model::default();
    refused(&terms, &model, &[root, no]);
    let assignments = complete(&terms, &model, &[root]);
    model.install(&terms, assignments);
    let bad = eq_bv(&mut terms, cell, 6, 40);
    let quantified = terms.mk_forall(vec![("unused".into(), Sort::bitvec(2))], bad);
    assert_confirmed(&confirm_completed_model(&terms, &model, &[root]));
    assert_violates(&confirm_completed_model(
        &terms,
        &model,
        &[root, quantified],
    ));
}
