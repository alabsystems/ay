// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Carrier bounds and eager-dependency controls; no SAT search.

#![cfg(test)]

use super::*;
use ay_core::Symbol;

#[test]
fn exact_reads_are_not_folded_associations_and_repeated_folds_are_deduplicated() {
    let mut terms = TermStore::new();
    let zero = terms.mk_bitvec(0.into(), 8);
    let constant = terms.mk_const_array(Sort::bitvec(64), zero);
    let variable = terms.mk_var("array", terms.sort(constant).clone());
    let index = terms.mk_var("index", Sort::bitvec(64));
    let mut reads = LateArrayReads::default();
    let raw = reads.materialize_read(&mut terms, variable, index);
    assert!(matches!(terms.get(raw), TermData::App(sym, args)
        if sym.name() == "select" && args.as_slice() == [variable, index]));
    assert_eq!(reads.get(variable, index), None);
    let before = terms.len();
    for _ in 0..8 {
        assert_eq!(reads.materialize_read(&mut terms, constant, index), zero);
    }
    assert_eq!(terms.len(), before, "folding must not mint a raw select");
    assert_eq!(reads.folded.len(), 1);
    assert_eq!(reads.get(constant, index), Some(zero));
    assert_eq!(reads.added_roots(), 0, "associations are not new roots");
}

#[test]
fn association_cap_bounds_many_obligations_aliasing_one_value_without_stopping_rewrites() {
    let mut terms = TermStore::new();
    let zero = terms.mk_bitvec(0.into(), 8);
    let array = terms.mk_const_array(Sort::bitvec(16), zero);
    let mut reads = LateArrayReads::default();
    let mut indices = Vec::new();
    for ordinal in 0..=MAX_LATE_ARRAY_READS {
        let index = terms.mk_bitvec(ordinal.into(), 16);
        assert_eq!(reads.materialize_read(&mut terms, array, index), zero);
        indices.push(index);
    }
    assert_eq!(reads.folded.len(), MAX_LATE_ARRAY_READS);
    for &index in &indices[..MAX_LATE_ARRAY_READS] {
        assert_eq!(reads.get(array, index), Some(zero));
    }
    let refused_index = indices[MAX_LATE_ARRAY_READS];
    assert_eq!(reads.get(array, refused_index), None);
    // A full association carrier still returns the arena's actual rewrite;
    // neither an unrelated root nor a later invocation inherits its allowance.
    let one = terms.mk_bitvec(1.into(), 8);
    let other_array = terms.mk_const_array(Sort::bitvec(16), one);
    assert_eq!(
        reads.materialize_read(&mut terms, other_array, refused_index),
        one
    );
    assert_eq!(reads.get(other_array, refused_index), None);
    assert_eq!(reads.materialize_read(&mut terms, array, indices[0]), zero);
    assert_eq!(reads.get(array, indices[0]), Some(zero));
    reads.note_added_root();
    assert_eq!(reads.added_roots(), 1);
    assert_eq!(reads.folded.len(), MAX_LATE_ARRAY_READS);
    let mut fresh = LateArrayReads::default();
    assert_eq!(fresh.get(array, indices[0]), None);
    assert_eq!(
        fresh.materialize_read(&mut terms, array, refused_index),
        zero
    );
    assert_eq!(fresh.get(array, refused_index), Some(zero));
}

#[test]
fn non_scalar_folds_return_the_actual_value_without_granting_an_association() {
    let mut terms = TermStore::new();
    let integer = terms.mk_var("integer", Sort::Int);
    let scalar_array = terms.mk_const_array(Sort::bitvec(8), integer);
    let nested = terms.mk_const_array(Sort::bitvec(8), scalar_array);
    let index = terms.mk_var("i", Sort::bitvec(8));
    let mut reads = LateArrayReads::default();
    for (array, expected) in [(scalar_array, integer), (nested, scalar_array)] {
        assert_eq!(reads.materialize_read(&mut terms, array, index), expected);
        assert_eq!(reads.get(array, index), None);
    }
    assert!(reads.folded.is_empty());
}

#[test]
fn rewritten_raw_read_keeps_the_requested_array_and_index_association() {
    let mut terms = TermStore::new();
    let value = terms.mk_bitvec(7.into(), 8);
    let constant = terms.mk_const_array(Sort::bitvec(8), value);
    let base = terms.mk_var("base", terms.sort(constant).clone());
    let zero = terms.mk_bitvec(0.into(), 8);
    let one = terms.mk_bitvec(1.into(), 8);
    let stored = terms.mk_store(base, zero, value);
    let expected = terms.mk_select(base, one);
    let mut reads = LateArrayReads::default();
    assert_eq!(reads.materialize_read(&mut terms, stored, one), expected);
    assert_eq!(reads.get(stored, one), Some(expected));
    assert_eq!(reads.get(base, one), None);
    assert_eq!(reads.materialize_read(&mut terms, stored, zero), value);
    assert_eq!(reads.get(stored, zero), Some(value));
}

fn conditional_default(terms: &mut TermStore) -> (TermId, TermId, Vec<TermId>) {
    let x = terms.mk_var("x", Sort::bitvec(16));
    let y = terms.mk_var("y", Sort::bitvec(16));
    let product = terms.mk_app(Symbol::named("bvmul"), [x, y], Sort::bitvec(16));
    let condition = terms.mk_app(Symbol::named("bvult"), [product, x], Sort::Bool);
    let negated = terms.mk_not_raw(condition);
    let value = terms.mk_ite_raw(negated, x, y);
    (value, condition, vec![value, x, y, product])
}

#[test]
fn eager_walk_reaches_bv_dependencies_below_boolean_conditions_without_scanning_the_arena() {
    let mut terms = TermStore::new();
    let (value, condition, expected) = conditional_default(&mut terms);
    let value_array = terms.mk_const_array(Sort::bitvec(8), value);
    let bool_array = terms.mk_const_array(Sort::bitvec(8), condition);
    let index = terms.mk_var("index", Sort::bitvec(8));
    let unrelated = terms.mk_var("unrelated", Sort::bitvec(32));
    let preexisting = terms.mk_var("already-eager", Sort::bitvec(32));
    let mut reads = LateArrayReads::default();
    let _ = reads.materialize_read(&mut terms, value_array, index);
    let _ = reads.materialize_read(&mut terms, bool_array, index);
    let mut eager = HashSet::default();
    eager.insert(preexisting);
    reads.extend_eager_terms(&terms, &mut eager);
    for term in expected {
        assert!(eager.contains(&term));
    }
    assert!(eager.contains(&preexisting));
    assert!(!eager.contains(&condition));
    assert!(!eager.contains(&index));
    assert!(!eager.contains(&unrelated));
    assert_eq!(eager.len(), 5);
    let original = eager.clone();
    reads.extend_eager_terms(&terms, &mut eager);
    assert_eq!(eager, original);
}

#[test]
fn folded_arithmetic_is_really_encoded_when_delay_mode_is_enabled() {
    let mut terms = TermStore::new();
    let (value, condition, _) = conditional_default(&mut terms);
    let array = terms.mk_const_array(Sort::bitvec(8), value);
    let bool_array = terms.mk_const_array(Sort::bitvec(8), condition);
    let index = terms.mk_var("index", Sort::bitvec(8));
    let mut reads = LateArrayReads::default();
    let _ = reads.materialize_read(&mut terms, array, index);
    let _ = reads.materialize_read(&mut terms, bool_array, index);
    let mut uncontrolled = BvSolver::new(&terms);
    uncontrolled.set_delay_enabled(true);
    reads.materialize_bits(&mut uncontrolled, &terms);
    assert!(
        !uncontrolled.delayed_ops().is_empty(),
        "fixture must exercise delay"
    );
    let mut eager = HashSet::default();
    reads.extend_eager_terms(&terms, &mut eager);
    let mut encoded = BvSolver::new(&terms);
    encoded.set_delay_enabled(true);
    encoded.set_eager_terms(eager);
    reads.materialize_bits(&mut encoded, &terms);
    assert!(encoded.delayed_ops().is_empty());
    assert_eq!(encoded.get_term_bits(value).unwrap().len(), 16);
    assert!(encoded.bool_to_var().contains_key(&condition));
    assert_ne!(encoded.clauses(), []);
    let (variables, clauses) = (encoded.num_vars(), encoded.clauses().len());
    reads.materialize_bits(&mut encoded, &terms);
    assert_eq!(encoded.num_vars(), variables);
    assert_eq!(encoded.clauses().len(), clauses);
}

#[test]
fn eager_walk_does_not_cross_a_residual_selects_array_operand() {
    let mut terms = TermStore::new();
    let (value, _, dependencies) = conditional_default(&mut terms);
    let constant = terms.mk_const_array(Sort::bitvec(8), value);
    let base = terms.mk_var("base", terms.sort(constant).clone());
    let symbolic_index = terms.mk_var("k", Sort::bitvec(8));
    let inner = terms.mk_store(base, symbolic_index, value);
    let zero = terms.mk_bitvec(0.into(), 8);
    let one = terms.mk_bitvec(1.into(), 8);
    let outer_value = terms.mk_bitvec(9.into(), 16);
    let outer = terms.mk_store(inner, zero, outer_value);
    let mut reads = LateArrayReads::default();
    let residual = reads.materialize_read(&mut terms, outer, one);
    assert!(matches!(terms.get(residual), TermData::App(sym, args)
        if sym.name() == "select" && args.as_slice() == [inner, one]));
    assert_eq!(reads.get(outer, one), Some(residual));
    let mut eager = HashSet::default();
    reads.extend_eager_terms(&terms, &mut eager);
    assert!(eager.contains(&residual));
    assert!(eager.contains(&one));
    assert_eq!(eager.len(), 2);
    for hidden in dependencies {
        assert!(!eager.contains(&hidden));
    }
    // The existing store collector owns eager policy for these positions;
    // this helper must not expand it just because a folded read points here.
    assert!(!eager.contains(&symbolic_index));
    assert!(!eager.contains(&outer_value));
}
