// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exercise late materialization and the real axiom producer, without SAT search.

#![cfg(test)]

use super::*;

mod boolean;
mod circuit;
mod equal_indices;
mod fc_shared_guards;
mod precedence;
mod row_equal_indices;

use circuit::{materialize, raw_select, Circuit};

#[test]
fn constant_default_gets_bits_and_restores_row2_even_when_old_bits_are_preallocated() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("v", Sort::bitvec(1));
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let base = terms.mk_const_array(Sort::bitvec(2), zero);
    let store = terms.mk_store(base, i, value);
    let result = raw_select(terms, store, j);
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.added_roots(), 1);
    assert_eq!(reads.get(base, j), Some(zero));
    assert!(roots.contains(&zero));

    let mut bv = materialize(&executor, &roots, None, &[]);
    assert!(bv.get_term_bits(zero).is_none());
    executor.materialize_array_bv_terms(&mut bv, &roots, Some(&reads));
    assert!(bv.get_term_bits(zero).is_some());
    let observed = [i, j, value, result];
    let linked = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    linked.check_relation(|v| v[3] == if v[0] == v[1] { v[2] } else { 0 });
    // Both versions see IDENTICAL already-materialized bits. Only the retained
    // association differs: a scalar zero root is not a raw select lookup.
    let omitted = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    omitted.check_relation(|v| v[0] != v[1] || v[3] == v[2]);
    assert!(linked.axioms.len() > omitted.axioms.len());
}

#[test]
fn variable_base_keeps_identical_clauses_and_complete_row1_row2_semantics() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let base = terms.mk_var("base", Sort::array(Sort::bitvec(2), Sort::bitvec(1)));
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("v", Sort::bitvec(1));
    let store = terms.mk_store(base, i, value);
    let result = raw_select(terms, store, j);
    let base_read = terms.mk_select(base, j);
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.added_roots(), 1);
    assert_eq!(reads.get(base, j), None);
    assert!(roots.contains(&base_read));
    let bv = materialize(&executor, &roots, Some(&reads), &[]);
    let observed = [i, j, value, base_read, result];
    let old = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    let new = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    assert_eq!(new.axioms, old.axioms);
    assert_eq!(new.num_vars, old.num_vars);
    assert_eq!(new.clauses, old.clauses);
    new.check_relation(|v| v[4] == if v[0] == v[1] { v[2] } else { v[3] });
}

#[test]
fn inner_store_read_folds_to_its_value_without_losing_the_outer_row2_link() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let base = terms.mk_var("base", Sort::array(Sort::bitvec(2), Sort::bitvec(1)));
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let inner_value = terms.mk_var("inner", Sort::bitvec(1));
    let outer_value = terms.mk_var("outer", Sort::bitvec(1));
    let inner = terms.mk_store(base, j, inner_value);
    let outer = terms.mk_store(inner, i, outer_value);
    let result = raw_select(terms, outer, j);
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.get(inner, j), Some(inner_value));
    let bv = materialize(&executor, &roots, Some(&reads), &[]);
    let observed = [i, j, inner_value, outer_value, result];
    let cnf = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    cnf.check_relation(|v| v[4] == if v[0] == v[1] { v[3] } else { v[2] });
    let omitted = Circuit::new(&executor, &bv, &roots, None, &observed, &BTreeMap::new());
    omitted.check_relation(|v| v[0] != v[1] || v[4] == v[3]);
}

#[test]
fn mixed_ite_branch_reads_use_the_actual_mapped_condition() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let condition = terms.mk_var("condition", Sort::Bool);
    let index = terms.mk_var("index", Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let then_array = terms.mk_const_array(Sort::bitvec(2), zero);
    let else_array = terms.mk_var("else", terms.sort(then_array).clone());
    let choice = terms.mk_ite_raw(condition, then_array, else_array);
    let result = raw_select(terms, choice, index);
    let else_read = terms.mk_select(else_array, index);
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.get(then_array, index), Some(zero));
    assert_eq!(reads.get(else_array, index), None);
    assert!(roots.contains(&else_read));
    let bv = materialize(&executor, &roots, Some(&reads), &[condition]);
    let mapping = circuit::condition_map(&bv, condition);
    let observed = [condition, else_read, result];
    let linked = Circuit::new(&executor, &bv, &roots, Some(&reads), &observed, &mapping);
    linked.check_relation(|v| v[2] == if v[0] == 1 { 0 } else { v[1] });
    let omitted = Circuit::new(&executor, &bv, &roots, None, &observed, &mapping);
    omitted.check_relation(|_| true);
}

#[test]
fn two_folded_ite_branches_do_not_bypass_the_existing_condition_mapping_gate() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let condition = terms.mk_var("condition", Sort::Bool);
    let index = terms.mk_var("index", Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0), 1);
    let one = terms.mk_bitvec(BigInt::from(1), 1);
    let a = terms.mk_const_array(Sort::bitvec(2), zero);
    let b = terms.mk_const_array(Sort::bitvec(2), one);
    let choice = terms.mk_ite_raw(condition, a, b);
    let result = raw_select(terms, choice, index);
    let mut roots = vec![result];
    let reads = executor.materialize_array_row2_read_terms(&mut roots);
    assert_eq!(reads.get(a, index), Some(zero));
    assert_eq!(reads.get(b, index), Some(one));
    let bv = materialize(&executor, &roots, Some(&reads), &[condition]);
    let observed = [condition, result];
    let mapping = circuit::condition_map(&bv, condition);
    let linked = Circuit::new(&executor, &bv, &roots, Some(&reads), &observed, &mapping);
    linked.check_relation(|v| v[1] == 1 - v[0]);
    assert_eq!(linked.axioms.len(), 4);
    let unmapped = Circuit::new(
        &executor,
        &bv,
        &roots,
        Some(&reads),
        &observed,
        &BTreeMap::new(),
    );
    unmapped.check_relation(|_| true);
    assert!(unmapped.axioms.is_empty());
    let omitted = Circuit::new(&executor, &bv, &roots, None, &observed, &mapping);
    omitted.check_relation(|_| true);
    assert!(omitted.axioms.is_empty());
}
