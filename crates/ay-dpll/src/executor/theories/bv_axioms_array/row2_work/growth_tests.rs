// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deterministic discovery-work checks, not solver runtime/RSS measurements.

#![cfg(test)]

use super::*;
use ay_core::{Sort, Symbol};

struct Chain {
    executor: Executor,
    roots: Vec<TermId>,
    arrays: Vec<TermId>,
    indices: Vec<TermId>,
}

fn symbolic_chain(depth: usize, reads: usize) -> Chain {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let base = terms.mk_var("base", array_sort);
    let value = terms.mk_var("value", Sort::bitvec(8));
    let mut arrays = vec![base];
    let mut array = base;
    for position in 0..depth {
        let index = terms.mk_var(format!("store-index-{position}"), Sort::bitvec(64));
        array = terms.mk_store(array, index, value);
        arrays.push(array);
    }
    let mut indices = Vec::new();
    let mut roots = Vec::new();
    for position in 0..reads {
        let index = terms.mk_var(format!("read-index-{position}"), Sort::bitvec(64));
        roots.push(terms.mk_select(array, index));
        indices.push(index);
    }
    Chain {
        executor,
        roots,
        arrays,
        indices,
    }
}

#[test]
fn shared_symbolic_store_chains_expand_each_node_and_child_edge_once() {
    for depth in [1, 8, 64, 283] {
        for count in [1, 3] {
            check_chain_work(depth, count);
        }
    }
}

fn check_chain_work(depth: usize, count: usize) {
    let mut chain = symbolic_chain(depth, count);
    let initial_roots = chain.roots.clone();
    let output =
        materialize_with_limit(&mut chain.executor, &mut chain.roots, MAX_LATE_ARRAY_READS);
    let stats = &output.stats;
    // D stores + D store indices + base/value + K read indices and K*(D+1)
    // raw selects. Only the read roots added by this invocation are revisited.
    assert_eq!(stats.unique_nodes, 2 * depth + 2 + count * (depth + 2));
    assert_eq!(stats.child_edges, 3 * depth + 2 * count * (depth + 1));
    assert_eq!(stats.root_attempts, count * (depth + 1));
    assert_eq!(stats.rounds, depth + 1);
    assert_eq!(stats.row2_jobs, count * depth);
    assert_eq!(stats.ite_jobs, 0);
    assert_eq!(stats.max_new_selects, count);
    assert_eq!(output.reads.added_roots(), count * depth);
    assert_eq!(&chain.roots[..count], &initial_roots);
    assert_eq!(chain.executor.ctx.assertions, [] as [TermId; 0]);
    let root_set: HashSet<_> = chain.roots.iter().copied().collect();
    assert_eq!(root_set.len(), count * (depth + 1));
    let before = chain.executor.ctx.terms.len();
    for &array in &chain.arrays {
        for &index in &chain.indices {
            let read = chain.executor.ctx.terms.mk_select(array, index);
            assert!(root_set.contains(&read));
        }
    }
    assert_eq!(
        chain.executor.ctx.terms.len(),
        before,
        "every read already exists"
    );
}

#[test]
fn duplicate_edges_of_a_wide_root_are_not_rescanned_for_each_store_layer() {
    let depth = 64;
    let fanout = 4096;
    let mut chain = symbolic_chain(depth, 1);
    let selected = chain.roots[0];
    let wide = chain.executor.ctx.terms.mk_app(
        Symbol::named("wide-observation"),
        vec![selected; fanout],
        Sort::Bool,
    );
    chain.roots = vec![wide];
    let output =
        materialize_with_limit(&mut chain.executor, &mut chain.roots, MAX_LATE_ARRAY_READS);
    assert_eq!(output.stats.unique_nodes, 3 * depth + 5);
    assert_eq!(output.stats.child_edges, 5 * depth + 2 + fanout);
    assert_eq!(output.stats.root_attempts, depth + 1);
    assert_eq!(output.stats.max_new_selects, 1);
    assert_eq!(output.stats.row2_jobs, depth);
    assert_eq!(output.reads.added_roots(), depth);
    assert_eq!(chain.roots[0], wide);
}

#[test]
fn a_later_index_reactivates_an_already_discovered_and_used_store() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let base = terms.mk_var("base", Sort::array(Sort::bitvec(64), Sort::bitvec(8)));
    let value = terms.mk_var("value", Sort::bitvec(8));
    let i = terms.mk_var("i", Sort::bitvec(64));
    let j = terms.mk_var("j", Sort::bitvec(64));
    let k = terms.mk_var("k", Sort::bitvec(64));
    let condition = terms.mk_var("condition", Sort::Bool);
    let zero = terms.mk_bitvec(0.into(), 8);
    let constant = terms.mk_const_array(Sort::bitvec(64), zero);
    let store = terms.mk_store(base, i, value);
    let first = terms.mk_select(store, j);
    let choice = terms.mk_ite_raw(condition, store, constant);
    let second = terms.mk_select(choice, k);
    let mut roots = vec![first, second];
    let output = materialize_with_limit(&mut executor, &mut roots, MAX_LATE_ARRAY_READS);
    let terms = &mut executor.ctx.terms;
    let later_read = terms.mk_select(store, k);
    let first_base = terms.mk_select(base, j);
    let later_base = terms.mk_select(base, k);
    assert_eq!(
        roots,
        vec![first, second, later_read, zero, first_base, later_base]
    );
    assert_eq!(output.reads.added_roots(), 4);
    assert_eq!(output.reads.get(constant, k), Some(zero));
    assert_eq!(output.stats.ite_jobs, 2);
    assert_eq!(output.stats.row2_jobs, 2);
    assert_eq!(output.stats.rounds, 3);
    assert_eq!(executor.ctx.assertions, [] as [TermId; 0]);
}

#[test]
fn an_assertion_reachable_read_still_counts_as_a_new_supplemental_root() {
    let mut chain = symbolic_chain(1, 1);
    let terms = &mut chain.executor.ctx.terms;
    let base_read = terms.mk_select(chain.arrays[0], chain.indices[0]);
    let value = terms.mk_var("value", Sort::bitvec(8));
    let assertion = terms.mk_app(Symbol::named("="), [base_read, value], Sort::Bool);
    chain.executor.ctx.assertions.push(assertion);
    let first = chain.roots[0];
    let output =
        materialize_with_limit(&mut chain.executor, &mut chain.roots, MAX_LATE_ARRAY_READS);
    assert_eq!(output.reads.added_roots(), 1);
    assert_eq!(chain.roots, vec![first, base_read]);
    assert_eq!(chain.executor.ctx.assertions, vec![assertion]);
    assert_eq!(output.stats.unique_nodes, 8);
    assert_eq!(output.stats.child_edges, 9);
    assert_eq!(output.stats.root_attempts, 3);
    assert_eq!(output.stats.row2_jobs, 1);
    assert_eq!(output.stats.rounds, 2);
}

#[test]
fn deeply_nested_observation_roots_use_iterative_discovery() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let depth = 12_000;
    let mut root = terms.mk_var("observed", Sort::Bool);
    for _ in 0..depth {
        root = terms.mk_not_raw(root);
    }
    executor.ctx.assertions.push(root);
    let mut roots = Vec::new();
    let output = materialize_with_limit(&mut executor, &mut roots, MAX_LATE_ARRAY_READS);
    assert_eq!(output.stats.unique_nodes, depth + 1);
    assert_eq!(output.stats.child_edges, depth);
    assert_eq!(output.stats.root_attempts, 1);
    assert_eq!(output.stats.rounds, 1);
    assert_eq!(output.stats.max_new_selects, 0);
    assert_eq!((output.stats.ite_jobs, output.stats.row2_jobs), (0, 0));
    assert_eq!(output.reads.added_roots(), 0);
    assert_eq!(roots, [] as [TermId; 0]);
    assert_eq!(executor.ctx.assertions, vec![root]);
}
