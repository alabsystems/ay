// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pure collector/membership tests, not solver verdicts or RSS measurements.

use super::super::{Executor, HashSet, Sort, Symbol, TermData};
use super::*;

mod oracle;

type Select = (TermId, TermId, TermId);
type Store = (TermId, TermId, TermId, TermId);

struct Census {
    selects: Vec<Select>,
    stores: Vec<Store>,
    arrays: HashSet<TermId>,
    suffix_links: usize,
    contributions: usize,
}

fn compare(executor: &Executor) -> Census {
    let mut selects = Vec::new();
    let mut stores = Vec::new();
    let mut visited = HashSet::default();
    for &root in &executor.ctx.assertions {
        executor.collect_array_terms(root, &mut selects, &mut stores, &mut visited);
    }
    let (expected, suffix_links) = oracle::membership(&executor.ctx.terms, &stores);
    let mut contributions = 0;
    let arrays: HashSet<_> = store_arrays(&stores)
        .inspect(|_| contributions += 1)
        .collect();
    assert_eq!(arrays, expected, "exact frozen membership set");
    assert_eq!(contributions, 2 * stores.len());
    let expected_count = selects
        .iter()
        .filter(|&&(_, array, _)| expected.contains(&array))
        .count();
    assert_eq!(
        executor.count_complex_array_selects_in_assertions(),
        expected_count,
        "the existing fixpoint gate sees exactly the same count"
    );
    Census {
        selects,
        stores,
        arrays,
        suffix_links,
        contributions,
    }
}

fn raw_read(terms: &mut ay_core::TermStore, array: TermId, index: TermId) -> TermId {
    let sort = terms.sort(array).array_element().unwrap().clone();
    terms.mk_app(Symbol::named("select"), [array, index], sort)
}

fn source_chain(depth: usize, reads: usize) -> Executor {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let zero = terms.mk_bitvec(0.into(), 8);
    let base = terms.mk_const_array(Sort::bitvec(64), zero);
    let mut arrays = vec![base];
    for position in 0..depth {
        let index = terms.mk_bitvec(position.into(), 64);
        let value = terms.mk_bitvec((position % 255 + 1).into(), 8);
        let next = terms.mk_store(*arrays.last().unwrap(), index, value);
        arrays.push(next);
    }
    let mut roots = vec![*arrays.last().unwrap()];
    for position in 0..reads {
        let index = terms.mk_var(format!("read-{position}"), Sort::bitvec(64));
        for &array in &arrays {
            roots.push(raw_read(terms, array, index));
        }
    }
    let root = terms.mk_app(Symbol::named("observe"), roots, Sort::Bool);
    executor.ctx.assertions.extend([root, root]);
    executor
}

#[test]
fn concrete_store_chain_membership_has_two_contributions_per_store() {
    for depth in [0, 1, 8, 64, 283] {
        for reads in [0, 1, 3] {
            let executor = source_chain(depth, reads);
            let census = compare(&executor);
            assert_eq!(census.stores.len(), depth);
            assert_eq!(census.selects.len(), (depth + 1) * reads);
            assert_eq!(census.arrays.len(), if depth == 0 { 0 } else { depth + 1 });
            assert_eq!(census.suffix_links, depth * depth.saturating_sub(1) / 2);
            assert_eq!(census.contributions, 2 * depth);
            assert_eq!(
                executor.count_complex_array_selects_in_assertions(),
                if depth == 0 { 0 } else { (depth + 1) * reads }
            );
        }
    }
}

#[test]
fn exact_retained_reducer_parses_without_solving_and_keeps_all_283_stores() {
    let source = include_str!(
        "../../../../../../../benchmarks/smt/model_checker_consumer_const_store_chain_memout.smt2"
    );
    assert_eq!(source.matches("(store ").count(), 283);
    let commands = ay_frontend::parse(source).unwrap();
    let mut executor = Executor::new();
    let mut checks = 0;
    for command in &commands {
        if matches!(command, ay_frontend::Command::CheckSat) {
            checks += 1;
        } else {
            // Frontend elaboration only; never Executor::execute/check_sat.
            executor.ctx.process_command(command).unwrap();
        }
    }
    assert_eq!(checks, 1);
    let census = compare(&executor);
    assert_eq!(census.stores.len(), 283);
    assert!(
        census.selects.is_empty(),
        "source reads are introduced by later phases"
    );
    assert_eq!(census.arrays.len(), 284);
    assert_eq!(census.suffix_links, 39_903);
    assert_eq!(census.contributions, 566);
    assert_eq!(executor.count_complex_array_selects_in_assertions(), 0);
}

#[test]
fn shared_prefixes_ite_and_indexed_apps_preserve_exact_collector_membership() {
    let mut executor = source_chain(8, 1);
    let before = compare(&executor);
    let shared = before.stores[3].0;
    let terms = &mut executor.ctx.terms;
    let condition = terms.mk_var("condition", Sort::Bool);
    let index = terms.mk_var("branch-index", Sort::bitvec(64));
    let value = terms.mk_var("branch-value", Sort::bitvec(8));
    let branch = terms.mk_store(shared, index, value);
    let branch_read = raw_read(terms, branch, index);
    let old_read = before.selects[0].0;
    let choice = terms.mk_ite_raw(condition, branch_read, old_read);
    let indexed = terms.mk_app(
        Symbol::indexed("extract", vec![3, 0]),
        [choice],
        Sort::bitvec(4),
    );
    let equality = terms.mk_app(Symbol::named("="), [indexed, indexed], Sort::Bool);
    let root = terms.mk_not_raw(equality);
    executor.ctx.assertions.extend([root, root]);
    let after = compare(&executor);
    assert_eq!(after.stores.len(), before.stores.len() + 1);
    assert_eq!(after.selects.len(), before.selects.len() + 1);
    assert_eq!(after.arrays.len(), before.arrays.len() + 1);
    assert!(after.arrays.contains(&branch));
    assert!(after.arrays.contains(&shared));
}

#[test]
fn malformed_named_store_is_only_an_opaque_base_not_an_extra_store() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let index = terms.mk_var("index", Sort::bitvec(64));
    let value = terms.mk_var("value", Sort::Bool);
    let malformed = terms.mk_app(Symbol::named("store"), [base, index], sort.clone());
    let outer = terms.mk_app(Symbol::named("store"), [malformed, index, value], sort);
    let a = raw_read(terms, malformed, index);
    let b = raw_read(terms, outer, index);
    let c = raw_read(terms, base, index);
    let root = terms.mk_app(Symbol::named("and"), [a, b, c], Sort::Bool);
    executor.ctx.assertions.push(root);
    let census = compare(&executor);
    assert_eq!(census.stores.len(), 1);
    assert_eq!(census.arrays, HashSet::from_iter([malformed, outer]));
    assert_eq!(executor.count_complex_array_selects_in_assertions(), 2);
}

#[test]
fn let_and_quantifier_bodies_stay_hidden_while_indexed_store_names_keep_existing_behavior() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let sort = Sort::array(Sort::bitvec(64), Sort::Bool);
    let base = terms.mk_var("base", sort.clone());
    let index = terms.mk_var("index", Sort::bitvec(64));
    let value = terms.mk_var("value", Sort::Bool);
    let store = terms.mk_app(
        Symbol::indexed("store", vec![7]),
        [base, index, value],
        sort,
    );
    let read = terms.mk_app(
        Symbol::indexed("select", vec![9]),
        [store, index],
        Sort::Bool,
    );
    let body = terms.mk_app(Symbol::named("and"), [read, read], Sort::Bool);
    let hidden = terms.mk_let(vec![("read".to_owned(), read)], body);
    let quantified = terms.mk_forall_with_triggers(vec![], body, vec![vec![read]]);
    let visible = terms.mk_not_raw(body);
    executor.ctx.assertions.extend([hidden, quantified]);
    let before = compare(&executor);
    assert!(before.stores.is_empty() && before.selects.is_empty());
    assert_eq!(executor.count_complex_array_selects_in_assertions(), 0);
    executor.ctx.assertions.push(visible);
    let after = compare(&executor);
    assert_eq!(after.stores.len(), 1);
    assert_eq!(after.selects.len(), 1);
    assert_eq!(after.arrays, HashSet::from_iter([base, store]));
    assert_eq!(executor.count_complex_array_selects_in_assertions(), 1);
}
