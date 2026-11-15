// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::super::{HashMap, Sort, Symbol, TermData};
use super::*;
use ay_core::TermStore;
use num_bigint::BigInt;

mod boundary;
mod fixtures;
mod oracle;

use fixtures::{raw_select, Fixture};

fn compare(mut fixture: Fixture, limit: usize) -> (Fixture, LateArrayReads) {
    let mut legacy = Executor::new();
    legacy.ctx.terms = fixture.executor.ctx.terms.clone();
    legacy.ctx.assertions = fixture.executor.ctx.assertions.clone();
    let mut expected_roots = fixture.roots.clone();
    let assertions = fixture.executor.ctx.assertions.clone();
    let old = oracle::materialize(&mut legacy, &mut expected_roots, limit);
    let current = materialize_with_limit(&mut fixture.executor, &mut fixture.roots, limit);
    assert_eq!(fixture.roots, expected_roots, "ordered extra roots");
    assert_eq!(current.reads.added_roots(), old.added_roots());
    assert_eq!(
        fixture.executor.ctx.terms.entries_snapshot(),
        legacy.ctx.terms.entries_snapshot(),
        "exact arena entries and positional IDs"
    );
    assert_eq!(
        fixture.executor.ctx.terms.boolean_constant_ids(),
        legacy.ctx.terms.boolean_constant_ids()
    );
    assert_eq!(fixture.executor.ctx.assertions, assertions);
    assert_eq!(legacy.ctx.assertions, assertions);
    for &(array, index) in &fixture.probes {
        assert_eq!(
            current.reads.get(array, index),
            old.get(array, index),
            "association ({array:?}, {index:?})"
        );
    }
    (fixture, current.reads)
}

fn assert_select(terms: &TermStore, read: TermId, array: TermId, index: TermId) {
    assert!(matches!(terms.get(read), TermData::App(symbol, args)
        if symbol.name() == "select" && args.as_slice() == [array, index]));
}

#[test]
fn shared_subtree_that_is_also_a_later_sibling_keeps_recursive_first_visit() {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let sort = Sort::array(Sort::bitvec(2), Sort::bitvec(1));
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort);
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("value", Sort::bitvec(1));
    let sa = terms.mk_store(a, i, value);
    let sb = terms.mk_store(b, i, value);
    let ra = raw_select(terms, sa, j);
    let rb = raw_select(terms, sb, j);
    let shared = terms.mk_app(Symbol::named("="), [ra, value], Sort::Bool);
    let other = terms.mk_app(Symbol::named("="), [rb, value], Sort::Bool);
    let nested = terms.mk_app(Symbol::named("and"), [shared, other], Sort::Bool);
    let root = terms.mk_app(Symbol::named("and"), [nested, shared], Sort::Bool);
    fixture.executor.ctx.assertions.push(root);
    fixture.probes.extend([(a, j), (b, j)]);
    let (fixture, reads) = compare(fixture, MAX_LATE_ARRAY_READS);
    assert_eq!(reads.added_roots(), 2);
    assert_select(&fixture.executor.ctx.terms, fixture.roots[0], a, j);
    assert_select(&fixture.executor.ctx.terms, fixture.roots[1], b, j);
}

#[test]
fn previously_discovered_store_order_wins_over_reversed_select_encounter_order() {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let sort = Sort::array(Sort::bitvec(2), Sort::bitvec(1));
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort);
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("value", Sort::bitvec(1));
    let sa = terms.mk_store(a, i, value);
    let sb = terms.mk_store(b, i, value);
    let prelude = terms.mk_app(Symbol::named("inspect-arrays"), [sa, sb], Sort::Bool);
    let rb = raw_select(terms, sb, j);
    let ra = raw_select(terms, sa, j);
    let reads = terms.mk_app(Symbol::named("="), [rb, ra], Sort::Bool);
    fixture.executor.ctx.assertions.extend([prelude, reads]);
    fixture.probes.extend([(a, j), (b, j)]);
    let (fixture, reads) = compare(fixture, MAX_LATE_ARRAY_READS);
    assert_eq!(reads.added_roots(), 2);
    assert_select(&fixture.executor.ctx.terms, fixture.roots[0], a, j);
    assert_select(&fixture.executor.ctx.terms, fixture.roots[1], b, j);
}

#[test]
fn shared_dfs_keeps_ite_phase_then_store_order_and_wakes_an_old_store_next_generation() {
    let (fixture, reads) = compare(fixtures::ordered(), MAX_LATE_ARRAY_READS);
    let appended = &fixture.roots[2..];
    assert_eq!(reads.added_roots(), 5);
    assert_eq!(
        fixture.roots[0], fixture.roots[1],
        "initial duplicates survive"
    );
    assert_eq!(
        appended[0],
        fixture.named("first-read"),
        "assertion reachability does not make an extra root already known"
    );
    let terms = &fixture.executor.ctx.terms;
    assert_select(
        terms,
        appended[1],
        fixture.named("second-store"),
        fixture.named("j"),
    );
    assert_select(terms, appended[2], fixture.named("a"), fixture.named("j"));
    assert_select(terms, appended[3], fixture.named("b"), fixture.named("k"));
    assert_select(terms, appended[4], fixture.named("b"), fixture.named("j"));
}

#[test]
fn closure_reentry_preserves_roots_and_arena_without_counting_existing_roots_again() {
    let (fixture, _) = compare(fixtures::ordered(), MAX_LATE_ARRAY_READS);
    let previous = fixture.roots.clone();
    let entries = fixture.executor.ctx.terms.entries_snapshot();
    let (fixture, reads) = compare(fixture, MAX_LATE_ARRAY_READS);
    assert_eq!(reads.added_roots(), 0);
    assert_eq!(fixture.roots, previous);
    assert_eq!(fixture.executor.ctx.terms.entries_snapshot(), entries);
}

#[test]
fn folded_const_store_map_and_ite_results_keep_first_phase_order_and_duplicate_binding() {
    let (fixture, reads) = compare(fixtures::folded(), MAX_LATE_ARRAY_READS);
    let appended = &fixture.roots[2..];
    assert_eq!(reads.added_roots(), 3);
    assert_eq!(appended[0], fixture.named("one"));
    assert_eq!(appended[1], fixture.named("inner-value"));
    assert_eq!(
        reads.get(fixture.named("zero-array"), fixture.named("j")),
        Some(fixture.named("zero"))
    );
    assert_eq!(
        reads.get(fixture.named("inner-store"), fixture.named("j")),
        Some(appended[1])
    );
    assert_eq!(
        reads.get(fixture.named("map"), fixture.named("j")),
        Some(appended[2])
    );
    assert!(
        matches!(fixture.executor.ctx.terms.get(appended[2]), TermData::App(symbol, args)
        if symbol.name() == "bvnot" && args.as_slice() == [fixture.named("zero")])
    );
}

#[test]
fn frozen_grammar_ignores_let_and_quantifier_bodies_but_visits_not_and_indexed_apps() {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let array = terms.mk_var("a", Sort::array(Sort::bitvec(2), Sort::bitvec(1)));
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let value = terms.mk_var("value", Sort::bitvec(1));
    let store = terms.mk_store(array, i, value);
    let read = terms.mk_app(
        Symbol::indexed("select", vec![17]),
        [store, j],
        Sort::bitvec(1),
    );
    let body = terms.mk_app(Symbol::named("="), [read, value], Sort::Bool);
    let hidden = terms.mk_let(vec![("read".to_owned(), read)], body);
    let quantified = terms.mk_forall_with_triggers(vec![], body, vec![vec![read]]);
    let negated = terms.mk_not_raw(body);
    fixture.executor.ctx.assertions.extend([hidden, quantified]);
    fixture.probes.push((array, j));
    let before = fixture.executor.ctx.terms.entries_snapshot();
    let (mut fixture, ignored) = compare(fixture, MAX_LATE_ARRAY_READS);
    assert_eq!(ignored.added_roots(), 0);
    assert_eq!(fixture.executor.ctx.terms.entries_snapshot(), before);
    fixture.roots.push(negated);
    let (fixture, visible) = compare(fixture, MAX_LATE_ARRAY_READS);
    assert_eq!(visible.added_roots(), 1);
    assert_select(&fixture.executor.ctx.terms, fixture.roots[1], array, j);
}

#[test]
fn folded_map_result_discovers_its_new_residual_select_in_the_next_generation() {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let sort = Sort::array(Sort::bitvec(2), Sort::bitvec(1));
    let base = terms.mk_var("base", sort.clone());
    let i = terms.mk_var("i", Sort::bitvec(2));
    let j = terms.mk_var("j", Sort::bitvec(2));
    let k = terms.mk_var("k", Sort::bitvec(2));
    let inner_value = terms.mk_var("inner-value", Sort::bitvec(1));
    let outer_value = terms.mk_var("outer-value", Sort::bitvec(1));
    let inner = terms.mk_store(base, k, inner_value);
    let mapped = terms.mk_array_map("bvnot", vec![inner], sort);
    let outer = terms.mk_store(mapped, i, outer_value);
    let root = raw_select(terms, outer, j);
    fixture.roots.push(root);
    fixture.probes.extend([(mapped, j), (inner, j), (base, j)]);
    let initial_entries = terms.entries_snapshot().len();
    let (fixture, reads) = compare(fixture, MAX_LATE_ARRAY_READS);
    assert_eq!(reads.added_roots(), 2);
    assert_eq!(fixture.roots[0], root);
    let folded = fixture.roots[1];
    let terms = &fixture.executor.ctx.terms;
    let TermData::App(symbol, arguments) = terms.get(folded) else {
        panic!("map result must retain the scalar operator");
    };
    assert_eq!(symbol.name(), "bvnot");
    assert_eq!(arguments.len(), 1);
    assert_select(terms, arguments[0], inner, j);
    assert_select(terms, fixture.roots[2], base, j);
    assert_eq!(reads.get(mapped, j), Some(folded));
    // Nested mk_select calls are discovered as terms, not invented carrier
    // associations; the subsequent ordinary ROW2 read stays a raw select.
    assert_eq!(reads.get(inner, j), None);
    assert_eq!(reads.get(base, j), None);
    assert_eq!(terms.entries_snapshot().len(), initial_entries + 3);
}

#[test]
fn nested_array_ite_reads_keep_then_else_order_across_generation_barriers() {
    let mut fixture = Fixture::empty();
    let terms = &mut fixture.executor.ctx.terms;
    let sort = Sort::array(Sort::bitvec(2), Sort::bitvec(1));
    let arrays: Vec<_> = ["a", "b", "c", "d"]
        .into_iter()
        .map(|name| terms.mk_var(name, sort.clone()))
        .collect();
    let root_condition = terms.mk_var("root-condition", Sort::Bool);
    let left_condition = terms.mk_var("left-condition", Sort::Bool);
    let right_condition = terms.mk_var("right-condition", Sort::Bool);
    let index = terms.mk_var("index", Sort::bitvec(2));
    let left = terms.mk_ite_raw(left_condition, arrays[0], arrays[1]);
    let right = terms.mk_ite_raw(right_condition, arrays[2], arrays[3]);
    let nested = terms.mk_ite_raw(root_condition, left, right);
    let root = raw_select(terms, nested, index);
    fixture.roots.push(root);
    let expected_arrays = [left, right, arrays[0], arrays[1], arrays[2], arrays[3]];
    fixture
        .probes
        .extend(expected_arrays.into_iter().map(|array| (array, index)));
    let initial_entries = terms.entries_snapshot().len();
    let (fixture, reads) = compare(fixture, MAX_LATE_ARRAY_READS);
    assert_eq!(reads.added_roots(), 6);
    assert_eq!(fixture.roots[0], root);
    assert_eq!(fixture.roots.len(), 7);
    for (read, array) in fixture.roots[1..].iter().zip(expected_arrays) {
        assert_select(&fixture.executor.ctx.terms, *read, array, index);
        assert_eq!(reads.get(array, index), None);
    }
    assert_eq!(
        fixture.executor.ctx.terms.entries_snapshot().len(),
        initial_entries + 6
    );
}
