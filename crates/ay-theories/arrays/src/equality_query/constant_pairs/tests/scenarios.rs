// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn merged_value_classes_span_multiple_blocks_and_parallel_disequalities_deduplicate() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let a = select(&mut terms, "a", i);
    let b = select(&mut terms, "b", i);
    let c = select(&mut terms, "c", j);
    let d = select(&mut terms, "d", j);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let equalities = [
        terms.mk_eq(a, one),
        terms.mk_eq(c, one),
        terms.mk_eq(b, two),
        terms.mk_eq(d, two),
    ];
    let disequalities = [terms.mk_eq(a, b), terms.mk_eq(c, d), terms.mk_eq(a, d)];
    let index_equality = terms.mk_eq(i, j);
    for reverse in [false, true] {
        let mut solver = ArraySolver::new(&terms);
        let assignments: Vec<_> = equalities
            .iter()
            .map(|&id| (id, true))
            .chain(disequalities.iter().map(|&id| (id, false)))
            .collect();
        for &(id, value) in if reverse {
            assignments.iter().rev().collect::<Vec<_>>()
        } else {
            assignments.iter().collect()
        } {
            solver.assert_literal(id, value);
        }
        prepare(&mut solver);
        assert_eq!(
            check_oracle(&solver),
            [
                ArraySolver::ordered_pair(a, b),
                ArraySolver::ordered_pair(c, d)
            ]
        );
        solver.assert_literal(index_equality, true);
        prepare(&mut solver);
        assert_eq!(check_oracle(&solver).len(), 4);
    }
}

#[test]
fn explicit_disequalities_without_constants_and_same_class_disequalities_are_preserved() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let a = select(&mut terms, "a", i);
    let b = select(&mut terms, "b", i);
    let c = select(&mut terms, "c", i);
    let one = terms.mk_int(1.into());
    let ab = terms.mk_eq(a, b);
    let a_one = terms.mk_eq(a, one);
    let b_one = terms.mk_eq(b, one);
    let bc = terms.mk_eq(b, c);
    let mut solver = ArraySolver::new(&terms);
    solver.assert_literal(ab, false);
    solver.assert_literal(bc, false);
    prepare(&mut solver);
    let before = comparisons();
    assert_eq!(
        check_oracle(&solver),
        [
            ArraySolver::ordered_pair(a, b),
            ArraySolver::ordered_pair(b, c)
        ]
    );
    assert_eq!(comparisons() - before, 0);
    solver.assert_literal(a_one, true);
    solver.assert_literal(b_one, true);
    prepare(&mut solver);
    assert_eq!(
        solver.equiv_class_representative(a),
        solver.equiv_class_representative(b)
    );
    assert_eq!(check_oracle(&solver).len(), 3);
}

#[test]
fn affine_and_opaque_leaf_congruence_blocks_keep_exact_old_candidates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let plus_left = terms.mk_app(Symbol::named("+"), [x, one], Sort::Int);
    let plus_right = terms.mk_app(Symbol::named("+"), [one, x], Sort::Int);
    let opaque = terms.mk_app(Symbol::named("opaque"), [z], Sort::Int);
    let mixed_left = terms.mk_app(Symbol::named("+"), [x, opaque], Sort::Int);
    let mixed_right = terms.mk_app(Symbol::named("+"), [y, opaque], Sort::Int);
    let reads = [
        select(&mut terms, "a", plus_left),
        select(&mut terms, "b", plus_right),
        select(&mut terms, "c", mixed_left),
        select(&mut terms, "d", mixed_right),
    ];
    let bindings: Vec<_> = reads
        .iter()
        .enumerate()
        .map(|(n, &read)| terms.mk_eq(read, if n % 2 == 0 { one } else { two }))
        .collect();
    let xy = terms.mk_eq(x, y);
    let mut solver = ArraySolver::new(&terms);
    for binding in bindings {
        solver.assert_literal(binding, true);
    }
    prepare(&mut solver);
    assert_eq!(
        check_oracle(&solver),
        [ArraySolver::ordered_pair(reads[0], reads[1])]
    );
    solver.assert_literal(xy, true);
    prepare(&mut solver);
    assert!(solver
        .explain_equal_if_provable(mixed_left, mixed_right)
        .is_some());
    assert_eq!(
        check_oracle(&solver),
        [
            ArraySolver::ordered_pair(reads[0], reads[1]),
            ArraySolver::ordered_pair(reads[2], reads[3]),
        ]
    );
}

#[test]
fn unreasoned_sentinel_edges_keep_overapproximate_candidates_for_uninterpreted_indices() {
    let mut terms = TermStore::new();
    let index_sort = Sort::Uninterpreted("Index".into());
    let i = terms.mk_var("i", index_sort.clone());
    let j = terms.mk_var("j", index_sort);
    let a = select(&mut terms, "a", i);
    let b = select(&mut terms, "b", j);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let a_one = terms.mk_eq(a, one);
    let b_two = terms.mk_eq(b, two);
    let mut solver = ArraySolver::new(&terms);
    solver.assert_literal(a_one, true);
    solver.assert_literal(b_two, true);
    prepare(&mut solver);
    assert!(check_oracle(&solver).is_empty());
    assert!(solver.assert_external_equality(i, j));
    prepare(&mut solver);
    assert!(solver.eq_adj[&i]
        .iter()
        .any(|&(other, via)| other == j && via == TermId::SENTINEL));
    assert!(solver.explain_equal_if_provable(i, j).is_none());
    assert_eq!(check_oracle(&solver), [ArraySolver::ordered_pair(a, b)]);
}

#[test]
fn index_merge_push_pop_and_frozen_window_memo_preserve_old_sorted_results() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let a = select(&mut terms, "a", i);
    let b = select(&mut terms, "b", j);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let bindings = [terms.mk_eq(a, one), terms.mk_eq(b, two)];
    let ij = terms.mk_eq(i, j);
    let mut solver = ArraySolver::new(&terms);
    for binding in bindings {
        solver.assert_literal(binding, true);
    }
    prepare(&mut solver);
    assert!(check_oracle(&solver).is_empty());
    solver.push();
    solver.assert_literal(ij, true);
    prepare(&mut solver);
    let expected = check_oracle(&solver);
    assert_eq!(expected, [ArraySolver::ordered_pair(a, b)]);
    {
        let _guard = eq_paths_cache::activate();
        let before = comparisons();
        let first = solver.select_conflict_candidate_pairs();
        let second = solver.select_conflict_candidate_pairs();
        assert_eq!(first.as_ref(), expected.as_slice());
        assert_eq!(second.as_ref(), expected.as_slice());
        assert!(Rc::ptr_eq(&first, &second));
        assert_eq!(comparisons() - before, 1);
    }
    solver.pop();
    prepare(&mut solver);
    assert!(check_oracle(&solver).is_empty());
}
