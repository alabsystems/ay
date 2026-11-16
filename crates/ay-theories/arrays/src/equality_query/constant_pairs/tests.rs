// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Sort, Symbol, TermStore, TheorySolver};

mod oracle;
mod scenarios;

fn prepare(solver: &mut ArraySolver<'_>) {
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();
}

fn select(terms: &mut TermStore, name: &str, index: TermId) -> TermId {
    let array = terms.mk_var(name, Sort::array(terms.sort(index).clone(), Sort::Int));
    terms.mk_select(array, index)
}

fn check_oracle(solver: &ArraySolver<'_>) -> Vec<(TermId, TermId)> {
    let expected = oracle::pairs(solver);
    let actual = solver.select_conflict_candidate_pairs_uncached();
    assert_eq!(
        actual, expected,
        "complete sorted candidates, not just emitted conflicts"
    );
    assert!(actual.iter().all(|&(a, b)| a < b));
    assert!(actual.windows(2).all(|pair| pair[0] < pair[1]));
    actual
}

fn constant_case(count: usize, block_size: usize) -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let indices: Vec<_> = (0..count.div_ceil(block_size))
        .map(|i| terms.mk_var(format!("index{i}"), Sort::Int))
        .collect();
    let mut assignments = Vec::new();
    for i in 0..count {
        let read = select(&mut terms, &format!("array{i}"), indices[i / block_size]);
        let value = terms.mk_int(BigInt::from(i));
        assignments.push(terms.mk_eq(read, value));
    }
    (terms, assignments)
}

#[test]
fn singleton_index_blocks_do_no_constant_pair_comparisons_as_population_grows() {
    for count in [8, 32, 128] {
        let (terms, assignments) = constant_case(count, 1);
        let mut solver = ArraySolver::new(&terms);
        for atom in assignments {
            solver.assert_literal(atom, true);
        }
        prepare(&mut solver);
        assert_eq!(solver.select_cache.len(), count);
        let before = comparisons();
        assert_eq!(check_oracle(&solver).len(), 0);
        assert_eq!(comparisons() - before, 0);
        // The frozen reference still constructs this many global constant
        // comparisons; the assertion measures production loop events, not time.
        assert!(count * (count - 1) / 2 > count);
    }
}

#[test]
fn concrete_bv64_indices_in_one_array_keep_r22_candidates_empty_until_a_shared_index() {
    for count in [8, 32, 128] {
        for shared_index in [false, true] {
            let mut terms = TermStore::new();
            let array_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(32));
            let array = terms.mk_var("L", array_sort.clone());
            let mut bindings = Vec::new();
            let mut reads = Vec::new();
            for k in 0..count {
                let index = terms.mk_bitvec(BigInt::from(k), 64);
                let value = terms.mk_bitvec(BigInt::from(k), 32);
                let read = terms.mk_select(array, index);
                reads.push(read);
                bindings.push(terms.mk_eq(read, value));
            }
            let mut expected = Vec::new();
            if shared_index {
                let other_array = terms.mk_var("other", array_sort);
                let index = terms.mk_bitvec(5.into(), 64);
                let value = terms.mk_bitvec(BigInt::from(count), 32);
                let other_read = terms.mk_select(other_array, index);
                bindings.push(terms.mk_eq(other_read, value));
                expected.push(ArraySolver::ordered_pair(reads[5], other_read));
            }
            let mut solver = ArraySolver::new(&terms);
            for binding in bindings {
                solver.assert_literal(binding, true);
            }
            prepare(&mut solver);
            let expected_classes = count + usize::from(shared_index);
            assert_eq!(solver.select_cache.len(), expected_classes);
            let mut classes = HashSet::default();
            for &read in solver.select_cache.keys() {
                classes.insert(solver.equiv_class_representative(read));
                assert!(solver.get_equiv_class(read).into_iter().any(|term| {
                    matches!(terms.get(term), TermData::Const(Constant::BitVec { .. }))
                }));
            }
            assert_eq!(classes.len(), expected_classes);
            let before = comparisons();
            assert_eq!(check_oracle(&solver), expected);
            assert_eq!(comparisons() - before, usize::from(shared_index));
        }
    }
}

#[test]
fn two_class_blocks_scale_linearly_and_dense_blocks_retain_all_required_pairs() {
    for (count, block_size, expected) in [(32, 2, 16), (128, 2, 64), (8, 8, 28)] {
        let (terms, assignments) = constant_case(count, block_size);
        let mut solver = ArraySolver::new(&terms);
        for atom in assignments {
            solver.assert_literal(atom, true);
        }
        prepare(&mut solver);
        let before = comparisons();
        assert_eq!(check_oracle(&solver).len(), expected);
        assert_eq!(comparisons() - before, expected);
    }
}

#[test]
fn equal_constants_and_repeated_select_slots_do_not_create_new_class_pairs() {
    let constants = vec![
        (TermId(1), Constant::Int(1.into())),
        (TermId(2), Constant::Int(1.into())),
        (TermId(3), Constant::Int(2.into())),
    ];
    let mut groups = ClassBlockGroups::default();
    for &(class, _) in &constants {
        let mut blocks = HashMap::default();
        // Membership is per class/block, not per select occurrence.
        blocks.insert(TermId(20), vec![TermId(30), TermId(30), TermId(31)]);
        blocks.insert(TermId(21), vec![TermId(32)]);
        groups.insert(class, blocks);
    }
    let mut pairs = HashSet::default();
    pairs.insert((TermId(1), TermId(1))); // existing same-class disequality
    pairs.insert((TermId(1), TermId(2))); // explicit disequality wins equality
    let before = comparisons();
    add_pairs(&constants, &groups, &mut pairs);
    assert_eq!(comparisons() - before, 6);
    let mut actual: Vec<_> = pairs.into_iter().collect();
    actual.sort_unstable();
    assert_eq!(
        actual,
        [
            (TermId(1), TermId(1)),
            (TermId(1), TermId(2)),
            (TermId(1), TermId(3)),
            (TermId(2), TermId(3)),
        ]
    );
}
