// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::TheorySolver;

#[test]
fn exact_index_masks_preserve_all_four_emission_arms_and_seeded_order() {
    let mut terms = TermStore::new();
    let array = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("a", array.clone());
    let b = terms.mk_var("b", array.clone());
    let unrelated = terms.mk_var("unrelated", array);
    let indices: Vec<_> = (0..4).map(|i| terms.mk_int(i.into())).collect();
    let first_value = terms.mk_var("first_value", Sort::Int);
    let second_value = terms.mk_var("second_value", Sort::Int);
    let left = terms.mk_store(a, indices[0], first_value);
    let right = terms.mk_store(b, indices[1], second_value);
    let right_same_index = terms.mk_store(b, indices[0], second_value);
    let first_equal = terms.mk_eq(left, right);
    let second_equal = terms.mk_eq(left, right_same_index);
    let mut index_to_selects = HashMap::default();
    let mut reads = Vec::new();
    for &index in &indices[..3] {
        let on_a = terms.mk_select(a, index);
        let on_b = terms.mk_select(b, index);
        index_to_selects.insert(index, vec![(on_a, a), (on_b, b)]);
        reads.push((on_a, on_b));
    }
    let irrelevant = terms.mk_select(unrelated, indices[3]);
    index_to_selects.insert(indices[3], vec![(irrelevant, unrelated)]);
    let pairs = [(left, right), (left, right_same_index)];
    let input = CrossChainInput {
        select_indices: &indices,
        index_to_selects: &index_to_selects,
        eq_pairs: &pairs,
    };
    let mut solver = ArraySolver::new(&terms);
    solver.assert_literal(first_equal, true);
    solver.assert_literal(second_equal, true);
    solver.populate_caches();
    solver.rebuild_assign_indices();
    solver.build_equiv_class_cache();

    let _window = eq_paths_cache::activate();
    let candidates = solver.cross_chain_candidates(&input).unwrap();
    for bits in &candidates.per_pair {
        let bits = bits.as_ref().expect("each pair has real propagation work");
        assert!((0..3).all(|pos| bits.get(pos)));
        assert!(
            !bits.get(3),
            "an unrelated read must not fund either Base arm"
        );
    }
    for seeded in [false, true] {
        let mut seen = HashSet::default();
        let mut output = EqualityPropagationResult::default();
        if seeded {
            assert!(ArraySolver::push_discovered_equality(
                &mut seen,
                &mut output,
                first_value,
                reads[0].1,
                vec![TheoryLit::new(first_equal, true)],
            ));
        }
        let before = seen.clone();
        let prefix = output.equalities.len();
        assert!(!solver.cross_chain_emit(&input, Some(&candidates), &mut seen, &mut output));
        assert!(solver.debug_cross_chain_matches_unfiltered(&input, &before, prefix, &output));
        for (lhs, rhs) in [
            (first_value, reads[0].1),   // Value / Base
            (reads[1].0, second_value),  // Base / Value
            (reads[2].0, reads[2].1),    // Base / Base
            (first_value, second_value), // Value / Value
        ] {
            let pair = ArraySolver::ordered_pair(lhs, rhs);
            assert!(
                output.equalities.iter().any(|eq| {
                    ArraySolver::ordered_pair(eq.lhs, eq.rhs) == pair && !eq.reason.is_empty()
                }),
                "missing genuine reason-carrying emission for {pair:?}"
            );
        }
    }
}

#[test]
fn interrupted_candidate_construction_never_returns_a_complete_mask() {
    let mut terms = TermStore::new();
    let array = terms.mk_var("array", Sort::array(Sort::Int, Sort::Int));
    let index = terms.mk_int(0.into());
    let read = terms.mk_select(array, index);
    let indices = [index];
    let mut selects = HashMap::default();
    selects.insert(index, vec![(read, array)]);
    let pairs = [(array, array)];
    let input = CrossChainInput {
        select_indices: &indices,
        index_to_selects: &selects,
        eq_pairs: &pairs,
    };
    let mut solver = ArraySolver::new(&terms);
    solver.set_interrupt(Arc::new(AtomicBool::new(true)));
    assert!(solver.cross_chain_candidates(&input).is_none());
}
