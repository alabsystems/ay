// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

#[test]
fn roots_shared_ancestors_and_nested_join_bodies_are_detected() {
    for (nodes, edges, roots, expected) in [
        (2, vec![], vec![0, 0], true),
        (2, vec![], vec![0, 1], false),
        (3, vec![(1, vec![0]), (2, vec![0])], vec![1, 2], true),
        (
            4,
            vec![(1, vec![0]), (2, vec![0]), (3, vec![1, 2])],
            vec![3],
            true,
        ),
        (4, vec![(1, vec![0]), (3, vec![2])], vec![1, 3], false),
        // Unequal-depth sharing is deliberately conservative, not licensed by
        // the fact that this particular overlap would use different levels.
        (3, vec![(1, vec![0]), (2, vec![1])], vec![0, 2], true),
    ] {
        let problem = fixtures::graph(nodes, &edges, &roots);
        assert_eq!(has_shared_ancestry(&problem, &mut || true), Some(expected));
    }
}

#[test]
fn same_owner_cycles_and_alternative_rule_diamonds_terminate() {
    let edges = [
        (0, vec![1]),
        (0, vec![2]),
        (1, vec![3]),
        (2, vec![3]),
        (3, vec![0]),
    ];
    let problem = fixtures::graph(5, &edges, &[0, 4]);
    let polls = Cell::new(0usize);
    assert_eq!(
        has_shared_ancestry(&problem, &mut || {
            polls.set(polls.get() + 1);
            assert!(polls.get() < 100);
            true
        }),
        Some(false)
    );
    assert_eq!(
        has_shared_ancestry(&fixtures::graph(5, &edges, &[0, 3]), &mut || true),
        Some(true)
    );
}

#[test]
fn all_four_node_dags_match_independent_transitive_closure_oracle() {
    let candidates = [(1, 0), (2, 0), (2, 1), (3, 0), (3, 1), (3, 2)];
    for mask in 0u8..64 {
        let edges: Vec<_> = candidates
            .iter()
            .enumerate()
            .filter_map(|(bit, &(head, body))| {
                (mask & (1 << bit) != 0).then_some((head, vec![body]))
            })
            .collect();
        let mut reach = [[false; 4]; 4];
        for (index, row) in reach.iter_mut().enumerate() {
            row[index] = true;
        }
        for (head, body) in &edges {
            reach[*head][body[0]] = true;
        }
        for via in 0..4 {
            for from in 0..4 {
                for to in 0..4 {
                    let through = reach[from][via] && reach[via][to];
                    reach[from][to] |= through;
                }
            }
        }
        for left in 0..4 {
            for right in 0..4 {
                let expected =
                    (0..4).any(|ancestor| reach[left][ancestor] && reach[right][ancestor]);
                let problem = fixtures::graph(4, &edges, &[left, right]);
                assert_eq!(
                    has_shared_ancestry(&problem, &mut || true),
                    Some(expected),
                    "mask {mask}, roots {left}/{right}"
                );
            }
        }
    }
}

#[test]
fn deep_and_duplicate_definition_work_is_iterative_and_cancellable() {
    let edges: Vec<_> = (1..12_000).map(|head| (head, vec![head - 1])).collect();
    let problem = fixtures::graph(12_001, &edges, &[11_999, 12_000]);
    assert_eq!(has_shared_ancestry(&problem, &mut || true), Some(false));
    let visits = Cell::new(0usize);
    assert_eq!(
        has_shared_ancestry(&problem, &mut || {
            visits.set(visits.get() + 1);
            visits.get() < 12_100
        }),
        None
    );
    assert_eq!(
        visits.get(),
        12_100,
        "refusal occurs inside ancestry, after indexing"
    );

    let duplicate_edges = vec![(0, vec![1]); 4096];
    let problem = fixtures::graph(3, &duplicate_edges, &[0, 2]);
    let polls = Cell::new(0usize);
    assert_eq!(
        has_shared_ancestry(&problem, &mut || {
            polls.set(polls.get() + 1);
            true
        }),
        Some(false)
    );
    assert_eq!(
        polls.get(),
        3 * 4096 + 9,
        "same-owner nodes are queued once despite repeated definitions"
    );
}
