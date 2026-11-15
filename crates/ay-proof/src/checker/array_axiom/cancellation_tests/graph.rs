// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

fn graph(edges: [[bool; 3]; 3], duplicates: usize) -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let witnesses = [
        terms.mk_var("k0", Sort::Int),
        terms.mk_var("k1", Sort::Int),
        terms.mk_var("k2", Sort::Int),
    ];
    let mut steps = Vec::new();
    for (index, row) in edges.iter().enumerate() {
        let mut args = Vec::new();
        for (dependency, &present) in row.iter().enumerate() {
            if present {
                args.extend(std::iter::repeat_n(witnesses[dependency], duplicates));
            }
        }
        let sort = Sort::array(Sort::Int, Sort::Int);
        let left = terms.mk_app(Symbol::named(format!("array-{index}")), args, sort.clone());
        let right = terms.mk_var(format!("base-{index}"), sort);
        steps.push(intro(witnesses[index], left, right));
    }
    (terms, Proof::from_steps(steps))
}

// Independent Floyd-Warshall reachability, not the production Kahn algorithm.
fn acyclic(mut reachable: [[bool; 3]; 3]) -> bool {
    for through in 0..3 {
        for from in 0..3 {
            for to in 0..3 {
                reachable[from][to] |= reachable[from][through] && reachable[through][to];
            }
        }
    }
    (0..3).all(|node| !reachable[node][node])
}

#[test]
fn all_three_witness_dependency_graphs_match_independent_reachability() {
    for mask in 0..512usize {
        let edges = std::array::from_fn(|from| {
            std::array::from_fn(|to| mask & (1 << (3 * from + to)) != 0)
        });
        let (terms, proof) = graph(edges, 1);
        let expected = acyclic(edges);
        let result = ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| true);
        assert_eq!(result.is_ok(), expected, "graph mask {mask}");
        if let Ok(registry) = result {
            assert_eq!(registry.bindings.len(), 3);
        }
    }
}

#[test]
fn dependency_dag_self_cycle_and_long_cycle_all_poll_to_their_terminal_result() {
    for edges in [
        [
            [false, true, true],
            [false, false, true],
            [false, false, false],
        ],
        [[true, false, false], [false; 3], [false; 3]],
        [
            [false, true, false],
            [false, false, true],
            [true, false, false],
        ],
    ] {
        let (terms, proof) = graph(edges, 2);
        every_poll(&proof, &terms, &[]);
    }
}

#[test]
fn introduction_order_does_not_reject_a_valid_dependency_dag() {
    let edges = [[false, true, true], [false, false, true], [false; 3]];
    let (terms, proof) = graph(edges, 2);
    for order in [[0, 1, 2], [2, 1, 0], [1, 0, 2], [2, 0, 1]] {
        let reordered = Proof::from_steps(order.map(|index| proof.steps[index].clone()).to_vec());
        let registry =
            ExtDiffRegistry::collect_with_progress(&reordered, &terms, &[], &mut |_, _| true)
                .unwrap();
        assert_eq!(registry.bindings.len(), 3);
        for (index, step) in reordered.steps.iter().enumerate() {
            let ProofStep::Step { args, .. } = step else {
                panic!("introduction fixture");
            };
            let TermData::Var(name, _) = terms.get(args[0]) else {
                panic!("atomic witness");
            };
            assert_eq!(registry.get(name).unwrap().step, ProofId(index as u32));
        }
    }
}

#[test]
fn wide_duplicate_edges_are_polled_without_creating_false_dependencies() {
    let edges = [[false, true, false], [false; 3], [false; 3]];
    let (terms, proof) = graph(edges, 4096);
    let mut total = 0;
    let registry = ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| {
        total += 1;
        true
    })
    .unwrap();
    assert_eq!(registry.bindings.len(), 3);
    assert!(
        total >= 8192,
        "each duplicate queue push and pop must be polled"
    );
    for stop_at in [1, 4096, 8192, total] {
        let mut calls = 0;
        let result = ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| {
            calls += 1;
            calls != stop_at
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, stop_at);
    }
}

#[test]
fn cycle_diagnostic_preserves_lexical_cycle_start_and_exact_names() {
    let edges = [
        [false, true, false],
        [false, false, true],
        [true, false, false],
    ];
    let (terms, proof) = graph(edges, 1);
    let error =
        ExtDiffRegistry::collect_with_progress(&proof, &terms, &[], &mut |_, _| true).unwrap_err();
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { step: ProofId(0), reason }
        if reason.contains("dependency cycle `k0 -> k1 -> k2 -> k0`"))
    );
}
