// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for formula component decomposition.

use super::*;
use crate::literal::{Literal, Variable};

fn pos(var: usize) -> Literal {
    Literal::positive(Variable(var as u32))
}

fn neg(var: usize) -> Literal {
    Literal::negative(Variable(var as u32))
}

// ── Union-Find tests ──

#[test]
fn test_union_find_basic_operations() {
    let mut uf = UnionFind::new(5);

    // Initially, each element is its own root.
    for i in 0..5 {
        assert_eq!(uf.find(i), i);
    }

    // Union {0,1,2} and {3,4}
    assert!(uf.union(0, 1));
    assert!(uf.union(1, 2));
    assert!(uf.union(3, 4));

    // Redundant union returns false.
    assert!(!uf.union(0, 2));

    // Same root for {0,1,2}
    let root_0 = uf.find(0);
    let root_1 = uf.find(1);
    let root_2 = uf.find(2);
    assert_eq!(root_0, root_1);
    assert_eq!(root_1, root_2);

    // Same root for {3,4}
    let root_3 = uf.find(3);
    let root_4 = uf.find(4);
    assert_eq!(root_3, root_4);

    // Different groups
    assert_ne!(root_0, root_3);
}

#[test]
fn test_union_find_path_compression() {
    // Build a long chain: 0 <- 1 <- 2 <- 3 <- ... <- 99
    let mut uf = UnionFind::new(100);
    for i in 0..99 {
        uf.union(i, i + 1);
    }
    // After find(0), path halving should compress the chain.
    let root = uf.find(0);
    // All elements should now have a short path to root.
    for i in 0..100 {
        assert_eq!(uf.find(i), root);
    }
}

#[test]
fn test_union_find_empty() {
    let uf = UnionFind::new(0);
    // Should not panic.
    drop(uf);

    let mut uf = UnionFind::new(1);
    assert_eq!(uf.find(0), 0);
}

// ── Component finding tests ──

#[test]
fn test_single_component_connected() {
    // All variables connected through a chain of clauses.
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), pos(1)],
        vec![pos(1), pos(2)],
        vec![pos(2), pos(3)],
    ];
    let result = find_components(4, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 1);
    assert_eq!(result.component_sizes, vec![4]);
    assert!(!result.beneficial);
}

#[test]
fn test_two_disconnected_components() {
    // {0,1,2} and {3,4,5} are disconnected.
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), pos(1)],
        vec![pos(1), pos(2)],
        vec![pos(3), pos(4)],
        vec![pos(4), pos(5)],
    ];
    let result = find_components(6, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 2);
    assert_eq!(result.component_sizes, vec![3, 3]);
    // Not beneficial because components are too small (< 10).
    assert!(!result.beneficial);
}

#[test]
fn test_three_disconnected_components() {
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), neg(1)],
        vec![neg(2), pos(3)],
        vec![pos(4), pos(5), neg(6)],
    ];
    let result = find_components(7, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 3);
    assert_eq!(result.component_sizes, vec![3, 2, 2]);
    assert!(!result.beneficial);
}

#[test]
fn test_inactive_vars_excluded() {
    // Clause {0,1} and {1,2} and {3,4}, but var 1 is inactive.
    // Without var 1, vars 0 and 2 become isolated singletons.
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), pos(1)],
        vec![pos(1), pos(2)],
        vec![pos(3), pos(4)],
    ];
    let result = find_components(5, clauses.iter().map(Vec::as_slice), |vi| vi != 1);

    // var 0 alone, var 2 alone, {3,4} together = 3 components
    assert_eq!(result.num_components, 3);
    assert_eq!(result.component_sizes, vec![2, 1, 1]);
    assert!(!result.beneficial);
}

#[test]
fn test_empty_formula() {
    let clauses: Vec<Vec<Literal>> = vec![];
    let result = find_components(10, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 0);
    assert_eq!(result.component_sizes, Vec::<usize>::new());
    assert!(!result.beneficial);
}

#[test]
fn test_zero_vars() {
    let clauses: Vec<Vec<Literal>> = vec![];
    let result = find_components(0, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 0);
    assert!(!result.beneficial);
}

#[test]
fn test_unit_clauses_only() {
    // Unit clauses: each variable is its own component.
    let clauses: Vec<Vec<Literal>> = vec![vec![pos(0)], vec![pos(1)], vec![pos(2)], vec![pos(3)]];
    let result = find_components(4, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 4);
    assert_eq!(result.component_sizes, vec![1, 1, 1, 1]);
    assert!(!result.beneficial);
}

#[test]
fn test_negation_connects_same_variable() {
    // Positive and negative literals of the same variable connect to the same component.
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), neg(1)], // connects 0 and 1
        vec![pos(1), pos(2)], // connects 1 and 2
        vec![neg(3), neg(4)], // connects 3 and 4
    ];
    let result = find_components(5, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 2);
    assert_eq!(result.component_sizes, vec![3, 2]);
}

#[test]
fn test_beneficial_large_components() {
    // Two large components: {0..14} and {15..29}
    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    // Component 1: chain 0-1-2-...-14
    for i in 0..14 {
        clauses.push(vec![pos(i), pos(i + 1)]);
    }
    // Component 2: chain 15-16-...-29
    for i in 15..29 {
        clauses.push(vec![pos(i), pos(i + 1)]);
    }
    let result = find_components(30, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 2);
    assert_eq!(result.component_sizes, vec![15, 15]);
    assert!(
        result.beneficial,
        "Two components with 15 vars each should be beneficial"
    );
}

#[test]
fn test_beneficial_requires_two_large_components() {
    // One large component and one small: not beneficial.
    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    for i in 0..19 {
        clauses.push(vec![pos(i), pos(i + 1)]);
    }
    clauses.push(vec![pos(20), pos(21)]);
    let result = find_components(22, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 2);
    assert_eq!(result.component_sizes, vec![20, 2]);
    assert!(
        !result.beneficial,
        "One large + one tiny component is not beneficial"
    );
}

#[test]
fn test_all_vars_inactive_produces_no_components() {
    let clauses: Vec<Vec<Literal>> = vec![vec![pos(0), pos(1)], vec![pos(2), pos(3)]];
    let result = find_components(4, clauses.iter().map(Vec::as_slice), |_| false);

    assert_eq!(result.num_components, 0);
    assert_eq!(result.component_sizes, Vec::<usize>::new());
    assert!(!result.beneficial);
}

// ── Detailed decomposition tests ──

#[test]
fn test_find_components_detailed_two_components() {
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), pos(1)],
        vec![pos(1), pos(2)],
        vec![pos(3), pos(4)],
        vec![pos(4), pos(5)],
    ];
    let (result, decomp) = find_components_detailed(6, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 2);
    assert_eq!(decomp.num_components, 2);

    // Variables 0,1,2 should be in one component, 3,4,5 in another.
    assert_eq!(decomp.var_component[0], decomp.var_component[1]);
    assert_eq!(decomp.var_component[1], decomp.var_component[2]);
    assert_eq!(decomp.var_component[3], decomp.var_component[4]);
    assert_eq!(decomp.var_component[4], decomp.var_component[5]);
    assert_ne!(decomp.var_component[0], decomp.var_component[3]);

    // Verify component variable lists.
    let comp_a = decomp.var_component[0] as usize;
    let comp_b = decomp.var_component[3] as usize;
    assert_eq!(decomp.components[comp_a].len(), 3);
    assert_eq!(decomp.components[comp_b].len(), 3);
}

#[test]
fn test_find_components_detailed_inactive_vars() {
    // Clause {0,1} and {1,2} and {3,4}, but var 1 is inactive.
    let clauses: Vec<Vec<Literal>> = vec![
        vec![pos(0), pos(1)],
        vec![pos(1), pos(2)],
        vec![pos(3), pos(4)],
    ];
    let (result, decomp) =
        find_components_detailed(5, clauses.iter().map(Vec::as_slice), |vi| vi != 1);

    // var 0 alone, var 2 alone, {3,4} together = 3 components
    assert_eq!(result.num_components, 3);
    assert_eq!(decomp.num_components, 3);
    // var 1 should be u32::MAX (inactive).
    assert_eq!(decomp.var_component[1], u32::MAX);
}

#[test]
fn test_find_components_detailed_empty() {
    let clauses: Vec<Vec<Literal>> = vec![];
    let (result, decomp) = find_components_detailed(0, clauses.iter().map(Vec::as_slice), |_| true);

    assert_eq!(result.num_components, 0);
    assert_eq!(decomp.num_components, 0);
    assert!(decomp.components.is_empty());
}
