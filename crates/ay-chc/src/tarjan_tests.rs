// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn empty_graph() {
    let result = tarjan_scc_dense(0, |_| Vec::new());
    assert!(result.is_empty());
}

#[test]
fn single_node_no_self_loop() {
    let result = tarjan_scc_dense(1, |_| Vec::new());
    assert_eq!(result.len(), 1);
    assert_eq!(result[0], vec![0]);
}

#[test]
fn single_node_self_loop() {
    let result = tarjan_scc_dense(1, |_| vec![0]);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0], vec![0]);
}

#[test]
fn two_node_cycle() {
    let adj: &[&[usize]] = &[&[1], &[0]];
    let result = tarjan_scc_dense(2, |v| adj[v].to_vec());
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].len(), 2);
}

#[test]
fn two_node_chain() {
    let adj: &[&[usize]] = &[&[1], &[]];
    let result = tarjan_scc_dense(2, |v| adj[v].to_vec());
    assert_eq!(result.len(), 2);
    // Reverse topological: node 1 (leaf) first, then node 0
    assert_eq!(result[0], vec![1]);
    assert_eq!(result[1], vec![0]);
}

#[test]
fn diamond_with_cycle() {
    // 0 -> 1, 0 -> 2, 1 -> 3, 2 -> 3, 3 -> 0
    let adj: &[&[usize]] = &[&[1, 2], &[3], &[3], &[0]];
    let result = tarjan_scc_dense(4, |v| adj[v].to_vec());
    // All nodes in one SCC due to 3->0 back edge
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].len(), 4);
}
