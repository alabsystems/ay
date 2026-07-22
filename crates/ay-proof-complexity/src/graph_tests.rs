// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_complete_graph() {
    let k4 = Graph::complete(4);
    assert_eq!(k4.num_vertices(), 4);
    assert_eq!(k4.num_edges(), 6); // C(4,2) = 6

    for u in 0..4 {
        for v in 0..4 {
            if u != v {
                assert!(k4.has_edge(u, v));
            }
        }
    }
}

#[test]
fn test_cycle_graph() {
    let c5 = Graph::cycle(5);
    assert_eq!(c5.num_vertices(), 5);
    assert_eq!(c5.num_edges(), 5);

    for i in 0..5 {
        assert!(c5.has_edge(i, (i + 1) % 5));
        assert_eq!(c5.degree(i), 2);
    }
}

#[test]
fn test_path_graph() {
    let p4 = Graph::path(4);
    assert_eq!(p4.num_vertices(), 4);
    assert_eq!(p4.num_edges(), 3);

    assert_eq!(p4.degree(0), 1);
    assert_eq!(p4.degree(1), 2);
    assert_eq!(p4.degree(2), 2);
    assert_eq!(p4.degree(3), 1);
}

#[test]
fn test_grid_graph() {
    let g = Graph::grid(2, 3);
    assert_eq!(g.num_vertices(), 6);
    assert_eq!(g.num_edges(), 7); // 2 horizontal in each row + 3 vertical
}

#[test]
fn test_complete_bipartite() {
    let k23 = Graph::complete_bipartite(2, 3);
    assert_eq!(k23.num_vertices(), 5);
    assert_eq!(k23.num_edges(), 6);

    // Check that partition 1 (0,1) connects to partition 2 (2,3,4)
    assert!(k23.has_edge(0, 2));
    assert!(k23.has_edge(0, 3));
    assert!(k23.has_edge(0, 4));
    assert!(k23.has_edge(1, 2));

    // No edges within partitions
    assert!(!k23.has_edge(0, 1));
    assert!(!k23.has_edge(2, 3));
}
