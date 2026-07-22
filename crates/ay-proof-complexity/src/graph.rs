// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Simple graph representation for proof complexity formulas.

/// An undirected graph represented as adjacency lists.
#[derive(Debug, Clone)]
pub struct Graph {
    /// Adjacency lists for each vertex
    adj: Vec<Vec<usize>>,
}

impl Graph {
    /// Create an empty graph with n vertices and no edges.
    pub fn new(n: usize) -> Self {
        Self {
            adj: vec![Vec::new(); n],
        }
    }

    /// Number of vertices.
    pub fn num_vertices(&self) -> usize {
        self.adj.len()
    }

    /// Number of edges.
    pub fn num_edges(&self) -> usize {
        self.adj.iter().map(Vec::len).sum::<usize>() / 2
    }

    /// Add an edge between u and v.
    pub fn add_edge(&mut self, u: usize, v: usize) {
        assert!(
            u < self.adj.len() && v < self.adj.len(),
            "Vertex out of bounds"
        );
        if u != v && !self.has_edge(u, v) {
            self.adj[u].push(v);
            self.adj[v].push(u);
        }
    }

    /// Check if there is an edge between u and v.
    pub fn has_edge(&self, u: usize, v: usize) -> bool {
        u < self.adj.len() && v < self.adj.len() && self.adj[u].contains(&v)
    }

    /// Degree of vertex v.
    pub fn degree(&self, v: usize) -> usize {
        self.adj[v].len()
    }

    /// Neighbors of vertex v.
    pub fn neighbors(&self, v: usize) -> impl Iterator<Item = usize> + '_ {
        self.adj[v].iter().copied()
    }

    /// Iterate over all edges (u, v) with u < v.
    pub fn edges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        (0..self.adj.len()).flat_map(move |u| {
            self.adj[u]
                .iter()
                .copied()
                .filter(move |&v| u < v)
                .map(move |v| (u, v))
        })
    }

    /// Create a complete graph K_n.
    pub fn complete(n: usize) -> Self {
        let mut g = Self::new(n);
        for u in 0..n {
            for v in (u + 1)..n {
                g.add_edge(u, v);
            }
        }
        g
    }

    /// Create a cycle graph C_n.
    pub fn cycle(n: usize) -> Self {
        if n < 3 {
            return Self::new(n);
        }
        let mut g = Self::new(n);
        for i in 0..n {
            g.add_edge(i, (i + 1) % n);
        }
        g
    }

    /// Create a path graph P_n.
    pub fn path(n: usize) -> Self {
        if n < 2 {
            return Self::new(n);
        }
        let mut g = Self::new(n);
        for i in 0..(n - 1) {
            g.add_edge(i, i + 1);
        }
        g
    }

    /// Create a grid graph of size rows x cols.
    pub fn grid(rows: usize, cols: usize) -> Self {
        let n = rows * cols;
        let mut g = Self::new(n);
        for r in 0..rows {
            for c in 0..cols {
                let v = r * cols + c;
                if c + 1 < cols {
                    g.add_edge(v, v + 1);
                }
                if r + 1 < rows {
                    g.add_edge(v, v + cols);
                }
            }
        }
        g
    }

    /// Create a random Erdos-Renyi graph G(n, p).
    pub fn random(n: usize, p: f64, seed: u64) -> Self {
        use rand::prelude::*;
        use rand_chacha::ChaCha8Rng;

        let mut g = Self::new(n);
        let mut rng = ChaCha8Rng::seed_from_u64(seed);

        for u in 0..n {
            for v in (u + 1)..n {
                if rng.gen_bool(p) {
                    g.add_edge(u, v);
                }
            }
        }
        g
    }

    /// Create a bipartite graph with given sizes and edges between partitions.
    pub fn complete_bipartite(n1: usize, n2: usize) -> Self {
        let n = n1 + n2;
        let mut g = Self::new(n);
        for u in 0..n1 {
            for v in n1..(n1 + n2) {
                g.add_edge(u, v);
            }
        }
        g
    }
}

#[cfg(test)]
#[path = "graph_tests.rs"]
mod tests;
