// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Graph-based hard formula generators for proof complexity analysis.
//!
//! - Tseitin formulas (XOR constraints on a graph)
//! - Graph coloring
//! - Clique-coloring

use crate::cnf::{add_xor_equals_clauses, xor_clause_count, Cnf};
use crate::graph::Graph;
use crate::{Lit, Var};
use ay_core::kani_compat::DetHashMap as HashMap;

/// Generate Tseitin formula on a graph with given parities.
///
/// For each edge (u, v), we introduce a variable x_{u,v}.
/// For each vertex `v` with incident edges e_1, ..., e_k,
/// we add constraints encoding that XOR of x_{e_1}, ..., x_{e_k} = `parity[v]`.
///
/// This is satisfiable iff the sum of parities is 0 (mod 2).
///
/// **Proof complexity:**
/// - Tree Resolution: exponential (due to XOR width)
/// - General Resolution: polynomial with extension variables
///
/// # Arguments
/// * `graph` - The underlying graph
/// * `parities` - Parity constraint for each vertex (vertex i has odd degree iff `parities[i]`)
///
/// # Example
/// ```
/// use ay_proof_complexity::{tseitin, Graph};
///
/// // Triangle graph
/// let g = Graph::complete(3);
/// let parities = vec![true, true, true];  // Odd parity at each vertex
/// let formula = tseitin(&g, &parities);
/// // UNSAT: sum of parities is odd (3 mod 2 = 1)
/// ```
pub fn tseitin(graph: &Graph, parities: &[bool]) -> Cnf {
    let n = graph.num_vertices();
    assert_eq!(parities.len(), n, "Need parity for each vertex");

    let edges: Vec<(usize, usize)> = graph.edges().collect();
    let num_edge_vars = edges.len();

    if num_edge_vars == 0 {
        // No edges: check if all parities are false
        if parities.iter().any(|&p| p) {
            // Unsatisfiable: some vertex has odd constraint but no edges
            let mut cnf = Cnf::new_with_capacity(1, 1);
            cnf.add_clause(&[]); // empty clause = UNSAT
            return cnf;
        } else {
            // Satisfiable: all parities are 0, trivially true
            return Cnf::new_with_capacity(0, 0);
        }
    }

    // Map edge to variable index
    let mut edge_to_var = HashMap::default();
    for (idx, &(u, v)) in edges.iter().enumerate() {
        edge_to_var.insert((u.min(v), u.max(v)), Var::new(idx as u32));
    }

    let get_edge_var = |u: usize, v: usize| -> Var { edge_to_var[&(u.min(v), u.max(v))] };

    // Estimate clause count (each vertex with k neighbors contributes 2^{k-1} clauses)
    let mut total_clauses = 0;
    for (v, &parity) in parities.iter().enumerate() {
        total_clauses += xor_clause_count(graph.degree(v), parity);
    }

    let mut cnf = Cnf::new_with_capacity(num_edge_vars as u32, total_clauses);

    // For each vertex, add XOR constraint
    for (v, &parity) in parities.iter().enumerate() {
        let edge_vars: Vec<Var> = graph.neighbors(v).map(|u| get_edge_var(v, u)).collect();
        add_xor_equals_clauses(&edge_vars, parity, &mut cnf);
    }

    cnf
}

/// Generate the graph coloring formula.
///
/// Variables: c_{v,k} means vertex v has color k.
/// - Each vertex has at least one color
/// - Adjacent vertices have different colors
///
/// # Arguments
/// * `graph` - The graph to color
/// * `k` - Number of colors
///
/// Returns SAT iff graph is k-colorable.
pub fn graph_coloring(graph: &Graph, k: usize) -> Cnf {
    let n = graph.num_vertices();
    if n == 0 || k == 0 {
        let mut cnf = Cnf::new_with_capacity(0, usize::from(k == 0 && n > 0));
        if k == 0 && n > 0 {
            cnf.add_clause(&[]); // UNSAT: can't color with 0 colors
        }
        return cnf;
    }

    // Variable c_{v,c} -> v * k + c
    let var = |vertex: usize, color: usize| -> Var { Var::new((vertex * k + color) as u32) };

    let edges: Vec<_> = graph.edges().collect();
    let clause_count = n + edges.len() * k;
    let mut cnf = Cnf::new_with_capacity((n * k) as u32, clause_count);

    // At-least-one: each vertex has some color
    for v in 0..n {
        let clause: Vec<Lit> = (0..k).map(|c| Lit::positive(var(v, c))).collect();
        cnf.add_clause(&clause);
    }

    // Different colors for adjacent vertices
    for (u, v) in edges {
        for c in 0..k {
            cnf.add_clause(&[Lit::negative(var(u, c)), Lit::negative(var(v, c))]);
        }
    }

    cnf
}

/// Generate the clique-coloring formula.
///
/// Encodes: G has a k-clique AND the complement of G is k-colorable.
/// This is a classic NP-hard problem used in proof complexity.
///
/// # Arguments
/// * `graph` - The graph
/// * `k` - Size of clique / number of colors
pub fn clique_coloring(graph: &Graph, k: usize) -> Cnf {
    let n = graph.num_vertices();
    if n == 0 || k == 0 {
        return Cnf::new_with_capacity(0, 0);
    }

    // Variables:
    // Clique: clique_{v,i} means vertex v is the i-th element of the clique
    // Color: color_{v,c} means vertex v has color c
    let clique_var = |v: usize, i: usize| -> Var { Var::new((v * k + i) as u32) };
    let color_var = |v: usize, c: usize| -> Var { Var::new((n * k + v * k + c) as u32) };

    let mut cnf = Cnf::new_with_capacity((2 * n * k) as u32, 0);

    // CLIQUE PART
    // Each position i in the clique is filled by some vertex
    for i in 0..k {
        let clause: Vec<Lit> = (0..n).map(|v| Lit::positive(clique_var(v, i))).collect();
        cnf.add_clause(&clause);
    }

    // Each vertex fills at most one position
    for v in 0..n {
        for i in 0..k {
            for j in (i + 1)..k {
                cnf.add_clause(&[
                    Lit::negative(clique_var(v, i)),
                    Lit::negative(clique_var(v, j)),
                ]);
            }
        }
    }

    // Clique constraint: if u is position i and v is position j, then u and v must be adjacent
    for i in 0..k {
        for j in (i + 1)..k {
            for u in 0..n {
                for v in 0..n {
                    if u != v && !graph.has_edge(u, v) {
                        cnf.add_clause(&[
                            Lit::negative(clique_var(u, i)),
                            Lit::negative(clique_var(v, j)),
                        ]);
                    }
                }
            }
        }
    }

    // COLORING PART (complement graph)
    // Each vertex has some color
    for v in 0..n {
        let clause: Vec<Lit> = (0..k).map(|c| Lit::positive(color_var(v, c))).collect();
        cnf.add_clause(&clause);
    }

    // Non-adjacent vertices (edges in complement) must have different colors
    for u in 0..n {
        for v in (u + 1)..n {
            if !graph.has_edge(u, v) {
                for c in 0..k {
                    cnf.add_clause(&[
                        Lit::negative(color_var(u, c)),
                        Lit::negative(color_var(v, c)),
                    ]);
                }
            }
        }
    }

    cnf
}

#[cfg(test)]
#[path = "graph_formulas_tests.rs"]
mod tests;
