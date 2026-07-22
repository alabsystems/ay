// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cnf::Cnf;

fn solve(cnf: &Cnf) -> bool {
    use ay_sat::Solver;
    let mut solver = Solver::new(cnf.num_vars());
    for clause in cnf.clauses() {
        solver.add_clause(clause.clone());
    }
    solver.solve().is_sat()
}

#[test]
fn test_tseitin_satisfiable() {
    // Triangle with even parities everywhere
    let g = Graph::cycle(3);
    let parities = vec![false, false, false];
    let f = tseitin(&g, &parities);
    assert!(solve(&f)); // All edges = false satisfies all XOR = 0
}

#[test]
fn test_tseitin_unsatisfiable() {
    // Triangle with odd parities - sum is 3 (odd), so UNSAT
    let g = Graph::cycle(3);
    let parities = vec![true, true, true];
    let f = tseitin(&g, &parities);
    assert!(!solve(&f));
}

#[test]
fn test_graph_coloring_triangle() {
    let g = Graph::complete(3);

    // 2 colors: UNSAT (K3 needs 3 colors)
    let f2 = graph_coloring(&g, 2);
    assert!(!solve(&f2));

    // 3 colors: SAT
    let f3 = graph_coloring(&g, 3);
    assert!(solve(&f3));
}

#[test]
fn test_graph_coloring_bipartite() {
    // Path graph is bipartite
    let g = Graph::path(4);

    // 2 colors: SAT (bipartite graphs are 2-colorable)
    let f2 = graph_coloring(&g, 2);
    assert!(solve(&f2));
}
