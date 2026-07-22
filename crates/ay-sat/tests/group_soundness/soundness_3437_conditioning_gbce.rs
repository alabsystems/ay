// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for #3437: GBCE conditioning produces wrong-SAT.
//!
//! Root cause: AY's conditioning engine originally used single-witness
//! reconstruction (push_bce) but GBCE requires multi-literal autarky witnesses
//! as per CaDiCaL condition.cpp lines 787-793. Flipping a single autarky
//! literal can satisfy the removed clause but unsatisfy other clauses.
//!
//! These tests use programmatically generated UNSAT formulas with diverse
//! structure. Conditioning is enabled by default; these formulas verify the
//! solver returns UNSAT correctly through the full solve loop including
//! preprocessing and inprocessing.
//!
//! Formula families:
//! - Tseitin formulas on odd-degree graphs: parity-based UNSAT
//! - Graph 2-coloring on odd cycles: pigeonhole-like constraint propagation
//! - Pigeonhole principle: known-hard UNSAT that generates many conflicts
//! - Planted contradiction: industrial-like random structure with hidden UNSAT

use ay_sat::{parse_dimacs, SatResult, Solver};
use ntest::timeout;

/// Generate a Tseitin formula on a grid graph with odd parity assignment.
///
/// Grid graph: rows × cols vertices, each connected to its neighbors.
/// Edge variables represent XOR constraints at each vertex.
/// When the total parity demand is odd, the formula is UNSAT.
///
/// Grid formulas are harder than cycle formulas because the higher
/// connectivity creates richer clause interaction patterns that stress
/// conditioning's autarky partition refinement.
fn tseitin_grid_dimacs(rows: usize, cols: usize) -> String {
    let num_vertices = rows * cols;
    let vertex = |r: usize, c: usize| -> usize { r * cols + c };

    // Collect edges
    let mut edges = Vec::new();
    for r in 0..rows {
        for c in 0..cols {
            if c + 1 < cols {
                edges.push((vertex(r, c), vertex(r, c + 1)));
            }
            if r + 1 < rows {
                edges.push((vertex(r, c), vertex(r + 1, c)));
            }
        }
    }
    let num_vars = edges.len();

    // Build adjacency: for each vertex, which edge indices touch it
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_vertices];
    for (idx, &(u, v)) in edges.iter().enumerate() {
        adj[u].push(idx);
        adj[v].push(idx);
    }

    // Parity assignment: vertex 0 gets parity 1, all others get 0.
    // Total parity sum = 1 (odd) → UNSAT.
    let mut parity = vec![false; num_vertices];
    parity[0] = true;

    // Encode XOR constraint for each vertex:
    // XOR(edges at vertex) = parity[v]
    // For degree-d vertex with edges e1..ed, expand full XOR into clauses.
    let mut clauses = Vec::new();
    for v in 0..num_vertices {
        let edge_indices = &adj[v];
        let d = edge_indices.len();
        if d == 0 {
            continue;
        }

        // XOR of d variables = target_parity
        // Enumerate all 2^d assignments, keep those with wrong parity → add as blocking clause
        let target = parity[v];
        for mask in 0..(1u64 << d) {
            let bits_set = mask.count_ones() as usize;
            let xor_val = bits_set % 2 == 1;
            if xor_val != target {
                // This assignment violates the constraint → add blocking clause
                let clause: Vec<i32> = (0..d)
                    .map(|bit| {
                        let var = (edge_indices[bit] + 1) as i32;
                        if mask & (1 << bit) != 0 {
                            -var // was set to 1, negate to block
                        } else {
                            var // was set to 0, keep positive to block
                        }
                    })
                    .collect();
                clauses.push(clause);
            }
        }
    }

    format_dimacs(num_vars, &clauses)
}

/// Generate a graph 2-coloring formula on an odd cycle.
///
/// An odd cycle cannot be 2-colored. Each vertex gets a boolean variable
/// (color), and adjacent vertices must differ. For a cycle of odd length,
/// this creates a propagation chain that ultimately contradicts.
///
/// The chain structure creates a long sequence of forced assignments,
/// exercising the solver's unit propagation and conflict analysis deeply.
fn odd_cycle_coloring_dimacs(n: usize) -> String {
    assert!(n >= 3 && n % 2 == 1, "n must be odd and >= 3");
    let num_vars = n;

    // For each edge (i, (i+1)%n): vertices must have different colors.
    // Different colors: NOT(both true) AND NOT(both false)
    //   (¬x_i ∨ ¬x_{j}) ∧ (x_i ∨ x_{j})
    let mut clauses = Vec::new();
    for i in 0..n {
        let j = (i + 1) % n;
        let xi = (i + 1) as i32;
        let xj = (j + 1) as i32;
        clauses.push(vec![-xi, -xj]); // not both true
        clauses.push(vec![xi, xj]); // not both false
    }

    format_dimacs(num_vars, &clauses)
}

/// Generate a Pigeonhole Principle formula: PHP(pigeons, holes).
///
/// Encodes "pigeons pigeons into holes holes, each pigeon in exactly one hole,
/// no two pigeons in the same hole." When pigeons > holes, this is UNSAT.
///
/// PHP is known to be exponentially hard for CDCL solvers, making it ideal
/// for generating many conflicts and triggering inprocessing techniques.
///
/// Variable p_{i,j} = pigeon i is in hole j (1-indexed: var = i*holes + j + 1).
fn pigeonhole_dimacs(pigeons: usize, holes: usize) -> String {
    assert!(pigeons > holes, "need more pigeons than holes for UNSAT");
    let num_vars = pigeons * holes;
    let var = |pigeon: usize, hole: usize| -> i32 { (pigeon * holes + hole + 1) as i32 };

    let mut clauses = Vec::new();

    // At-least-one: each pigeon must be in some hole.
    for i in 0..pigeons {
        let clause: Vec<i32> = (0..holes).map(|j| var(i, j)).collect();
        clauses.push(clause);
    }

    // At-most-one: no two pigeons in the same hole.
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                clauses.push(vec![-var(i1, j), -var(i2, j)]);
            }
        }
    }

    format_dimacs(num_vars, &clauses)
}

/// Generate a random-looking but deterministic UNSAT formula using
/// a planted structure with XOR-based contradiction.
///
/// Creates a satisfiable core (clauses consistent with a fixed assignment),
/// then adds XOR-parity constraints that make a subset of variables
/// unsatisfiable. Unlike the previous version that used contradictory
/// unit clauses {1, -1, 2, -2}, this forces the solver through actual
/// search before discovering the contradiction.
fn planted_contradiction_dimacs(num_vars: usize, clause_ratio: f64, seed: u64) -> String {
    let num_clauses = (num_vars as f64 * clause_ratio) as usize;
    let mut rng = seed;

    let xorshift = |state: &mut u64| -> u64 {
        *state ^= *state << 13;
        *state ^= *state >> 7;
        *state ^= *state << 17;
        *state
    };

    // Fixed assignment: var i is true if i is even
    let assignment: Vec<bool> = (0..num_vars).map(|i| i % 2 == 0).collect();

    let mut clauses = Vec::new();

    // Generate random 3-SAT clauses satisfied by the assignment
    while clauses.len() < num_clauses {
        let v1 = (xorshift(&mut rng) as usize % num_vars) + 1;
        let v2 = (xorshift(&mut rng) as usize % num_vars) + 1;
        let v3 = (xorshift(&mut rng) as usize % num_vars) + 1;
        if v1 == v2 || v2 == v3 || v1 == v3 {
            continue;
        }

        let l1 = if assignment[v1 - 1] {
            v1 as i32
        } else {
            -(v1 as i32)
        };
        let l2 = if assignment[v2 - 1] {
            v2 as i32
        } else {
            -(v2 as i32)
        };
        let l3 = if assignment[v3 - 1] {
            v3 as i32
        } else {
            -(v3 as i32)
        };

        let flip = xorshift(&mut rng) % 4;
        let clause = match flip {
            0 => vec![-l1, l2, l3],
            1 => vec![l1, -l2, l3],
            2 => vec![l1, l2, -l3],
            _ => vec![l1, l2, l3],
        };
        clauses.push(clause);
    }

    // XOR-based contradiction on first 3 variables: x1 XOR x2 XOR x3 = true AND false.
    // XOR(x1, x2, x3) = 1 (odd parity) — 4 clauses:
    clauses.push(vec![1, 2, 3]);
    clauses.push(vec![-1, -2, 3]);
    clauses.push(vec![-1, 2, -3]);
    clauses.push(vec![1, -2, -3]);
    // XOR(x1, x2, x3) = 0 (even parity) — 4 clauses:
    clauses.push(vec![-1, -2, -3]);
    clauses.push(vec![1, 2, -3]);
    clauses.push(vec![1, -2, 3]);
    clauses.push(vec![-1, 2, 3]);

    format_dimacs(num_vars, &clauses)
}

fn format_dimacs(num_vars: usize, clauses: &[Vec<i32>]) -> String {
    let mut dimacs = format!("p cnf {} {}\n", num_vars, clauses.len());
    for clause in clauses {
        for &lit in clause {
            dimacs.push_str(&lit.to_string());
            dimacs.push(' ');
        }
        dimacs.push_str("0\n");
    }
    dimacs
}

fn solve_unsat(dimacs: &str, name: &str) -> Solver {
    let formula = parse_dimacs(dimacs).unwrap_or_else(|e| panic!("failed to parse {name}: {e}"));
    let mut solver = formula.into_solver();

    match solver.solve().into_inner() {
        SatResult::Unsat(_) => {} // Expected
        SatResult::Unknown => panic!("expected UNSAT for {name}, got UNKNOWN"),
        SatResult::Sat(_) => panic!(
            "SOUNDNESS BUG (#3437): {name} returned SAT (known UNSAT). \
             Conditioning GBCE likely re-enabled with single-witness reconstruction."
        ),
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }

    solver
}

/// Test 1: Tseitin formula on 5×4 grid — 31 edge vars, ~100 clauses.
///
/// Grid Tseitin creates dense clause interactions with higher-degree
/// vertices (degree 3-4) that force conditioning's autarky partition refinement
/// across multiple variables simultaneously.
#[test]
#[timeout(30_000)]
fn test_3437_tseitin_grid_5x4_unsat() {
    let dimacs = tseitin_grid_dimacs(5, 4);
    solve_unsat(&dimacs, "Tseitin-Grid-5x4");
}

/// Test 2: Tseitin formula on 7×5 grid — 58 edge vars, ~300 clauses.
///
/// Larger grid increases constraint density and search difficulty.
#[test]
#[timeout(30_000)]
fn test_3437_tseitin_grid_7x5_unsat() {
    let dimacs = tseitin_grid_dimacs(7, 5);
    solve_unsat(&dimacs, "Tseitin-Grid-7x5");
}

/// Test 3: Graph 2-coloring on odd cycle C_101 — 101 vars, 202 clauses.
///
/// The odd-cycle coloring creates a long chain of forced binary decisions.
/// The XOR-like NOT-EQUAL constraints create mixed positive/negative
/// literal patterns that conditioning must handle correctly during
/// autarky partition computation.
#[test]
#[timeout(30_000)]
fn test_3437_odd_cycle_coloring_101_unsat() {
    let dimacs = odd_cycle_coloring_dimacs(101);
    solve_unsat(&dimacs, "OddCycleColoring-101");
}

/// Test 4: Planted contradiction with XOR-based hidden UNSAT — 80 vars, ~340 clauses.
///
/// The satisfiable-looking structure (most clauses consistent with a fixed
/// assignment) creates autarky-rich partitions that conditioning might
/// exploit, while the XOR contradiction ensures UNSAT. Unlike contradictory
/// unit clauses, the XOR contradiction requires actual search to discover.
#[test]
#[timeout(30_000)]
fn test_3437_planted_contradiction_unsat() {
    let dimacs = planted_contradiction_dimacs(80, 4.27, 0xDEAD_BEEF);
    solve_unsat(&dimacs, "planted-contradiction-80-4.27");
}

/// Test 5: Pigeonhole PHP(9,8) — soundness through conditioning-enabled search.
///
/// PHP(9,8) with all default inprocessing (including conditioning). Verifies
/// the solver returns correct UNSAT when conditioning is enabled in the
/// inprocessing schedule.
///
/// Note: the solver may solve PHP(9,8) entirely during preprocessing,
/// in which case conditioning never fires. This is acceptable — the test
/// verifies correctness of the solve path, not that conditioning triggers.
/// The 4 tests above verify conditioning correctness on diverse formula
/// structures; this test ensures no regression on PHP under the full
/// inprocessing pipeline.
#[test]
#[timeout(120_000)]
fn test_3437_pigeonhole_9_8_conditioning_enabled() {
    let dimacs = pigeonhole_dimacs(9, 8);
    solve_unsat(&dimacs, "PHP(9,8)");
}
