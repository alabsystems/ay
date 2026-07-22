// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #8223: BVE reconstruction soundness.
//!
//! These tests exercise BVE reconstruction on structured UNSAT formulas
//! (graph coloring, pigeonhole) where BVE elimination is heavy and
//! reconstruction must correctly restore eliminated variable assignments.
//!
//! The original bug: AY returned SAT with an invalid model on an UNSAT
//! graph coloring formula (clique_n2_k10). Root causes:
//! 1. Gate-based BVE only pushed gate clauses to reconstruction stack,
//!    missing non-gate clauses (#8223, fixed in c135a1e6c).
//! 2. Stale BVE occurrence lists caused elimination to miss clauses
//!    (#8223, fixed with full occ list rebuild in body.rs).
//! 3. Backward subsumption deletion removed clauses needed for
//!    reconstruction (#8179, deletion disabled in 696785859).
//! 4. Missing reconstruction completeness guard allowing one-sided
//!    witness entries (#8179, guard added in eliminate.rs).

#![allow(clippy::panic)]

use ay_sat::{Literal, SatResult, Solver, Variable};
use ntest::timeout;

/// Generate a graph K_n coloring formula with k colors.
///
/// UNSAT when n > k (pigeonhole argument: complete graph on n vertices
/// requires exactly n colors).
///
/// Variables: x_{v,c} = vertex v gets color c (0-indexed).
/// Variable index: v * k + c.
///
/// Clauses:
/// 1. At-least-one: each vertex has at least one color
/// 2. At-most-one: each vertex has at most one color (pairwise exclusion)
/// 3. Edge: adjacent vertices (all pairs in K_n) have different colors
fn generate_graph_coloring(n: usize, k: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = n * k;
    let var =
        |v: usize, c: usize| -> Literal { Literal::positive(Variable::new((v * k + c) as u32)) };
    let nvar =
        |v: usize, c: usize| -> Literal { Literal::negative(Variable::new((v * k + c) as u32)) };

    let mut clauses = Vec::new();

    // At-least-one: each vertex has at least one color
    for v in 0..n {
        let clause: Vec<Literal> = (0..k).map(|c| var(v, c)).collect();
        clauses.push(clause);
    }

    // At-most-one: each vertex has at most one color
    for v in 0..n {
        for c1 in 0..k {
            for c2 in (c1 + 1)..k {
                clauses.push(vec![nvar(v, c1), nvar(v, c2)]);
            }
        }
    }

    // Edge constraints: adjacent vertices have different colors
    for v1 in 0..n {
        for v2 in (v1 + 1)..n {
            for c in 0..k {
                clauses.push(vec![nvar(v1, c), nvar(v2, c)]);
            }
        }
    }

    (num_vars, clauses)
}

/// Generate a pigeonhole formula: n pigeons into m holes (UNSAT when n > m).
fn generate_php(n: usize, m: usize) -> (usize, Vec<Vec<Literal>>) {
    let num_vars = n * m;
    let var =
        |i: usize, j: usize| -> Literal { Literal::positive(Variable::new((i * m + j) as u32)) };
    let nvar =
        |i: usize, j: usize| -> Literal { Literal::negative(Variable::new((i * m + j) as u32)) };

    let mut clauses = Vec::new();

    // Each pigeon has at least one hole
    for i in 0..n {
        let clause: Vec<Literal> = (0..m).map(|j| var(i, j)).collect();
        clauses.push(clause);
    }

    // No two pigeons in the same hole
    for j in 0..m {
        for i1 in 0..n {
            for i2 in (i1 + 1)..n {
                clauses.push(vec![nvar(i1, j), nvar(i2, j)]);
            }
        }
    }

    (num_vars, clauses)
}

/// Solve with BVE enabled, return the result.
fn solve_with_bve(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

/// Solve with BVE disabled, return the result.
fn solve_without_bve(num_vars: usize, clauses: &[Vec<Literal>]) -> SatResult {
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(false);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    solver.solve().into_inner()
}

/// Core test: verify BVE-enabled solver agrees with BVE-disabled solver
/// and that any SAT model satisfies the original clauses.
fn verify_bve_correctness(
    label: &str,
    num_vars: usize,
    clauses: &[Vec<Literal>],
    expected_unsat: bool,
) {
    let result_bve = solve_with_bve(num_vars, clauses);
    let result_no_bve = solve_without_bve(num_vars, clauses);

    // Check model validity for SAT results
    if let SatResult::Sat(ref model) = result_bve {
        super::common::assert_model_satisfies(clauses, model, &format!("{label} (BVE-on)"));
    }
    if let SatResult::Sat(ref model) = result_no_bve {
        super::common::assert_model_satisfies(clauses, model, &format!("{label} (BVE-off)"));
    }

    // Classify results
    let bve_unsat = result_bve.is_unsat();
    let no_bve_unsat = result_no_bve.is_unsat();

    // Both must agree (allowing Unknown as don't-care)
    if !matches!(result_bve, SatResult::Unknown) && !matches!(result_no_bve, SatResult::Unknown) {
        assert_eq!(
            bve_unsat, no_bve_unsat,
            "{label}: BVE-on={result_bve:?} but BVE-off={result_no_bve:?}"
        );
    }

    // If we know the expected answer, check it
    if expected_unsat {
        assert!(
            bve_unsat || matches!(result_bve, SatResult::Unknown),
            "{label}: expected UNSAT but BVE-on returned {result_bve:?}"
        );
    }
}

// ==========================================================================
// Graph coloring regression tests
// ==========================================================================

/// K_4 with 3 colors: UNSAT (chi(K_4) = 4 > 3).
/// Small formula, exercises basic BVE reconstruction.
#[test]
#[timeout(10_000)]
fn bve_recon_graph_coloring_k4_3colors() {
    let (nv, clauses) = generate_graph_coloring(4, 3);
    verify_bve_correctness("K4_3colors", nv, &clauses, true);
}

/// K_6 with 5 colors: UNSAT. Medium formula with more BVE opportunities.
#[test]
#[timeout(10_000)]
fn bve_recon_graph_coloring_k6_5colors() {
    let (nv, clauses) = generate_graph_coloring(6, 5);
    verify_bve_correctness("K6_5colors", nv, &clauses, true);
}

/// K_8 with 3 colors: UNSAT. More vertices, fewer colors -> many binary
/// clauses from edge constraints that BVE can exploit.
#[test]
#[timeout(10_000)]
fn bve_recon_graph_coloring_k8_3colors() {
    let (nv, clauses) = generate_graph_coloring(8, 3);
    verify_bve_correctness("K8_3colors", nv, &clauses, true);
}

/// K_10 with 2 colors: UNSAT. This is the formula class from the
/// original #8223 bug report (clique_n2_k10).
#[test]
#[timeout(10_000)]
fn bve_recon_graph_coloring_k10_2colors() {
    let (nv, clauses) = generate_graph_coloring(10, 2);
    verify_bve_correctness("K10_2colors", nv, &clauses, true);
}

/// K_15 with 3 colors: UNSAT. Larger formula stressing BVE elimination
/// chains and reconstruction depth.
#[test]
#[timeout(30_000)]
fn bve_recon_graph_coloring_k15_3colors() {
    let (nv, clauses) = generate_graph_coloring(15, 3);
    verify_bve_correctness("K15_3colors", nv, &clauses, true);
}

/// K_20 with 4 colors: UNSAT. Largest graph coloring test -- 80 variables,
/// exercises multi-round BVE with backward subsumption.
#[test]
#[timeout(30_000)]
fn bve_recon_graph_coloring_k20_4colors() {
    let (nv, clauses) = generate_graph_coloring(20, 4);
    verify_bve_correctness("K20_4colors", nv, &clauses, true);
}

// ==========================================================================
// Pigeonhole regression tests
// ==========================================================================

/// PHP(5,4): 5 pigeons, 4 holes. Classic BVE-heavy UNSAT formula.
#[test]
#[timeout(10_000)]
fn bve_recon_php_5_4() {
    let (nv, clauses) = generate_php(5, 4);
    verify_bve_correctness("PHP_5_4", nv, &clauses, true);
}

/// PHP(7,6): 7 pigeons, 6 holes. 42 variables, moderate BVE load.
#[test]
#[timeout(30_000)]
fn bve_recon_php_7_6() {
    let (nv, clauses) = generate_php(7, 6);
    verify_bve_correctness("PHP_7_6", nv, &clauses, true);
}

// ==========================================================================
// SAT formula tests (verify reconstruction doesn't corrupt valid models)
// ==========================================================================

/// K_4 with 4 colors: SAT (chi(K_4) = 4). BVE may eliminate variables,
/// and reconstruction must produce a valid model.
#[test]
#[timeout(10_000)]
fn bve_recon_graph_coloring_k4_4colors_sat() {
    let (nv, clauses) = generate_graph_coloring(4, 4);
    verify_bve_correctness("K4_4colors_SAT", nv, &clauses, false);
}

/// K_5 with 6 colors: SAT (chi(K_5) = 5 < 6). Over-provisioned colors
/// give BVE more elimination opportunities.
#[test]
#[timeout(10_000)]
fn bve_recon_graph_coloring_k5_6colors_sat() {
    let (nv, clauses) = generate_graph_coloring(5, 6);
    verify_bve_correctness("K5_6colors_SAT", nv, &clauses, false);
}
