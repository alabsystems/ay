// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end tests for the ladder-collapse pre-pass (`adv_gc` family shape):
//! shuffled sequential at-most-one ladders must collapse into their pairwise
//! closure, the orbitope route must then verify the restored row symmetry,
//! and SAT models must round-trip through reconstruction onto the ORIGINAL
//! ladder clauses. The recognizer's strictness unit tests live next to the
//! recognizer in `config_preprocess_symmetry/ladder_collapse.rs`.

use super::*;

/// A `colours`-colouring CNF where each vertex's at-most-one constraint is a
/// Sinz sequential ladder over a vertex-specific shuffled colour order —
/// the `adv_gc` encoding in miniature.
///
/// Base var `x(v, c) = colours*v + c`; register `s(v, i)` follows after all
/// base vars. Returns `(num_vars, clauses)`.
fn shuffled_ladder_colouring(
    n: usize,
    colours: usize,
    edges: &[(usize, usize)],
    orders: &[Vec<usize>],
) -> (usize, Vec<Vec<Literal>>) {
    assert_eq!(orders.len(), n);
    let x = |v: usize, c: usize| Variable((colours * v + c) as u32);
    let s = |v: usize, i: usize| Variable((colours * n + (colours - 1) * v + i) as u32);
    let num_vars = colours * n + (colours - 1) * n;
    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    for v in 0..n {
        // At-least-one colour.
        clauses.push((0..colours).map(|c| Literal::positive(x(v, c))).collect());
        // Shuffled sequential AMO ladder.
        let sigma = &orders[v];
        assert_eq!(sigma.len(), colours);
        clauses.push(vec![
            Literal::negative(x(v, sigma[0])),
            Literal::positive(s(v, 0)),
        ]);
        for i in 1..colours - 1 {
            clauses.push(vec![
                Literal::negative(x(v, sigma[i])),
                Literal::positive(s(v, i)),
            ]);
            clauses.push(vec![
                Literal::negative(s(v, i - 1)),
                Literal::positive(s(v, i)),
            ]);
            clauses.push(vec![
                Literal::negative(x(v, sigma[i])),
                Literal::negative(s(v, i - 1)),
            ]);
        }
        clauses.push(vec![
            Literal::negative(x(v, sigma[colours - 1])),
            Literal::negative(s(v, colours - 2)),
        ]);
    }
    for &(u, v) in edges {
        for c in 0..colours {
            clauses.push(vec![Literal::negative(x(u, c)), Literal::negative(x(v, c))]);
        }
    }
    (num_vars, clauses)
}

fn model_satisfies(model: &[bool], clauses: &[Vec<Literal>]) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|l| {
            let vi = l.variable().index();
            vi < model.len() && model[vi] == l.is_positive()
        })
    })
}

/// Triangle, 3 colours, a different σ per vertex. The ladders must collapse
/// (9 derived binaries, 15 ladder clauses gone, 6 registers retired), and the
/// orbitope route — which the shuffled ladders previously blinded — must then
/// verify all three colour rows and emit its fixing units.
#[test]
fn ladders_collapse_and_the_orbitope_route_fires() {
    let edges = [(0, 1), (0, 2), (1, 2)];
    let orders = vec![vec![0, 1, 2], vec![2, 0, 1], vec![1, 2, 0]];
    let (num_vars, clauses) = shuffled_ladder_colouring(3, 3, &edges, &orders);
    let mut solver = Solver::new(num_vars);
    solver.set_symmetry_oneshot(true);
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    let before = solver.arena.active_clause_count();

    let (unsat, changed) = solver.preprocess_symmetry();
    assert!(!unsat);
    assert!(changed, "collapse plus orbitope must change the formula");

    // Route telemetry: the collapse fired on all three ladders and the
    // orbitope route found the matrix it used to miss.
    let route = |name: &str| -> String {
        solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .find(|(r, _)| *r == name)
            .unwrap_or_else(|| panic!("route {name} not recorded"))
            .1
            .clone()
    };
    assert_eq!(
        route("ladder-collapse"),
        "3 of 3 ladders collapsed: +9 binaries, -15 ladder clauses, 6 registers retired"
    );
    assert!(
        route("orbitope").starts_with("added "),
        "orbitope must fire on the collapsed formula, got: {}",
        route("orbitope"),
    );

    // All 9 pairwise binaries are present (3 vertices x C(3,2) colour pairs).
    let active: Vec<Vec<Literal>> = solver
        .arena
        .active_indices()
        .filter(|&idx| !solver.arena.is_learned(idx))
        .map(|idx| {
            let mut lits = solver.arena.literals(idx).to_vec();
            lits.sort_unstable_by_key(|l| l.raw());
            lits
        })
        .collect();
    let mut derived = 0usize;
    for v in 0..3usize {
        for c in 0..3usize {
            for d in (c + 1)..3 {
                let mut expected = vec![
                    Literal::negative(Variable((3 * v + c) as u32)),
                    Literal::negative(Variable((3 * v + d) as u32)),
                ];
                expected.sort_unstable_by_key(|l| l.raw());
                assert!(
                    active.contains(&expected),
                    "missing derived binary for vertex {v}, colours {c}/{d}"
                );
                derived += 1;
            }
        }
    }
    assert_eq!(derived, 9);

    // Ladder clauses are gone: original count - 15 deleted + 9 binaries + the
    // orbitope fixing units (3 for a 3x3 matrix with no synthesized AMO).
    assert_eq!(solver.arena.active_clause_count(), before - 15 + 9 + 3);

    // Registers are retired from search.
    for v in 0..3usize {
        for i in 0..2usize {
            let s = 9 + 2 * v + i;
            assert!(
                solver.var_lifecycle.is_removed(s),
                "register var {s} must be eliminated"
            );
        }
    }
}

/// The pre-collapse formula is exactly the shape the orbitope detector
/// rejects: the ladder clauses break every colour swap, so the verified row
/// prefix stays below the fixing minimum. This pins the motivating bug.
#[test]
fn shuffled_ladders_blind_the_row_swap_gate_without_the_collapse() {
    use crate::symmetry::orbitope::{detect_row_amo_matrices, OrbitopeLimits};
    let edges = [(0, 1), (0, 2), (1, 2)];
    let orders = vec![vec![0, 1, 2], vec![2, 0, 1], vec![1, 2, 0]];
    let (_, clauses) = shuffled_ladder_colouring(3, 3, &edges, &orders);
    let mut sorted: Vec<Vec<Literal>> = clauses;
    for c in &mut sorted {
        c.sort_unstable_by_key(|l| l.raw());
    }
    let (matrices, _) = detect_row_amo_matrices(&sorted, OrbitopeLimits::default());
    assert!(
        matrices.is_empty() || matrices[0].verified_rows < 3,
        "shuffled ladders must not verify as fully row-interchangeable \
         without the collapse"
    );
}

/// A register with an occurrence outside its ladder must block the collapse
/// of THAT ladder only — the census is the soundness boundary.
#[test]
fn outside_register_occurrence_blocks_that_ladder() {
    let edges = [(0, 1)];
    let orders = vec![vec![1, 0, 2], vec![2, 1, 0]];
    let (num_vars, mut clauses) = shuffled_ladder_colouring(2, 3, &edges, &orders);
    // Vertex 0's first register is var 6 (= 3*2 + 0). Give it an outside
    // occurrence via a fresh variable.
    clauses.push(vec![
        Literal::negative(Variable(6)),
        Literal::positive(Variable(num_vars as u32)),
    ]);
    let mut solver = Solver::new(num_vars + 1);
    solver.set_symmetry_oneshot(true);
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    let (unsat, _) = solver.preprocess_symmetry();
    assert!(!unsat);
    let outcome = solver
        .cold
        .symmetry_stats
        .routes
        .iter()
        .find(|(r, _)| *r == "ladder-collapse")
        .map(|(_, o)| o.clone());
    assert_eq!(
        outcome.as_deref(),
        Some("1 of 1 ladders collapsed: +3 binaries, -5 ladder clauses, 2 registers retired"),
        "only vertex 1's untainted ladder may collapse"
    );
    assert!(
        !solver.var_lifecycle.is_removed(6),
        "the tainted register must stay active"
    );
    assert!(!solver.var_lifecycle.is_removed(7));
    // Vertex 1's registers: s(v, i) = 6 + 2*v + i.
    assert!(solver.var_lifecycle.is_removed(8));
    assert!(solver.var_lifecycle.is_removed(9));
}

/// SAT round trip: solve a colourable instance end to end and check the model
/// against the ORIGINAL clauses, ladders included. This exercises the
/// reconstruction stack entries (the registers are retired from search, so
/// their reported values exist ONLY through reconstruction).
#[test]
fn sat_ladder_instance_round_trips_through_reconstruction() {
    // A 4-path with 3 colours: plenty of models, orbitope fixing units and
    // ladder reconstruction both in play.
    let edges = [(0, 1), (1, 2), (2, 3)];
    let orders = vec![vec![0, 1, 2], vec![2, 0, 1], vec![1, 2, 0], vec![2, 1, 0]];
    let (num_vars, clauses) = shuffled_ladder_colouring(4, 3, &edges, &orders);
    let mut solver = Solver::new(num_vars);
    solver.set_symmetry_oneshot(true);
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    let result = solver.solve().into_inner();
    let SatResult::Sat(model) = result else {
        panic!("expected SAT, got {result:?}");
    };
    // The collapse must actually have fired, otherwise this test is vacuous.
    assert!(
        solver
            .cold
            .symmetry_stats
            .routes
            .iter()
            .any(|(r, o)| *r == "ladder-collapse" && o.starts_with("4 of 4")),
        "ladder collapse must fire during solve(); routes: {:?}",
        solver.cold.symmetry_stats.routes,
    );
    assert!(model.len() >= num_vars);
    assert!(
        model_satisfies(&model, &clauses),
        "reconstructed model must satisfy the ORIGINAL clauses, ladders included"
    );
}

/// Same round trip on an UNSAT instance (K4 with 3 colours): the collapse
/// must not manufacture satisfiability.
#[test]
fn unsat_ladder_instance_stays_unsat() {
    let edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];
    let orders = vec![vec![0, 1, 2], vec![2, 0, 1], vec![1, 2, 0], vec![2, 1, 0]];
    let (num_vars, clauses) = shuffled_ladder_colouring(4, 3, &edges, &orders);
    let mut solver = Solver::new(num_vars);
    solver.set_symmetry_oneshot(true);
    for clause in &clauses {
        assert!(solver.add_clause(clause.clone()));
    }
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Unsat(_)),
        "K4 is not 3-colourable, got {result:?}"
    );
}
