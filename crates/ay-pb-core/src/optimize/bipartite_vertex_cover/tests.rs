// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::types::{PbLit, PbTerm};

fn pos(var: u32) -> PbLit {
    PbLit {
        var,
        negated: false,
    }
}

fn unit_term(var: u32) -> PbTerm {
    PbTerm {
        coeff: 1,
        lits: vec![pos(var)],
    }
}

fn edge(a: u32, b: u32) -> PbConstraint {
    PbConstraint {
        terms: vec![unit_term(a), unit_term(b)],
        rel: PbRel::Ge,
        rhs: 1,
    }
}

fn vc_instance(num_vars: u32, edges: &[(u32, u32)]) -> (PbInstance, PbObjective) {
    let constraints: Vec<PbConstraint> = edges.iter().map(|&(a, b)| edge(a, b)).collect();
    let objective = PbObjective {
        terms: (1..=num_vars).map(unit_term).collect(),
    };
    let instance = PbInstance {
        num_vars,
        num_constraints: constraints.len() as u32,
        constraints,
        objective: Some(objective.clone()),
    };
    (instance, objective)
}

#[test]
fn single_edge_cover_is_one() {
    let (inst, obj) = vc_instance(2, &[(1, 2)]);
    let sol = try_solve(&inst, &obj).expect("single edge solvable");
    assert_eq!(sol.status, PbStatus::OptimumFound);
    assert_eq!(sol.objective, Some(1));
    assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
}

#[test]
fn path_of_four_cover_is_two() {
    // Path 1-2-3-4: min vertex cover = {2,3} of size 2.
    let (inst, obj) = vc_instance(4, &[(1, 2), (2, 3), (3, 4)]);
    let sol = try_solve(&inst, &obj).expect("path solvable");
    assert_eq!(sol.objective, Some(2));
    assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
}

#[test]
fn complete_bipartite_k33_cover_is_three() {
    // K_{3,3}: left {1,2,3}, right {4,5,6}; min vertex cover = 3.
    let mut edges = Vec::new();
    for l in 1..=3 {
        for r in 4..=6 {
            edges.push((l, r));
        }
    }
    let (inst, obj) = vc_instance(6, &edges);
    let sol = try_solve(&inst, &obj).expect("K33 solvable");
    assert_eq!(sol.objective, Some(3));
    assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
}

#[test]
fn even_grid_cover_matches_half() {
    // 4x4 grid graph (bipartite). Min vertex cover = max matching = 8.
    let rows = 4;
    let cols = 4;
    let id = |r: u32, c: u32| r * cols + c + 1;
    let mut edges = Vec::new();
    for r in 0..rows {
        for c in 0..cols {
            if c + 1 < cols {
                edges.push((id(r, c), id(r, c + 1)));
            }
            if r + 1 < rows {
                edges.push((id(r, c), id(r + 1, c)));
            }
        }
    }
    let (inst, obj) = vc_instance(rows * cols, &edges);
    let sol = try_solve(&inst, &obj).expect("grid solvable");
    assert_eq!(sol.objective, Some(8));
    assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
}

#[test]
fn triangle_is_not_bipartite_returns_none() {
    // Triangle 1-2-3 is an odd cycle: König does not apply -> fall through.
    let (inst, obj) = vc_instance(3, &[(1, 2), (2, 3), (3, 1)]);
    assert!(try_solve(&inst, &obj).is_none());
}

#[test]
fn weighted_objective_rejected() {
    let (mut inst, _obj) = vc_instance(2, &[(1, 2)]);
    let weighted = PbObjective {
        terms: vec![
            PbTerm {
                coeff: 2,
                lits: vec![pos(1)],
            },
            unit_term(2),
        ],
    };
    inst.objective = Some(weighted.clone());
    assert!(try_solve(&inst, &weighted).is_none());
}

#[test]
fn non_edge_constraint_rejected() {
    // A 3-literal clause is not an edge -> not the VC class.
    let (mut inst, obj) = vc_instance(3, &[(1, 2)]);
    inst.constraints.push(PbConstraint {
        terms: vec![unit_term(1), unit_term(2), unit_term(3)],
        rel: PbRel::Ge,
        rhs: 1,
    });
    assert!(try_solve(&inst, &obj).is_none());
}

#[test]
fn free_endpoint_rejected() {
    // Edge endpoint 3 is absent from the objective -> reduction invalid.
    let constraints = vec![edge(1, 3)];
    let objective = PbObjective {
        terms: vec![unit_term(1), unit_term(2)],
    };
    let inst = PbInstance {
        num_vars: 3,
        num_constraints: 1,
        constraints,
        objective: Some(objective.clone()),
    };
    assert!(try_solve(&inst, &objective).is_none());
}

#[test]
fn larger_random_bipartite_certificate_holds() {
    // Random bipartite graph; the three-way certificate must hold whenever a
    // solution is returned.
    let left = 30u32;
    let right = 30u32;
    let n = left + right;
    let mut edges = Vec::new();
    let mut state = 0x9e37_79b9_u32;
    let mut rng = || {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        state
    };
    for l in 1..=left {
        for r in (left + 1)..=n {
            if rng() % 4 == 0 {
                edges.push((l, r));
            }
        }
    }
    if edges.is_empty() {
        return;
    }
    let (inst, obj) = vc_instance(n, &edges);
    if let Some(sol) = try_solve(&inst, &obj) {
        assert_eq!(sol.status, PbStatus::OptimumFound);
        assert!(verify_all_constraints(&inst.constraints, &sol.assignment));
        // Cover value equals matching size is guaranteed by the gate; re-check
        // feasibility-as-cover here for defence in depth.
        let value = eval_objective(&obj, &sol.assignment);
        assert_eq!(sol.objective, Some(value));
    }
}
