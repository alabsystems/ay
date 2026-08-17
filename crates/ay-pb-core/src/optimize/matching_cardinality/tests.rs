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
fn unit(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![pos(var)],
    }
}
fn edge(a: u32, b: u32) -> PbConstraint {
    PbConstraint {
        terms: vec![unit(1, a), unit(1, b)],
        rel: PbRel::Ge,
        rhs: 1,
    }
}
/// `sum_{v in 1..=n} x_v <= k`  ==  `-1 x_1 ... -1 x_n >= -k`.
fn card(n: u32, k: i128) -> PbConstraint {
    PbConstraint {
        terms: (1..=n).map(|v| unit(-1, v)).collect(),
        rel: PbRel::Ge,
        rhs: -k,
    }
}

/// A bipartite grid graph (r x c) as edge constraints; `id(i,j)=i*c+j+1`.
fn grid_edges(rows: u32, cols: u32) -> Vec<PbConstraint> {
    let id = |r: u32, cc: u32| r * cols + cc + 1;
    let mut es = Vec::new();
    for r in 0..rows {
        for cc in 0..cols {
            if cc + 1 < cols {
                es.push(edge(id(r, cc), id(r, cc + 1)));
            }
            if r + 1 < rows {
                es.push(edge(id(r, cc), id(r + 1, cc)));
            }
        }
    }
    es
}

#[test]
fn matching_exceeds_budget_certifies_unsat() {
    // 4x4 grid: max matching = 8. Ask for a cover of size <= 7 -> UNSAT.
    let mut cs = grid_edges(4, 4);
    cs.push(card(16, 7));
    let r = matching_cardinality_refutation(&cs).expect("m=8 > k=7 must refute");
    assert_eq!(r.check(), Ok(()));
    assert!(matching_cardinality_unsat_cp_checked(&cs));
}

#[test]
fn single_edge_budget_zero_is_unsat() {
    // One edge {1,2}: matching = 1, budget 0 -> UNSAT (must cover the edge).
    let cs = vec![edge(1, 2), card(2, 0)];
    let r = matching_cardinality_refutation(&cs).expect("m=1 > k=0 refutes");
    // Final derived constraint must be the contradiction 0 >= 1.
    assert_eq!(r.check(), Ok(()));
}

#[test]
fn budget_at_least_matching_is_not_refuted() {
    // 4x4 grid, budget 8 == max matching == min cover: SAT, must NOT refute.
    let mut cs = grid_edges(4, 4);
    cs.push(card(16, 8));
    assert!(matching_cardinality_refutation(&cs).is_none());
    assert!(!matching_cardinality_unsat_cp_checked(&cs));
}

#[test]
fn generous_budget_not_refuted() {
    let mut cs = grid_edges(4, 4);
    cs.push(card(16, 12));
    assert!(matching_cardinality_refutation(&cs).is_none());
}

#[test]
fn odd_cycle_is_declined_even_when_truly_unsat() {
    // Triangle 1-2-3: min vertex cover = 2. Budget 1 IS unsatisfiable, but the
    // graph is non-bipartite so this König/matching path must DECLINE (the
    // matching lower bound is only 1, which does not exceed k=1). No false
    // UNSAT — the general engine handles it.
    let cs = vec![edge(1, 2), edge(2, 3), edge(3, 1), card(3, 1)];
    assert!(matching_cardinality_refutation(&cs).is_none());
    assert!(!matching_cardinality_unsat_cp_checked(&cs));
}

#[test]
fn missing_cardinality_row_declined() {
    let cs = grid_edges(3, 3); // edges only, no budget row
    assert!(matching_cardinality_refutation(&cs).is_none());
}

#[test]
fn two_cardinality_rows_declined() {
    let mut cs = grid_edges(3, 3);
    cs.push(card(9, 3));
    cs.push(card(9, 4));
    assert!(matching_cardinality_refutation(&cs).is_none());
}

#[test]
fn non_edge_row_declined() {
    // A 3-literal clause is not an edge -> not the class.
    let mut cs = vec![edge(1, 2)];
    cs.push(PbConstraint {
        terms: vec![unit(1, 1), unit(1, 2), unit(1, 3)],
        rel: PbRel::Ge,
        rhs: 1,
    });
    cs.push(card(3, 0));
    assert!(matching_cardinality_refutation(&cs).is_none());
}

#[test]
fn complete_bipartite_k33_budget_two_unsat() {
    // K_{3,3}: max matching = 3, min cover = 3. Budget 2 -> UNSAT.
    let mut cs = Vec::new();
    for l in 1..=3 {
        for r in 4..=6 {
            cs.push(edge(l, r));
        }
    }
    cs.push(card(6, 2));
    let r = matching_cardinality_refutation(&cs).expect("K33 m=3 > k=2 refutes");
    assert_eq!(r.check(), Ok(()));
}

#[test]
fn k33_budget_three_is_sat_not_refuted() {
    let mut cs = Vec::new();
    for l in 1..=3 {
        for r in 4..=6 {
            cs.push(edge(l, r));
        }
    }
    cs.push(card(6, 3));
    assert!(matching_cardinality_refutation(&cs).is_none());
}
