// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn solve(cnf: &Cnf) -> bool {
    use ay_sat::Solver;
    let mut solver = Solver::new(cnf.num_vars());
    for clause in cnf.clauses() {
        solver.add_clause(clause.clone());
    }
    solver.solve().is_sat()
}

#[test]
fn test_pigeonhole_small() {
    // PHP(1): 2 pigeons, 1 hole - UNSAT
    let php1 = pigeonhole(1);
    assert!(!solve(&php1));

    // PHP(2): 3 pigeons, 2 holes - UNSAT
    let php2 = pigeonhole(2);
    assert!(!solve(&php2));

    // PHP(3): 4 pigeons, 3 holes - UNSAT
    let php3 = pigeonhole(3);
    assert!(!solve(&php3));
}

#[test]
fn test_pigeonhole_structure() {
    let php2 = pigeonhole(2);
    // 3 pigeons * 2 holes = 6 variables
    // 3 at-least-one clauses + C(3,2) * 2 = 3 + 6 = 9 clauses
    assert_eq!(php2.num_vars(), 6);
    assert_eq!(php2.num_clauses(), 9);
}

#[test]
fn test_parity() {
    // XOR of 0 variables = 1 is impossible
    let p0 = parity(0);
    assert!(!solve(&p0));

    // XOR of 2 variables = 1: (x1 AND NOT x2) OR (NOT x1 AND x2)
    let p2 = parity(2);
    assert!(solve(&p2)); // SAT: x1=T, x2=F or x1=F, x2=T

    // XOR of 3 variables = 1
    let p3 = parity(3);
    assert!(solve(&p3)); // SAT

    // Structure: 2^{n-1} clauses
    assert_eq!(p0.num_clauses(), 1);
    assert_eq!(p2.num_clauses(), 2);
    assert_eq!(p3.num_clauses(), 4);
}

#[test]
fn test_random_k_cnf_deterministic() {
    let f1 = random_k_cnf(3, 10, 20, Some(42));
    let f2 = random_k_cnf(3, 10, 20, Some(42));
    // Same seed should give same formula
    assert_eq!(f1.num_clauses(), f2.num_clauses());
}

#[test]
fn test_random_k_cnf_structure() {
    let f = random_k_cnf(3, 100, 50, Some(123));
    assert_eq!(f.num_vars(), 100);
    assert_eq!(f.num_clauses(), 50);
}

#[test]
fn test_ordering_principle_small() {
    // OP(2): 2 elements with no minimum - UNSAT
    let op2 = ordering_principle(2);
    assert!(!solve(&op2));

    // OP(3): 3 elements with no minimum - UNSAT
    let op3 = ordering_principle(3);
    assert!(!solve(&op3));
}
