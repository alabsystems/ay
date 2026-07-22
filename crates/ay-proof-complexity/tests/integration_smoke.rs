// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_proof_complexity::{pigeonhole, tseitin, Graph};

#[test]
fn pigeonhole_formula_is_unsat() {
    let cnf = pigeonhole(2);
    let mut solver = cnf.into_solver();
    assert!(solver.solve().is_unsat());
}

#[test]
fn odd_parity_tseitin_cycle_is_unsat() {
    let graph = Graph::cycle(3);
    let cnf = tseitin(&graph, &[true, true, true]);
    let mut solver = cnf.into_solver();
    assert!(solver.solve().is_unsat());
}
