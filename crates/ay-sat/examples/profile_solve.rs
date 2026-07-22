#![allow(clippy::print_stderr, clippy::print_stdout)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Profile SAT solving on a larger benchmark

use ay_sat::{parse_dimacs, Solver};
use std::fs;

fn main() {
    // Pick a harder benchmark
    let path = "benchmarks/dimacs/uf200-010.cnf";
    let content = fs::read_to_string(path).expect("read");
    let formula = parse_dimacs(&content).expect("parse");

    // Run multiple times for better profiling
    for _ in 0..10 {
        let mut solver = Solver::new(formula.num_vars);
        for c in &formula.clauses {
            solver.add_clause(c.clone());
        }
        let _result = solver.solve().into_inner();
    }
}
