// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! Profile a single benchmark file for flamegraph analysis

use ay_sat::{parse_dimacs, Solver};
use std::fs;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let path = args
        .get(1)
        .map_or("benchmarks/dimacs/uf200-052.cnf", String::as_str);
    let iterations: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(10);

    let content = fs::read_to_string(path).expect("read");
    let formula = parse_dimacs(&content).expect("parse");

    eprintln!("File: {path}");
    eprintln!(
        "Variables: {}, Clauses: {}",
        formula.num_vars,
        formula.clauses.len()
    );
    eprintln!("Running {iterations} iterations");

    for _ in 0..iterations {
        let mut solver = Solver::new(formula.num_vars);
        for c in &formula.clauses {
            solver.add_clause(c.clone());
        }
        let _ = solver.solve().into_inner();
    }
}
