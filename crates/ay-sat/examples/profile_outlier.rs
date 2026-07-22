// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! Profile slow outlier cases to understand performance gaps

use ay_sat::{parse_dimacs, SatResult, Solver};
use std::fs;
use std::time::Instant;

fn profile_file(path: &str) {
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            println!("{path}: ERROR - {e}");
            return;
        }
    };
    let formula = parse_dimacs(&content).expect("parse");

    let mut solver = Solver::new(formula.num_vars);
    for c in &formula.clauses {
        solver.add_clause(c.clone());
    }

    let start = Instant::now();
    let result = solver.solve().into_inner();
    let elapsed = start.elapsed();

    let result_status = match result {
        SatResult::Sat(_) => "SAT",
        SatResult::Unsat(_) => "UNSAT",
        SatResult::Unknown => "UNKNOWN",
        _ => unreachable!(),
    };

    // Get statistics
    let conflicts = solver.num_conflicts();
    let restarts = solver.num_restarts();
    let decisions = solver.num_decisions();
    let propagations = solver.num_propagations();

    println!("{path}");
    println!(
        "  Result: {}  Time: {:.1}ms",
        result_status,
        elapsed.as_secs_f64() * 1000.0
    );
    println!(
        "  conflicts: {conflicts}  restarts: {restarts}  decisions: {decisions}  propagations: {propagations}"
    );
    if conflicts > 0 {
        println!(
            "  conflicts/restart: {:.0}  props/conflict: {:.1}",
            conflicts as f64 / restarts.max(1) as f64,
            propagations as f64 / conflicts as f64
        );
    }
    println!();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();

    if args.len() > 1 {
        // Profile specific files from command line
        for path in &args[1..] {
            profile_file(path);
        }
    } else {
        // Profile current outliers (from verbose benchmark run)
        println!("=== Slow outliers (>10x slower than CaDiCaL) ===\n");
        profile_file("benchmarks/satlib/uf250/uf250-029.cnf"); // 30.85x
        profile_file("benchmarks/satlib/uf250/uf250-054.cnf"); // 25.13x
        profile_file("benchmarks/satlib/uf250/uf250-09.cnf"); // 16.01x
        profile_file("benchmarks/satlib/uf250/uf250-077.cnf"); // 6.37x
        profile_file("benchmarks/satlib/uf250/uf250-07.cnf"); // 4.95x

        println!("=== Fast cases (AY wins, <0.20x) ===\n");
        profile_file("benchmarks/satlib/uf250/uf250-010.cnf"); // 0.17x
        profile_file("benchmarks/satlib/uf250/uf250-03.cnf"); // 0.15x
        profile_file("benchmarks/satlib/uf250/uf250-032.cnf"); // 0.16x
    }
}
