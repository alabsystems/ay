// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![allow(clippy::print_stdout)]

use ay_sat::{parse_dimacs, SatResult, Solver};
use ay_xor::solve_with_xor_detection_stats;
use std::fs;
use std::path::PathBuf;

fn main() {
    let files = [
        "par8-1.cnf",
        "par8-2.cnf",
        "par8-3.cnf",
        "par16-1.cnf",
        "par16-2.cnf",
        // par32 is too slow currently - skip for benchmarking
    ];
    let path =
        PathBuf::from(env!("CARGO_MANIFEST_DIR").to_string() + "/../../benchmarks/sat/crypto");

    println!(
        "{:15} | {:>12} | {:>12} | {:>8} | {:>6}",
        "File", "Plain", "XOR", "Speedup", "XORs"
    );
    println!("{}", "-".repeat(70));

    for filename in &files {
        let file_path = path.join(filename);
        if !file_path.exists() {
            println!("{filename:15} | SKIP - file not found");
            continue;
        }

        let content = fs::read_to_string(&file_path).unwrap();
        let formula = parse_dimacs(&content).unwrap();

        // Plain SAT
        let start = std::time::Instant::now();
        let mut solver = Solver::new(formula.num_vars);
        for clause in &formula.clauses {
            solver.add_clause(clause.clone());
        }
        let plain_result = solver.solve().into_inner();
        let plain_time = start.elapsed();

        // XOR-aware
        let start = std::time::Instant::now();
        let xor_result = solve_with_xor_detection_stats(formula.num_vars, &formula.clauses);
        let xor_time = start.elapsed();

        let speedup = plain_time.as_secs_f64() / xor_time.as_secs_f64();

        let plain_sat = matches!(plain_result, SatResult::Sat(_));
        let xor_sat = xor_result.result.is_sat();

        if plain_sat != xor_sat {
            println!("{filename:15} | ERROR: result mismatch!");
            continue;
        }

        println!(
            "{:15} | {:>10.2}ms | {:>10.2}ms | {:>7.2}x | {:>6}",
            filename,
            plain_time.as_secs_f64() * 1000.0,
            xor_time.as_secs_f64() * 1000.0,
            speedup,
            xor_result.stats.xors_detected
        );
    }
}
