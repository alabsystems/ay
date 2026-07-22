// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::case_sensitive_file_extension_comparisons
)]

//! Benchmark vivification on uf200 files

use ay_sat::{parse_dimacs, Solver};
use std::fs;
use std::time::Instant;

fn main() {
    let benchmark_dir = "benchmarks/dimacs";
    let mut files: Vec<_> = fs::read_dir(benchmark_dir)
        .expect("read dir")
        .filter_map(Result::ok)
        .filter(|e| {
            let name = e.file_name().to_string_lossy().to_string();
            name.starts_with("uf200") && name.ends_with(".cnf")
        })
        .map(|e| e.path())
        .collect();
    files.sort();
    let files: Vec<_> = files.into_iter().take(20).collect();

    println!("\nBenchmarking {} uf200 files", files.len());
    println!("{}", "=".repeat(70));

    let mut total_v = std::time::Duration::ZERO;
    let mut total_nv = std::time::Duration::ZERO;

    for path in &files {
        let content = fs::read_to_string(path).expect("read");
        let formula = parse_dimacs(&content).expect("parse");
        let name = path.file_name().unwrap().to_string_lossy().to_string();

        // With vivification
        let mut solver = Solver::new(formula.num_vars);
        solver.set_vivify_enabled(true);
        for c in &formula.clauses {
            solver.add_clause(c.clone());
        }
        let start = Instant::now();
        let r1 = solver.solve().into_inner();
        let t1 = start.elapsed();
        total_v += t1;

        // Without vivification
        let mut solver = Solver::new(formula.num_vars);
        solver.set_vivify_enabled(false);
        for c in &formula.clauses {
            solver.add_clause(c.clone());
        }
        let start = Instant::now();
        let r2 = solver.solve().into_inner();
        let t2 = start.elapsed();
        total_nv += t2;

        let ratio = t1.as_secs_f64() / t2.as_secs_f64();
        let status1 = match r1 {
            ay_sat::SatResult::Sat(_) => "SAT",
            ay_sat::SatResult::Unsat(_) => "UNSAT",
            ay_sat::SatResult::Unknown => "UNK",
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        };
        let status2 = match r2 {
            ay_sat::SatResult::Sat(_) => "SAT",
            ay_sat::SatResult::Unsat(_) => "UNSAT",
            ay_sat::SatResult::Unknown => "UNK",
            #[allow(unreachable_patterns)]
            _ => unreachable!(),
        };
        println!(
            "{:20} vivify:{}({:>7.1}ms) no_vivify:{}({:>7.1}ms) ratio:{:.2}x",
            name,
            status1,
            t1.as_secs_f64() * 1000.0,
            status2,
            t2.as_secs_f64() * 1000.0,
            ratio
        );
    }

    println!("{}", "=".repeat(70));
    println!(
        "Total with vivify:    {:.1}ms",
        total_v.as_secs_f64() * 1000.0
    );
    println!(
        "Total without vivify: {:.1}ms",
        total_nv.as_secs_f64() * 1000.0
    );
    println!(
        "Vivify overhead:      {:.2}x",
        total_v.as_secs_f64() / total_nv.as_secs_f64()
    );
}
