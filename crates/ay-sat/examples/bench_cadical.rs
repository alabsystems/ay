// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(
    clippy::print_stderr,
    clippy::print_stdout,
    clippy::unnecessary_debug_formatting,
    clippy::case_sensitive_file_extension_comparisons
)]

//! Benchmark AY vs CaDiCaL on SATLIB benchmarks
//!
//! Usage: cargo run --release --example bench_cadical [prefix]
//! Default prefix is "uf200". Use "uf250" for harder benchmarks.

use ay_sat::{parse_dimacs, Solver};
use std::fs;
use std::io::Write;
use std::process::Command;
use std::time::Instant;

fn main() {
    let benchmark_dir = "benchmarks/dimacs";
    let cadical = "reference/cadical/build/cadical";

    // Get benchmark prefix from command line (default: uf200)
    let prefix = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "uf200".to_string());

    // Check CaDiCaL exists
    if !std::path::Path::new(cadical).exists() {
        eprintln!("CaDiCaL not found at {cadical}");
        std::process::exit(1);
    }

    let mut files: Vec<_> = fs::read_dir(benchmark_dir)
        .expect("read dir")
        .filter_map(Result::ok)
        .filter(|e| {
            let name = e.file_name().to_string_lossy().to_string();
            name.starts_with(&prefix) && name.ends_with(".cnf")
        })
        .map(|e| e.path())
        .collect();
    files.sort();

    // Use up to 100 files
    let files: Vec<_> = files.into_iter().take(100).collect();

    println!(
        "\nBenchmarking {} {} files: AY vs CaDiCaL",
        files.len(),
        prefix
    );
    println!("{}", "=".repeat(80));

    let mut total_ay = std::time::Duration::ZERO;
    let mut total_cadical = std::time::Duration::ZERO;
    let mut ay_wins = 0;
    let mut cadical_wins = 0;
    let mut disagreements = 0;

    for path in &files {
        let path_str = path.to_string_lossy().to_string();
        let name = path.file_name().unwrap().to_string_lossy().to_string();

        // Run AY
        let content = fs::read_to_string(path).expect("read");
        let formula = parse_dimacs(&content).expect("parse");
        let mut solver = Solver::new(formula.num_vars);
        for c in &formula.clauses {
            solver.add_clause(c.clone());
        }
        let start = Instant::now();
        let ay_result = solver.solve().into_inner();
        let ay_time = start.elapsed();
        total_ay += ay_time;

        // Run CaDiCaL
        let start = Instant::now();
        let output = Command::new(cadical)
            .arg("-q")
            .arg(&path_str)
            .output()
            .expect("cadical");
        let cadical_time = start.elapsed();
        total_cadical += cadical_time;

        // Parse CaDiCaL result (exit code: 10=SAT, 20=UNSAT)
        let cadical_sat = match output.status.code() {
            Some(10) => true,
            Some(20) => false,
            _ => {
                eprintln!("CaDiCaL unexpected exit: {:?}", output.status);
                continue;
            }
        };

        let ay_sat = ay_result.is_sat();

        // Check agreement
        if ay_sat != cadical_sat {
            disagreements += 1;
            eprintln!("DISAGREEMENT on {name}: AY={ay_sat} CaDiCaL={cadical_sat}");
        }

        // Track wins
        if ay_time < cadical_time {
            ay_wins += 1;
        } else {
            cadical_wins += 1;
        }

        let ratio = ay_time.as_secs_f64() / cadical_time.as_secs_f64();
        let ay_status = if ay_sat { "SAT" } else { "UNSAT" };
        print!(
            "\r{:20} AY:{:>7.1}ms CaDiCaL:{:>7.1}ms ratio:{:.2}x {}",
            name,
            ay_time.as_secs_f64() * 1000.0,
            cadical_time.as_secs_f64() * 1000.0,
            ratio,
            ay_status
        );
        std::io::stdout().flush().unwrap();
    }

    println!("\n{}", "=".repeat(80));
    println!("Total AY:      {:.1}ms", total_ay.as_secs_f64() * 1000.0);
    println!(
        "Total CaDiCaL: {:.1}ms",
        total_cadical.as_secs_f64() * 1000.0
    );
    println!(
        "AY/CaDiCaL:    {:.2}x",
        total_ay.as_secs_f64() / total_cadical.as_secs_f64()
    );
    println!(
        "AY wins:       {}/{} (CaDiCaL: {})",
        ay_wins,
        files.len(),
        cadical_wins
    );
    println!("Disagreements: {disagreements}");
}
