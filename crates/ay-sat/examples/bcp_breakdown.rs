// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout, clippy::panic)]

//! Benchmark SAT solver performance on uf250 instances.
//!
//! Reports wall-clock time and integer counters (propagations, conflicts,
//! decisions) per benchmark — no internal timing syscalls.
//!
//! Usage: bcp_breakdown [DIR] [LIMIT]
//!   DIR   - directory containing uf250-*.cnf files (default: reference/creusat/tests/cnf-hard/sat)
//!   LIMIT - max files to process (default: all)

use ay_sat::{parse_dimacs, Solver};
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let dir = args
        .get(1)
        .map_or("reference/creusat/tests/cnf-hard/sat", String::as_str);
    let limit: usize = args
        .get(2)
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);

    let mut paths: Vec<PathBuf> = fs::read_dir(dir)
        .unwrap_or_else(|e| panic!("cannot read {dir}: {e}"))
        .filter_map(Result::ok)
        .map(|e| e.path())
        .filter(|p| {
            let name_match = p
                .file_name()
                .and_then(|n| n.to_str())
                .is_some_and(|n| n.starts_with("uf250-"));
            let ext_match = p
                .extension()
                .is_some_and(|ext| ext.eq_ignore_ascii_case("cnf"));
            name_match && ext_match
        })
        .collect();
    paths.sort();
    paths.truncate(limit);

    if paths.is_empty() {
        eprintln!("No uf250-*.cnf files found in: {dir}");
        std::process::exit(1);
    }

    eprintln!("Profiling {} uf250 benchmarks from {dir}", paths.len());
    println!("benchmark,total_ms,propagations,conflicts,decisions,props_per_sec");

    let mut sum_total = 0.0_f64;
    let mut sum_propagations: u64 = 0;
    let mut sum_conflicts: u64 = 0;
    let mut sum_decisions: u64 = 0;

    for path in &paths {
        let content = fs::read_to_string(path).expect("read");
        let formula = parse_dimacs(&content).expect("parse");
        let name = path.file_name().unwrap().to_string_lossy();

        let mut solver = Solver::new(formula.num_vars);
        for c in &formula.clauses {
            solver.add_clause(c.clone());
        }

        let start = Instant::now();
        let _ = solver.solve().into_inner();
        let total = start.elapsed();

        let total_ms = total.as_secs_f64() * 1000.0;
        let props = solver.num_propagations();
        let conflicts = solver.num_conflicts();
        let decisions = solver.num_decisions();
        let props_per_sec = if total.as_secs_f64() > 0.0 {
            props as f64 / total.as_secs_f64()
        } else {
            0.0
        };

        sum_total += total_ms;
        sum_propagations += props;
        sum_conflicts += conflicts;
        sum_decisions += decisions;

        println!("{name},{total_ms:.2},{props},{conflicts},{decisions},{props_per_sec:.0}");
    }

    let total_secs = sum_total / 1000.0;
    let agg_props_per_sec = if total_secs > 0.0 {
        sum_propagations as f64 / total_secs
    } else {
        0.0
    };

    eprintln!("\n--- Aggregate ---");
    eprintln!("Total time:    {sum_total:.1}ms");
    eprintln!("Propagations:  {sum_propagations} ({agg_props_per_sec:.0}/sec)");
    eprintln!("Conflicts:     {sum_conflicts}");
    eprintln!("Decisions:     {sum_decisions}");

    println!(
        "TOTAL,{sum_total:.2},{sum_propagations},{sum_conflicts},{sum_decisions},{agg_props_per_sec:.0}",
    );
}
