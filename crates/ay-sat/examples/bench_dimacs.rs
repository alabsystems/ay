// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr, clippy::print_stdout)]

//! Benchmark ay-sat on DIMACS files
//!
//! Usage: cargo run --release --example bench_dimacs -- [--warmup N] [--repeat N] [DIMACS_FILE...]
//!
//! Reads DIMACS CNF files, solves them with ay-sat, and reports solve timing.

use ay_sat::{parse_dimacs, SatTechnique, Solver};
use std::time::Instant;

/// Read `AY_SAT_DISABLE_*` env vars and return the techniques to disable.
///
/// This is a standalone function for the bench_dimacs example, which does not
/// go through the `ay` CLI. The canonical CLI path uses `--disable` flags
/// and a global `OnceLock` instead of env vars (#8331).
fn disabled_techniques_from_env() -> Vec<SatTechnique> {
    const TABLE: &[(&str, SatTechnique)] = &[
        ("PREPROCESS", SatTechnique::Preprocess),
        ("BVE", SatTechnique::Bve),
        ("BCE", SatTechnique::Bce),
        ("CCE", SatTechnique::Cce),
        ("SWEEP", SatTechnique::Sweep),
        ("PROBE", SatTechnique::Probe),
        ("SUBSUME", SatTechnique::Subsume),
        ("VIVIFY", SatTechnique::Vivify),
        ("HTR", SatTechnique::Htr),
        ("TRANSRED", SatTechnique::Transred),
        ("GATE", SatTechnique::Gate),
        ("GATES", SatTechnique::Congruence),
        ("WALK", SatTechnique::Walk),
        ("WARMUP", SatTechnique::Warmup),
        ("FACTOR", SatTechnique::Factor),
        ("SBVA", SatTechnique::Sbva),
        ("SHRINK", SatTechnique::Shrink),
        ("CONGRUENCE", SatTechnique::Congruence),
        ("DECOMPOSE", SatTechnique::Decompose),
        ("CONDITION", SatTechnique::Condition),
        ("ELIMFAST", SatTechnique::Elimfast),
        ("INPROCESS", SatTechnique::Inprocess),
        ("FLIP", SatTechnique::Flip),
        ("JIT", SatTechnique::Jit),
    ];
    let mut disabled = Vec::new();
    for &(suffix, technique) in TABLE {
        if std::env::var(format!("AY_SAT_DISABLE_{suffix}")).is_ok() {
            disabled.push(technique);
        }
    }
    disabled
}

#[derive(Debug)]
struct Options {
    paths: Vec<String>,
    repeat: usize,
    warmup: usize,
}

#[derive(Debug)]
struct SolveMeasurement {
    status: &'static str,
    solve_elapsed: f64,
    overall_elapsed: f64,
    conflicts: u64,
    decisions: u64,
    restarts: u64,
    propagations: u64,
}

fn usage(program: &str) {
    eprintln!("Usage: {program} [--warmup N] [--repeat N] <dimacs_file>...");
    eprintln!("       {program} --warmup 1 --repeat 5 benchmarks/sat/satcomp2024-sample/*.cnf");
}

fn parse_count(flag: &str, raw: &str) -> usize {
    match raw.parse::<usize>() {
        Ok(value) => value,
        Err(error) => {
            eprintln!("{flag} must be a non-negative integer: {error}");
            std::process::exit(2);
        }
    }
}

fn parse_count_arg(flag: &str, args: &[String], index: usize) -> usize {
    let Some(raw) = args.get(index + 1) else {
        eprintln!("{flag} requires a value");
        std::process::exit(2);
    };
    parse_count(flag, raw)
}

fn parse_options(args: &[String]) -> Options {
    let mut paths = Vec::new();
    let mut repeat = 1usize;
    let mut warmup = 0usize;
    let mut positional_only = false;
    let mut index = 1usize;

    while index < args.len() {
        let arg = &args[index];
        if positional_only {
            paths.push(arg.clone());
            index += 1;
            continue;
        }

        match arg.as_str() {
            "-h" | "--help" => {
                usage(&args[0]);
                std::process::exit(0);
            }
            "--" => {
                positional_only = true;
                index += 1;
            }
            "--repeat" => {
                repeat = parse_count_arg("--repeat", args, index);
                if repeat == 0 {
                    eprintln!("--repeat must be at least 1");
                    std::process::exit(2);
                }
                index += 2;
            }
            "--warmup" => {
                warmup = parse_count_arg("--warmup", args, index);
                index += 2;
            }
            _ if arg.starts_with("--repeat=") => {
                repeat = parse_count("--repeat", &arg["--repeat=".len()..]);
                if repeat == 0 {
                    eprintln!("--repeat must be at least 1");
                    std::process::exit(2);
                }
                index += 1;
            }
            _ if arg.starts_with("--warmup=") => {
                warmup = parse_count("--warmup", &arg["--warmup=".len()..]);
                index += 1;
            }
            _ if arg.starts_with('-') => {
                eprintln!("unknown option: {arg}");
                usage(&args[0]);
                std::process::exit(2);
            }
            _ => {
                paths.push(arg.clone());
                index += 1;
            }
        }
    }

    Options {
        paths,
        repeat,
        warmup,
    }
}

fn solve_once(
    content: &str,
    disabled: &[SatTechnique],
) -> Result<SolveMeasurement, Box<dyn std::error::Error>> {
    let overall_start = Instant::now();
    let formula = parse_dimacs(content)?;
    let mut solver: Solver = formula.into_solver();
    for &technique in disabled {
        solver.disable_technique(technique);
    }

    let solve_start = Instant::now();
    let result = solver.solve().into_inner();
    let solve_elapsed = solve_start.elapsed().as_secs_f64();
    let overall_elapsed = overall_start.elapsed().as_secs_f64();
    let status = match &result {
        ay_sat::SatResult::Sat(_) => "SAT",
        ay_sat::SatResult::Unsat(_) => "UNSAT",
        ay_sat::SatResult::Unknown => "UNKNOWN",
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    };

    Ok(SolveMeasurement {
        status,
        solve_elapsed,
        overall_elapsed,
        conflicts: solver.num_conflicts(),
        decisions: solver.num_decisions(),
        restarts: solver.num_restarts(),
        propagations: solver.num_propagations(),
    })
}

fn median(values: &mut [f64]) -> f64 {
    values.sort_by(f64::total_cmp);
    let mid = values.len() / 2;
    if values.len().is_multiple_of(2) {
        f64::midpoint(values[mid - 1], values[mid])
    } else {
        values[mid]
    }
}

fn print_measurement(path: &str, measurements: &[SolveMeasurement], warmup: usize) {
    let last = measurements.last().expect("at least one measurement");
    let solve_sum: f64 = measurements.iter().map(|m| m.solve_elapsed).sum();
    let overall_sum: f64 = measurements.iter().map(|m| m.overall_elapsed).sum();
    let propagation_sum: f64 = measurements.iter().map(|m| m.propagations as f64).sum();
    let avg_solve = solve_sum / measurements.len() as f64;
    let avg_overall = overall_sum / measurements.len() as f64;
    let best_solve = measurements
        .iter()
        .map(|m| m.solve_elapsed)
        .fold(f64::INFINITY, f64::min);
    let mut solve_times: Vec<f64> = measurements.iter().map(|m| m.solve_elapsed).collect();
    let median_solve = median(&mut solve_times);
    let props_per_sec = if solve_sum > 0.0 {
        propagation_sum / solve_sum
    } else {
        0.0
    };

    if std::env::var("VERBOSE").is_ok() {
        println!(
            "{:6} avg:{:8.3}ms best:{:8.3}ms med:{:8.3}ms total_avg:{:8.3}ms runs:{:>2} warmup:{:>2} c:{:>8} d:{:>8} r:{:>6} p:{:>10} pps:{:>10.0}  {}",
            last.status,
            avg_solve * 1000.0,
            best_solve * 1000.0,
            median_solve * 1000.0,
            avg_overall * 1000.0,
            measurements.len(),
            warmup,
            last.conflicts,
            last.decisions,
            last.restarts,
            last.propagations,
            props_per_sec,
            path
        );
    } else {
        println!(
            "{:6} avg:{:8.3}ms best:{:8.3}ms med:{:8.3}ms runs:{:>2}  {}",
            last.status,
            avg_solve * 1000.0,
            best_solve * 1000.0,
            median_solve * 1000.0,
            measurements.len(),
            path
        );
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let options = parse_options(&args);

    if options.paths.is_empty() {
        usage(&args[0]);
        std::process::exit(1);
    }

    let mut total_solve_time = 0.0;
    let mut total_overall_time = 0.0;
    let mut sat_count = 0;
    let mut unsat_count = 0;
    let mut error_count = 0;
    let mut measured_count = 0usize;
    let disabled = disabled_techniques_from_env();

    for path in &options.paths {
        match std::fs::read_to_string(path) {
            Ok(content) => {
                for _ in 0..options.warmup {
                    if let Err(error) = solve_once(&content, &disabled) {
                        error_count += 1;
                        eprintln!("SOLVE ERROR during warmup: {path} - {error}");
                    }
                }

                let mut measurements = Vec::with_capacity(options.repeat);
                for _ in 0..options.repeat {
                    match solve_once(&content, &disabled) {
                        Ok(measurement) => measurements.push(measurement),
                        Err(error) => {
                            error_count += 1;
                            eprintln!("SOLVE ERROR: {path} - {error}");
                        }
                    }
                }

                let Some(last) = measurements.last() else {
                    error_count += 1;
                    eprintln!("SOLVE ERROR: {path} - no successful measured runs");
                    continue;
                };

                match last.status {
                    "SAT" => sat_count += 1,
                    "UNSAT" => unsat_count += 1,
                    "UNKNOWN" => {}
                    _ => unreachable!(),
                }

                total_solve_time += measurements.iter().map(|m| m.solve_elapsed).sum::<f64>();
                total_overall_time += measurements.iter().map(|m| m.overall_elapsed).sum::<f64>();
                measured_count += measurements.len();
                print_measurement(path, &measurements, options.warmup);
            }
            Err(error) => {
                error_count += 1;
                eprintln!("READ ERROR: {path} - {error}");
            }
        }
    }

    println!("\n--- Summary ---");
    println!(
        "Total: {} files, {} SAT, {} UNSAT, {} errors",
        options.paths.len(),
        sat_count,
        unsat_count,
        error_count
    );
    println!("Measured runs: {measured_count}");
    println!("Total solve time: {total_solve_time:.3}s");
    println!("Total overall time: {total_overall_time:.3}s");
    if measured_count > 0 {
        println!(
            "Average solve time: {:.3}ms",
            total_solve_time * 1000.0 / measured_count as f64
        );
    }
}
