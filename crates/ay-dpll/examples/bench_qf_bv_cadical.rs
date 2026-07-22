// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Benchmark QF_BV encoding vs CaDiCaL on the *equivalent SAT problem*.
//!
//! This builds AY's BV->CNF encoding, then compares:
//! - ay-sat on the produced CNF (in-process)
//! - CaDiCaL on the same CNF (written to a temp DIMACS file)
//!
//! Usage:
//!   cargo run --release -p ay-dpll --example bench_qf_bv_cadical -- [benchmark_dir] [limit] [cadical_path]
//!
//! Defaults:
//!   benchmark_dir = benchmarks/smt/QF_BV
//!   limit         = all files
//!
//! Notes:
//! - CaDiCaL must be built at `reference/cadical/build/cadical`
//! - This does not benchmark incremental clause retention (Priority 1.2).

use std::ffi::OsStr;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::process::Command as ProcessCommand;
use std::time::{Duration, Instant};

use ay_bv::BvSolver;
use ay_core::{CnfClause, TermId, TermStore, Tseitin};
use ay_dpll::Executor;
use ay_frontend::{parse, Command};
use ay_sat::{Literal, SatResult, Solver as SatSolver};

fn collect_smt2_files(dir: &Path, out: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        let meta = entry.metadata()?;
        if meta.is_dir() {
            collect_smt2_files(&path, out)?;
            continue;
        }
        if path.extension() == Some(OsStr::new("smt2")) {
            out.push(path);
        }
    }
    Ok(())
}

fn write_dimacs(path: &Path, num_vars: u32, clauses: &[CnfClause]) -> std::io::Result<()> {
    let file = fs::File::create(path)?;
    let mut w = BufWriter::new(file);
    writeln!(w, "p cnf {} {}", num_vars, clauses.len())?;
    for clause in clauses {
        for &lit in clause.literals() {
            write!(w, "{lit} ")?;
        }
        writeln!(w, "0")?;
    }
    Ok(())
}

/// Build the QF_BV CNF encoding used by `Executor::solve_bv` (non-incremental).
fn build_qf_bv_cnf(terms: &TermStore, assertions: &[TermId]) -> (u32, Vec<CnfClause>) {
    // Boolean structure.
    let tseitin = Tseitin::new(terms);
    let tseitin_result = tseitin.transform_all(assertions);

    // BV constraints.
    let mut bv_solver = BvSolver::new(terms);
    let bv_clauses = bv_solver.bitblast_all(assertions);

    let mut all_clauses = tseitin_result.clauses.clone();
    let var_offset = tseitin_result.num_vars as i32;

    // Offset BV variables so they don't collide with Tseitin variables.
    for clause in bv_clauses {
        let offset_lits: Vec<i32> = clause
            .literals()
            .iter()
            .map(|&lit| {
                if lit > 0 {
                    lit + var_offset
                } else {
                    lit - var_offset
                }
            })
            .collect();
        all_clauses.push(CnfClause::new(offset_lits));
    }

    // Connect Tseitin variables for nested BV predicates to their bitblasted results (#858).
    for (&tseitin_var, &term) in &tseitin_result.var_to_term {
        if let Some(bv_lit) = bv_solver.bitblast_predicate(term) {
            let bv_lit_offset = if bv_lit > 0 {
                bv_lit + var_offset
            } else {
                bv_lit - var_offset
            };
            let tseitin_lit = tseitin_var as i32;
            all_clauses.push(CnfClause::binary(-tseitin_lit, bv_lit_offset));
            all_clauses.push(CnfClause::binary(tseitin_lit, -bv_lit_offset));
        }
    }

    // Add any extra BV clauses generated while bitblasting nested predicates.
    for clause in bv_solver.take_clauses() {
        let offset_lits: Vec<i32> = clause
            .literals()
            .iter()
            .map(|&lit| {
                if lit > 0 {
                    lit + var_offset
                } else {
                    lit - var_offset
                }
            })
            .collect();
        all_clauses.push(CnfClause::new(offset_lits));
    }

    let total_vars = tseitin_result.num_vars + bv_solver.num_vars();
    (total_vars, all_clauses)
}

fn main() -> anyhow::Result<()> {
    let mut args = std::env::args().skip(1);
    let benchmark_dir = args
        .next()
        .unwrap_or_else(|| "benchmarks/smt/QF_BV".to_string());
    let limit: Option<usize> = args.next().map(|s| s.parse()).transpose()?;

    let cadical_path = args
        .next()
        .or_else(|| std::env::var("CADICAL").ok())
        .unwrap_or_else(|| "reference/cadical/build/cadical".to_string());
    let cadical = Path::new(&cadical_path);
    if !cadical.exists() {
        anyhow::bail!(
            "CaDiCaL not found at {cadical_path} (set CADICAL=... or pass cadical_path as argv[3])"
        );
    }

    // Warm CaDiCaL binary/code pages to avoid a misleading cold-start first sample.
    {
        let warm_path = std::env::temp_dir().join("ay_qfbv_cadical_warmup.cnf");
        fs::write(&warm_path, "p cnf 1 1\n1 0\n")?;
        let _ = ProcessCommand::new(cadical)
            .arg("-q")
            .arg(&warm_path)
            .output();
        let _ = fs::remove_file(&warm_path);
    }

    let mut files = Vec::new();
    collect_smt2_files(Path::new(&benchmark_dir), &mut files)?;
    files.sort();
    if let Some(limit) = limit {
        files.truncate(limit);
    }
    if files.is_empty() {
        anyhow::bail!("No .smt2 files found under {benchmark_dir}");
    }

    println!(
        "Benchmarking QF_BV CNF vs CaDiCaL on {} file(s) from {}",
        files.len(),
        benchmark_dir
    );
    println!("{}", "=".repeat(96));
    println!(
        "{:38} {:>7} {:>9} {:>10} {:>10} {:>10} {:>8}",
        "File", "Vars", "Clauses", "CNF(ms)", "AY(ms)", "CaD(ms)", "Ratio"
    );

    let mut total_cnf = Duration::ZERO;
    let mut total_ay = Duration::ZERO;
    let mut total_cadical = Duration::ZERO;
    let mut disagreements = 0usize;

    for (idx, path) in files.iter().enumerate() {
        let name = path.file_name().unwrap_or_default().to_string_lossy();
        let content = fs::read_to_string(path)?;

        let commands = parse(&content)?;
        let mut exec = Executor::new();

        // Build the assertion stack, but do not solve.
        for cmd in &commands {
            match cmd {
                Command::CheckSat | Command::CheckSatAssuming(_) | Command::Exit => break,
                _ => {
                    let _ = exec.execute(cmd)?;
                }
            }
        }

        // Only benchmark QF_BV inputs (skip any mismatches).
        match exec.context().logic() {
            Some("QF_BV") => {}
            other => {
                eprintln!("SKIP {:38} (logic={:?})", name, other.unwrap_or("<none>"));
                continue;
            }
        }

        let cnf_start = Instant::now();
        let (num_vars, clauses) =
            build_qf_bv_cnf(&exec.context().terms, &exec.context().assertions);
        let cnf_time = cnf_start.elapsed();
        total_cnf += cnf_time;

        // Solve with ay-sat (in-memory CNF).
        let ay_start = Instant::now();
        let mut solver = SatSolver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(
                clause
                    .literals()
                    .iter()
                    .copied()
                    .map(Literal::from_dimacs)
                    .collect(),
            );
        }
        let ay_result = solver.solve();
        let ay_time = ay_start.elapsed();
        total_ay += ay_time;

        // Solve with CaDiCaL (DIMACS file).
        let cnf_path = std::env::temp_dir().join(format!("ay_qfbv_{idx}_{name}.cnf"));
        write_dimacs(&cnf_path, num_vars, &clauses)?;

        let cadical_start = Instant::now();
        let output = ProcessCommand::new(cadical)
            .arg("-q")
            .arg(&cnf_path)
            .output()?;
        let cadical_time = cadical_start.elapsed();
        total_cadical += cadical_time;

        let _ = fs::remove_file(&cnf_path);

        let cadical_sat = match output.status.code() {
            Some(10) => true,
            Some(20) => false,
            other => {
                eprintln!("CaDiCaL unexpected exit on {name}: code={other:?}");
                continue;
            }
        };
        let ay_sat = matches!(ay_result.into_inner(), SatResult::Sat(_));
        if ay_sat != cadical_sat {
            disagreements += 1;
        }

        let ratio = if cadical_time.as_nanos() > 0 {
            ay_time.as_secs_f64() / cadical_time.as_secs_f64()
        } else {
            f64::INFINITY
        };

        println!(
            "{:38} {:>7} {:>9} {:>10.1} {:>10.1} {:>10.1} {:>7.2}x{}",
            name,
            num_vars,
            clauses.len(),
            cnf_time.as_secs_f64() * 1000.0,
            ay_time.as_secs_f64() * 1000.0,
            cadical_time.as_secs_f64() * 1000.0,
            ratio,
            if ay_sat != cadical_sat { " !" } else { "" }
        );
    }

    println!("{}", "=".repeat(96));
    println!(
        "Totals: CNF={:.1}ms  AY={:.1}ms  CaDiCaL={:.1}ms  AY/CaDiCaL={:.2}x  disagreements={}",
        total_cnf.as_secs_f64() * 1000.0,
        total_ay.as_secs_f64() * 1000.0,
        total_cadical.as_secs_f64() * 1000.0,
        total_ay.as_secs_f64() / total_cadical.as_secs_f64(),
        disagreements
    );

    Ok(())
}
