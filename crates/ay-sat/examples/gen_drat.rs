// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use ay_sat::{parse_dimacs, SatResult, Solver};
use std::io::Write;
use std::path::Path;

fn write_stderr(message: &str) {
    let _ = writeln!(std::io::stderr(), "{message}");
}

fn usage(bin: &str) {
    write_stderr(&format!("Usage: {bin} <input.cnf> <output.drat>"));
}

fn generate_drat(input: &Path, output: &Path) -> Result<(), String> {
    let dimacs = std::fs::read_to_string(input)
        .map_err(|e| format!("failed to read '{}': {e}", input.display()))?;
    let formula =
        parse_dimacs(&dimacs).map_err(|e| format!("failed to parse '{}': {e}", input.display()))?;

    let mut solver = Solver::with_proof(formula.num_vars, Vec::new());
    for clause in formula.clauses {
        solver.add_clause(clause);
    }

    match solver.solve().into_inner() {
        SatResult::Unsat(_) => {
            let proof_output = solver
                .take_proof_writer()
                .ok_or_else(|| "proof writer missing for UNSAT result".to_string())?;
            let proof = proof_output
                .into_vec()
                .map_err(|e| format!("proof I/O error during solve: {e}"))?;
            if proof.is_empty() {
                return Err("generated DRAT proof is empty".to_string());
            }
            std::fs::write(output, &proof)
                .map_err(|e| format!("failed to write '{}': {e}", output.display()))?;
            Ok(())
        }
        SatResult::Sat(_) => Err(format!("formula '{}' is SAT", input.display())),
        SatResult::Unknown => Err(format!("solver returned UNKNOWN for '{}'", input.display())),
        _ => unreachable!(),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 3 {
        usage(&args[0]);
        std::process::exit(2);
    }

    if let Err(err) = generate_drat(Path::new(&args[1]), Path::new(&args[2])) {
        write_stderr(&err);
        std::process::exit(1);
    }
}
