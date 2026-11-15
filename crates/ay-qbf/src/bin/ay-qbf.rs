// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

use std::fs;
use std::path::Path;
use std::process::ExitCode;

use ay_qbf::{parse_qdimacs, QbfResult, QbfSolver};

fn main() -> ExitCode {
    // FIRST statement of main: arm() re-execs this process under a kernel-held
    // memory bound, so anything above it is discarded work, and it sets an env
    // var (sound only while single-threaded). See crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();

    let args = std::env::args().skip(1).collect::<Vec<_>>();
    // Returning the status (rather than calling the diverging
    // `std::process::exit`) yields the same exit codes: 0/10/20, or 2 on error.
    let exit_code = run(args).unwrap_or_else(|message| {
        eprintln!("ERROR: {message}");
        2
    });
    ExitCode::from(exit_code)
}

fn run(args: Vec<String>) -> Result<u8, String> {
    if args == ["--version"] || args == ["-V"] {
        println!("ay-qbf {}", env!("CARGO_PKG_VERSION"));
        return Ok(0);
    }

    let file = match args.as_slice() {
        [cmd, subcmd, file] if cmd == "qbf" && subcmd == "solve" => file,
        [subcmd, file] if subcmd == "solve" => file,
        [file] if !file.starts_with('-') => file,
        _ => return Err(usage()),
    };

    solve(Path::new(file))
}

fn usage() -> String {
    "usage: ay-qbf qbf solve FILE".to_string()
}

fn solve(path: &Path) -> Result<u8, String> {
    let input = fs::read_to_string(path)
        .map_err(|err| format!("failed to read '{}': {err}", path.display()))?;
    let formula = parse_qdimacs(&input)
        .map_err(|err| format!("failed to parse '{}': {err}", path.display()))?;
    let mut solver = QbfSolver::new(formula);

    match solver.solve() {
        QbfResult::Sat(_) => {
            println!("s TRUE");
            Ok(10)
        }
        QbfResult::Unsat(_) => {
            println!("s FALSE");
            Ok(20)
        }
        QbfResult::Unknown => {
            println!("s UNKNOWN");
            Ok(0)
        }
    }
}
