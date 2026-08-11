// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::fs;
use std::path::Path;

use ay_qbf::{parse_qdimacs, QbfResult, QbfSolver};

fn main() {
    // FIRST statement of main: arm() re-execs this process under a kernel-held
    // memory bound, so anything above it is discarded work, and it sets an env
    // var (sound only while single-threaded). See crates/ay-sys/src/govern.rs.
    ay_sys::govern::arm();

    let args = std::env::args().skip(1).collect::<Vec<_>>();
    match run(args) {
        Ok(exit_code) => std::process::exit(exit_code),
        Err(message) => {
            eprintln!("ERROR: {message}");
            std::process::exit(2);
        }
    }
}

fn run(args: Vec<String>) -> Result<i32, String> {
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

fn solve(path: &Path) -> Result<i32, String> {
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
