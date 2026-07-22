// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
//! Minimal SMT-LIB2 runner for differential soundness sweeps.
//!
//! Bypasses the full `ay` CLI (which pulls ay-pb/ay-maxsat) so soundness
//! sweeps can run even when those crates are mid-WIP. Reads an .smt2 file,
//! parses it, runs the executor, and prints the ordered sat/unsat/unknown
//! answers (one per line) — the same surface a differential harness compares.
//!
//!   cargo run -p ay-dpll --example smt_run --release -- path/to/file.smt2

use std::io::Write;

fn main() {
    let path = match std::env::args().nth(1) {
        Some(p) => p,
        None => {
            eprintln!("usage: smt_run <file.smt2>");
            std::process::exit(2);
        }
    };
    let input = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("read error: {e}");
            std::process::exit(2);
        }
    };
    let commands = match ay_frontend::parse(&input) {
        Ok(c) => c,
        Err(e) => {
            // Emit nothing on stdout; a harness records this as a parse error.
            eprintln!("parse error: {e:?}");
            std::process::exit(3);
        }
    };
    let mut exec = ay_dpll::Executor::new();
    let all = std::env::var_os("AY_SMT_RUN_ALL").is_some();
    let stdout = std::io::stdout();
    let mut w = stdout.lock();
    // Stream per-command and flush each answer immediately. The previous
    // `execute_all` buffered every output and only printed after the WHOLE file
    // finished — so on a timeout (long QF_LRA k-induction files have 100+
    // check-sats) the partial answers were lost, making a slow-but-progressing
    // solve look like zero output. Per-command streaming mirrors the real `ay`
    // CLI / z3 and lets a harness see how many check-sats completed before a cap.
    for cmd in &commands {
        match exec.execute(cmd) {
            Ok(Some(o)) => {
                if all || matches!(o.as_str(), "sat" | "unsat" | "unknown") {
                    let _ = writeln!(w, "{o}");
                    let _ = w.flush();
                }
            }
            Ok(None) => {}
            Err(e) => {
                eprintln!("execute error: {e:?}");
                std::process::exit(4);
            }
        }
    }
}
