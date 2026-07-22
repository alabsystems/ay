// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! String theory verification tests (Phase A + Phase B integration).
//!
//! Phase A (#3294): logic detection, frontend typing, executor dispatch.
//! Phase B (#3319): QF_S routes through StringSolver (constant conflicts,
//! cycle detection, disequality checking). QF_SLIA uses StringsLiaSolver
//! (Strings + EUF + LIA via Nelson-Oppen) with length axiom injection.
//!
//! See `known_ay_z3_mismatches` for QF_SLIA string+LIA correctness tests.

#[path = "string_theory_verification/advanced_solver/mod.rs"]
mod advanced_solver;
#[path = "string_theory_verification/core_solver.rs"]
mod core_solver;
#[path = "string_theory_verification/differential.rs"]
mod differential;
#[path = "string_theory_verification/extf_and_contains.rs"]
mod extf_and_contains;
#[path = "string_theory_verification/prover_audit.rs"]
mod prover_audit;
#[path = "string_theory_verification/routing.rs"]
mod routing;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

fn solve_or_error(smt: &str) -> Result<String, String> {
    let commands = match parse(smt) {
        Ok(c) => c,
        Err(e) => return Err(format!("parse error: {e}")),
    };
    let mut exec = Executor::new();
    match exec.execute_all(&commands) {
        Ok(outputs) => Ok(outputs.join("\n")),
        Err(e) => Err(format!("{e}")),
    }
}

/// Solve with a per-case timeout. Returns Ok("unknown") on timeout.
fn solve_with_timeout(smt: &str, timeout_secs: u64) -> Result<String, String> {
    let commands = parse(smt).map_err(|e| format!("parse error: {e}"))?;
    let mut exec = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    exec.set_interrupt(Arc::clone(&interrupt));

    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer = std::thread::spawn(move || {
        if cancel_rx
            .recv_timeout(Duration::from_secs(timeout_secs))
            .is_err()
        {
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    let result = exec.execute_all(&commands);
    let timed_out = interrupt.load(Ordering::Relaxed);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    if timed_out {
        Ok("unknown".to_string())
    } else {
        result
            .map(|outputs| outputs.join("\n"))
            .map_err(|e| format!("{e}"))
    }
}

fn z3_available() -> bool {
    Command::new("z3")
        .arg("--version")
        .output()
        .map(|output| output.status.success())
        .unwrap_or(false)
}

fn solve_with_z3(smt: &str) -> Result<String, String> {
    let mut child = Command::new("z3")
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| format!("failed to spawn z3: {e}"))?;

    if let Some(stdin) = child.stdin.as_mut() {
        stdin
            .write_all(smt.as_bytes())
            .map_err(|e| format!("failed to write SMT to z3 stdin: {e}"))?;
    }

    let output = child
        .wait_with_output()
        .map_err(|e| format!("failed waiting for z3: {e}"))?;
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        return Err(format!("z3 exited with status {}: {stderr}", output.status));
    }
    Ok(String::from_utf8_lossy(&output.stdout).to_string())
}
