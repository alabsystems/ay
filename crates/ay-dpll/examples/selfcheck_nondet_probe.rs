// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Repeat one SMT-LIB file N times in ONE process with the certification
//! rejection probe armed, and print the VERDICT SEQUENCE.
//!
//! Companion to `verdict_determinism_probe`, which prints search counters. This
//! one is about the CERTIFICATION outcome: which funnel gate refused, and with
//! what budget left.
//!
//! Usage:
//!   selfcheck_nondet_probe FILE [ITERATIONS] [TIMEOUT_MS]
//!
//! `TIMEOUT_MS > 0` installs an executor timeout, mirroring the embedder
//! (deductive-checks hands ay a 30_000 ms nominal budget through `with_limits`).

use std::time::Duration;

fn main() {
    let mut args = std::env::args().skip(1);
    let path = args
        .next()
        .expect("usage: selfcheck_nondet_probe FILE [N] [TIMEOUT_MS] [MEMORY_MB]");
    let iterations: usize = args.next().and_then(|a| a.parse().ok()).unwrap_or(10);
    let timeout_ms: u64 = args.next().and_then(|a| a.parse().ok()).unwrap_or(0);
    let memory_mb: usize = args.next().and_then(|a| a.parse().ok()).unwrap_or(0);

    // `set_global_misc_cli_flags_with` is documented as the library seam for the
    // diagnostic carriers but is not re-exported from `ay_core`'s root, so use
    // the thread-local override; the solves below run on this thread.
    let installed = std::env::var_os("PROBE").is_some();
    let mut flags = ay_core::misc_cli_flags().clone();
    flags.probe_cert_reject = installed;
    let _probe_guard = ay_core::misc_test_override::set(flags);

    let input = std::fs::read_to_string(&path).expect("readable SMT-LIB2 file");
    let commands = ay_frontend::parse(&input).expect("parseable SMT-LIB2 file");

    let mut verdicts: Vec<String> = Vec::with_capacity(iterations);
    let mut millis: Vec<u128> = Vec::with_capacity(iterations);
    for _ in 0..iterations {
        let mut executor = ay_dpll::Executor::new();
        if timeout_ms > 0 {
            executor.set_timeout(Some(Duration::from_millis(timeout_ms)));
        }
        if memory_mb > 0 {
            executor.set_memory_limit(Some(memory_mb * 1024 * 1024));
        }
        let started = std::time::Instant::now();
        let mut answers: Vec<String> = Vec::new();
        for command in &commands {
            match executor.execute(command) {
                Ok(Some(output)) => {
                    if matches!(output.as_str(), "sat" | "unsat" | "unknown") {
                        answers.push(output);
                    }
                }
                Ok(None) => {}
                Err(error) => {
                    answers.push(format!("error:{error:?}"));
                    break;
                }
            }
        }
        let stats = executor.statistics();
        let reason = stats
            .get_string("unknown.reason")
            .unwrap_or("-")
            .to_string();
        millis.push(started.elapsed().as_millis());
        verdicts.push(format!("{}[{reason}]", answers.join(",")));
    }

    println!("TESTS_RAN {}", verdicts.len());
    println!(
        "FILE {path} TIMEOUT_MS {timeout_ms} PROBE_INSTALLED {installed} PROBE {}",
        std::env::var_os("PROBE").is_some()
    );
    for (i, verdict) in verdicts.iter().enumerate() {
        println!("  solve {i:>3}: {verdict:<48} {:>7}ms", millis[i]);
    }
    let distinct: std::collections::BTreeSet<&String> = verdicts.iter().collect();
    println!("SEQUENCE {}", verdicts.join(" "));
    println!("DISTINCT_VERDICTS {}", distinct.len());
    println!(
        "VERDICT_DRIFT {}",
        if distinct.len() > 1 { "yes" } else { "no" }
    );
}
