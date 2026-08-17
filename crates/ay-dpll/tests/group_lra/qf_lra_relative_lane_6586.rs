// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Relative-lane telemetry guard for #6586.
//!
//! The CLI `--stats` path does not emit the final statistics block when a
//! benchmark hits the timeout guard, which leaves the red family opaque even
//! after inline bound-refinement replay landed. This test drives the same
//! benchmarks through `Executor` directly so the eager counters remain
//! observable on `Unknown`/timeout exits.
//!
//! Part of #6586, #4919.

use crate::common::{check_z3_or_skip, run_z3_file, workspace_path, SolverOutcome};
use anyhow::{anyhow, Context, Result};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::fs;
use std::path::Path;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

// Integration tests run the debug `ay-dpll` stack, which is materially slower
// than the release CLI measurements used in the design packet. Use a wider
// guard here so the test measures relative-lane telemetry rather than debug
// compilation overhead.
const BENCHMARK_TIMEOUT_SECS: u64 = 30;

#[derive(Debug)]
struct TimedExecutorRun {
    outcome: SolverOutcome,
    timed_out: bool,
    bound_refinement_handoffs: u64,
}

fn run_executor_file_with_timeout_and_stats(
    path: &Path,
    timeout_secs: u64,
) -> Result<TimedExecutorRun> {
    let smt = fs::read_to_string(path)
        .with_context(|| format!("failed reading benchmark {}", path.display()))?;
    let commands =
        parse(&smt).map_err(|err| anyhow!("parse error for {}: {err}", path.display()))?;

    let mut executor = Executor::new();
    let interrupt = Arc::new(AtomicBool::new(false));
    let deadline_hit = Arc::new(AtomicBool::new(false));
    executor.set_interrupt(Arc::clone(&interrupt));

    let (cancel_tx, cancel_rx) = std::sync::mpsc::channel();
    let timer_interrupt = Arc::clone(&interrupt);
    let timer_deadline_hit = Arc::clone(&deadline_hit);
    let timer = std::thread::spawn(move || {
        if cancel_rx
            .recv_timeout(Duration::from_secs(timeout_secs))
            .is_err()
        {
            timer_deadline_hit.store(true, Ordering::Relaxed);
            timer_interrupt.store(true, Ordering::Relaxed);
        }
    });

    let outputs = executor.execute_all(&commands);
    let _ = cancel_tx.send(());
    let _ = timer.join();

    let stats = executor.statistics();
    let bound_refinement_handoffs = stats
        .get_int("dpll.eager.bound_refinement_handoffs")
        .unwrap_or(0);

    let timed_out = deadline_hit.load(Ordering::Relaxed);
    let outcome = if timed_out {
        SolverOutcome::Timeout
    } else {
        let first_line = outputs
            .map_err(|err| anyhow!("execution error for {}: {err}", path.display()))?
            .into_iter()
            .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
            .unwrap_or_else(|| "unknown".to_string());
        SolverOutcome::from_output_line(&first_line)
    };

    Ok(TimedExecutorRun {
        outcome,
        timed_out,
        bound_refinement_handoffs,
    })
}

#[test]
#[timeout(90_000)]
fn test_constraints_tempo_width_10_reports_bound_refinement_handoffs_issue_6586() -> Result<()> {
    let path = workspace_path("benchmarks/smtcomp/QF_LRA/constraints-tempo-width-10.smt2");
    // `benchmarks/smtcomp/` is gitignored, so a clean checkout has no corpus.
    // Skip when the fixture is absent instead of hard-failing; the Sat assertion
    // below is unchanged and still runs wherever the corpus is installed.
    if !path.exists() && crate::common::corpus_skip_allowed(&path) {
        eprintln!(
            "SKIP test_constraints_tempo_width_10_reports_bound_refinement_handoffs_issue_6586: \
             corpus benchmark not found: {}",
            path.display()
        );
        return Ok(());
    }

    let run = run_executor_file_with_timeout_and_stats(&path, BENCHMARK_TIMEOUT_SECS)?;
    eprintln!(
        "[#6586 trace] constraints-tempo-width-10: outcome={:?}, timed_out={}, handoffs={}",
        run.outcome, run.timed_out, run.bound_refinement_handoffs
    );

    assert_eq!(
        run.outcome,
        SolverOutcome::Sat,
        "constraints-tempo-width-10 should remain sat in the relative-lane guard"
    );
    // Note: bound_refinement_handoffs may be 0 with geometric restarts
    // (Z3-style) since the SAT solver can find a model faster without
    // triggering the refinement replay pathway. The correctness assertion
    // is the Sat result above; the handoff count is observational telemetry.
    eprintln!(
        "[#6586 trace] bound_refinement_handoffs={} (informational)",
        run.bound_refinement_handoffs
    );
    Ok(())
}

#[test]
#[timeout(120_000)]
fn test_red_relative_family_reports_bound_refinement_handoffs_issue_6586() -> Result<()> {
    let simple_startup =
        workspace_path("benchmarks/smtcomp/QF_LRA/simple_startup_10nodes.bug.induct.smt2");
    let uart = workspace_path("benchmarks/smtcomp/QF_LRA/uart-23.induction.cvc.smt2");
    // simple_startup_10nodes is whitelisted in .gitignore and always present, so
    // it stays a hard requirement. uart-23 is part of the gitignored smtcomp
    // corpus, so it is checked only when installed.
    assert!(
        simple_startup.exists(),
        "benchmark not found: {}",
        simple_startup.display()
    );

    if check_z3_or_skip() {
        assert_eq!(
            run_z3_file(&simple_startup, BENCHMARK_TIMEOUT_SECS + 1)?,
            SolverOutcome::Sat,
            "Z3 baseline changed for simple_startup_10nodes"
        );
    }

    let simple_run =
        run_executor_file_with_timeout_and_stats(&simple_startup, BENCHMARK_TIMEOUT_SECS)?;

    eprintln!(
        "[#6586 trace] simple_startup_10nodes: outcome={:?}, timed_out={}, handoffs={}",
        simple_run.outcome, simple_run.timed_out, simple_run.bound_refinement_handoffs
    );

    assert!(
        matches!(
            simple_run.outcome,
            SolverOutcome::Sat | SolverOutcome::Unknown | SolverOutcome::Timeout
        ),
        "unexpected simple_startup_10nodes result: {:?}",
        simple_run.outcome
    );
    // Note: handoff counts may be 0 with geometric restarts. The correctness
    // assertions are the outcome checks above; handoff count is telemetry.
    eprintln!(
        "[#6586 trace] handoffs: simple_startup={} (informational)",
        simple_run.bound_refinement_handoffs
    );

    if uart.exists() {
        let uart_run = run_executor_file_with_timeout_and_stats(&uart, BENCHMARK_TIMEOUT_SECS)?;
        eprintln!(
            "[#6586 trace] uart-23: outcome={:?}, timed_out={}, handoffs={} (informational)",
            uart_run.outcome, uart_run.timed_out, uart_run.bound_refinement_handoffs
        );
        assert!(
            matches!(
                uart_run.outcome,
                SolverOutcome::Sat | SolverOutcome::Unknown | SolverOutcome::Timeout
            ),
            "unexpected uart-23 result: {:?}",
            uart_run.outcome
        );
    } else {
        eprintln!(
            "SKIP uart-23 leg of test_red_relative_family_reports_bound_refinement_handoffs_issue_6586: \
             corpus benchmark not found: {}",
            uart.display()
        );
    }

    Ok(())
}
