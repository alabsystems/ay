// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Additive compound wakeup trace harness for #6579.
//!
//! Runs sc-6 (green control) and sc-21 (red target) with `--stats` to
//! capture compound wakeup counters from the LRA solver's statistics output.
//!
//! The test extracts `lra_simplex_sat`, `lra_compound_use_vars`,
//! `lra_compound_wake_dirty_hits`, `lra_compound_wake_candidates`, and
//! `lra_compound_queued` from the SMT-LIB `:statistics` section.
//!
//! Part of #6579

use std::collections::HashMap;
use std::process::Command;

struct TraceRun {
    result: String,
    stats: HashMap<String, u64>,
}

#[derive(Clone, Copy)]
struct CompoundStats {
    simplex_sat: u64,
    compound_use_vars: u64,
    wake_dirty_hits: u64,
    wake_candidates: u64,
    compound_queued: u64,
}

fn workspace_root() -> String {
    format!("{}/../../", env!("CARGO_MANIFEST_DIR"))
}

fn run_ay_stats(benchmark: &str, timeout_secs: u64) -> Option<TraceRun> {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let benchmark_path = format!(
        "{}benchmarks/smtcomp/QF_LRA/{}",
        workspace_root(),
        benchmark
    );
    if !std::path::Path::new(&benchmark_path).exists() {
        eprintln!("SKIP: optional SMT-COMP benchmark not found: {benchmark_path}");
        return None;
    }

    let output = Command::new("timeout")
        .arg(format!("{timeout_secs}"))
        .arg(ay_path)
        .arg("--stats")
        .arg(&benchmark_path)
        .output()
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();

    // Extract result (first non-empty line of stdout)
    let result = stdout
        .lines()
        .find(|l| !l.trim().is_empty())
        .unwrap_or("timeout")
        .trim()
        .to_string();

    // Extract stats from SMT-LIB :statistics output on stderr.
    // Format: "  :key value" (inside (:statistics ...) block)
    let mut stats = HashMap::new();
    for line in stderr.lines() {
        let trimmed = line.trim();
        if let Some(rest) = trimmed.strip_prefix(':') {
            let parts: Vec<&str> = rest.splitn(2, ' ').collect();
            if parts.len() == 2 {
                if let Ok(val) = parts[1].trim().parse::<u64>() {
                    stats.insert(parts[0].to_string(), val);
                }
            }
        }
    }

    Some(TraceRun { result, stats })
}

fn read_compound_stats(stats: &HashMap<String, u64>) -> CompoundStats {
    CompoundStats {
        simplex_sat: stats.get("lra_simplex_sat").copied().unwrap_or(0),
        compound_use_vars: stats.get("lra_compound_use_vars").copied().unwrap_or(0),
        wake_dirty_hits: stats
            .get("lra_compound_wake_dirty_hits")
            .copied()
            .unwrap_or(0),
        wake_candidates: stats
            .get("lra_compound_wake_candidates")
            .copied()
            .unwrap_or(0),
        compound_queued: stats.get("lra_compound_queued").copied().unwrap_or(0),
    }
}

fn emit_sc21_trace(result: &str, raw_stats: &HashMap<String, u64>, stats: CompoundStats) {
    eprintln!("[#6579 trace] sc-21: result={result}");
    if raw_stats.is_empty() {
        eprintln!("[#6579 trace] sc-21: statistics unavailable from `--stats` output");
        return;
    }

    eprintln!(
        "[#6579 trace] sc-21: simplex_sat={}, compound_use_vars={}, \
         wake_dirty_hits={}, wake_candidates={}, compound_queued={}",
        stats.simplex_sat,
        stats.compound_use_vars,
        stats.wake_dirty_hits,
        stats.wake_candidates,
        stats.compound_queued
    );
}

fn emit_sc21_finding(result: &str, raw_stats: &HashMap<String, u64>, stats: CompoundStats) {
    // Routing diagnostic based on the adopted #6585 direct-bound wake packet.
    if result == "timeout" || result.is_empty() {
        // Stats are not available on timeout (solver killed before printing).
        // Fall back to the AY_DEBUG_LRA=1 evidence plus the executor-side
        // measurement packet recorded in the development design notes
        // additive-trace-routing.md.
        eprintln!(
            "[#6579 FINDING] TIMEOUT — no stats available. \
             Manual investigation with AY_DEBUG_LRA=1 and the executor-side \
             measurement both show simplex never reaches Sat on sc-21 while \
             compound atoms are already registered. \
             ROUTING: #6585 — direct-bound compound wakeups on the \
             TheoryResult::Unknown branch."
        );
    } else if raw_stats.is_empty() {
        eprintln!(
            "[#6579 FINDING] STATS MISSING — solver returned `{result}` without \
             a `:statistics` block, so counter-based routing is not trustworthy. \
             Re-run with the executor-side measurement path before classifying \
             this lane."
        );
    } else if stats.simplex_sat == 0 {
        eprintln!(
            "[#6579 FINDING] ARCHITECTURAL DEAD PATH (variant of Case 4): \
             simplex_sat=0 means the post-simplex compound wakeup path never executed. \
             Compound machinery is structurally sound (see sc-6) but unreachable \
             when simplex never reaches Sat on this path. \
             ROUTING: #6585 — direct-bound compound wakeups on the \
             TheoryResult::Unknown branch."
        );
    } else if stats.compound_use_vars == 0 {
        eprintln!(
            "[#6579 FINDING] REGISTRATION GAP (Case 1): compound_use_vars=0. \
             Fix: investigate atom registration for compound_use_index population."
        );
    } else if stats.wake_dirty_hits == 0 {
        eprintln!(
            "[#6579 FINDING] DIRTY-VAR WAKE GAP (Case 2): \
             compound_use_vars={} but wake_dirty_hits=0. \
             Fix: investigate dirty-var seeding in post-simplex path.",
            stats.compound_use_vars
        );
    } else if stats.compound_queued == 0 {
        eprintln!(
            "[#6579 FINDING] CANDIDATE REJECTION GAP (Case 3): \
             wake_dirty_hits={}, wake_candidates={}, but compound_queued=0. \
             Fix: investigate try_queue_compound_propagation() rejection logic.",
            stats.wake_dirty_hits, stats.wake_candidates
        );
    } else {
        eprintln!(
            "[#6579 FINDING] TIMING/SPLIT-LOOP GAP (Case 4): \
             compound_queued={} — wakeups exist. ROUTING: #6503/#4919.",
            stats.compound_queued
        );
    }
}

/// Trace sc-6 (green control benchmark) compound wakeup counters.
///
/// sc-6 is the green control benchmark for the #6579 harness.
#[test]
#[ntest::timeout(90_000)]
fn test_sc6_additive_trace_6579() {
    // The release-path regression is fixed, but the test-profile binary built
    // for integration tests is materially slower than `cargo build --release`.
    let Some(trace) = run_ay_stats("sc-6.induction3.cvc.smt2", 60) else {
        return;
    };
    let result = trace.result;
    let stats = read_compound_stats(&trace.stats);
    // sc-6 is SAT per Z3 (597 decisions with LP-based bound propagation).
    // AY currently returns "unknown" because it lacks Z3's arith-bound-propagations-lp
    // feature (731 LP propagations in Z3 vs 0 in AY), causing AY to need 25K+
    // decisions and give up after 37 split-loop round trips. Accept both results
    // until LP-based bound propagation is implemented.
    assert!(
        result == "sat" || result == "unknown" || result == "timeout",
        "sc-6 should return sat or unknown (pending LP-based bound propagation), got: {result}"
    );

    eprintln!(
        "[#6579 trace] sc-6: result={result}, stats_count={}",
        trace.stats.len()
    );
    eprintln!(
        "[#6579 trace] sc-6: simplex_sat={}, compound_use_vars={}, wake_dirty_hits={}, \
         wake_candidates={}, compound_queued={}",
        stats.simplex_sat,
        stats.compound_use_vars,
        stats.wake_dirty_hits,
        stats.wake_candidates,
        stats.compound_queued
    );

    // When the solver reaches SAT, verify compound registration is active.
    if result == "sat" {
        assert!(
            stats.compound_use_vars > 0,
            "sc-6 should have compound atoms registered (compound_use_vars={})",
            stats.compound_use_vars
        );
        assert!(
            stats.simplex_sat > 0,
            "sc-6 should have at least one SAT simplex result (simplex_sat={})",
            stats.simplex_sat
        );
    }
}

/// Trace sc-21 (red target benchmark) compound wakeup counters.
///
/// sc-21 is expected to be sat (per Z3) but AY times out. This test
/// captures the compound wakeup state to diagnose why.
#[test]
#[ntest::timeout(30_000)]
fn test_sc21_additive_trace_6579() {
    let Some(trace) = run_ay_stats("sc-21.induction2.cvc.smt2", 10) else {
        return;
    };
    let result = trace.result;
    let stats = read_compound_stats(&trace.stats);

    emit_sc21_trace(&result, &trace.stats, stats);
    emit_sc21_finding(&result, &trace.stats, stats);

    // We don't assert sat because sc-21 is a known timeout. Just capture data.
    assert!(
        result == "sat" || result == "unknown" || result == "timeout" || result.is_empty(),
        "sc-21 unexpected result: {result}"
    );
}
