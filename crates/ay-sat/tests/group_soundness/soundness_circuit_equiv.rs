// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for circuit equivalence benchmarks (eq.atree.braun family).
//!
//! These are known-UNSAT benchmarks encoding non-equivalence of Braun tree
//! adder circuits. Any SAT result is a soundness bug. UNKNOWN (timeout) is
//! acceptable for harder instances.
//!
//! Regression coverage for the BVE restricted resolution soundness bug
//! (e0dc2c277) where kitten-based semantic gate definitions caused gate
//! clauses to be dropped from resolution.
//!
//! Extended with:
//! - Complete UNSAT corpus (27 benchmarks)
//! - Inprocessing configuration matrix (BVE-only, sweep-only, etc.)
//! - FINALIZE_SAT_FAIL (InvalidSatModel) audit tests (#7917)

#![allow(clippy::panic)]

use ay_sat::{parse_dimacs, SatResult, SatUnknownReason, Solver};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

// ---------------------------------------------------------------------------
// Core assertion helpers
// ---------------------------------------------------------------------------

fn spawn_interrupt_timer(flag: &Arc<AtomicBool>, timeout_secs: u64) -> std::thread::JoinHandle<()> {
    let flag_clone = flag.clone();
    std::thread::spawn(move || {
        let deadline = Instant::now() + Duration::from_secs(timeout_secs);
        while !flag_clone.load(Ordering::Relaxed) {
            let now = Instant::now();
            if now >= deadline {
                flag_clone.store(true, Ordering::Relaxed);
                break;
            }
            std::thread::sleep((deadline - now).min(Duration::from_millis(10)));
        }
    })
}

fn load_optional_benchmark(path: &str, label: &str) -> Option<String> {
    let cnf = super::common::load_optional_repo_benchmark(path);
    if cnf.is_none() {
        eprintln!("SKIP: {label} benchmark not available at {path}");
    }
    cnf
}

/// Run a known-UNSAT benchmark with a timeout. Panics on SAT (soundness bug).
/// UNSAT and UNKNOWN (timeout) are both acceptable.
fn assert_not_sat(path: &str, label: &str, timeout_secs: u64) {
    let Some(cnf) = load_optional_benchmark(path, label) else {
        return;
    };
    let formula = parse_dimacs(&cnf).expect("parse");

    let mut solver = formula.into_solver();

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let handle = spawn_interrupt_timer(&flag, timeout_secs);

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    match result {
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {label} is known-UNSAT but solver returned SAT");
        }
        SatResult::Unsat(_) => {
            // Correct.
        }
        SatResult::Unknown => {
            eprintln!("{label}: timeout (Unknown) -- performance gap, not soundness bug");
        }
        _ => unreachable!(),
    }
}

/// Run a known-UNSAT benchmark and require UNSAT (not just "not SAT").
fn assert_unsat(path: &str, label: &str, timeout_secs: u64) {
    let Some(cnf) = load_optional_benchmark(path, label) else {
        return;
    };
    let formula = parse_dimacs(&cnf).expect("parse");

    let mut solver = formula.into_solver();

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let handle = spawn_interrupt_timer(&flag, timeout_secs);

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    match result {
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {label} is known-UNSAT but solver returned SAT");
        }
        SatResult::Unsat(_) => {
            // Correct.
        }
        SatResult::Unknown => {
            panic!("PERFORMANCE REGRESSION: {label} should solve within {timeout_secs}s but returned Unknown");
        }
        _ => unreachable!(),
    }
}

fn assert_gate_extraction_unsat(path: &str, label: &str, timeout_secs: u64) {
    let cnf = super::common::load_repo_benchmark(path);
    let formula = parse_dimacs(&cnf).expect("parse");
    let original_clauses = formula.clauses.clone();

    let mut solver = formula.into_solver();
    solver.set_bve_enabled(true);
    solver.set_gate_enabled(true);
    solver.set_congruence_enabled(true);

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let handle = spawn_interrupt_timer(&flag, timeout_secs);

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    match result {
        SatResult::Unsat(_) => {}
        SatResult::Sat(model) => {
            let violated = original_clauses
                .iter()
                .position(|clause| {
                    !clause.iter().any(|lit| {
                        let var_idx = lit.variable().index();
                        let var_value = model.get(var_idx).copied().unwrap_or(false);
                        if lit.is_positive() {
                            var_value
                        } else {
                            !var_value
                        }
                    })
                })
                .map_or_else(|| "none".to_string(), |idx| idx.to_string());
            panic!(
                "SOUNDNESS BUG: {label} is known-UNSAT but gate-aware solver returned SAT \
                 (first violated original clause: {violated})"
            );
        }
        SatResult::Unknown => {
            panic!(
                "PERFORMANCE REGRESSION: gate-aware solver returned Unknown on {label} within {timeout_secs}s"
            );
        }
        #[allow(unreachable_patterns)]
        _ => unreachable!(),
    }

    let total_gates = solver.gate_stats().total_gates();
    let gates_analyzed = solver.congruence_stats().gates_analyzed;
    if total_gates == 0 && gates_analyzed == 0 {
        eprintln!(
            "{label}: solved before gate extraction/congruence ran; correctness checked by UNSAT result"
        );
    }
}

// ---------------------------------------------------------------------------
// Inprocessing configuration variants (#7904)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Copy)]
enum InprocConfig {
    NoInprocessing,
    BveOnly,
    SweepOnly,
    CongruenceOnly,
    BveAndGate,
    BveSweepCongruence,
    AllEnabled,
}

impl InprocConfig {
    fn label(self) -> &'static str {
        match self {
            Self::NoInprocessing => "no-inproc",
            Self::BveOnly => "bve-only",
            Self::SweepOnly => "sweep-only",
            Self::CongruenceOnly => "cong-only",
            Self::BveAndGate => "bve+gate",
            Self::BveSweepCongruence => "bve+sweep+cong",
            Self::AllEnabled => "all-enabled",
        }
    }

    fn configure(self, solver: &mut Solver) {
        match self {
            Self::NoInprocessing => {
                super::common::disable_all_inprocessing(solver);
            }
            Self::BveOnly => {
                super::common::disable_all_inprocessing(solver);
                solver.set_bve_enabled(true);
            }
            Self::SweepOnly => {
                super::common::disable_all_inprocessing(solver);
                solver.set_sweep_enabled(true);
            }
            Self::CongruenceOnly => {
                super::common::disable_all_inprocessing(solver);
                solver.set_congruence_enabled(true);
            }
            Self::BveAndGate => {
                super::common::disable_all_inprocessing(solver);
                solver.set_bve_enabled(true);
                solver.set_gate_enabled(true);
            }
            Self::BveSweepCongruence => {
                super::common::disable_all_inprocessing(solver);
                solver.set_bve_enabled(true);
                solver.set_sweep_enabled(true);
                solver.set_congruence_enabled(true);
            }
            Self::AllEnabled => {}
        }
    }
}

const ALL_CONFIGS: [InprocConfig; 7] = [
    InprocConfig::NoInprocessing,
    InprocConfig::BveOnly,
    InprocConfig::SweepOnly,
    InprocConfig::CongruenceOnly,
    InprocConfig::BveAndGate,
    InprocConfig::BveSweepCongruence,
    InprocConfig::AllEnabled,
];

/// Returns true if FINALIZE_SAT_FAIL (InvalidSatModel) was detected.
fn assert_not_sat_with_config(
    path: &str,
    label: &str,
    timeout_secs: u64,
    config: InprocConfig,
) -> bool {
    let Some(cnf) = load_optional_benchmark(path, label) else {
        return false;
    };
    let formula = parse_dimacs(&cnf).expect("parse");

    let mut solver = formula.into_solver();
    config.configure(&mut solver);

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let handle = spawn_interrupt_timer(&flag, timeout_secs);

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    let config_label = config.label();
    let full_label = format!("{label}[{config_label}]");

    let is_finalize_sat_fail = matches!(result, SatResult::Unknown)
        && solver.last_unknown_reason() == Some(SatUnknownReason::InvalidSatModel);

    match result {
        SatResult::Sat(_) => {
            panic!("SOUNDNESS BUG: {full_label} is known-UNSAT but solver returned SAT");
        }
        SatResult::Unsat(_) => {}
        SatResult::Unknown => {
            if is_finalize_sat_fail {
                eprintln!(
                    "FINALIZE_SAT_FAIL: {full_label} returned Unknown with InvalidSatModel reason"
                );
            } else {
                eprintln!("{full_label}: timeout (Unknown) -- performance gap, not soundness bug");
            }
        }
        _ => unreachable!(),
    }

    is_finalize_sat_fail
}

const SMALL_UNSAT_SUBSET: &[&str] = &[
    "benchmarks/sat/unsat/at_most_1_of_5.cnf",
    "benchmarks/sat/unsat/blocked_chain_8.cnf",
    "benchmarks/sat/unsat/cardinality_8.cnf",
    "benchmarks/sat/unsat/double_parity_5.cnf",
    "benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf",
    "benchmarks/sat/unsat/graph_coloring_k4_5clique.cnf",
    "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
    "benchmarks/sat/unsat/mutex_4proc.cnf",
    "benchmarks/sat/unsat/mutex_6proc.cnf",
    "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
    "benchmarks/sat/unsat/ordering_cycle_5.cnf",
    "benchmarks/sat/unsat/parity_6.cnf",
    "benchmarks/sat/unsat/php_4_3.cnf",
    "benchmarks/sat/unsat/php_5_4.cnf",
    "benchmarks/sat/unsat/resolution_chain_12.cnf",
];

include!("soundness_circuit_equiv/braun_and_small_corpus.rs");

/// Run `assert_not_sat` on a thread with an adequate stack (matching the solver
/// binary's main thread) — large UNSAT instances drive recursive clause
/// minimization deeper than the 2 MB default test-thread stack.
fn assert_not_sat_on_big_stack(path: &'static str, label: &'static str, timeout_secs: u64) {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || assert_not_sat(path, label, timeout_secs))
        .unwrap_or_else(|e| panic!("spawn {label} soundness thread: {e}"))
        .join()
        .unwrap_or_else(|_| panic!("{label} soundness thread panicked"));
}

include!("soundness_circuit_equiv/satcomp_configuration_and_audit.rs");
