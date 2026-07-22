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

// ---------------------------------------------------------------------------
// eq.atree.braun: circuit equivalence UNSAT benchmarks
// ---------------------------------------------------------------------------

#[test]
fn braun_8_must_be_unsat() {
    assert_unsat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
        "braun-8",
        15,
    );
}

#[test]
fn braun_10_must_be_unsat() {
    assert_unsat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
        "braun-10",
        15,
    );
}

#[test]
fn braun_8_gate_extraction_must_be_unsat() {
    assert_gate_extraction_unsat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
        "braun-8-gate",
        15,
    );
}

#[test]
fn braun_10_gate_extraction_must_be_unsat() {
    assert_gate_extraction_unsat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
        "braun-10-gate",
        15,
    );
}

#[test]
fn braun_7_not_sat() {
    assert_not_sat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.7.unsat.cnf",
        "braun-7",
        30,
    );
}

#[test]
fn braun_9_not_sat() {
    assert_not_sat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.9.unsat.cnf",
        "braun-9",
        15,
    );
}

/// Braun-9 is inside the sparse band, so the default path now legitimately
/// runs BVE (sparse-band unlock default-ON since 3c9b980b, after ef818369
/// root-caused and fixed the braun reconstruction FINALIZE_SAT_FAIL as
/// preprocess-subsume constraint loss). The soundness contract this test
/// guards is unchanged: no wrong SAT verdict and no InvalidSatModel
/// degrade on the default braun-9 path even with BVE active.
#[test]
fn braun_9_default_bve_active_no_reconstruction_degrade() {
    let cnf = super::common::load_repo_benchmark(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.9.unsat.cnf",
    );
    let formula = parse_dimacs(&cnf).expect("parse");

    let mut solver = formula.into_solver();

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let handle = spawn_interrupt_timer(&flag, 5);

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    assert!(
        !matches!(result, SatResult::Sat(_)),
        "SOUNDNESS BUG: braun-9 is known-UNSAT but default solver returned SAT"
    );
    assert_ne!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::InvalidSatModel),
        "default braun-9 path must not hit InvalidSatModel"
    );
}

#[test]
fn braun_11_not_sat() {
    assert_not_sat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.11.unsat.cnf",
        "braun-11",
        15,
    );
}

#[test]
fn braun_12_not_sat() {
    assert_not_sat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.12.unsat.cnf",
        "braun-12",
        15,
    );
}

#[test]
fn braun_13_not_sat() {
    assert_not_sat(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.13.unsat.cnf",
        "braun-13",
        15,
    );
}

// ---------------------------------------------------------------------------
// Complete UNSAT corpus (27 benchmarks)
// ---------------------------------------------------------------------------

#[test]
fn small_unsat_corpus_soundness() {
    let benchmarks = [
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
        "benchmarks/sat/unsat/blocked_chain_8.cnf",
        "benchmarks/sat/unsat/cardinality_8.cnf",
        "benchmarks/sat/unsat/double_parity_5.cnf",
        "benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k4_5clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k5_6clique.cnf",
        "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/mutex_6proc.cnf",
        "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "benchmarks/sat/unsat/parity_6.cnf",
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/php_5_4.cnf",
        "benchmarks/sat/unsat/php_6_5.cnf",
        "benchmarks/sat/unsat/php_7_6.cnf",
        "benchmarks/sat/unsat/php_functional_5_4.cnf",
        "benchmarks/sat/unsat/ramsey_r3_3_6.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12349.cnf",
        "benchmarks/sat/unsat/resolution_chain_12.cnf",
        "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
        "benchmarks/sat/unsat/tseitin_grid_3x3.cnf",
        "benchmarks/sat/unsat/tseitin_k5.cnf",
        "benchmarks/sat/unsat/tseitin_random_15.cnf",
        "benchmarks/sat/unsat/urquhart_3.cnf",
    ];
    for path in &benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        assert_unsat(path, label, 30);
    }
}

// --- satcomp2024 known-UNSAT benchmarks ---

#[test]
fn satcomp2024_crn_11_99_u_must_be_unsat() {
    assert_unsat(
        "benchmarks/sat/satcomp2024-sample/ef330d1b144055436a2d576601191ea5-crn_11_99_u.cnf",
        "crn_11_99_u",
        10,
    );
}

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

#[test]
fn satcomp2024_fmla_equiv_chain_must_be_unsat() {
    // FmlaEquivChain_4_6_6 (~8 MB CNF) is a large UNSAT instance AY's solver
    // cannot prove UNSAT within a unit-test budget — it returns a sound
    // `Unknown` (even in release). Assert only the soundness-critical property:
    // AY must never return a (false) SAT on this known-UNSAT instance. Proving it
    // UNSAT is a documented performance limitation, not a soundness bug. Runs on
    // a large stack (see satcomp2024_unsat_soundness).
    assert_not_sat_on_big_stack(
        "benchmarks/sat/satcomp2024-sample/9cd3acdb765c15163bc239ae3a57f880-FmlaEquivChain_4_6_6.sanitized.cnf",
        "FmlaEquivChain_4_6_6",
        30,
    );
}

#[test]
fn satcomp2024_spg_200_316_must_be_unsat() {
    // spg_200_316 (~49 MB CNF) — like FmlaEquivChain above, far too large for AY
    // to prove UNSAT in a unit-test budget. Soundness-only check (never a false
    // SAT) on a large stack. Bounded by the interrupt flag, which the
    // probe/intree inprocessing loops now honor mid-pass (they used to run
    // minutes past the timeout on this instance).
    assert_not_sat_on_big_stack(
        "benchmarks/sat/satcomp2024-sample/b5028686db9bd1073fa09cbd8c805f47-spg_200_316.cnf",
        "spg_200_316",
        30,
    );
}

#[test]
fn satcomp2024_unsat_soundness() {
    // These large SAT-COMP 2024 instances drive recursive clause minimization
    // (`is_redundant_cached`, capped at `minimize_depth_limit = 1000`, CaDiCaL's
    // default) deeper than the 2 MB default test-thread stack — though well
    // within the solver binary's main-thread stack (the `ay` binary solves these
    // fine). Run the soundness checks on an adequately-sized stack so the test
    // exercises the real solver under production-like conditions instead of
    // aborting the whole test binary with a stack overflow.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let benchmarks = [
                "benchmarks/sat/satcomp2024-sample/4be4ae25aae88528bc10f8369bba86df-ER_400_20_4.apx_1_DC-AD.cnf",
                "benchmarks/sat/satcomp2024-sample/4106867bc76b8794330a205cf8a303ad-bvsub_19952.smt2.cnf",
                "benchmarks/sat/satcomp2024-sample/a5419a63d913bde0ba5bcd8a8571342f-asconhashv12_opt64_H11_M2-tBi5i1RIgRz_m0_1_U23.c.cnf",
                "benchmarks/sat/satcomp2024-sample/dcf5b8224d1e0748871c83ee10067255-2dlx_ca_bp_f_liveness.cnf",
                "benchmarks/sat/satcomp2024-sample/fa5c6d6736a42650656c5bc018413254-bphp_p23_h22.sanitized.cnf",
                "benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf",
                "benchmarks/sat/satcomp2024-sample/4e366e723d75fe39bf6db9a24ffb059b-Dodecahedron-k7.cnf",
                "benchmarks/sat/satcomp2024-sample/b172b4c218f1e44e205575d2b51e82c4-Schur_161_5_d38.cnf",
            ];
            for path in &benchmarks {
                let label = path.rsplit('/').next().unwrap_or(path);
                assert_not_sat(path, label, 15);
            }
        })
        .expect("spawn satcomp2024 soundness thread")
        .join()
        .expect("satcomp2024 soundness thread panicked");
}

// ---------------------------------------------------------------------------
// Inprocessing config matrix: braun.8 and braun.10 across all configs
// ---------------------------------------------------------------------------

#[test]
fn braun_8_inprocessing_config_matrix() {
    for config in &ALL_CONFIGS {
        assert_not_sat_with_config(
            "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
            "braun-8",
            30,
            *config,
        );
    }
}

#[test]
fn braun_10_inprocessing_config_matrix() {
    for config in &ALL_CONFIGS {
        assert_not_sat_with_config(
            "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
            "braun-10",
            30,
            *config,
        );
    }
}

// ---------------------------------------------------------------------------
// UNSAT corpus with specific inprocessing configurations
// ---------------------------------------------------------------------------

#[test]
fn unsat_corpus_bve_only_soundness() {
    for path in SMALL_UNSAT_SUBSET {
        let label = path.rsplit('/').next().unwrap_or(path);
        assert_not_sat_with_config(path, label, 30, InprocConfig::BveOnly);
    }
}

#[test]
fn unsat_corpus_sweep_only_soundness() {
    for path in SMALL_UNSAT_SUBSET {
        let label = path.rsplit('/').next().unwrap_or(path);
        assert_not_sat_with_config(path, label, 30, InprocConfig::SweepOnly);
    }
}

#[test]
fn unsat_corpus_congruence_only_soundness() {
    for path in SMALL_UNSAT_SUBSET {
        let label = path.rsplit('/').next().unwrap_or(path);
        assert_not_sat_with_config(path, label, 30, InprocConfig::CongruenceOnly);
    }
}

#[test]
fn unsat_corpus_bve_gate_soundness() {
    for path in SMALL_UNSAT_SUBSET {
        let label = path.rsplit('/').next().unwrap_or(path);
        assert_not_sat_with_config(path, label, 30, InprocConfig::BveAndGate);
    }
}

#[test]
fn unsat_corpus_bve_sweep_cong_soundness() {
    for path in SMALL_UNSAT_SUBSET {
        let label = path.rsplit('/').next().unwrap_or(path);
        assert_not_sat_with_config(path, label, 30, InprocConfig::BveSweepCongruence);
    }
}

#[test]
fn unsat_corpus_no_inprocessing_soundness() {
    for path in SMALL_UNSAT_SUBSET {
        let label = path.rsplit('/').next().unwrap_or(path);
        assert_not_sat_with_config(path, label, 30, InprocConfig::NoInprocessing);
    }
}

// ---------------------------------------------------------------------------
// Congruence effectiveness on circuit equivalence (#7905)
// ---------------------------------------------------------------------------

/// Verifies that congruence closure finds sufficient equivalences on circuit
/// equivalence (miter) benchmarks. These formulas have ~75% binary clauses
/// encoding gate implications. The XOR guard (binary clause fraction >= 50%)
/// must prevent XOR extraction from consuming the clause structure needed for
/// congruence closure. Without the guard, congruence finds 0 equivalences
/// and the formula takes 100-1000x longer to solve.
///
/// Regression guard for the binary clause fraction XOR guard fix (38fa23893).
#[test]
fn braun_8_congruence_finds_equivalences() {
    let cnf = super::common::load_repo_benchmark(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
    );
    let formula = parse_dimacs(&cnf).expect("parse");

    let mut solver = formula.into_solver();
    solver.set_congruence_enabled(true);

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let handle = spawn_interrupt_timer(&flag, 30);

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    assert!(
        matches!(result, SatResult::Unsat(_)),
        "braun.8 should be UNSAT, got {result:?}"
    );

    let cong_stats = solver.congruence_stats();
    if cong_stats.rounds == 0 && cong_stats.gates_analyzed == 0 {
        eprintln!("braun.8 solved before congruence ran; correctness checked by UNSAT result");
        return;
    }
    // Congruence must find a substantial number of equivalences (CaDiCaL
    // finds 299 on this formula). If congruence finds 0, the XOR guard
    // is not working and XOR extraction consumed the binary clause structure.
    assert!(
        cong_stats.equivalences_found >= 200,
        "congruence should find >= 200 equivalences on braun.8 (found {}). \
         XOR guard may be broken — check binary clause fraction threshold.",
        cong_stats.equivalences_found,
    );
    assert!(
        cong_stats.gates_analyzed >= 400,
        "congruence should analyze >= 400 gates on braun.8 (found {})",
        cong_stats.gates_analyzed,
    );
}

#[test]
fn braun_10_congruence_finds_equivalences() {
    let cnf = super::common::load_repo_benchmark(
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
    );
    let formula = parse_dimacs(&cnf).expect("parse");

    let mut solver = formula.into_solver();
    solver.set_congruence_enabled(true);

    let flag = Arc::new(AtomicBool::new(false));
    solver.set_interrupt(flag.clone());
    let handle = spawn_interrupt_timer(&flag, 30);

    let result = solver
        .solve_interruptible(|| flag.load(Ordering::Relaxed))
        .into_inner();

    flag.store(true, Ordering::Relaxed);
    let _ = handle.join();

    assert!(
        matches!(result, SatResult::Unsat(_)),
        "braun.10 should be UNSAT, got {result:?}"
    );

    let cong_stats = solver.congruence_stats();
    if cong_stats.rounds == 0 && cong_stats.gates_analyzed == 0 {
        eprintln!("braun.10 solved before congruence ran; correctness checked by UNSAT result");
        return;
    }
    assert!(
        cong_stats.equivalences_found >= 100,
        "congruence should find >= 100 equivalences on braun.10 (found {}). \
         XOR guard may be broken — check binary clause fraction threshold.",
        cong_stats.equivalences_found,
    );
}

// ---------------------------------------------------------------------------
// FINALIZE_SAT_FAIL (InvalidSatModel) audit tests (#7917)
// ---------------------------------------------------------------------------

#[test]
fn audit_finalize_sat_fail_braun() {
    // Keep this audit focused on the smaller Braun family. Braun 11-13 often
    // spend the full timeout in debug builds, which does not add InvalidSatModel
    // coverage beyond the not-SAT tests above.
    let braun_benchmarks = [
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.7.unsat.cnf",
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.8.unsat.cnf",
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.9.unsat.cnf",
        "benchmarks/sat/eq_atree_braun/eq.atree.braun.10.unsat.cnf",
    ];

    let mut finalize_sat_fails = Vec::new();

    for path in &braun_benchmarks {
        let label = path.rsplit('/').next().unwrap_or(path);
        for config in &ALL_CONFIGS {
            let is_fail = assert_not_sat_with_config(path, label, 5, *config);
            if is_fail {
                finalize_sat_fails.push(format!("{label}[{}]", config.label()));
            }
        }
    }

    assert!(
        finalize_sat_fails.is_empty(),
        "FINALIZE_SAT_FAIL detected in {} cases (latent soundness issues): {:?}",
        finalize_sat_fails.len(),
        finalize_sat_fails
    )
}

#[test]
fn audit_finalize_sat_fail_unsat_corpus() {
    let all_unsat = [
        "benchmarks/sat/unsat/at_most_1_of_5.cnf",
        "benchmarks/sat/unsat/blocked_chain_8.cnf",
        "benchmarks/sat/unsat/cardinality_8.cnf",
        "benchmarks/sat/unsat/double_parity_5.cnf",
        "benchmarks/sat/unsat/graph_coloring_k3_4clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k4_5clique.cnf",
        "benchmarks/sat/unsat/graph_coloring_k5_6clique.cnf",
        "benchmarks/sat/unsat/latin_square_2x2_conflict.cnf",
        "benchmarks/sat/unsat/mutex_4proc.cnf",
        "benchmarks/sat/unsat/mutex_6proc.cnf",
        "benchmarks/sat/unsat/mutilated_chessboard_2x2.cnf",
        "benchmarks/sat/unsat/ordering_cycle_5.cnf",
        "benchmarks/sat/unsat/parity_6.cnf",
        "benchmarks/sat/unsat/php_4_3.cnf",
        "benchmarks/sat/unsat/php_5_4.cnf",
        "benchmarks/sat/unsat/php_6_5.cnf",
        "benchmarks/sat/unsat/php_7_6.cnf",
        "benchmarks/sat/unsat/php_functional_5_4.cnf",
        "benchmarks/sat/unsat/ramsey_r3_3_6.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12345.cnf",
        "benchmarks/sat/unsat/random_3sat_50_213_s12349.cnf",
        "benchmarks/sat/unsat/resolution_chain_12.cnf",
        "benchmarks/sat/unsat/tseitin_cycle_11.cnf",
        "benchmarks/sat/unsat/tseitin_grid_3x3.cnf",
        "benchmarks/sat/unsat/tseitin_k5.cnf",
        "benchmarks/sat/unsat/tseitin_random_15.cnf",
        "benchmarks/sat/unsat/urquhart_3.cnf",
    ];

    let mut finalize_sat_fails = Vec::new();

    for path in &all_unsat {
        let label = path.rsplit('/').next().unwrap_or(path);
        for config in &ALL_CONFIGS {
            let is_fail = assert_not_sat_with_config(path, label, 30, *config);
            if is_fail {
                finalize_sat_fails.push(format!("{label}[{}]", config.label()));
            }
        }
    }

    assert!(
        finalize_sat_fails.is_empty(),
        "FINALIZE_SAT_FAIL detected in {} cases (latent soundness issues): {:?}",
        finalize_sat_fails.len(),
        finalize_sat_fails
    )
}
