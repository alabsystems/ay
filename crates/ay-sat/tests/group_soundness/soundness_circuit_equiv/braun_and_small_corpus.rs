// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_circuit_equiv` to preserve test FQNs.

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
