// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_circuit_equiv` to preserve test FQNs.

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
