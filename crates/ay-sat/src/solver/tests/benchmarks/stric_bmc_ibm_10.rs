// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Diagnostic test for #3366: stric-bmc-ibm-10 preprocessing gap vs CaDiCaL.
/// CaDiCaL: 0.30s, 63 conflicts, 18.22% vars eliminated (congruence+SCC+factor).
/// Run: cargo test -p ay-sat --release test_stric_bmc_ibm_10_stats -- --nocapture
#[test]
fn test_stric_bmc_ibm_10_stats() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reference/creusat/tests/cnf-hard/stric-bmc-ibm-10.cnf");
    if !path.exists() {
        eprintln!("stric-bmc-ibm-10: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let formula = crate::parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    // 10s timeout — sufficient for diagnostic stats (reduced from 20s).
    setup_timeout(&mut solver, 10);
    let start = ay_core::time::Instant::now();
    let result = solver.solve().into_inner();
    let elapsed = start.elapsed();

    let fixed = solver.num_fixed();
    let bve_stats = solver.bve_stats();
    let eliminated = bve_stats.vars_eliminated;
    let probe = solver.probe_stats();
    let subsume = solver.subsume_stats();
    let decompose = solver.decompose_stats();
    let congruence = solver.congruence_stats();
    let conflicts = solver.num_conflicts();
    let props = solver.num_propagations();
    let nclauses = solver.num_clauses();
    let factor_total = solver.cold.factor_factored_total;
    eprintln!(
        "stric-bmc-ibm-10: result={result:?} time={:.2}s \
         fixed={fixed} eliminated={eliminated} substituted={} \
         factored={factor_total} conflicts={conflicts} props={props} \
         nclauses={nclauses}",
        elapsed.as_secs_f64(),
        decompose.substituted,
    );
    eprintln!(
        "stric-bmc-ibm-10 detail: probe_failed={} probe_rounds={} \
         subsume_fwd={} subsume_strengthened={} \
         cong_rounds={} cong_equivs={} cong_gates={} \
         bve_phases={}",
        probe.failed,
        probe.rounds,
        subsume.forward_subsumed,
        subsume.strengthened_clauses,
        congruence.rounds,
        congruence.equivalences_found,
        congruence.gates_analyzed,
        solver.cold.bve_phases,
    );
    eprintln!(
        "stric-bmc-ibm-10: CaDiCaL ref: time=0.30s conflicts=63 \
         cong_equivs=9273 gates=23427(AND=23004,XOR=423) \
         substituted=24132 eliminated=11752(18.22%) factored=5451"
    );
    // stric-bmc-ibm-10 is SAT (CaDiCaL + Kissat agree). UNSAT = soundness bug.
    assert!(
        !matches!(result, SatResult::Unsat(_)),
        "FALSE UNSAT on stric-bmc-ibm-10 — soundness bug"
    );
}

/// Soundness bisection for stric-bmc-ibm-10 (#3366).
/// Disables preprocessing techniques one at a time to find which
/// produces false UNSAT (CaDiCaL+Kissat agree: SAT).
#[test]
fn test_stric_bmc_ibm_10_soundness_bisect() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reference/creusat/tests/cnf-hard/stric-bmc-ibm-10.cnf");
    if !path.exists() {
        eprintln!("stric-bmc-ibm-10: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");

    // Config: (name, bve, congruence, decompose, factor, sweep, backbone)
    let configs: Vec<(&str, bool, bool, bool, bool, bool, bool)> = vec![
        ("all-disabled", false, false, false, false, false, false),
        ("bve-only", true, false, false, false, false, false),
        ("bve+cong+decomp", true, true, true, false, false, false),
        (
            "bve+cong+decomp+factor",
            true,
            true,
            true,
            true,
            false,
            false,
        ),
        (
            "bve+cong+decomp+sweep",
            true,
            true,
            true,
            false,
            true,
            false,
        ),
        // Backbone isolation: does backbone+factor cause timeout?
        ("bve+cong+decomp+bb", true, true, true, false, false, true),
        (
            "bve+cong+decomp+factor+bb",
            true,
            true,
            true,
            true,
            false,
            true,
        ),
        (
            "bve+cong+decomp+sweep+bb",
            true,
            true,
            true,
            false,
            true,
            true,
        ),
        (
            "bve+cong+decomp+factor+sweep",
            true,
            true,
            true,
            true,
            true,
            false,
        ),
        // Full pipeline (default config)
        ("all-enabled", true, true, true, true, true, true),
    ];

    for (name, bve, cong, decomp, factor, sweep, backbone) in configs {
        let formula = crate::parse_dimacs(&content).expect("parse");
        let mut solver = formula.into_solver();
        solver.set_bve_enabled(bve);
        solver.set_congruence_enabled(cong);
        solver.set_decompose_enabled(decomp);
        solver.set_factor_enabled(factor);
        solver.set_sweep_enabled(sweep);
        solver.set_backbone_enabled(backbone);
        // 3s per config — false UNSAT manifests during preprocessing or
        // early search. 3s sufficient without wasting 80s (10 configs × 8s).
        setup_timeout(&mut solver, 3);
        let result = solver.solve().into_inner();
        let cong_stats = solver.congruence_stats();
        let decomp_stats = solver.decompose_stats();
        let bve_stats = solver.bve_stats();
        eprintln!(
            "  {name}: result={result:?} conflicts={} fixed={} equivs={} subst={} elim={} factor={} sweep_rwt={}",
            solver.num_conflicts(),
            solver.num_fixed(),
            cong_stats.equivalences_found,
            decomp_stats.substituted,
            bve_stats.vars_eliminated,
            solver.cold.factor_factored_total,
            solver.sweep_stats().literals_rewritten,
        );
        // stric-bmc-ibm-10 is SAT (CaDiCaL + Kissat agree). UNSAT is a
        // soundness bug. Unknown (timeout) is acceptable for some configs.
        assert!(
            !matches!(result, SatResult::Unsat(_)),
            "FALSE UNSAT on stric-bmc-ibm-10 with config: {name} — soundness bug"
        );
    }
}
