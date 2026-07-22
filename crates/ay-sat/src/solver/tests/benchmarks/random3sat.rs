// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Diagnostic test for #6928: 2x+ conflict overhead on random 3-SAT vs CaDiCaL.
/// Loads Python-generated random 3-SAT (500 vars, ratio 4.2, seed 42) from file.
/// Run: cargo test -p ay-sat --release test_random3sat_conflict_overhead -- --nocapture
#[test]
fn test_random3sat_conflict_overhead() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/random3sat_500_42.cnf");
    if !path.exists() {
        eprintln!("random3sat_500_42: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let formula = crate::parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();

    // 10s sufficient — CaDiCaL solves in 0.53s, AY in ~8s debug.
    let start = ay_core::time::Instant::now();
    let result = solve_with_timeout(&mut solver, 10);
    let elapsed = start.elapsed();

    let conflicts = solver.num_conflicts();
    let decisions = solver.num_decisions();
    let props = solver.num_propagations();
    let restarts = solver.num_restarts();
    let fixed = solver.num_fixed();
    let reductions = solver.num_reductions();
    let ticks_focused = solver.search_ticks[0];
    let ticks_stable = solver.search_ticks[1];
    let mode_switches = solver.cold.mode_switch_count;
    let rephase_total = solver.cold.rephase_count;
    let rephase_stable = solver.cold.rephase_count_stable;
    let rephase_focused = solver.cold.rephase_count_focused;
    let chrono = solver.num_chrono_backtracks();
    let bve = solver.bve_stats();
    let probe = solver.probe_stats();
    let vivify = solver.vivify_stats();
    let subsume = solver.subsume_stats();
    let learned = solver
        .num_clauses()
        .saturating_sub(solver.num_original_clauses);
    let nclauses = solver.num_clauses();

    eprintln!(
        "random3sat_500: result={result:?} time={:.3}s",
        elapsed.as_secs_f64()
    );
    eprintln!("  conflicts={conflicts} decisions={decisions} props={props} restarts={restarts}");
    eprintln!(
        "  reductions={reductions} fixed={fixed} bve_elim={} probe_failed={} \
         learned_live={learned} nclauses={nclauses}",
        bve.vars_eliminated, probe.failed,
    );
    eprintln!(
        "  mode_switches={mode_switches} stable_ticks={ticks_stable} \
         focused_ticks={ticks_focused}"
    );
    eprintln!(
        "  rephase_total={rephase_total} rephase_stable={rephase_stable} \
         rephase_focused={rephase_focused}"
    );
    eprintln!(
        "  vivify_examined={} vivify_strengthened={} \
         subsume_fwd={} subsume_strengthened={}",
        vivify.clauses_examined,
        vivify.clauses_strengthened,
        subsume.forward_subsumed,
        subsume.strengthened_clauses,
    );
    let forced = solver.num_forced_backtracks();
    let (ema_checks, ema_fires) = solver.focused_ema_stats();
    let reluctant_fires = solver.stable_reluctant_fires();
    eprintln!(
        "  chrono_bt={chrono} forced_bt={forced} dec/confl={:.2}",
        decisions as f64 / conflicts.max(1) as f64
    );
    eprintln!(
        "  focused_ema: checks={ema_checks} fires={ema_fires} fire_rate={:.3}%",
        100.0 * ema_fires as f64 / ema_checks.max(1) as f64
    );
    eprintln!(
        "  stable_reluctant_fires={reluctant_fires} \
         focused_restarts={ema_fires} stable_restarts={reluctant_fires}"
    );
    let (ema_fast, ema_slow) = solver.lbd_ema_values();
    let lbd_avg = solver.stats.lbd_sum as f64 / solver.stats.lbd_count.max(1) as f64;
    eprintln!(
        "  ema_fast={ema_fast:.2} ema_slow={ema_slow:.2} \
         lbd_avg={lbd_avg:.2} lbd_count={}",
        solver.stats.lbd_count
    );
    let blocked = solver.stats.focused_ema_blocked_by_conflict_gate;
    let focused_dec = solver.stats.focused_decisions;
    let stable_dec = solver.stats.stable_decisions;
    eprintln!(
        "  ema_blocked_by_conflict_gate={blocked} \
         focused_dec={focused_dec} stable_dec={stable_dec}"
    );
    eprintln!(
        "  focused_dec/confl={:.2} stable_dec/confl=N/A",
        focused_dec as f64 / conflicts.max(1) as f64
    );
    eprintln!(
        "  CaDiCaL ref: conflicts=28020 decisions=49978 restarts=540 \
         reductions=14 time=0.53s mode_stable=43.9% chrono=5837(20.8%) \
         ema_fire_rate=3.43% (534/15563)"
    );
    // Smoke test: with 30s timeout, the solver should make progress (not stuck
    // in preprocessing with 0 conflicts). CaDiCaL solves in 0.53s.
    if !matches!(result, SatResult::Unknown) {
        assert!(
            conflicts > 0 || fixed > 0,
            "Solver returned {result:?} with 0 conflicts and 0 fixed — suspicious"
        );
    }
}
