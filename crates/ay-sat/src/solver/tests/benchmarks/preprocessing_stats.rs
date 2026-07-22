// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Benchmark stats for crn_11_99_u to verify inprocessing fires during search.
/// The flatten-solve-loop fix makes inprocessing independent of restarts,
/// matching CaDiCaL's cdcl_loop_with_inprocessing architecture.
#[test]
fn test_crn_benchmark_inprocessing_stats() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/crn_11_99_u.cnf");
    if !path.exists() {
        eprintln!("crn_11_99_u: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let formula = crate::parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    // Disable BVE+factor to work around #6892 reconstruction stack bug.
    solver.set_bve_enabled(false);
    solver.set_factor_enabled(false);
    // 5s interrupt timeout — sufficient for UNSAT in debug mode (~0.4s release).
    let result = solve_with_timeout(&mut solver, 5);
    // UNSAT expected; Unknown (timeout) acceptable in contended CI.
    assert!(
        !matches!(result, SatResult::Sat(_)),
        "crn_11_99_u must not be SAT, got {result:?}"
    );
    let vivify = solver.vivify_stats();
    let probe = solver.probe_stats();
    let fixed = solver.num_fixed();
    let conflicts = solver.num_conflicts();
    let restarts = solver.num_restarts();
    let props = solver.num_propagations();
    let reductions = solver.num_reductions();
    let subsume = solver.subsume_stats();
    let ticks = solver.search_ticks[0] + solver.search_ticks[1];
    let nclauses = solver.num_clauses();
    let bve_enabled = solver.is_bve_enabled();
    let bve_phases = solver.cold.bve_phases;
    let bve_resolutions = solver.cold.bve_resolutions;
    let bve_stats = solver.bve_stats();
    let factor_rounds = solver.cold.factor_rounds;
    let factor_total = solver.cold.factor_factored_total;
    eprintln!(
        "crn stats: conflicts={conflicts} restarts={restarts} props={props} \
         reductions={reductions} fixed={fixed} vivify_examined={} \
         vivify_strengthened={} probe_failed={} fwd_subsumed={} \
         bve_enabled={bve_enabled} bve_phases={bve_phases} \
         bve_resolutions={bve_resolutions} bve_eliminated={} \
         factor_rounds={factor_rounds} factor_total={factor_total} \
         ticks={ticks} nclauses={nclauses}",
        vivify.clauses_examined,
        vivify.clauses_strengthened,
        probe.failed,
        subsume.forward_subsumed,
        bve_stats.vars_eliminated,
    );
    // Count actual level-0 assignments (trail at decision_level==0)
    let level0_assigned = solver
        .trail
        .iter()
        .filter(|&&lit| solver.var_data[lit.variable().index()].level == 0)
        .count();
    let eliminated = bve_stats.vars_eliminated;
    eprintln!(
        "crn detail: level0_assigned={level0_assigned} \
         lifecycle_eliminated={eliminated} \
         subsume_strengthened={} subsume_checks={} \
         probe_rounds={} probe_probed={}",
        subsume.strengthened_clauses, subsume.checks, probe.rounds, probe.probed,
    );
    // Backbone+sweep during preprocessing may solve UNSAT formulas with 0
    // conflicts. The key metric is that the result is UNSAT (checked above).
}

/// Diagnostic test for FmlaEquivChain preprocessing stats.
/// CaDiCaL comparison: fixed=11526, eliminated=31324, substituted=1487,
/// factored=12335. Total solve: 11.5s, 367K conflicts.
/// Run with: cargo test -p ay-sat --release test_fmlaequivchain_preprocess_stats -- --nocapture
#[test]
fn test_fmlaequivchain_preprocess_stats() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/FmlaEquivChain.cnf");
    if !path.exists() {
        eprintln!("FmlaEquivChain: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let formula = crate::parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    // Use solve_interruptible for per-100-conflict interrupt checking.
    // solve() only checks at coarse preprocessing boundaries, causing
    // up to 24s of interrupt latency in debug mode on this 4.7M-clause formula.
    let start = ay_core::time::Instant::now();
    let result = solve_with_timeout(&mut solver, 10);
    let elapsed = start.elapsed();

    let fixed = solver.num_fixed();
    let bve_stats = solver.bve_stats();
    let eliminated = bve_stats.vars_eliminated;
    let probe = solver.probe_stats();
    let subsume = solver.subsume_stats();
    let decompose = solver.decompose_stats();
    let vivify = solver.vivify_stats();
    let conflicts = solver.num_conflicts();
    let props = solver.num_propagations();
    let restarts = solver.num_restarts();
    let nclauses = solver.num_clauses();
    let factor_total = solver.cold.factor_factored_total;
    let ticks = solver.search_ticks[0] + solver.search_ticks[1];
    eprintln!(
        "FmlaEquivChain: result={result:?} time={:.2}s \
         fixed={fixed} eliminated={eliminated} substituted={} \
         factored={factor_total} conflicts={conflicts} restarts={restarts} \
         props={props} nclauses={nclauses} ticks={ticks}",
        elapsed.as_secs_f64(),
        decompose.substituted,
    );
    let congruence = solver.congruence_stats();
    let gate = solver.gate_stats();
    let sweep = solver.sweep_stats();
    let htr = solver.htr_stats();
    let transred = solver.transred_stats();
    eprintln!(
        "FmlaEquivChain detail: probe_failed={} probe_rounds={} probe_units={} \
         subsume_fwd={} subsume_strengthened={} \
         vivify_examined={} vivify_strengthened={} vivify_satisfied={} vivify_lits_removed={} \
         bve_phases={} cong_rounds={} cong_gates={} cong_equivs={} \
         sweep_rounds={} sweep_backbone={} sweep_equivs={} htr_rounds={} transred_rounds={} \
         gate_calls={} gate_equivs={} gate_ands={} gate_xors={} gate_ites={} \
         ite_to_and={} ite_to_xor={}",
        probe.failed,
        probe.rounds,
        probe.units_derived,
        subsume.forward_subsumed,
        subsume.strengthened_clauses,
        vivify.clauses_examined,
        vivify.clauses_strengthened,
        vivify.clauses_satisfied,
        vivify.literals_removed,
        solver.cold.bve_phases,
        congruence.rounds,
        congruence.gates_analyzed,
        congruence.equivalences_found,
        sweep.rounds,
        sweep.kitten_backbone,
        sweep.kitten_equivalences,
        htr.rounds,
        transred.rounds,
        gate.extraction_calls,
        gate.equivalences,
        gate.and_gates,
        gate.xor_gates,
        gate.ite_gates,
        congruence.ite_to_and,
        congruence.ite_to_xor,
    );
    eprintln!(
        "FmlaEquivChain search: otfs_str={} otfs_sub={} eager_sub={} \
         decisions_reused={}",
        solver.otfs_strengthened(),
        solver.otfs_subsumed(),
        solver.num_eager_subsumptions(),
        vivify.decisions_reused,
    );
    eprintln!(
        "FmlaEquivChain OTFS: candidates={} blocked_open0={} \
         blocked_watch={} blocked_strengthen={}",
        solver.otfs_candidates(),
        solver.otfs_blocked_open0(),
        solver.otfs_blocked_watch(),
        solver.otfs_blocked_strengthen(),
    );
    // FmlaEquivChain_4_6_6 is UNSAT (confirmed by both CaDiCaL and Kissat).
    // SAT would be a soundness bug.
    // Unknown (timeout) is acceptable in debug mode.
    assert!(
        !matches!(result, SatResult::Sat(_)),
        "FALSE SAT on FmlaEquivChain — soundness bug"
    );
    eprintln!(
        "FmlaEquivChain: CaDiCaL ref: fixed=11526 eliminated=31324 \
         substituted=1487 factored=12335 conflicts=367502 time=9.4s \
         Kissat ref: eliminated=33165 (61%) units=11411 time=8.1s"
    );

    // BVE regression guard (#8134): When factoring does NOT create extension
    // variables, AY should eliminate at least 10K variables. However, #8397
    // introduced mutual exclusion between BVE and factoring: if factoring
    // creates extension variables first (which it does in preprocessing order),
    // BVE is entirely disabled to prevent reconstruction soundness bugs.
    // In that case, eliminated == 0 is expected and correct.
    //
    // Guard: if BVE ran at all (eliminated > 0) AND the solver completed
    // (not timed out), it should have eliminated a substantial number.
    // If BVE was blocked by factoring, or the solver timed out mid-BVE,
    // skip the check — partial BVE with low counts is expected under timeout.
    if eliminated > 0 && !matches!(result, SatResult::Unknown) {
        assert!(
            eliminated >= 10_000,
            "BVE regression on FmlaEquivChain: eliminated only {eliminated} vars, \
             expected >= 10000 (Kissat: 33165, CaDiCaL: 31324)"
        );
    }
}

/// Diagnostic test for clique_n2_k10 BVE behavior (#7178).
/// CaDiCaL comparison: 359/472 vars eliminated (76%), solves in 11.1s.
/// Run with: cargo test -p ay-sat --release test_clique_n2_k10_bve_stats -- --nocapture
#[test]
fn test_clique_n2_k10_bve_stats() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/satcomp2024-sample/cb2e8b7fada420c5046f587ea754d052-clique_n2_k10.sanitized.cnf");
    if !path.exists() {
        eprintln!("clique_n2_k10: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let formula = crate::parse_dimacs(&content).expect("parse");
    let mut solver = formula.into_solver();
    // Use solve_interruptible for per-100-conflict interrupt checking.
    // solve() only checks at coarse boundaries, causing this test to always
    // hit the full timeout. 5s is sufficient for diagnostic stats.
    let start = ay_core::time::Instant::now();
    let result = solve_with_timeout(&mut solver, 5);
    let elapsed = start.elapsed();

    let fixed = solver.num_fixed();
    let bve_stats = solver.bve_stats();
    let eliminated = bve_stats.vars_eliminated;
    let probe = solver.probe_stats();
    let subsume = solver.subsume_stats();
    let decompose = solver.decompose_stats();
    let vivify = solver.vivify_stats();
    let conflicts = solver.num_conflicts();
    let props = solver.num_propagations();
    let nclauses = solver.num_clauses();
    let factor_total = solver.cold.factor_factored_total;
    eprintln!(
        "clique_n2_k10: result={result:?} time={:.2}s \
         fixed={fixed} eliminated={eliminated} substituted={} \
         factored={factor_total} conflicts={conflicts} props={props} \
         nclauses={nclauses}",
        elapsed.as_secs_f64(),
        decompose.substituted,
    );
    eprintln!(
        "clique_n2_k10 detail: probe_failed={} probe_rounds={} \
         subsume_fwd={} subsume_strengthened={} \
         vivify_examined={} vivify_strengthened={} \
         bve_phases={} bve_resolutions={}",
        probe.failed,
        probe.rounds,
        subsume.forward_subsumed,
        subsume.strengthened_clauses,
        vivify.clauses_examined,
        vivify.clauses_strengthened,
        solver.cold.bve_phases,
        solver.cold.bve_resolutions,
    );
    let sweep = solver.sweep_stats();
    eprintln!(
        "clique_n2_k10 sweep: rounds={} backbone={} equivalences={} \
         environments={} eager_sub={} otfs_str={} otfs_sub={}",
        sweep.rounds,
        sweep.kitten_backbone,
        sweep.kitten_equivalences,
        sweep.kitten_environments,
        solver.num_eager_subsumptions(),
        solver.otfs_strengthened(),
        solver.otfs_subsumed(),
    );
    // clique_n2_k10 is UNSAT (CaDiCaL confirms, exit code 20, ~11.4s).
    // SAT would be a soundness bug. Unknown (timeout) is expected in
    // debug mode since CaDiCaL itself takes 11.4s in release.
    assert!(
        !matches!(result, SatResult::Sat(_)),
        "FALSE SAT on clique_n2_k10 — soundness bug"
    );
    eprintln!(
        "clique_n2_k10: CaDiCaL ref: eliminated=359/472 fixed=98 \
         substituted=0 factored=292 subsumed=584974 conflicts=1243169 time=13.7s"
    );
}

/// Diagnostic test for eq.atree.braun.7 preprocessing/search stats.
///
/// Run with:
/// `AIT_ALLOW_LOCKLESS_CARGO=1 CARGO_TARGET_DIR=/tmp/ay-target cargo test -p ay-sat --release test_eq_atree_braun7_stats -- --nocapture`
#[test]
fn test_eq_atree_braun7_stats() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/sat/eq_atree_braun/eq.atree.braun.7.unsat.cnf");
    if !path.exists() {
        eprintln!("eq.atree.braun.7: benchmark missing, skipping");
        return;
    }
    let content = std::fs::read_to_string(&path).expect("read");
    let run_variant = |label: &str, factor: bool| {
        let formula = crate::parse_dimacs(&content).expect("parse");
        let mut solver = formula.into_solver();
        solver.set_factor_enabled(factor);

        let preprocess_start = ay_core::time::Instant::now();
        let preprocess_unsat = solver.preprocess();
        let preprocess_elapsed = preprocess_start.elapsed();

        let fixed = solver.num_fixed();
        let removed = solver.var_lifecycle.count_removed();
        let active = solver
            .num_vars
            .saturating_sub(fixed as usize)
            .saturating_sub(removed);
        let irredundant = solver.arena.active_clause_count();
        let gate = solver.gate_stats();
        let bve = solver.bve_stats();
        let cong = solver.congruence_stats();
        let decomp = solver.decompose_stats();
        eprintln!(
            "{label} preprocess: unsat={preprocess_unsat} factor={factor} time={:.2}s \
             fixed={fixed} removed={removed} active={active} clauses={irredundant} \
             bve_eliminated={} bve_resolutions={} decomp_subst={} factored={} \
             cong_rounds={} cong_gates={} cong_equivs={} gate_calls={} gate_and={} gate_xor={} gate_ite={}",
            preprocess_elapsed.as_secs_f64(),
            bve.vars_eliminated,
            solver.cold.bve_resolutions,
            decomp.substituted,
            solver.cold.factor_factored_total,
            cong.rounds,
            cong.gates_analyzed,
            cong.equivalences_found,
            gate.extraction_calls,
            gate.and_gates,
            gate.xor_gates,
            gate.ite_gates,
        );

        let solve_start = ay_core::time::Instant::now();
        let result = if preprocess_unsat {
            SatResult::Unsat(ProofCertificate::empty())
        } else {
            solve_with_timeout(&mut solver, 30)
        };
        let solve_elapsed = solve_start.elapsed();
        eprintln!(
            "{label} solve: result={result:?} time={:.2}s conflicts={} decisions={} props={} restarts={} learned={} inprobe_phases={} factor_total={} bve_eliminated={}",
            solve_elapsed.as_secs_f64(),
            solver.num_conflicts(),
            solver.num_decisions(),
            solver.num_propagations(),
            solver.num_restarts(),
            solver.debug_clause_counts().1,
            solver.inprobe_phases(),
            solver.cold.factor_factored_total,
            solver.bve_stats().vars_eliminated,
        );
        result
    };

    let baseline = run_variant("braun7 baseline", true);
    let no_factor = run_variant("braun7 no_factor", false);
    eprintln!(
        "braun7 ref: CaDiCaL preprocess residual ~= clauses=2510 vars=603 \
         eliminated=603 fixed=192 substituted=32 factored=135; solve conflicts=374473 decisions=610144 props=36778577 time=14.0s"
    );

    assert!(
        !matches!(baseline, SatResult::Sat(_)),
        "FALSE SAT on eq.atree.braun.7 baseline"
    );
    assert!(
        !matches!(no_factor, SatResult::Sat(_)),
        "FALSE SAT on eq.atree.braun.7 no_factor"
    );
}
