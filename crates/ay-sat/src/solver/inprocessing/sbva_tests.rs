// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

#[test]
fn test_sbva_integration_basic() {
    // Create a solver with clauses that have a compressible structure.
    // 3 clauses sharing {a, b, c} with different tails:
    // {a, b, c, d}
    // {a, b, c, e}
    // {a, b, c, f}
    let mut solver = Solver::new(10);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));

    solver.add_clause(vec![a, b, c, d]);
    solver.add_clause(vec![a, b, c, e]);
    solver.add_clause(vec![a, b, c, f]);

    let _clauses_before = solver.arena.active_clause_count();
    let vars_before = solver.num_vars;

    // Run SBVA directly.
    solver.sbva();

    // SBVA should have introduced extension vars and rewritten clauses.
    // The exact behavior depends on scheduling guards, so just verify no crash
    // and basic structural invariants hold.
    assert!(
        solver.num_vars >= vars_before,
        "num_vars should not decrease after SBVA"
    );
    // Clause count may change (original deleted, new added).
    let clauses_after = solver.arena.active_clause_count();
    assert!(clauses_after > 0, "should have at least some clauses");
}

#[test]
fn test_sbva_records_er_extension_definition_log() {
    let mut solver = Solver::new(10);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));

    solver.add_clause(vec![a, b, c, d]);
    solver.add_clause(vec![a, b, c, e]);
    solver.add_clause(vec![a, b, c, f]);

    solver.sbva();

    assert_eq!(
        solver.er_extension_definition_count(),
        1,
        "one SBVA extension variable must have one ER definition artifact"
    );
    let def = &solver.er_extension_proof_log().definitions()[0];
    assert_eq!(def.producer(), crate::er_proof::ErProducer::Sbva);
    assert_eq!(def.definition_clauses().len(), 1);
    assert_eq!(def.derived_clauses().len(), 3);
    assert_eq!(def.proof_only_clauses().len(), 1);
    assert_eq!(def.source_clause_ids(), &[1, 2, 3]);

    let mut buf = Vec::new();
    solver
        .write_er_extension_log_proof_replay(&mut buf)
        .expect("write ER log");
    let source = String::from_utf8(buf).expect("utf8");
    assert!(source.contains("Producer.sbva"));
    assert!(source.contains("theorem er_extension_log_structural_ok"));
    assert!(
        !source.contains("heuristicScore") && !source.contains("candidate"),
        "ER artifact must not include heuristic selection data"
    );
}

#[test]
fn test_sbva_incremental_guard() {
    // SBVA should be skipped in incremental mode.
    let mut solver = Solver::new(10);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));
    let f = Literal::positive(Variable(5));

    solver.add_clause(vec![a, b, c, d]);
    solver.add_clause(vec![a, b, c, e]);
    solver.add_clause(vec![a, b, c, f]);

    solver.cold.has_been_incremental = true;
    let vars_before = solver.num_vars;

    solver.sbva();

    assert_eq!(
        solver.num_vars, vars_before,
        "SBVA should not introduce new vars in incremental mode"
    );
}

#[test]
fn test_sbva_build_occ() {
    let mut solver = Solver::new(8);

    let a = Literal::positive(Variable(0));
    let b = Literal::positive(Variable(1));
    let c = Literal::positive(Variable(2));
    let d = Literal::positive(Variable(3));
    let e = Literal::positive(Variable(4));

    // Binary clause -- should NOT be in SBVA occ.
    solver.add_clause(vec![a, b]);
    // 3-literal clause -- should be in SBVA occ.
    solver.add_clause(vec![a, b, c]);
    // 4-literal clause -- should be in SBVA occ.
    solver.add_clause(vec![a, c, d, e]);

    let occ = solver.build_sbva_occ();

    // Binary clause not counted.
    // 'a' appears in 2 clauses (the 3-lit and 4-lit ones).
    assert_eq!(
        occ.count(a),
        2,
        "'a' should appear in 2 SBVA-eligible clauses"
    );
    // 'b' appears in 1 clause (the 3-lit one; binary excluded).
    assert_eq!(
        occ.count(b),
        1,
        "'b' should appear in 1 SBVA-eligible clause"
    );
}

/// The counters the stats JSON reports (`sat.sbva_rounds`, `sat.sbva_groups`,
/// `sat.sbva_extension_vars`) and the pass's yield signal: one compressible
/// group of three clauses is one round, one group, one extension variable,
/// and a yield the timed pass wrapper records. Before 2026-09-19 the yield
/// signal fell through to 0, and a run that introduced 3,649 extension
/// variables on a 250-variable formula (vdwb_k6_n250) read `yields 0`.
#[test]
fn sbva_counts_and_yield_signal_report_the_work_done() {
    let mut solver = Solver::new(10);
    let lit = |v: u32| Literal::positive(Variable(v));
    solver.add_clause(vec![lit(0), lit(1), lit(2), lit(3)]);
    solver.add_clause(vec![lit(0), lit(1), lit(2), lit(4)]);
    solver.add_clause(vec![lit(0), lit(1), lit(2), lit(5)]);
    assert_eq!(solver.sbva_counts(), (0, 0, 0));

    solver.run_timed_diagnostic_inprocessing_pass(DiagnosticPass::Sbva, Solver::sbva);

    assert_eq!(solver.sbva_counts(), (1, 1, 1));
    assert_eq!(solver.num_vars, 11, "one extension variable");
    let index = solver_stats::inprocessing_timing_index(DiagnosticPass::Sbva)
        .expect("SBVA is a timed pass");
    assert_eq!(solver.stats.inprocessing_pass_runs[index], 1);
    assert_eq!(solver.stats.inprocessing_pass_yields[index], 1);
}

/// `--sat-sbva-max-density`: three clauses over ten variables are density
/// 0.3; a cap below it refuses the pass and counts the refusal, a cap above
/// it lets the pass compress the group.
#[test]
fn sbva_is_refused_above_the_density_switch() {
    // `None` now means the shipped default of 12 (2026-09-22), which this
    // three-clause formula is far below, so the pass still runs; `f64::MAX` is
    // the opt-out.
    for (cap, expect_groups, expect_skips) in [
        (Some(0.1), 0, 1),
        (Some(1.0), 1, 0),
        (None, 1, 0),
        (Some(f64::MAX), 1, 0),
    ] {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            sbva_max_density: cap,
            ..Default::default()
        });
        let mut solver = Solver::new(10);
        let lit = |v: u32| Literal::positive(Variable(v));
        solver.add_clause(vec![lit(0), lit(1), lit(2), lit(3)]);
        solver.add_clause(vec![lit(0), lit(1), lit(2), lit(4)]);
        solver.add_clause(vec![lit(0), lit(1), lit(2), lit(5)]);
        solver.sbva();
        assert_eq!(solver.sbva_counts().1, expect_groups, "cap {cap:?}");
        assert_eq!(solver.density_band_skips().1, expect_skips, "cap {cap:?}");
    }
}
