// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-analysis-ticks-kissat`: conflict analysis charges search ticks
//! only for large reasons in minimize, shrink and reason-side bumping.

use super::*;

/// Ticks `analyze_conflict` charges for the conflict of deciding d in
/// (-d | a), (-d | -a | b), (-a | -b | c), (-b | -c | -d).
fn analysis_ticks(kissat: bool) -> u64 {
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        analysis_ticks_kissat: Some(kissat),
        ..Default::default()
    });
    let (d, a, b, c) = (Variable(0), Variable(1), Variable(2), Variable(3));
    let mut solver = Solver::new(4);
    solver.add_clause(vec![Literal::negative(d), Literal::positive(a)]);
    solver.add_clause(vec![
        Literal::negative(d),
        Literal::negative(a),
        Literal::positive(b),
    ]);
    solver.add_clause(vec![
        Literal::negative(a),
        Literal::negative(b),
        Literal::positive(c),
    ]);
    solver.add_clause(vec![
        Literal::negative(b),
        Literal::negative(c),
        Literal::negative(d),
    ]);
    solver.initialize_watches();
    assert!(solver.process_initial_clauses().is_none());
    solver.decide(Literal::positive(d));
    let conflict = solver
        .search_propagate()
        .expect("deciding d propagates to a conflict");
    let before = solver.search_ticks[0] + solver.search_ticks[1];
    solver.analyze_conflict(conflict);
    solver.search_ticks[0] + solver.search_ticks[1] - before
}

#[test]
fn analysis_ticks_kissat_charges_no_resolution_ticks() {
    let default = analysis_ticks(false);
    let kissat = analysis_ticks(true);
    assert!(
        default >= 1 + 3 + 3,
        "the conflict and its resolved reasons: {default}"
    );
    assert!(
        kissat < default,
        "kissat {kissat} against default {default}"
    );
}
