// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

fn add_triangle_orbitope_formula(solver: &mut Solver) {
    let variable = |vertex: u32, color: u32| Variable(3 * vertex + color);
    for vertex in 0..3 {
        assert!(solver.add_clause(
            (0..3)
                .map(|color| Literal::positive(variable(vertex, color)))
                .collect(),
        ));
        for first in 0..3 {
            for second in (first + 1)..3 {
                assert!(solver.add_clause(vec![
                    Literal::negative(variable(vertex, first)),
                    Literal::negative(variable(vertex, second)),
                ]));
            }
        }
    }
    for (left, right) in [(0, 1), (0, 2), (1, 2)] {
        for color in 0..3 {
            assert!(solver.add_clause(vec![
                Literal::negative(variable(left, color)),
                Literal::negative(variable(right, color)),
            ]));
        }
    }
}

fn shipped_symmetry_switches() -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default())
}

#[test]
fn orbitope_no_proof_route_still_installs_fixing_units() {
    let _switches = shipped_symmetry_switches();
    let mut solver = Solver::new(9);
    solver.set_symmetry_oneshot(true);
    add_triangle_orbitope_formula(&mut solver);

    let clauses_before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();

    assert!(!unsat);
    assert!(changed, "the no-proof orbitope route must remain enabled");
    assert_eq!(solver.arena.active_clause_count(), clauses_before + 3);
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 3);
}

#[test]
fn orbitope_drat_route_still_emits_witnessed_steps() {
    use ay_drat_check::drat_parser::ProofStep;

    let _switches = shipped_symmetry_switches();
    let mut solver = Solver::with_proof(9, Vec::<u8>::new());
    solver.set_symmetry_oneshot(true);
    add_triangle_orbitope_formula(&mut solver);

    let clauses_before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();

    assert!(!unsat);
    assert!(
        changed,
        "the witnessed DRAT orbitope route must remain enabled"
    );
    assert_eq!(solver.arena.active_clause_count(), clauses_before + 3);
    let proof = solver
        .take_proof_writer()
        .expect("DRAT writer remains attached")
        .into_vec()
        .expect("in-memory DRAT output");
    let steps = ay_drat_check::drat_parser::parse_drat(&proof).expect("valid DSR syntax");
    assert_eq!(steps.len(), 3);
    assert!(
        steps
            .iter()
            .all(|step| matches!(step, ProofStep::AddPr { .. })),
        "every orbitope fixing unit must carry its DSR witness"
    );
}

#[test]
fn orbitope_is_skipped_with_bare_lrat_tracking() {
    let _switches = shipped_symmetry_switches();
    let mut solver = Solver::new(9);
    solver.enable_lrat();
    solver.set_symmetry_oneshot(true);
    add_triangle_orbitope_formula(&mut solver);

    let clauses_before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();

    assert!(!unsat);
    assert!(!changed, "bare LRAT cannot carry orbitope DSR steps");
    assert_eq!(solver.arena.active_clause_count(), clauses_before);
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 0);
}

#[test]
fn orbitope_is_skipped_with_lrat_output() {
    let _switches = shipped_symmetry_switches();
    let output = ProofOutput::lrat_text(Vec::<u8>::new(), 21);
    let mut solver = Solver::with_proof_output(9, output);
    solver.set_symmetry_oneshot(true);
    add_triangle_orbitope_formula(&mut solver);

    let clauses_before = solver.arena.active_clause_count();
    let (unsat, changed) = solver.preprocess_symmetry();

    assert!(!unsat);
    assert!(!changed, "LRAT output cannot carry orbitope DSR steps");
    assert_eq!(solver.arena.active_clause_count(), clauses_before);
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 0);
}

#[test]
fn orbitope_is_skipped_with_clause_trace_reconstruction() {
    let _switches = shipped_symmetry_switches();
    let mut solver = Solver::new(9);
    solver.enable_clause_trace();
    solver.set_symmetry_oneshot(true);
    add_triangle_orbitope_formula(&mut solver);

    let clauses_before = solver.arena.active_clause_count();
    let trace_before = solver
        .clause_trace()
        .expect("clause trace enabled")
        .entries()
        .len();
    let (unsat, changed) = solver.preprocess_symmetry();

    assert!(!unsat);
    assert!(!changed, "clause trace cannot carry orbitope DSR steps");
    assert_eq!(solver.arena.active_clause_count(), clauses_before);
    let trace = solver
        .clause_trace()
        .expect("clause trace remains attached");
    assert_eq!(trace.entries().len(), trace_before);
    assert!(trace.entries().iter().all(|entry| entry.is_original));
    assert_eq!(solver.cold.symmetry_stats.sb_clauses_added, 0);
}
