// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_comprehensive` to preserve test FQNs.

// ===========================================================================
// TEST: Pigeonhole Principle
// ===========================================================================

#[test]
fn php_3_2_unsat() {
    let (nv, clauses) = generate_php(3, 2);
    solve_and_verify(nv, &clauses, "PHP(3,2)", Some(false));
}

#[test]
fn php_4_3_unsat() {
    let (nv, clauses) = generate_php(4, 3);
    solve_and_verify(nv, &clauses, "PHP(4,3)", Some(false));
}

#[test]
fn php_5_4_unsat() {
    let (nv, clauses) = generate_php(5, 4);
    solve_and_verify(nv, &clauses, "PHP(5,4)", Some(false));
}

#[test]
fn php_6_5_unsat() {
    let (nv, clauses) = generate_php(6, 5);
    solve_and_verify(nv, &clauses, "PHP(6,5)", Some(false));
}

#[test]
fn php_7_6_unsat() {
    let (nv, clauses) = generate_php(7, 6);
    solve_and_verify_with_timeout(nv, &clauses, "PHP(7,6)", Some(false), 15);
}

#[test]
fn php_8_7_unsat() {
    let (nv, clauses) = generate_php(8, 7);
    // PHP(8,7) may timeout; that's acceptable. SAT would be a soundness bug.
    solve_and_verify_with_timeout(nv, &clauses, "PHP(8,7)", Some(false), 15);
}

/// PHP(n, n) is satisfiable (n pigeons, n holes -- each pigeon gets one hole).
#[test]
fn php_3_3_sat() {
    let (nv, clauses) = generate_php(3, 3);
    solve_and_verify(nv, &clauses, "PHP(3,3)", Some(true));
}

#[test]
fn php_4_4_sat() {
    let (nv, clauses) = generate_php(4, 4);
    solve_and_verify(nv, &clauses, "PHP(4,4)", Some(true));
}

#[test]
fn php_5_5_sat() {
    let (nv, clauses) = generate_php(5, 5);
    solve_and_verify(nv, &clauses, "PHP(5,5)", Some(true));
}

// ===========================================================================
// TEST: Pigeonhole with no-inprocessing (differential)
// ===========================================================================

#[test]
fn php_differential_3_2() {
    let (nv, clauses) = generate_php(3, 2);
    let r1 = solve_and_verify(nv, &clauses, "PHP(3,2)-default", Some(false));
    let r2 = solve_no_inprocessing_and_verify(nv, &clauses, "PHP(3,2)-baseline", Some(false));
    assert_eq!(classify(&r1), classify(&r2), "PHP(3,2) disagreement");
}

#[test]
fn php_differential_4_3() {
    let (nv, clauses) = generate_php(4, 3);
    let r1 = solve_and_verify(nv, &clauses, "PHP(4,3)-default", Some(false));
    let r2 = solve_no_inprocessing_and_verify(nv, &clauses, "PHP(4,3)-baseline", Some(false));
    assert_eq!(classify(&r1), classify(&r2), "PHP(4,3) disagreement");
}

#[test]
fn php_differential_5_4() {
    let (nv, clauses) = generate_php(5, 4);
    let r1 = solve_and_verify(nv, &clauses, "PHP(5,4)-default", Some(false));
    let r2 = solve_no_inprocessing_and_verify(nv, &clauses, "PHP(5,4)-baseline", Some(false));
    let v1 = classify(&r1);
    let v2 = classify(&r2);
    if v1 != Verdict::Unknown && v2 != Verdict::Unknown {
        assert_eq!(v1, v2, "PHP(5,4) disagreement");
    }
}

// ===========================================================================
// TEST: Graph Coloring (complete graph)
// ===========================================================================

/// K_4 with 3 colors: UNSAT (chromatic number of K_4 is 4)
#[test]
fn graph_coloring_k4_3colors_unsat() {
    let (nv, clauses) = generate_graph_coloring_complete(4, 3);
    solve_and_verify(nv, &clauses, "K4-3color", Some(false));
}

/// K_5 with 4 colors: UNSAT
#[test]
fn graph_coloring_k5_4colors_unsat() {
    let (nv, clauses) = generate_graph_coloring_complete(5, 4);
    solve_and_verify(nv, &clauses, "K5-4color", Some(false));
}

/// K_6 with 5 colors: UNSAT
#[test]
fn graph_coloring_k6_5colors_unsat() {
    let (nv, clauses) = generate_graph_coloring_complete(6, 5);
    solve_and_verify_with_timeout(nv, &clauses, "K6-5color", Some(false), 15);
}

/// K_3 with 3 colors: SAT (exact chromatic number)
#[test]
fn graph_coloring_k3_3colors_sat() {
    let (nv, clauses) = generate_graph_coloring_complete(3, 3);
    solve_and_verify(nv, &clauses, "K3-3color", Some(true));
}

/// K_4 with 4 colors: SAT
#[test]
fn graph_coloring_k4_4colors_sat() {
    let (nv, clauses) = generate_graph_coloring_complete(4, 4);
    solve_and_verify(nv, &clauses, "K4-4color", Some(true));
}

/// K_5 with 5 colors: SAT
#[test]
fn graph_coloring_k5_5colors_sat() {
    let (nv, clauses) = generate_graph_coloring_complete(5, 5);
    solve_and_verify(nv, &clauses, "K5-5color", Some(true));
}

// ===========================================================================
// TEST: Ordering cycle (UNSAT)
// ===========================================================================

#[test]
fn ordering_cycle_3_unsat() {
    let (nv, clauses) = generate_ordering_cycle(3);
    solve_and_verify(nv, &clauses, "order-cycle-3", Some(false));
}

#[test]
fn ordering_cycle_5_unsat() {
    let (nv, clauses) = generate_ordering_cycle(5);
    solve_and_verify(nv, &clauses, "order-cycle-5", Some(false));
}

#[test]
fn ordering_cycle_10_unsat() {
    let (nv, clauses) = generate_ordering_cycle(10);
    solve_and_verify(nv, &clauses, "order-cycle-10", Some(false));
}

#[test]
fn ordering_cycle_20_unsat() {
    let (nv, clauses) = generate_ordering_cycle(20);
    solve_and_verify(nv, &clauses, "order-cycle-20", Some(false));
}

// ===========================================================================
// TEST: Random 3-SAT near phase transition
// ===========================================================================

/// Run a batch of random 3-SAT instances at the phase transition ratio.
/// Verifies SAT models against original clauses. Does not assert SAT/UNSAT
/// outcome since these are random.
#[test]
fn random_3sat_phase_transition_batch() {
    let mut rng = Rng::new(0x7904_DEAD_BEEF_0001);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;
    let mut unknown_count = 0usize;

    // 50 instances, 20 variables, ~85 clauses (ratio 4.267)
    for i in 0..50 {
        let num_vars = 20u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("random-3sat-20v-{i}");

        let result = solve_and_verify(nv, &clauses, &label, None);
        match classify(&result) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => unknown_count += 1,
        }
    }

    eprintln!(
        "random 3-SAT phase transition (20v): {sat_count} SAT, {unsat_count} UNSAT, {unknown_count} unknown (of 50)"
    );
    // At the phase transition, roughly half should be SAT and half UNSAT.
    // We just need at least some of each to have meaningful coverage.
    assert!(
        sat_count + unsat_count > 0,
        "Expected at least one random 3-SAT to resolve"
    );
}

/// Larger instances: 50 variables, ~213 clauses.
#[test]
fn random_3sat_50v_phase_transition() {
    let mut rng = Rng::new(0x7904_DEAD_BEEF_0002);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..30 {
        let num_vars = 50u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("random-3sat-50v-{i}");

        let result = solve_and_verify_with_timeout(nv, &clauses, &label, None, 10);
        match classify(&result) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!("random 3-SAT phase transition (50v): {sat_count} SAT, {unsat_count} UNSAT (of 30)");
    assert!(
        sat_count + unsat_count > 0,
        "Expected at least one 50v random 3-SAT to resolve within 10s"
    );
}

/// 100 variables near phase transition -- exercises more of the CDCL machinery.
#[test]
fn random_3sat_100v_phase_transition() {
    let mut rng = Rng::new(0x7904_DEAD_BEEF_0003);
    let mut sat_count = 0usize;
    let mut unsat_count = 0usize;

    for i in 0..20 {
        let num_vars = 100u32;
        let num_clauses = (f64::from(num_vars) * 4.267).round() as usize;
        let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);
        let label = format!("random-3sat-100v-{i}");

        let result = solve_and_verify_with_timeout(nv, &clauses, &label, None, 10);
        match classify(&result) {
            Verdict::Sat => sat_count += 1,
            Verdict::Unsat => unsat_count += 1,
            Verdict::Unknown => {}
        }
    }

    eprintln!("random 3-SAT phase transition (100v): {sat_count} SAT, {unsat_count} UNSAT (of 20)");
}

// ===========================================================================
// TEST: Known-SAT formulas with model verification
// ===========================================================================

/// Trivially satisfiable: single positive unit clause.
#[test]
fn trivial_sat_unit_clause() {
    let clauses = vec![vec![Literal::positive(Variable::new(0))]];
    solve_and_verify(1, &clauses, "unit-pos", Some(true));
}

/// Satisfiable: 3 independent positive units.
#[test]
fn sat_independent_units() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::positive(Variable::new(1))],
        vec![Literal::positive(Variable::new(2))],
    ];
    solve_and_verify(3, &clauses, "independent-units", Some(true));
}

/// Satisfiable: mixed polarity units (forces a specific assignment).
#[test]
fn sat_mixed_units() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::negative(Variable::new(1))],
        vec![Literal::positive(Variable::new(2))],
        vec![Literal::negative(Variable::new(3))],
    ];
    solve_and_verify(4, &clauses, "mixed-units", Some(true));
}

/// Empty formula is SAT.
#[test]
fn sat_empty_formula() {
    let clauses: Vec<Vec<Literal>> = vec![];
    solve_and_verify(0, &clauses, "empty-formula", Some(true));
}

/// Single empty clause is UNSAT.
#[test]
fn unsat_empty_clause() {
    let clauses = vec![vec![]];
    solve_and_verify(0, &clauses, "empty-clause", Some(false));
}

/// Formula with forced SAT assignment (generated).
#[test]
fn generated_forced_sat_small() {
    let mut rng = Rng::new(0x0790_45A7_0001);
    for i in 0..20 {
        let (nv, clauses, _assignment) = generate_forced_sat(&mut rng, 15);
        let label = format!("forced-sat-15v-{i}");
        solve_and_verify(nv, &clauses, &label, Some(true));
    }
}

/// Larger forced SAT formulas.
#[test]
fn generated_forced_sat_medium() {
    let mut rng = Rng::new(0x0790_45A7_0002);
    for i in 0..10 {
        let (nv, clauses, _assignment) = generate_forced_sat(&mut rng, 50);
        let label = format!("forced-sat-50v-{i}");
        solve_and_verify(nv, &clauses, &label, Some(true));
    }
}
