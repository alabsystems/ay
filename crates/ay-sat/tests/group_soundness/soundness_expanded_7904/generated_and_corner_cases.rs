// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::soundness_expanded_7904` to preserve test FQNs.

// ===========================================================================
// TEST: Tseitin formula generation (structured UNSAT)
// ===========================================================================

#[test]
fn tseitin_cycle_3_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(3);
    solve_and_verify(nv, &clauses, "tseitin-cycle-3", Some(false));
}

#[test]
fn tseitin_cycle_5_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(5);
    solve_and_verify(nv, &clauses, "tseitin-cycle-5", Some(false));
}

#[test]
fn tseitin_cycle_7_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(7);
    solve_and_verify(nv, &clauses, "tseitin-cycle-7", Some(false));
}

#[test]
fn tseitin_cycle_15_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(15);
    solve_and_verify(nv, &clauses, "tseitin-cycle-15", Some(false));
}

#[test]
fn tseitin_cycle_51_unsat() {
    let (nv, clauses) = generate_tseitin_cycle(51);
    solve_and_verify(nv, &clauses, "tseitin-cycle-51", Some(false));
}

#[test]
fn tseitin_cycle_4_sat() {
    let (nv, clauses) = generate_tseitin_cycle(4);
    solve_and_verify(nv, &clauses, "tseitin-cycle-4", Some(true));
}

#[test]
fn tseitin_cycle_6_sat() {
    let (nv, clauses) = generate_tseitin_cycle(6);
    solve_and_verify(nv, &clauses, "tseitin-cycle-6", Some(true));
}

#[test]
fn tseitin_cycle_50_sat() {
    let (nv, clauses) = generate_tseitin_cycle(50);
    solve_and_verify(nv, &clauses, "tseitin-cycle-50", Some(true));
}

#[test]
fn tseitin_complete_k5_unsat() {
    let (nv, clauses) = generate_tseitin_complete(5);
    solve_and_verify_with_timeout(nv, &clauses, "tseitin-K5", Some(false), 15);
}

#[test]
fn tseitin_complete_k3_unsat() {
    let (nv, clauses) = generate_tseitin_complete(3);
    solve_and_verify(nv, &clauses, "tseitin-K3", Some(false));
}

// ===========================================================================
// TEST: XOR / parity constraints
// ===========================================================================

#[test]
fn xor_cycle_3_unsat() {
    let (nv, clauses) = generate_xor_unsat(3);
    solve_and_verify(nv, &clauses, "xor-cycle-3", Some(false));
}

#[test]
fn xor_cycle_5_unsat() {
    let (nv, clauses) = generate_xor_unsat(5);
    solve_and_verify(nv, &clauses, "xor-cycle-5", Some(false));
}

#[test]
fn xor_cycle_11_unsat() {
    let (nv, clauses) = generate_xor_unsat(11);
    solve_and_verify(nv, &clauses, "xor-cycle-11", Some(false));
}

#[test]
fn xor_cycle_25_unsat() {
    let (nv, clauses) = generate_xor_unsat(25);
    solve_and_verify(nv, &clauses, "xor-cycle-25", Some(false));
}

#[test]
fn xor_cycle_101_unsat() {
    let (nv, clauses) = generate_xor_unsat(101);
    solve_and_verify(nv, &clauses, "xor-cycle-101", Some(false));
}

#[test]
fn parity_4_forced_unsat() {
    let (nv, clauses) = generate_parity_unsat(4);
    solve_and_verify(nv, &clauses, "parity-4-forced", Some(false));
}

#[test]
fn parity_6_forced_unsat() {
    let (nv, clauses) = generate_parity_unsat(6);
    solve_and_verify(nv, &clauses, "parity-6-forced", Some(false));
}

#[test]
fn parity_10_forced_unsat() {
    let (nv, clauses) = generate_parity_unsat(10);
    solve_and_verify(nv, &clauses, "parity-10-forced", Some(false));
}

// ===========================================================================
// TEST: Cardinality constraints
// ===========================================================================

#[test]
fn cardinality_atmost1_of_5_unsat() {
    let (nv, clauses) = generate_cardinality_unsat(5, 1);
    solve_and_verify(nv, &clauses, "card-amo1-of-5", Some(false));
}

#[test]
fn cardinality_atmost2_of_6_unsat() {
    let (nv, clauses) = generate_cardinality_unsat(6, 2);
    solve_and_verify(nv, &clauses, "card-amo2-of-6", Some(false));
}

#[test]
fn cardinality_atmost3_of_8_unsat() {
    let (nv, clauses) = generate_cardinality_unsat(8, 3);
    solve_and_verify(nv, &clauses, "card-amo3-of-8", Some(false));
}

// ===========================================================================
// TEST: Latin square constraints
// ===========================================================================

#[test]
fn latin_square_2x2_conflict_unsat() {
    let (nv, clauses) = generate_latin_square_unsat();
    solve_and_verify(nv, &clauses, "latin-2x2-conflict", Some(false));
}

// ===========================================================================
// TEST: DRAT proof verification on generated UNSAT instances
// ===========================================================================

#[test]
fn drat_xor_cycle_3() {
    let (nv, clauses) = generate_xor_unsat(3);
    let r = solve_and_verify_drat(nv, &clauses, "drat-xor-3", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_xor_cycle_5() {
    let (nv, clauses) = generate_xor_unsat(5);
    let r = solve_and_verify_drat(nv, &clauses, "drat-xor-5", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_tseitin_cycle_3() {
    let (nv, clauses) = generate_tseitin_cycle(3);
    let r = solve_and_verify_drat(nv, &clauses, "drat-tseitin-3", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_cardinality_atmost1_of_5() {
    let (nv, clauses) = generate_cardinality_unsat(5, 1);
    let r = solve_and_verify_drat(nv, &clauses, "drat-card-amo1-5", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_parity_4_forced() {
    let (nv, clauses) = generate_parity_unsat(4);
    let r = solve_and_verify_drat(nv, &clauses, "drat-parity-4", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

#[test]
fn drat_latin_square_2x2() {
    let (nv, clauses) = generate_latin_square_unsat();
    let r = solve_and_verify_drat(nv, &clauses, "drat-latin-2x2", Some(false));
    assert!(matches!(r, SatResult::Unsat(_)));
}

// ===========================================================================
// TEST: Incremental solve soundness
// ===========================================================================

/// Solve SAT, add contradicting clause via push/pop, re-solve as UNSAT.
#[test]
fn incremental_sat_then_unsat() {
    let mut solver = Solver::new(5);

    solver.add_clause(vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ]);
    solver.add_clause(vec![
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ]);

    let r1 = solver.solve().into_inner();
    assert!(matches!(r1, SatResult::Sat(_)), "first solve should be SAT");

    // Add contradicting units
    solver.add_clause(vec![Literal::positive(Variable::new(4))]);
    solver.add_clause(vec![Literal::negative(Variable::new(4))]);

    let r2 = solver.solve().into_inner();
    assert!(
        matches!(r2, SatResult::Unsat(_)),
        "second solve should be UNSAT after adding x4 AND NOT x4"
    );
}

/// Solve a formula with an extra constraining clause and verify the model
/// satisfies all clauses including the tighter constraint.
#[test]
fn incremental_sat_tighten() {
    let clause1 = vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ];
    let clause2 = vec![
        Literal::positive(Variable::new(2)),
        Literal::positive(Variable::new(3)),
    ];

    let r1 = solve_and_verify(
        4,
        &[clause1.clone(), clause2.clone()],
        "tighten-base",
        Some(true),
    );
    assert!(matches!(r1, SatResult::Sat(_)));

    let clause3 = vec![Literal::negative(Variable::new(0))];
    let tighter = vec![clause1, clause2, clause3];
    let r2 = solve_and_verify(4, &tighter, "tighten-constrained", Some(true));

    if let SatResult::Sat(model) = &r2 {
        assert!(
            model.get(1).copied().unwrap_or(false),
            "x1 must be true since x0 is forced false"
        );
    }
}

// ===========================================================================
// TEST: SAT-to-UNSAT transition via unit clause injection
// ===========================================================================

#[test]
fn sat_to_unsat_unit_injection() {
    let mut rng = Rng::new(0x7904_DEAD);
    for seed_offset in 0..10 {
        let (nv, clauses, assignment) = generate_forced_sat(&mut rng, 10);
        let label = format!("sat-to-unsat-{seed_offset}");

        let r = solve_and_verify(nv, &clauses, &format!("{label}-sat"), Some(true));
        assert!(matches!(r, SatResult::Sat(_)), "{label}: expected SAT");

        let mut unsat_clauses = clauses.clone();
        let forced_val = assignment[0];
        let contra = if forced_val {
            Literal::negative(Variable::new(0))
        } else {
            Literal::positive(Variable::new(0))
        };
        unsat_clauses.push(vec![contra]);
        let original = if forced_val {
            Literal::positive(Variable::new(0))
        } else {
            Literal::negative(Variable::new(0))
        };
        unsat_clauses.push(vec![original]);

        let r2 = solve_and_verify(nv, &unsat_clauses, &format!("{label}-unsat"), Some(false));
        assert!(matches!(r2, SatResult::Unsat(_)), "{label}: expected UNSAT");
    }
}

// ===========================================================================
// TEST: Multi-seed reproducibility (determinism check)
// ===========================================================================

#[test]
fn determinism_same_formula_5_runs() {
    let mut rng = Rng::new(0x7904_DE70);
    let num_vars = 30u32;
    let num_clauses = (f64::from(num_vars) * 3.5).round() as usize;
    let (nv, clauses) = generate_random_3sat(&mut rng, num_vars, num_clauses);

    let mut results = Vec::new();
    for i in 0..5 {
        let r = solve_and_verify(nv, &clauses, &format!("det-run-{i}"), None);
        results.push(classify(&r));
    }
    let first = results[0];
    for (i, r) in results.iter().enumerate().skip(1) {
        assert_eq!(
            first, *r,
            "Determinism failure: run 0 = {first:?}, run {i} = {r:?}"
        );
    }
}

#[test]
fn determinism_unsat_5_runs() {
    let (nv, clauses) = generate_xor_unsat(7);
    for i in 0..5 {
        let r = solve_and_verify(nv, &clauses, &format!("det-unsat-run-{i}"), Some(false));
        assert!(matches!(r, SatResult::Unsat(_)), "run {i}: expected UNSAT");
    }
}

// ===========================================================================
// TEST: Crafted corner cases
// ===========================================================================

#[test]
fn corner_single_var_pos() {
    let clauses = vec![vec![Literal::positive(Variable::new(0))]];
    solve_and_verify(1, &clauses, "single-var-pos", Some(true));
}

#[test]
fn corner_single_var_neg() {
    let clauses = vec![vec![Literal::negative(Variable::new(0))]];
    solve_and_verify(1, &clauses, "single-var-neg", Some(true));
}

#[test]
fn corner_single_var_contradiction() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::negative(Variable::new(0))],
    ];
    solve_and_verify(1, &clauses, "single-var-contra", Some(false));
}

#[test]
fn corner_two_var_full_contradiction() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![Literal::negative(Variable::new(0))],
        vec![Literal::positive(Variable::new(1))],
        vec![Literal::negative(Variable::new(1))],
    ];
    solve_and_verify(2, &clauses, "two-var-full-contra", Some(false));
}

#[test]
fn corner_long_clause_all_negated() {
    let n = 20;
    let long_clause: Vec<Literal> = (0..n)
        .map(|i| Literal::positive(Variable::new(i)))
        .collect();
    let mut clauses = vec![long_clause];
    for i in 0..n {
        clauses.push(vec![Literal::negative(Variable::new(i))]);
    }
    solve_and_verify(n as usize, &clauses, "long-clause-negated", Some(false));
}

#[test]
fn corner_implication_chain_cycle() {
    let n = 15;
    let mut clauses = Vec::new();
    clauses.push(vec![Literal::positive(Variable::new(0))]);
    for i in 0..(n - 1) {
        clauses.push(vec![
            Literal::negative(Variable::new(i)),
            Literal::positive(Variable::new(i + 1)),
        ]);
    }
    clauses.push(vec![
        Literal::negative(Variable::new(n - 1)),
        Literal::negative(Variable::new(0)),
    ]);
    solve_and_verify(n as usize, &clauses, "impl-chain-cycle", Some(false));
}

#[test]
fn corner_all_negative_binary_sat() {
    let n = 10u32;
    let mut clauses = Vec::new();
    for i in 0..(n - 1) {
        clauses.push(vec![
            Literal::negative(Variable::new(i)),
            Literal::negative(Variable::new(i + 1)),
        ]);
    }
    solve_and_verify(n as usize, &clauses, "all-neg-binary", Some(true));
}

#[test]
fn corner_pure_literals_100() {
    let n = 100u32;
    let mut clauses = Vec::new();
    for i in 0..n {
        clauses.push(vec![
            Literal::positive(Variable::new(i)),
            Literal::positive(Variable::new((i + 1) % n)),
        ]);
    }
    solve_and_verify(n as usize, &clauses, "pure-100", Some(true));
}

#[test]
fn corner_tautological_clause_sat() {
    let clauses: Vec<Vec<Literal>> = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(0)),
        ],
        vec![Literal::positive(Variable::new(1))],
    ];
    solve_and_verify(2, &clauses, "tautological-sat", Some(true));
}

#[test]
fn corner_tautological_with_contradiction() {
    let clauses = vec![
        vec![
            Literal::positive(Variable::new(0)),
            Literal::negative(Variable::new(0)),
        ],
        vec![Literal::positive(Variable::new(1))],
        vec![Literal::negative(Variable::new(1))],
    ];
    solve_and_verify(2, &clauses, "tautological-unsat", Some(false));
}

#[test]
fn corner_duplicate_clauses_sat() {
    let clause = vec![
        Literal::positive(Variable::new(0)),
        Literal::positive(Variable::new(1)),
    ];
    let mut clauses = Vec::new();
    for _ in 0..50 {
        clauses.push(clause.clone());
    }
    clauses.push(vec![Literal::negative(Variable::new(2))]);
    solve_and_verify(3, &clauses, "duplicate-50x", Some(true));
}

#[test]
fn corner_subsumed_clauses() {
    let clauses = vec![
        vec![Literal::positive(Variable::new(0))],
        vec![
            Literal::positive(Variable::new(0)),
            Literal::positive(Variable::new(1)),
        ],
        vec![Literal::negative(Variable::new(2))],
        vec![
            Literal::negative(Variable::new(2)),
            Literal::positive(Variable::new(3)),
        ],
    ];
    solve_and_verify(4, &clauses, "subsumed-clauses", Some(true));
}
