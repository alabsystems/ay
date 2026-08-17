// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `group_soundness::sat_soundness_regression` to preserve test FQNs.

#[test]
fn feature_isolation_vivify() {
    test_single_feature("vivify", |s| s.set_vivify_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_subsume() {
    test_single_feature("subsume", |s| s.set_subsume_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_probe() {
    test_single_feature("probe", |s| s.set_probe_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_bve() {
    test_single_feature("bve", |s| s.set_bve_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_bce() {
    test_single_feature("bce", |s| s.set_bce_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_factor() {
    test_single_feature("factor", |s| s.set_factor_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_decompose() {
    test_single_feature(
        "decompose",
        |s| s.set_decompose_enabled(true),
        20,
        0..20,
        4.267,
    );
}

#[test]
fn feature_isolation_gate() {
    test_single_feature("gate", |s| s.set_gate_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_congruence() {
    test_single_feature(
        "congruence",
        |s| s.set_congruence_enabled(true),
        20,
        0..20,
        4.267,
    );
}

#[test]
fn feature_isolation_sweep() {
    test_single_feature("sweep", |s| s.set_sweep_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_condition() {
    test_single_feature(
        "condition",
        |s| s.set_condition_enabled(true),
        20,
        0..20,
        4.267,
    );
}

#[test]
fn feature_isolation_backbone() {
    test_single_feature(
        "backbone",
        |s| s.set_backbone_enabled(true),
        20,
        0..20,
        4.267,
    );
}

#[test]
fn feature_isolation_shrink() {
    test_single_feature("shrink", |s| s.set_shrink_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_cce() {
    test_single_feature("cce", |s| s.set_cce_enabled(true), 20, 0..20, 4.267);
}

#[test]
fn feature_isolation_transred() {
    test_single_feature(
        "transred",
        |s| s.set_transred_enabled(true),
        20,
        0..20,
        4.267,
    );
}

#[test]
fn feature_isolation_htr() {
    test_single_feature("htr", |s| s.set_htr_enabled(true), 20, 0..20, 4.267);
}

// ===========================================================================
// Test 5: Assumption-based solving soundness
// ===========================================================================

#[test]
fn assumption_sat_model_satisfies_clauses_and_assumptions() {
    let num_vars: u32 = 15;

    for seed in 0..30u64 {
        let mut rng = Rng::new(0xABCD_0000_u64.wrapping_add(seed));
        // Use a low ratio so the base formula is likely SAT.
        let clauses = generate_3sat_at_ratio(&mut rng, num_vars, 2.0);
        let label = format!("assume-sat-s{seed}");

        let mut solver = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver.add_clause(clause.clone());
        }

        // Pick 2 random assumption literals.
        let a1_var = rng.next_bounded(num_vars as u64) as u32;
        let a1 = if rng.next_bool() {
            Literal::positive(Variable::new(a1_var))
        } else {
            Literal::negative(Variable::new(a1_var))
        };
        let a2_var = rng.next_bounded(num_vars as u64) as u32;
        let a2 = if rng.next_bool() {
            Literal::positive(Variable::new(a2_var))
        } else {
            Literal::negative(Variable::new(a2_var))
        };
        let assumptions = vec![a1, a2];

        let result = solver.solve_with_assumptions(&assumptions).into_inner();

        match &result {
            ay_sat::AssumeResult::Sat(model) => {
                // Verify model satisfies all original clauses.
                if let Some(ci) = find_violated_clause(&clauses, model) {
                    panic!(
                        "SOUNDNESS BUG [{label}]: assumption-SAT model violates clause {ci}: {:?}",
                        clauses[ci]
                    );
                }
                // Verify model satisfies all assumption literals.
                for assume_lit in &assumptions {
                    let var_idx = assume_lit.variable().index();
                    let model_val = model.get(var_idx).copied().unwrap_or(false);
                    let expected = assume_lit.is_positive();
                    assert_eq!(
                        model_val, expected,
                        "SOUNDNESS BUG [{label}]: model does not satisfy assumption {assume_lit:?}"
                    );
                }
            }
            ay_sat::AssumeResult::Unsat(core, _) => {
                // Unsat core must be a subset of the assumptions.
                for core_lit in core {
                    assert!(
                        assumptions.contains(core_lit),
                        "SOUNDNESS BUG [{label}]: unsat core contains {core_lit:?} \
                         which is not in assumptions {assumptions:?}"
                    );
                }
            }
            ay_sat::AssumeResult::Unknown => {}
            _ => unreachable!(),
        }
    }
}

/// Verify that contradictory assumptions yield UNSAT with a core.
#[test]
fn assumption_contradictory_pair_yields_unsat() {
    let num_vars: u32 = 10;

    for var_idx in 0..num_vars {
        let mut solver = Solver::new(num_vars as usize);
        // Add a trivially satisfiable clause.
        solver.add_clause(vec![Literal::positive(Variable::new(0))]);

        let pos = Literal::positive(Variable::new(var_idx));
        let neg = Literal::negative(Variable::new(var_idx));
        let assumptions = vec![pos, neg];

        let result = solver.solve_with_assumptions(&assumptions).into_inner();

        match &result {
            ay_sat::AssumeResult::Unsat(core, _) => {
                // Core should contain at least one of the contradictory pair.
                let has_pos = core.contains(&pos);
                let has_neg = core.contains(&neg);
                assert!(
                    has_pos || has_neg,
                    "contradictory assumption var={var_idx}: unsat core {core:?} \
                     missing both {pos:?} and {neg:?}"
                );
            }
            ay_sat::AssumeResult::Sat(_) => {
                panic!("SOUNDNESS BUG: contradictory assumptions for var {var_idx} returned SAT");
            }
            ay_sat::AssumeResult::Unknown => {
                // Acceptable: solver gave up.
            }
            _ => unreachable!(),
        }
    }
}

// ===========================================================================
// Test 6: Clause density sweep across phase transition
// ===========================================================================

/// Sweep the clause-to-variable ratio from 3.0 to 5.5 in steps of 0.25
/// with 10 seeds per step. Verify model correctness at every step.
#[test]
fn clause_density_sweep_phase_transition() {
    let num_vars: u32 = 20;
    let seeds_per_step = 10;

    // Ratios from 3.0 to 5.5 in steps of 0.25 => 11 steps
    let mut ratio = 3.0f64;
    let mut sat_by_ratio = Vec::new();

    #[allow(clippy::while_float)]
    while ratio <= 5.501 {
        let mut sat_count = 0usize;
        let mut unsat_count = 0usize;

        for seed_offset in 0..seeds_per_step {
            let seed = 0x7777_u64
                .wrapping_mul((ratio * 1000.0) as u64)
                .wrapping_add(seed_offset);
            let mut rng = Rng::new(seed);
            let clauses = generate_3sat_at_ratio(&mut rng, num_vars, ratio);
            let label = format!("density-v{num_vars}-r{ratio:.2}-s{seed_offset}");

            let result = solve_and_verify(num_vars as usize, &clauses, &label, None);

            match result {
                SatResult::Sat(_) => sat_count += 1,
                SatResult::Unsat(_) => unsat_count += 1,
                _ => panic!("20-var formula should not return Unknown"),
            }
        }

        sat_by_ratio.push((ratio, sat_count, unsat_count));
        ratio += 0.25;
    }

    // Verify monotonicity: SAT fraction should generally decrease as ratio
    // increases (not a strict requirement due to randomness, but a sanity
    // check).
    let first_sat_frac = sat_by_ratio[0].1 as f64 / seeds_per_step as f64;
    let last_sat_frac = sat_by_ratio.last().unwrap().1 as f64 / seeds_per_step as f64;
    assert!(
        first_sat_frac >= last_sat_frac,
        "phase transition sanity: SAT fraction at ratio {:.2} ({first_sat_frac:.1}) should be \
         >= fraction at ratio {:.2} ({last_sat_frac:.1})",
        sat_by_ratio[0].0,
        sat_by_ratio.last().unwrap().0,
    );

    eprintln!("clause_density_sweep results:");
    for (r, sat, unsat) in &sat_by_ratio {
        eprintln!("  ratio={r:.2}: sat={sat} unsat={unsat}");
    }
}

// ===========================================================================
// Test 7: Repeated solve with clause addition between solves
// ===========================================================================

/// Create a solver, solve, add more clauses, solve again. Verify that internal
/// state cleanup preserves soundness across multiple solve calls.
#[test]
fn repeated_solve_with_incremental_clauses() {
    let num_vars: u32 = 15;

    for seed in 0..20u64 {
        let mut rng = Rng::new(0xBEEF_CAFE_u64.wrapping_add(seed));
        let label_base = format!("incr-s{seed}");

        let mut solver = Solver::new(num_vars as usize);

        // Phase 1: add a few clauses, solve.
        let clauses_phase1 = generate_random_ksat(&mut rng, num_vars, 20, 3);
        let mut all_clauses = clauses_phase1.clone();
        for clause in &clauses_phase1 {
            solver.add_clause(clause.clone());
        }

        let result1 = solver.solve().into_inner();
        verify_result(&result1, &all_clauses, &format!("{label_base}-p1"), None);

        // Phase 2: add more clauses, solve again.
        let clauses_phase2 = generate_random_ksat(&mut rng, num_vars, 30, 3);
        for clause in &clauses_phase2 {
            all_clauses.push(clause.clone());
            solver.add_clause(clause.clone());
        }

        let result2 = solver.solve().into_inner();
        verify_result(&result2, &all_clauses, &format!("{label_base}-p2"), None);

        // Phase 3: add even more clauses (high density, likely UNSAT).
        let clauses_phase3 = generate_random_ksat(&mut rng, num_vars, 60, 3);
        for clause in &clauses_phase3 {
            all_clauses.push(clause.clone());
            solver.add_clause(clause.clone());
        }

        let result3 = solver.solve().into_inner();
        verify_result(&result3, &all_clauses, &format!("{label_base}-p3"), None);

        // Monotonicity: if phase N was UNSAT, phase N+1 must also be UNSAT
        // (adding clauses can only make a formula harder).
        if matches!(result1, SatResult::Unsat(_)) {
            assert!(
                matches!(result2, SatResult::Unsat(_)),
                "SOUNDNESS BUG [{label_base}]: phase1 UNSAT but phase2 not UNSAT"
            );
        }
        if matches!(result2, SatResult::Unsat(_)) {
            assert!(
                matches!(result3, SatResult::Unsat(_)),
                "SOUNDNESS BUG [{label_base}]: phase2 UNSAT but phase3 not UNSAT"
            );
        }
    }
}

// ===========================================================================
// Test 8: Cross-configuration differential (default vs no-inprocessing)
// ===========================================================================

/// Solve the same formula with default config and with all inprocessing
/// disabled. The results must agree (both SAT or both UNSAT).
#[test]
fn cross_config_default_vs_no_inprocessing() {
    let num_vars: u32 = 20;
    let ratio = 4.267;
    let num_seeds = 30;

    let mut agree = 0usize;
    let mut disagree = Vec::new();

    for seed in 0..num_seeds {
        let mut rng = Rng::new(0xFACE_u64.wrapping_add(seed));
        let clauses = generate_3sat_at_ratio(&mut rng, num_vars, ratio);

        // Default configuration.
        let mut solver_default = Solver::new(num_vars as usize);
        for clause in &clauses {
            solver_default.add_clause(clause.clone());
        }
        let result_default = solver_default.solve().into_inner();
        verify_result(
            &result_default,
            &clauses,
            &format!("crosscfg-default-s{seed}"),
            None,
        );

        // No inprocessing.
        let mut solver_noinproc = Solver::new(num_vars as usize);
        super::common::disable_all_inprocessing(&mut solver_noinproc);
        for clause in &clauses {
            solver_noinproc.add_clause(clause.clone());
        }
        let result_noinproc = solver_noinproc.solve().into_inner();
        verify_result(
            &result_noinproc,
            &clauses,
            &format!("crosscfg-noinproc-s{seed}"),
            None,
        );

        let d_sat = matches!(result_default, SatResult::Sat(_));
        let d_unsat = matches!(result_default, SatResult::Unsat(_));
        let n_sat = matches!(result_noinproc, SatResult::Sat(_));
        let n_unsat = matches!(result_noinproc, SatResult::Unsat(_));

        if (d_sat && n_sat) || (d_unsat && n_unsat) {
            agree += 1;
        } else if (d_sat && n_unsat) || (d_unsat && n_sat) {
            disagree.push(format!(
                "seed {seed}: default={} noinproc={}",
                if d_sat { "SAT" } else { "UNSAT" },
                if n_sat { "SAT" } else { "UNSAT" },
            ));
        }
        // If either is Unknown, we skip the comparison.
    }

    assert!(
        disagree.is_empty(),
        "SOUNDNESS BUG: cross-config disagreements ({}):\n{}",
        disagree.len(),
        disagree.join("\n"),
    );
    eprintln!("cross_config_default_vs_no_inprocessing: {agree} agreements");
}

// ===========================================================================
// Test 9: Larger random 3-SAT (20 vars, 80 clauses) with DRAT
// ===========================================================================

/// The specific parameters requested in the issue: 20 vars, 80 clauses
/// (ratio=4.0), with DRAT verification on UNSAT results.
#[test]
fn random_3sat_20v_80c_drat_verified() {
    let num_vars: u32 = 20;
    let num_clauses = 80;
    let num_seeds = 40;
    let mut verified = 0usize;

    for seed in 0..num_seeds {
        let mut rng = Rng::new(0x9999_u64.wrapping_add(seed));
        let clauses = generate_random_ksat(&mut rng, num_vars, num_clauses, 3);
        let label = format!("20v80c-drat-s{seed}");

        let result = solve_and_verify_drat(num_vars as usize, &clauses, &label, None);

        if !matches!(result, SatResult::Unknown) {
            verified += 1;
        }
    }

    assert_eq!(
        verified, num_seeds as usize,
        "all 20-var, 80-clause formulas should be resolved"
    );
}

// ===========================================================================
// Test 10: Mixed clause widths (2-SAT, 3-SAT, mixed)
// ===========================================================================

/// Test soundness on formulas with mixed clause widths (2-4 literals per
/// clause), which exercises different BCP and inprocessing paths.
#[test]
fn mixed_clause_widths_soundness() {
    let num_vars: u32 = 20;

    for seed in 0..30u64 {
        let mut rng = Rng::new(0xAAAA_BBBB_u64.wrapping_add(seed));
        let num_clauses = 60 + (rng.next_bounded(40) as usize); // 60-99 clauses
        let mut clauses = Vec::with_capacity(num_clauses);

        for _ in 0..num_clauses {
            let width = (rng.next_bounded(3) + 2) as usize; // 2, 3, or 4
            let mut clause = Vec::with_capacity(width);
            for _ in 0..width {
                let var = rng.next_bounded(num_vars as u64) as u32;
                let lit = if rng.next_bool() {
                    Literal::positive(Variable::new(var))
                } else {
                    Literal::negative(Variable::new(var))
                };
                clause.push(lit);
            }
            clauses.push(clause);
        }

        let label = format!("mixed-width-v{num_vars}-s{seed}");
        let _result = solve_and_verify(num_vars as usize, &clauses, &label, None);
    }
}
