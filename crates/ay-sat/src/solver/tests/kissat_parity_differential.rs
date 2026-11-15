// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Every Kissat 4.0.4 parity switch on at once against the defaults, on random
//! formulas mixing binary and ternary clauses near the threshold: the verdicts
//! agree and every model satisfies the formula.

use super::*;

fn mixed_formula(
    num_vars: usize,
    binaries: usize,
    ternaries: usize,
    seed: u64,
) -> Vec<Vec<Literal>> {
    let mut state = seed.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    let mut clauses = Vec::with_capacity(binaries + ternaries);
    for width in std::iter::repeat_n(2, binaries).chain(std::iter::repeat_n(3, ternaries)) {
        let clause = (0..width)
            .map(|_| {
                let var = Variable((next() % num_vars as u64) as u32);
                if next() % 2 == 0 {
                    Literal::positive(var)
                } else {
                    Literal::negative(var)
                }
            })
            .collect();
        clauses.push(clause);
    }
    clauses
}

fn all_parity_switches() -> ay_core::SatAbSwitches {
    let on = Some(true);
    ay_core::SatAbSwitches {
        mode_equiticks: on,
        inproc_nlogn_schedule: on,
        keep_learned_binaries: on,
        bve_kissat_schedule: on,
        reduce_kissat_tiers: on,
        reorder_kissat: on,
        target_kissat: on,
        walk_kissat: on,
        jump_reasons_kissat: on,
        rephase_kissat: on,
        mode_length_kissat: on,
        reduce_kissat_recompute: on,
        target_kissat_pop: on,
        restart_gate_kissat: on,
        initial_phase_kissat: on,
        reduce_schedule_kissat: on,
        best_stable_kissat: on,
        restart_fixpoint_kissat: on,
        mode_delta_kissat: on,
        inproc_passes_kissat: on,
        backbone_binary_kissat: on,
        randec_kissat: on,
        preprocess_kissat: on,
        subst_kissat: on,
        queue_freeze_kissat: on,
        analysis_ticks_kissat: on,
        two_stage_warm_scores_kissat: on,
        vivify_kissat: on,
        eliminate_cadence_kissat: on,
        binary_irredundant_kissat: on,
        probe_round_kissat: on,
        reduce_protect_kissat: on,
        subsume_kissat: on,
        learned_order_kissat: on,
        factor_schedule_kissat: on,
        reluctant_cap_kissat: on,
        reorder_weights_kissat: on,
        shrink_bump_uip_kissat: on,
        shrink_removable_kissat: on,
        sweep_env_kissat: on,
        ..Default::default()
    }
}

/// `Some(true)` SAT with a checked model, `Some(false)` UNSAT, with the
/// conflicts it took.
fn solve(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    switches: ay_core::SatAbSwitches,
) -> (Option<bool>, u64) {
    let _switches = ay_core::sat_ab_test_override::set(switches);
    let mut solver = Solver::new(num_vars);
    solver.set_bve_enabled(true);
    solver.set_congruence_enabled(true);
    solver.set_subsume_enabled(true);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    let verdict = match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            for clause in clauses {
                assert!(
                    clause
                        .iter()
                        .any(|&lit| model[lit.variable().index()] == lit.is_positive()),
                    "model falsifies {clause:?}"
                );
            }
            Some(true)
        }
        SatResult::Unsat(_) => Some(false),
        _ => None,
    };
    (verdict, solver.num_conflicts)
}

#[test]
fn kissat_parity_switches_agree_with_the_defaults() {
    // 300 variables near the 3-SAT threshold: enough conflicts for several
    // reductions and simplification rounds, where most switches act.
    let mut answered = 0;
    let mut hardest = 0;
    for seed in 0..12u64 {
        let clauses = mixed_formula(300, 30, 1_250, seed);
        let (default, _) = solve(300, &clauses, ay_core::SatAbSwitches::default());
        let (kissat, conflicts) = solve(300, &clauses, all_parity_switches());
        assert_eq!(kissat, default, "seed {seed}");
        answered += usize::from(default.is_some());
        hardest = hardest.max(conflicts);
    }
    assert_eq!(answered, 12);
    assert!(
        hardest >= 5_000,
        "the formulas reach reductions and rounds: {hardest}"
    );
}

/// Like `solve`, through the Default DIMACS variant (the AUTO collapse
/// route, feature profile and hot-path plan that `ay solve` uses).
fn solve_default_route(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    switches: ay_core::SatAbSwitches,
) -> Option<bool> {
    let _switches = ay_core::sat_ab_test_override::set(switches);
    let mut solver = Solver::new(num_vars);
    let input =
        crate::VariantInput::new(num_vars, clauses.len(), crate::VariantProofMode::Disabled);
    crate::VariantConfig::for_variant(crate::SolverVariant::Default, input)
        .apply_to_solver(&mut solver);
    for clause in clauses {
        solver.add_clause(clause.clone());
    }
    match solver.solve().into_inner() {
        SatResult::Sat(model) => {
            for clause in clauses {
                assert!(
                    clause
                        .iter()
                        .any(|&lit| model[lit.variable().index()] == lit.is_positive()),
                    "model falsifies {clause:?}"
                );
            }
            Some(true)
        }
        SatResult::Unsat(_) => Some(false),
        _ => None,
    }
}

/// The review's test gap (2026-09-29): dense formulas above the AUTO dense
/// disarm (parsed density 24) and near-threshold ones, through the Default
/// variant, with every parity switch on and with none.
#[test]
fn kissat_parity_switches_agree_on_the_default_route() {
    for seed in 0..6u64 {
        let dense = mixed_formula(50, 0, 1_200, 1_000 + seed);
        let default = solve_default_route(50, &dense, ay_core::SatAbSwitches::default());
        let kissat = solve_default_route(50, &dense, all_parity_switches());
        assert!(default.is_some());
        assert_eq!(kissat, default, "dense seed {seed}");
    }
    for seed in 0..6u64 {
        let clauses = mixed_formula(250, 25, 1_040, 2_000 + seed);
        let default = solve_default_route(250, &clauses, ay_core::SatAbSwitches::default());
        let kissat = solve_default_route(250, &clauses, all_parity_switches());
        assert!(default.is_some());
        assert_eq!(kissat, default, "threshold seed {seed}");
    }
}
