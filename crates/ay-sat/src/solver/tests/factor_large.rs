// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-factor-large` (lever 3): the switch opens the factor gates only in
//! its band, only when set, and never under LRAT or after an incremental call.

use super::*;
use crate::solver::factor_large::factor_large_band_counts;
use crate::solver::inprocessing::FactorSkipReason;

/// A formula the expensive-pass size gate refuses on its variable count, with
/// a 6x6 grid of binaries that factoring compresses through one fresh
/// variable: 36 clauses become 12.
fn large_grid_solver(proof: Option<ProofOutput>) -> Solver {
    let num_vars = PREPROCESS_EXPENSIVE_MAX_VARS + 1;
    let mut solver: Solver = match proof {
        Some(proof) => Solver::with_proof_output(num_vars, proof),
        None => Solver::new(num_vars),
    };
    for i in 0..6 {
        for j in 0..6 {
            solver.add_clause_db(
                &[
                    Literal::positive(Variable(i)),
                    Literal::positive(Variable(100 + j)),
                ],
                false,
            );
        }
    }
    solver.initialize_watches();
    solver
}

fn switched(value: Option<bool>) -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        factor_large: value,
        ..Default::default()
    })
}

#[test]
fn the_band_is_the_refused_region_below_the_giant_and_dense_ceilings() {
    // k275 (1,529,550 vars, 8,599,702 clauses, density 5.6) is in.
    assert!(factor_large_band_counts(1_529_550, 8_599_702));
    // Just over the variable gate with few clauses is in; at the gate is not refused.
    assert!(factor_large_band_counts(200_001, 6));
    assert!(!factor_large_band_counts(200_000, 3_000_000));
    // Just over the clause gate is in when the density allows it.
    assert!(factor_large_band_counts(200_000, 3_000_001));
    // Above 2M variables, above 10M clauses, or denser than 20: out.
    assert!(!factor_large_band_counts(2_000_001, 6));
    assert!(!factor_large_band_counts(1_000_000, 10_000_001));
    assert!(!factor_large_band_counts(100_000, 5_000_000));
    assert!(!factor_large_band_counts(0, 5_000_000));
}

#[test]
fn false_keeps_the_delay_gate_closed_on_a_large_formula_and_unset_opens_it() {
    let _switches = switched(Some(false));
    let solver = large_grid_solver(None);
    assert!(solver.factor_delay_gate_holds());
    assert!(!solver.should_preprocess_factor());
    assert!(!solver.factor_large_unlock_active());
    drop(_switches);
    // The default since 2026-09-18: unset reads as on.
    let _switches = switched(None);
    let solver = large_grid_solver(None);
    assert!(solver.factor_large_unlock_active());
    assert!(!solver.factor_delay_gate_holds());
}

#[test]
fn the_switch_opens_the_delay_gate_in_the_band_but_not_under_lrat_or_incremental() {
    let _switches = switched(Some(true));
    let mut solver = large_grid_solver(None);
    assert!(solver.factor_large_unlock_active());
    assert!(!solver.factor_delay_gate_holds());
    assert!(solver.should_preprocess_factor());

    solver.cold.lrat_enabled = true;
    assert!(
        !solver.factor_large_unlock_active(),
        "LRAT clamps factoring; the switch stays closed"
    );
    assert!(solver.factor_delay_gate_holds());
    solver.cold.lrat_enabled = false;

    solver.cold.has_been_incremental = true;
    assert!(
        !solver.factor_large_unlock_active(),
        "an incremental solver keeps the shipped gates"
    );
    assert!(solver.factor_delay_gate_holds());
}

#[test]
fn the_switch_leaves_a_formula_inside_the_size_gate_alone() {
    let _switches = switched(Some(true));
    // 12 variables: the size gate admits it, so the switch has nothing to open,
    // and the delay gate is what it was (log10(12) = 1 <= 4: open anyway).
    let mut solver: Solver = Solver::new(12);
    solver.add_clause_db(
        &[
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ],
        false,
    );
    solver.initialize_watches();
    assert!(!solver.factor_large_unlock_active());
    assert!(!solver.factor_delay_gate_holds());
}

#[test]
fn in_search_factoring_runs_on_a_large_formula_only_under_the_switch() {
    for (value, expect_factoring) in [(None, true), (Some(false), false), (Some(true), true)] {
        let _switches = switched(value);
        let proof = ProofOutput::drat_text(Vec::<u8>::new());
        let mut solver = large_grid_solver(Some(proof));
        solver.disable_all_inprocessing();
        solver.set_factor_enabled(true);
        solver.cold.next_inprobe_conflict = 0;
        solver.inproc_ctrl.factor.next_conflict = 0;
        solver.num_conflicts = FACTOR_INTERVAL;
        let added_before = solver.proof_manager.as_ref().map_or(0, |m| m.added_count());

        assert!(
            !solver.run_restart_inprocessing(),
            "switch={value:?}: no UNSAT here"
        );

        let factored = solver.cold.factor_factored_total;
        let delay_guard = solver.cold.factor_skip_counts[FactorSkipReason::DelayGuard.index()];
        let added = solver.proof_manager.as_ref().map_or(0, |m| m.added_count()) - added_before;
        if expect_factoring {
            assert!(factored > 0, "switch={value:?}: the grid must factor");
            assert_eq!(delay_guard, 0, "switch={value:?}");
            assert!(
                added > 0,
                "switch={value:?}: factoring must write its proof steps"
            );
        } else {
            assert_eq!(factored, 0, "switch={value:?}");
            assert_eq!(
                delay_guard, 1,
                "switch={value:?}: the delay gate must be the skip"
            );
            assert_eq!(added, 0, "switch={value:?}");
        }
    }
}

/// The pass polls the solve's stop between applications: an interrupted solve
/// factors nothing, installs nothing, and counts the stop.
#[test]
fn an_interrupted_solve_ends_the_factor_pass_before_its_first_application() {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    let _switches = switched(Some(true));
    let proof = ProofOutput::drat_text(Vec::<u8>::new());
    let mut solver = large_grid_solver(Some(proof));
    solver.disable_all_inprocessing();
    solver.set_factor_enabled(true);
    solver.cold.next_inprobe_conflict = 0;
    solver.inproc_ctrl.factor.next_conflict = 0;
    solver.num_conflicts = FACTOR_INTERVAL;
    let clauses_before = solver.arena.active_clause_count();
    let interrupt = Arc::new(AtomicBool::new(true));
    solver.set_interrupt(Arc::clone(&interrupt));
    let added_before = solver.proof_manager.as_ref().map_or(0, |m| m.added_count());

    solver.factorize();

    assert_eq!(solver.cold.factor_factored_total, 0);
    assert_eq!(solver.cold.factor_stops, 1);
    assert_eq!(solver.arena.active_clause_count(), clauses_before);
    assert_eq!(
        solver.proof_manager.as_ref().map_or(0, |m| m.added_count()),
        added_before
    );

    // Lifted, the same solver factors the grid.
    interrupt.store(false, Ordering::SeqCst);
    solver.inproc_ctrl.factor.next_conflict = 0;
    solver.factorize();
    assert!(solver.cold.factor_factored_total > 0);
    assert_eq!(solver.cold.factor_stops, 1);
}

/// `--sat-giant-band-max-vars` (plan-2 lever 7) raises the band's variable
/// ceiling for the factor band and the giant raw-BVE band together; unset,
/// both stay at 2M.
#[test]
fn the_giant_band_ceiling_switch_raises_both_bands_together() {
    let baseballcover = (3_560_000usize, 7_121_306usize);
    let giant_control = (7_300_000usize, 40_700_000usize);
    {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());
        assert_eq!(crate::variant::giant_band_max_vars(), 2_000_000);
        assert!(!factor_large_band_counts(baseballcover.0, baseballcover.1));
    }
    {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            giant_band_max_vars: Some(4_100_000),
            ..Default::default()
        });
        assert_eq!(crate::variant::giant_band_max_vars(), 4_100_000);
        assert!(factor_large_band_counts(baseballcover.0, baseballcover.1));
        assert!(
            !factor_large_band_counts(giant_control.0, giant_control.1),
            "the 7.3M-variable control stays out"
        );
        let input = crate::variant::VariantInput::new(
            baseballcover.0,
            baseballcover.1,
            crate::variant::VariantProofMode::Drat,
        );
        let config = crate::SolverVariant::Default.config(input);
        assert!(
            !config.bve_giant_raw_route_active(),
            "the giant raw band still needs --sat-bve-giant-raw true"
        );
    }
    {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            giant_band_max_vars: Some(4_100_000),
            bve_giant_raw: Some(true),
            ..Default::default()
        });
        let input = crate::variant::VariantInput::new(
            baseballcover.0,
            baseballcover.1,
            crate::variant::VariantProofMode::Drat,
        );
        assert!(crate::SolverVariant::Default
            .config(input)
            .bve_giant_raw_route_active());
        let input = crate::variant::VariantInput::new(
            giant_control.0,
            giant_control.1,
            crate::variant::VariantProofMode::Drat,
        );
        assert!(!crate::SolverVariant::Default
            .config(input)
            .bve_giant_raw_route_active());
    }
}

/// `--sat-giant-inproc-permille` applies above 1,000,000 variables only, sets
/// the vivify permille to the value and the probe permille to a quarter.
#[test]
fn the_giant_inprocessing_effort_switch_scales_vivify_and_probe_above_a_million_variables() {
    use crate::solver::xp_probe_vivify::giant_inproc_permille;
    {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());
        assert_eq!(giant_inproc_permille(3_560_000), None);
    }
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        giant_inproc_permille: Some(10),
        ..Default::default()
    });
    assert_eq!(giant_inproc_permille(3_560_000), Some((10, 2)));
    assert_eq!(
        giant_inproc_permille(1_000_000),
        None,
        "at the threshold the shipped budgets stand"
    );
    assert_eq!(giant_inproc_permille(2), None);
    let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        giant_inproc_permille: Some(2),
        ..Default::default()
    });
    assert_eq!(
        giant_inproc_permille(3_560_000),
        Some((2, 1)),
        "the probe permille floors at 1"
    );
}

/// `--sat-factor-max-density`: the 6x6 binary grid over 106 variables (36
/// clauses, density 0.34 on the 106 structural variables) factors into 12
/// clauses through one fresh variable; a cap below the density refuses the
/// pass and counts the refusal, a cap above it lets it run.
#[test]
fn the_factor_pass_is_refused_above_the_density_switch() {
    for (cap, expect_factored, expect_skips) in [(Some(0.1), 0, 1), (Some(5.0), 1, 0), (None, 1, 0)]
    {
        let _switches = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
            factor_max_density: cap,
            ..Default::default()
        });
        let mut solver = Solver::new(106);
        for i in 0..6 {
            for j in 0..6 {
                solver.add_clause_db(
                    &[
                        Literal::positive(Variable(i)),
                        Literal::positive(Variable(100 + j)),
                    ],
                    false,
                );
            }
        }
        solver.initialize_watches();
        solver.factorize();
        assert_eq!(
            solver.factor_stats().factored_count,
            expect_factored,
            "cap {cap:?}"
        );
        assert_eq!(solver.density_band_skips().0, expect_skips, "cap {cap:?}");
    }
}
