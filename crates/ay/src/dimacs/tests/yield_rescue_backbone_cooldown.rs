// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// DIMACS solver configuration coverage for the M3 yield-rescue cooldown.

#[test]
fn test_configure_dimacs_solver_yield_rescue_backbone_cooldown_env_gate() {
    // M3 default flip (2026-08-19): the #9084 cooldown ships ON; the tri-state
    // switch's `false` arm is the opt-out. Mirrors the M2 rescue gate above.
    let _lock = lock_env();
    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches::default());

    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.inprocessing_yield_rescue_backbone_cooldown_enabled(),
        "the #9084 yield-rescue backbone cooldown ships default-on (M3)"
    );

    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        yield_rescue_backbone_cooldown: Some(false),
        ..Default::default()
    });
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        !solver.inprocessing_yield_rescue_backbone_cooldown_enabled(),
        "--sat-yield-rescue-backbone-cooldown false must opt out of the M3 default"
    );

    let _g = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        yield_rescue_backbone_cooldown: Some(true),
        ..Default::default()
    });
    let mut solver = SatSolver::new(1);
    configure_dimacs_solver(
        &mut solver,
        stats_output::StatsConfig {
            human: false,
            json: false,
        },
    );
    assert!(
        solver.inprocessing_yield_rescue_backbone_cooldown_enabled(),
        "--sat-yield-rescue-backbone-cooldown true should keep the #9084 cooldown enabled"
    );
}
