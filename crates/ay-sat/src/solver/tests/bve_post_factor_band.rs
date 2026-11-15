// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-bve-post-factor-band`: the Default route's BVE sparse band judged on
//! the formula factoring leaves. The predicate qualifies only with the switch
//! on, BVE still off, extension variables added by factoring, and the factored
//! formula inside the band.

use super::*;

fn switched(value: Option<bool>) -> ay_core::sat_ab_test_override::Guard {
    ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        bve_post_factor_band: value,
        ..Default::default()
    })
}

/// A solver over `vars` variables holding `clauses` binary clauses, as if
/// factoring had added `factored` variables on top of `vars - factored`.
fn solver_after_factoring(vars: usize, clauses: usize, factored: usize) -> Solver {
    let mut solver = Solver::new(vars);
    for i in 0..clauses {
        let a = (i % vars) as u32;
        let b = ((i * 7 + 1) % vars) as u32;
        let b = if a == b { (b + 1) % vars as u32 } else { b };
        assert!(solver.add_clause(vec![
            Literal::positive(Variable(a)),
            Literal::negative(Variable(b)),
        ]));
    }
    solver.inproc_ctrl.bve.enabled = false;
    solver.cold.pre_factor_num_vars = vars - factored;
    solver
}

#[test]
fn a_factored_formula_inside_the_band_qualifies() {
    let _guard = switched(Some(true));
    // 400 clauses over 100 variables: density 4, factoring added 40.
    let solver = solver_after_factoring(100, 400, 40);
    assert!(solver.bve_post_factor_band_qualifies());
}

#[test]
fn nothing_qualifies_with_the_switch_off() {
    let _guard = switched(None);
    let solver = solver_after_factoring(100, 400, 40);
    assert!(!solver.bve_post_factor_band_qualifies());
}

#[test]
fn a_formula_factoring_did_not_touch_does_not_qualify() {
    let _guard = switched(Some(true));
    let solver = solver_after_factoring(100, 400, 0);
    assert!(!solver.bve_post_factor_band_qualifies());
}

#[test]
fn a_factored_formula_still_above_the_band_does_not_qualify() {
    let _guard = switched(Some(true));
    // 1,500 clauses over 100 variables: density 15 > 12.
    let solver = solver_after_factoring(100, 1_500, 40);
    assert!(!solver.bve_post_factor_band_qualifies());
}

#[test]
fn bve_already_on_is_left_alone() {
    let _guard = switched(Some(true));
    let mut solver = solver_after_factoring(100, 400, 40);
    solver.inproc_ctrl.bve.enabled = true;
    assert!(!solver.bve_post_factor_band_qualifies());
}
