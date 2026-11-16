// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct NoTheory;
impl Extension for NoTheory {
    fn propagate(&mut self, _: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::default()
    }
}

#[test]
fn zero_effort_refuses_all_extension_entry_and_resume_paths() {
    let mut solver = empty_case(false);
    attach(&mut solver, &owner(0));
    assert!(matches!(
        solver.solve_with_extension(&mut NoTheory).into_inner(),
        SatResult::Unknown
    ));
    assert!(matches!(
        solver
            .solve_with_extension_and_assumptions(&mut NoTheory, &[])
            .into_inner(),
        SatResult::Unknown
    ));
    assert!(matches!(
        solver
            .solve_with_extension_and_assumptions_core(&mut NoTheory, &[], None::<&fn() -> bool>)
            .into_inner(),
        AssumeResult::Unknown
    ));
    assert!(matches!(
        solver
            .continue_solving_with_extension(&mut NoTheory, || false)
            .into_inner(),
        SatResult::Unknown
    ));
    assert!(matches!(
        solver
            .resume_solving_with_extension(&mut NoTheory, || false)
            .into_inner(),
        SatResult::Unknown
    ));
    assert!(matches!(
        solver.solve_with_phase_hints(&NoTheory).into_inner(),
        SatResult::Unknown
    ));
    assert_eq!(
        solver.last_unknown_reason(),
        Some(SatUnknownReason::ResourceBudget)
    );
}

#[test]
fn ic3_entry_has_zero_effort_and_healthy_sat_unsat_controls() {
    for grant in [0, 1000] {
        for unsat in [false, true] {
            let mut solver = empty_case(unsat);
            solver.set_ic3_mode();
            let original = owner(grant);
            attach(&mut solver, &original);
            let mut clone = solver.clone_for_ic3();
            let result = clone.solve_incremental_ic3(&[]).into_inner();
            if grant == 0 {
                assert!(matches!(result, AssumeResult::Unknown));
            } else if unsat {
                assert!(matches!(result, AssumeResult::Unsat(..)));
            } else {
                assert!(matches!(result, AssumeResult::Sat(_)));
            }
            assert_eq!(
                clone.counted_admission_usage().unwrap().unwrap(),
                original.usage().unwrap()
            );
        }
    }
}

#[test]
fn entry_credit_is_not_renewed_by_continue_or_resume() {
    let mut solver = empty_case(false);
    let original = owner(2);
    attach(&mut solver, &original);
    definitive(solver.solve().into_inner(), false);
    assert_eq!(original.usage().unwrap().work_remaining, 0);
    assert!(matches!(
        solver
            .continue_solving_with_extension(&mut NoTheory, || false)
            .into_inner(),
        SatResult::Unknown
    ));
    assert!(matches!(
        solver
            .resume_solving_with_extension(&mut NoTheory, || false)
            .into_inner(),
        SatResult::Unknown
    ));
    assert_eq!(original.usage().unwrap().work_admitted, 2);
}
