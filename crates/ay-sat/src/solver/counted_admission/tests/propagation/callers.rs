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
fn actual_solve_chain_requires_bcp_credit_for_both_sat_and_unsat() {
    for unsat in [false, true] {
        let mut healthy = chain(64, unsat);
        let original = granted(1_000_000, 1 << 20);
        attach(&mut healthy, &original);
        definitive(healthy.solve().into_inner(), unsat);
        assert!(original.usage().unwrap().work_admitted > 64);
        let mut stopped = chain(64, unsat);
        let original = granted(8, 1 << 20);
        attach(&mut stopped, &original);
        assert!(matches!(stopped.solve().into_inner(), SatResult::Unknown));
        assert_eq!(
            stopped.last_unknown_reason(),
            Some(SatUnknownReason::ResourceBudget)
        );
        assert_eq!(original.check(), Err(CountedAdmissionError::WorkExhausted));
    }
}

#[test]
fn assumption_and_ic3_drivers_propagate_typed_bcp_refusal() {
    for ic3 in [false, true] {
        for grant in [8, 1_000_000] {
            let mut solver = Solver::new(64);
            for index in 1..64 {
                assert!(solver.add_clause(vec![lit(index - 1).negated(), lit(index)]));
            }
            if ic3 {
                solver.set_ic3_mode();
            }
            let original = granted(grant, 1 << 20);
            attach(&mut solver, &original);
            let result = if ic3 {
                solver.solve_incremental_ic3(&[lit(0)]).into_inner()
            } else {
                solver.solve_with_assumptions(&[lit(0)]).into_inner()
            };
            if grant == 8 {
                assert!(matches!(result, AssumeResult::Unknown));
                assert_eq!(
                    solver.last_unknown_reason(),
                    Some(SatUnknownReason::ResourceBudget)
                );
            } else {
                assert!(matches!(result, AssumeResult::Sat(_)));
                assert!(original.usage().unwrap().work_admitted > 64);
            }
        }
    }
}

#[test]
fn extension_initialization_cannot_treat_stopped_bcp_as_a_fixpoint() {
    for unsat in [false, true] {
        for grant in [8, 1_000_000] {
            let mut solver = chain(64, unsat);
            attach(&mut solver, &granted(grant, 1 << 20));
            let result = solver.solve_with_extension(&mut NoTheory).into_inner();
            if grant == 8 {
                assert!(matches!(result, SatResult::Unknown));
                assert_eq!(
                    solver.last_unknown_reason(),
                    Some(SatUnknownReason::ResourceBudget)
                );
            } else {
                definitive(result, unsat);
            }
        }
    }
}
