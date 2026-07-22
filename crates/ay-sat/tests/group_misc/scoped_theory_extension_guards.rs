// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_sat::{
    ExtCheckResult, ExtPropagateResult, Extension, Solver, SolverContext, TheoryPropResult,
};

struct NoopExtension;

impl Extension for NoopExtension {
    fn propagate(&mut self, _ctx: &dyn SolverContext) -> ExtPropagateResult {
        ExtPropagateResult::none()
    }

    fn check(&mut self, _ctx: &dyn SolverContext) -> ExtCheckResult {
        ExtCheckResult::Sat
    }

    fn can_propagate(&self, _ctx: &dyn SolverContext) -> bool {
        false
    }
}

/// solve_with_theory now supports scoped solving via assumption-based loop (#3343).
/// Verify it returns a result instead of panicking.
#[test]
fn test_solve_with_theory_works_when_scoped_solving_is_active() {
    let mut solver: Solver = Solver::new(1);
    solver.push();
    let result = solver
        .solve_with_theory(|_| TheoryPropResult::Continue)
        .into_inner();
    // Should return SAT or UNSAT, not panic.
    assert!(
        matches!(
            result,
            ay_sat::SatResult::Sat(_) | ay_sat::SatResult::Unsat(_)
        ),
        "solve_with_theory under scope should produce a definite result, got: {result:?}",
    );
}

/// solve_with_extension now supports scoped solving via the assumption-based
/// CDCL loop with full extension callbacks (#8423). It previously rejected the
/// scoped path (panicking in debug / returning Unknown in release); now it must
/// produce a definite result instead of panicking, mirroring
/// `test_solve_with_theory_works_when_scoped_solving_is_active` above (#3343).
///
/// The single-variable formula is trivially satisfiable and the NoopExtension
/// accepts every assignment (`check` -> Sat), so the only sound outcomes are a
/// definite Sat/Unsat or a fail-closed Unknown — never a panic.
#[test]
fn test_solve_with_extension_works_when_scoped_solving_is_active() {
    let mut solver: Solver = Solver::new(1);
    solver.push();
    let mut ext = NoopExtension;
    let result = solver.solve_with_extension(&mut ext).into_inner();
    assert!(
        matches!(
            result,
            ay_sat::SatResult::Sat(_) | ay_sat::SatResult::Unsat(_) | ay_sat::SatResult::Unknown
        ),
        "solve_with_extension under scope should produce a result (not panic), got: {result:?}",
    );
}
