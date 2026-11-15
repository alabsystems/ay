// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A solver told not to build the enumeration (`set_support_enumeration`),
//! as each local solve of AY's SAT sweep is
//! (`crate::solve_resolution_dag_counted_local`): it parks nothing on an
//! instance the gate admits, begins no build at all, and a short counted
//! solve decides exactly as it did with the enumeration parked behind its
//! head start.

use super::*;
use crate::{
    solve_resolution_dag_counted, solve_resolution_dag_counted_local, ResolutionProofLimits,
    ResolutionSolveOutcome,
};

#[test]
fn a_solver_without_support_enumeration_parks_nothing() {
    let (nv, clauses) = resolvent_forced_and_chains(34);
    let mut parked = solver_from(nv, &clauses);
    parked.prepare_indep_enum_at_startup();
    assert!(
        parked.cold.indep_enum_pending.is_some(),
        "the gate admits this instance"
    );
    let mut plain = solver_from(nv, &clauses);
    plain.set_support_enumeration(false);
    plain.prepare_indep_enum_at_startup();
    assert!(plain.cold.indep_enum_pending.is_none());
    assert_eq!(plain.stats.indep_enum_admitted, 0, "nothing was built");
    let builds = Solver::support_enumeration_builds();
    plain.prepare_indep_enum_at_startup();
    assert_eq!(
        Solver::support_enumeration_builds(),
        builds,
        "none was begun"
    );
    parked.prepare_indep_enum_at_startup();
    assert_eq!(Solver::support_enumeration_builds(), builds + 1);
    // The switch is the solver's own and survives an incremental clone.
    let mut copy = plain.clone_for_incremental();
    copy.prepare_indep_enum_at_startup();
    assert!(copy.cold.indep_enum_pending.is_none());
}

#[test]
fn a_local_solve_decides_as_the_counted_solve_does() {
    let (nv, clauses) = resolvent_forced_and_chains(34);
    let clauses: Vec<Vec<Literal>> = clauses
        .iter()
        .map(|clause| clause.iter().map(|&l| lit(l)).collect())
        .collect();
    for conflicts in [1, 100, 5_000] {
        let limits = ResolutionProofLimits {
            deadline: Some(ay_core::time::Instant::now() + Duration::from_secs(30)),
            max_conflicts: Some(conflicts),
            max_decisions: Some(conflicts.saturating_mul(64)),
            ..ResolutionProofLimits::default()
        };
        let builds = Solver::support_enumeration_builds();
        let (counted, counted_spent) =
            solve_resolution_dag_counted(nv, &clauses, &limits, &mut || true);
        assert_eq!(Solver::support_enumeration_builds(), builds + 1);
        let (local, local_spent) =
            solve_resolution_dag_counted_local(nv, &clauses, &limits, &mut || true);
        assert_eq!(
            Solver::support_enumeration_builds(),
            builds + 1,
            "the local solve built one"
        );
        assert_eq!(local_spent, counted_spent, "{conflicts} conflicts");
        match (counted, local) {
            (Ok(ResolutionSolveOutcome::Sat(a)), Ok(ResolutionSolveOutcome::Sat(b))) => {
                assert_eq!(a, b, "the same model at {conflicts} conflicts");
            }
            (Err(a), Err(b)) => assert_eq!(a, b, "{conflicts} conflicts"),
            (a, b) => panic!("{conflicts} conflicts: {a:?} against {b:?}"),
        }
    }
}
