// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_extract_stats_includes_entry_inductive_failure_counts() {
    use crate::ChcProblem;

    let mut solver = PdrSolver::new(ChcProblem::new(), PdrConfig::default());
    solver
        .telemetry
        .entry_inductive_failure_counts
        .insert(EntryInductiveFailureReason::EntryCegarDisabled, 2);
    solver
        .telemetry
        .entry_inductive_failure_counts
        .insert(EntryInductiveFailureReason::SatHyperedge, 1);

    let stats = solver.extract_stats();

    assert_eq!(
        stats
            .entry_inductive_failure_counts
            .get("entry_cegar_disabled")
            .copied(),
        Some(2),
        "expected entry_cegar_disabled counter in exported stats"
    );
    assert_eq!(
        stats
            .entry_inductive_failure_counts
            .get("sat_hyperedge")
            .copied(),
        Some(1),
        "expected sat_hyperedge counter in exported stats"
    );
}
