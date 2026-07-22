// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermId;

/// Out-of-range source indices: debug_assert fires in debug mode (detecting
/// the upstream bug), while release mode gracefully falls back to all equalities.
#[test]
fn test_dioph_infeasible_conflict_sources_out_of_range_falls_back_to_all_equalities() {
    let equalities = vec![TermId::new(11), TermId::new(42), TermId::new(99)];

    // In debug mode, the debug_assert! fires to flag the upstream bug.
    #[cfg(debug_assertions)]
    {
        let result = std::panic::catch_unwind(|| {
            LiaSolver::dioph_infeasible_conflict_from_sources(&equalities, &[7, 8])
        });
        assert!(
            result.is_err(),
            "debug_assert should fire on out-of-range source indices"
        );
    }

    // In release mode, the fallback path returns all equalities.
    #[cfg(not(debug_assertions))]
    {
        let conflict = LiaSolver::dioph_infeasible_conflict_from_sources(&equalities, &[7, 8]);
        let expected: Vec<_> = equalities
            .iter()
            .map(|&lit| TheoryLit::new(lit, true))
            .collect();
        assert_eq!(
            conflict, expected,
            "out-of-range source indices must not yield an empty conflict"
        );
    }
}

#[test]
fn test_dioph_infeasible_conflict_valid_sources_keep_reduced_core() {
    let equalities = vec![TermId::new(3), TermId::new(5), TermId::new(7)];
    let conflict = LiaSolver::dioph_infeasible_conflict_from_sources(&equalities, &[2, 0]);
    assert_eq!(
        conflict,
        vec![
            TheoryLit::new(TermId::new(7), true),
            TheoryLit::new(TermId::new(3), true)
        ]
    );
}
