// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fail-closed reasons for SAT hint and RUP reconstruction.

use ay_core::TermId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum HintDerivationError {
    NoUsableHints,
    NoResolutionPivot {
        usable_hint_count: usize,
    },
    FinalClauseMismatch {
        expected_clause: Vec<TermId>,
        derived_clause: Vec<TermId>,
    },
    /// RUP replay: the target clause contains complementary literals, so it
    /// is a tautology and not derivable by unit-propagation replay (#rank-4).
    RupTautologicalTarget,
    /// RUP replay reached fixpoint without producing a conflict (#rank-4).
    RupNoConflict {
        usable_hint_count: usize,
        propagations: usize,
    },
}
