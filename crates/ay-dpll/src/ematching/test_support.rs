// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test-only entry points for E-matching with fresh persistent state.

use super::*;

#[allow(clippy::panic)]
pub(super) fn perform_ematching(terms: &mut TermStore, assertions: &[TermId]) -> EMatchingResult {
    perform_ematching_with_config(terms, assertions, &EMatchingConfig::default())
}

#[allow(clippy::panic)]
pub(super) fn perform_ematching_with_config(
    terms: &mut TermStore,
    assertions: &[TermId],
    config: &EMatchingConfig,
) -> EMatchingResult {
    let mut state = PersistentMatchState::new();
    perform_ematching_with_generations(
        terms,
        assertions,
        config,
        GenerationTracker::new(),
        None,
        &|| false,
        &mut state,
        None,
    )
}
