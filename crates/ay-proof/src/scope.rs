// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Problem-scope helpers for in-process proof export.

use ay_core::{TermId, TermStore};

/// The problem-declared symbol names the Alethe exporter treats as already in
/// scope.
///
/// When problem text is unavailable, this supplies the round-trip checker's
/// in-process scope. Sort names remain unknown; see `ProblemScope::from_symbols`.
#[must_use]
pub fn problem_scope_symbol_names(terms: &TermStore, problem_assertions: &[TermId]) -> Vec<String> {
    super::variables::problem_scope_symbol_names(terms, problem_assertions)
}
