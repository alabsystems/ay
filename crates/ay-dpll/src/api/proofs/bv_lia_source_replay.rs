// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source-bound replay for deferred mixed BV/LIA clauses.

use ay_core::{TermId, TermStore};

/// Prove either the standalone clause or its entailment from exact authored
/// assertions with the independent bounded source interpreter. One deadline is
/// shared by both attempts; every unsupported or exhausted query fails closed.
pub(super) fn discharge_source_bv_lia(
    terms: &TermStore,
    clause: &[TermId],
    assertions: &[TermId],
) -> bool {
    let mut replay_terms = terms.clone();
    let negated: Vec<_> = clause
        .iter()
        .map(|&literal| replay_terms.mk_not(literal))
        .collect();
    let deadline = ay_core::time::Instant::now() + std::time::Duration::from_secs(1);
    if ay_proof::authenticate_bv_lia_unsat_query(&replay_terms, &negated, Some(deadline)).is_ok() {
        return true;
    }
    let Some(root_count) = assertions.len().checked_add(negated.len()) else {
        return false;
    };
    if assertions.is_empty() || root_count > ay_proof::MAX_BV_LIA_QUERY_ROOTS {
        return false;
    }
    let mut roots = Vec::new();
    if roots.try_reserve_exact(root_count).is_err() {
        return false;
    }
    roots.extend_from_slice(assertions);
    roots.extend_from_slice(&negated);
    ay_proof::authenticate_bv_lia_unsat_query(&replay_terms, &roots, Some(deadline)).is_ok()
}
