// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source-bound replay for deferred mixed BV/LIA clauses.

use ay_core::{TermId, TermStore};

use super::TrustClauseDischargeControls;

/// Prove either the standalone clause or its entailment from exact authored
/// assertions with the independent bounded source interpreter. Its bound is
/// the interpreter's own counted work (`ay_proof`'s `MAX_WORK`), never a
/// clock; the envelope's backstop, if any, is passed through as a stop.
/// Every unsupported or exhausted query fails closed.
pub(super) fn discharge_source_bv_lia(
    terms: &TermStore,
    clause: &[TermId],
    assertions: &[TermId],
    controls: &TrustClauseDischargeControls,
) -> bool {
    if !controls.clone_fits(terms) {
        return false;
    }
    let mut replay_terms = terms.clone();
    if controls.stop_requested(&replay_terms) || !controls.accept_fits(&replay_terms) {
        return false;
    }
    let mut negated = Vec::new();
    if negated.try_reserve_exact(clause.len()).is_err() {
        return false;
    }
    for &literal in clause {
        if controls.stop_requested(&replay_terms) {
            return false;
        }
        negated.push(replay_terms.mk_not(literal));
    }
    if !controls.accept_fits(&replay_terms) {
        return false;
    }
    if ay_proof::authenticate_bv_lia_unsat_query(&replay_terms, &negated, controls.backstop).is_ok()
    {
        return true;
    }
    if controls.stop_requested(&replay_terms) {
        return false;
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
    ay_proof::authenticate_bv_lia_unsat_query(&replay_terms, &roots, controls.backstop).is_ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn replay_clone_honors_deadline_and_its_own_term_store_limit() {
        let mut terms = TermStore::new();
        let first = terms.mk_var("source_replay_first", ay_core::Sort::Bool);
        let not_first = terms.mk_not_raw(first);
        let mut tautological_clause = vec![first, not_first];
        for index in 0..900 {
            tautological_clause.push(terms.mk_var(
                format!("source_replay_padding_{index}"),
                ay_core::Sort::Bool,
            ));
        }

        assert!(discharge_source_bv_lia(
            &terms,
            &tautological_clause,
            &[],
            &TrustClauseDischargeControls::default(),
        ));

        let expired = ay_core::time::Instant::now()
            .checked_sub(std::time::Duration::from_millis(1))
            .expect("one millisecond must fit before the current instant");
        assert!(!discharge_source_bv_lia(
            &terms,
            &tautological_clause,
            &[],
            &TrustClauseDischargeControls::new(
                None,
                Some(expired),
                None,
                None,
                super::super::CertificationEffort::default(),
            ),
        ));

        let source_limit = terms.true_memory_bytes();
        assert!(!terms.instance_memory_exceeded(source_limit));
        let mut expected_replay = terms.clone();
        for &literal in &tautological_clause {
            let _ = expected_replay.mk_not(literal);
        }
        assert!(
            expected_replay.instance_memory_exceeded(source_limit),
            "fixture must grow the replay store beyond the still-live source ceiling"
        );
        assert!(!discharge_source_bv_lia(
            &terms,
            &tautological_clause,
            &[],
            &TrustClauseDischargeControls::new(
                None,
                None,
                None,
                Some(source_limit),
                super::super::CertificationEffort::default(),
            ),
        ));
    }
}
