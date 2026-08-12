// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict replay for internally certified mixed Bool/Int/BV tautologies.

use ay_core::{ProofId, Sort, TermData, TermId, TermStore};

use super::super::ProofCheckError;
use super::{authenticate_bv_lia_unsat_query, MAX_BV_LIA_QUERY_ROOTS};

/// Validate one internally certified mixed Bool/Int/BV tautology.
///
/// The clause must be exactly `¬R1 ∨ ... ∨ ¬Rn`, with every outer negation
/// represented explicitly. Its validity is re-derived by proving the
/// conjunction `R1 ∧ ... ∧ Rn` UNSAT with the bounded source interpreter.
/// Requiring the explicit outer `not` makes the inverse mapping unambiguous,
/// including when a root is itself negated (the clause then contains a raw
/// double negation).
pub(crate) fn validate_bv_lia_tautology(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    has_farkas: bool,
    has_lia: bool,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("BvLiaTautology: {reason}"),
    };
    if has_farkas || has_lia {
        return Err(invalid(
            "bounded semantic certificates must not carry arithmetic annotations".to_string(),
        ));
    }
    if clause.len() > MAX_BV_LIA_QUERY_ROOTS {
        return Err(invalid(format!(
            "exact clause has {} roots, above the limit {MAX_BV_LIA_QUERY_ROOTS}",
            clause.len()
        )));
    }

    let mut roots = Vec::new();
    roots
        .try_reserve_exact(clause.len())
        .map_err(|error| invalid(format!("root allocation failed for exact clause: {error}")))?;
    for &literal in clause {
        if terms.entry_stamp(literal).is_none() || terms.sort(literal) != &Sort::Bool {
            return Err(invalid(
                "every clause literal must be a live Bool term".to_string(),
            ));
        }
        let TermData::Not(root) = terms.get(literal) else {
            return Err(invalid(
                "every clause literal must be an explicit outer negation".to_string(),
            ));
        };
        if terms.entry_stamp(*root).is_none() || terms.sort(*root) != &Sort::Bool {
            return Err(invalid(
                "every recovered source root must be a live Bool term".to_string(),
            ));
        }
        roots.push(*root);
    }
    authenticate_bv_lia_unsat_query(terms, &roots, None)
        .map(|_| ())
        .map_err(|error| invalid(error.to_string()))
}
