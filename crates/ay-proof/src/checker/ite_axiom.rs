// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode validation for `TheoryLemmaKind::IteSame`: the if-then-else
//! axiom instance `(ite c x x) = x` — a conditional whose two branches are the
//! SAME term equals that branch, for ANY condition `c` and ANY sort of `x`.
//!
//! This is a purely SYNTACTIC schema: the lemma is a unit positive equality
//! `(= L R)` where one side is `(ite c t e)` with `t` and `e` the identical
//! `TermId`, and the other side is that same `TermId`. The condition is never
//! inspected — `(ite c x x) = x` holds in every model regardless of `c`. The
//! principle is the standard `ite`-with-equal-branches reduction.

use ay_core::{ProofId, TermData, TermId, TermStore};

use super::ProofCheckError;

/// Recognize whether `clause` is a valid `(ite c x x) = x` lemma — i.e. whether
/// [`validate_ite_same`] would accept it. Used by the `ay-dpll` reconstruction
/// to gate its emitted lemma on the exact validator the strict checker runs.
#[must_use]
pub fn recognize_ite_same(terms: &TermStore, clause: &[TermId]) -> bool {
    validate_ite_same(terms, ProofId(0), clause).is_ok()
}

/// Validate an `IteSame` lemma in strict mode.
///
/// Accepts the unit positive equality `(= (ite c x x) x)` (the `ite` may be on
/// either side) exactly when the two `ite` branches are the same `TermId` and
/// equal to the other side of the equality. Fails closed otherwise.
pub(crate) fn validate_ite_same(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    let invalid = |reason: String| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason,
    };

    if clause.len() != 1 {
        return Err(invalid(
            "ite-same clause must be a unit positive equality".to_string(),
        ));
    }
    let (lhs, rhs) = equality_sides(terms, clause[0])
        .ok_or_else(|| invalid("ite-same literal must be a positive equality".to_string()))?;

    for (ite_side, value_side) in [(lhs, rhs), (rhs, lhs)] {
        if let TermData::Ite(_cond, then_branch, else_branch) = terms.get(ite_side) {
            if then_branch == else_branch && *then_branch == value_side {
                return Ok(());
            }
        }
    }
    Err(invalid(
        "ite-same does not match `(= (ite c x x) x)` (identical branches equal to \
         the other side)"
            .to_string(),
    ))
}

/// Decode a positive equality `(= a b)` into `(a, b)`.
fn equality_sides(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}
