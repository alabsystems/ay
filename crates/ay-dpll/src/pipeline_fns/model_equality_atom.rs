// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The SAT-visible atom of a requested model equality, and the round-budget
//! freshness test that reads it (#model-eq-encoded-atom).
//!
//! [`super::encode_model_equality`] puts `mk_eq_coerce(lhs, rhs)` on the
//! solver. That is not always the raw `(= lhs rhs)` a `find_eq` lookup
//! returns: `mk_eq_coerce` folds two distinct constants to `false`, coerces
//! an Int side against a Real one, and normalizes. The round-budget
//! replenishment of #1145 (4e96ceb50) asks whether a request's atom is
//! already encoded, to tell finite progress (a new atom replenishes the
//! budget) from a re-request (counts against it). Asked about the `find_eq`
//! term, a re-request whose encoded atom differs reads as new forever and
//! refills the budget on every dispatch, so the loop the budget bounds never
//! ends. `cegqi_ce_strip_identity::v07_real_elements_never_unsat`
//! re-requested `(= 3 0)` (encoded as `false`) about 24 000 times and ran
//! 17 s against its 10 s limit, instead of failing closed in 0.8 s.

use ay_core::{TermId, TermStore};

/// The equality atom [`super::encode_model_equality`] encodes for a requested
/// model equality `lhs = rhs`.
pub(crate) fn model_equality_atom(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_eq_coerce(lhs, rhs)
}

/// Whether the requested model equality `lhs = rhs` is new work for the
/// round budget: its encoded atom ([`model_equality_atom`]) is not yet live
/// on the solver. `is_live` says whether a term is mapped to a SAT variable
/// (and not withheld).
pub(crate) fn model_equality_request_is_new(
    terms: &mut TermStore,
    lhs: TermId,
    rhs: TermId,
    is_live: impl Fn(TermId) -> bool,
) -> bool {
    !is_live(model_equality_atom(terms, lhs, rhs))
}

#[cfg(test)]
#[path = "model_equality_atom_tests.rs"]
mod tests;
