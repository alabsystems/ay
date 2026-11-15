// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One fresh, owning legacy construction with the original borrowed ledger.

use std::cell::Cell;

use ay_core::original_query::WorkBudget;
use ay_core::term::{TermId, TermStore};
use ay_core::CnfLit;
use ay_fp::{FpBuildError, FpBuildProgress, FpBuiltEncoding, FpConstruction};

use super::source::Plan;
use super::FpAdapterError;

pub(super) struct Built {
    pub roots: Vec<CnfLit>,
    pub encoding: FpBuiltEncoding,
}

pub(super) fn build(
    terms: &TermStore,
    roots: &[TermId],
    plan: &Plan,
    budget: &mut WorkBudget<'_>,
) -> Result<Built, FpAdapterError> {
    // Source planning already authenticated and prepaid EVERY occurrence and
    // descendant. Exact root identity reuse must not discount that envelope.
    // Prepay the bounded scalar search before borrowing this ledger in `poll`;
    // there is no new map, storage grant, or composite-predicate cache.
    let comparisons = roots
        .len()
        .checked_mul(roots.len().saturating_sub(1))
        .ok_or_else(|| budget.refuse_exhaustion())?
        / 2;
    budget.charge(comparisons)?;
    // This Vec and every legacy allocation already have full pre-entry cost.
    let mut root_lits = Vec::new();
    root_lits
        .try_reserve_exact(roots.len())
        .map_err(|_| budget.refuse_exhaustion())?;
    let refusal = Cell::new(None);
    let mut poll = |progress: FpBuildProgress| {
        if refusal.get().is_some() {
            return true;
        }
        if let Err(error) = budget.charge(0) {
            refusal.set(Some(FpAdapterError::Owner(error)));
            return true;
        }
        if progress.variables as usize > plan.gates || progress.clauses > plan.clauses {
            // An invalid complete resource envelope is terminal on this SAME
            // ledger; it may not restart native work through a permissive poll.
            refusal.set(Some(FpAdapterError::Owner(budget.refuse_exhaustion())));
            return true;
        }
        false
    };
    let native = (|| {
        let mut attempt = FpConstruction::new_closed_data(terms, &mut poll)?;
        for (index, &root) in roots.iter().enumerate() {
            let lit = if let Some(first) = roots[..index].iter().position(|&old| old == root) {
                // A reused root still crosses the SAME poisoned construction
                // owner's checkpoint. Preserve its occurrence in the output,
                // not a fresh equivalent literal or a removed assertion.
                attempt.try_has_encoding_gap()?;
                root_lits[first]
            } else {
                attempt.try_encode_bool_condition(root)?
            };
            root_lits.push(lit);
        }
        attempt.finish()
    })();
    let encoding = native.map_err(|error| {
        refusal.get().unwrap_or_else(|| match error {
            FpBuildError::Interrupted => {
                FpAdapterError::Encoding("native construction interrupted")
            }
            FpBuildError::VariableLimit => FpAdapterError::Encoding("native variable namespace"),
        })
    })?;
    if encoding.has_encoding_gap
        || !encoding.pending_condition_links.is_empty()
        || !encoding.cache.to_bv_unspec_sites.is_empty()
        || !encoding.cache.ieee_nan_encodings.is_empty()
        || !encoding.cache.rm_terms.is_empty()
    {
        return Err(FpAdapterError::Encoding(
            "unsupported pending/gap/conversion state",
        ));
    }
    Ok(Built {
        roots: root_lits,
        encoding,
    })
}
