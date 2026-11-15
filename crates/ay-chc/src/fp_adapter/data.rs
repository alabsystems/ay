// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Whole owned clause DATA; no temporary source arena or proof capability.

use std::sync::Arc;

use ay_core::original_query::WorkBudget;

use super::{namespace, FpAdapterError};
use crate::{ChcExpr, ChcOp, ClauseBody};

/// Owned complete Bool/BV relation, never a SAT/Safe/Unsafe credential.
///
/// Constructible only by consuming a complete adapter output. Preserve the
/// original typed roots and input links independently. All roots of one clause
/// must be batched: separate encodings use the same reserved auxiliary names.
pub struct FpClauseData {
    constraint: ChcExpr,
}

impl FpClauseData {
    pub(super) fn new(constraint: ChcExpr) -> Self {
        Self { constraint }
    }

    /// Borrow the complete relation, not individual clauses or chosen roots.
    pub fn constraint(&self) -> &ChcExpr {
        &self.constraint
    }

    /// Move the whole relation into the original body, preserving its predicate
    /// arguments and old constraint. Reserved names in that body refuse before
    /// attachment, including auxiliaries from a separately encoded relation.
    ///
    /// Auxiliary variables remain body-local; nothing modifies a head, action,
    /// predicate signature, source-query ordinal, or result/proof authority.
    /// The caller must use the SAME original ledger and retain source identities.
    /// Fees cover newly created attachment storage and bounded borrowed scans,
    /// not arbitrary pre-existing body capacities or their disposal on refusal;
    /// the original caller remains responsible for that owned input storage.
    pub fn conjoin_body(
        self,
        body: ClauseBody,
        budget: &mut WorkBudget<'_>,
    ) -> Result<ClauseBody, FpAdapterError> {
        let result = attach(self, body, budget);
        // All temporary census state has been destroyed before this fence.
        budget.charge(0)?;
        result
    }
}

fn attach(
    data: FpClauseData,
    mut body: ClauseBody,
    budget: &mut WorkBudget<'_>,
) -> Result<ClauseBody, FpAdapterError> {
    budget.charge(0)?;
    namespace::validate_body(&body, budget)?;
    // At most two Arc allocations and a two-entry Vec, with moves only.
    budget.admit(1024, 1024)?;
    let mut constraints = Vec::new();
    constraints
        .try_reserve_exact(2)
        .map_err(|_| budget.refuse_exhaustion())?;
    if let Some(old) = body.constraint.take() {
        constraints.push(Arc::new(old));
    }
    constraints.push(Arc::new(data.constraint));
    body.constraint = Some(ChcExpr::Op(ChcOp::And, constraints));
    budget.charge(0)?;
    Ok(body)
}
