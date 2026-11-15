// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed whole-clause FP DATA bridge, not a parser or solver credential.
//!
//! Original immutable Expr references survive the private positional arena.
//! All ordered roots (including repetitions and unchosen arms) use ONE native
//! construction, preventing body-local auxiliary aliasing. The complete source
//! namespace and exact free-input links remain borrowed alongside the output.
//! A caller must authenticate its compiler IR, Rust FP semantics and later
//! solve/replay/cache/result admission; this API does not grant those powers.
//! Accounting covers newly created bridge storage and bounded borrowed scans.
//! Pre-existing caller-owned Expr/namespace/body storage and its disposal remain
//! the caller's responsibility, including an input body dropped on refusal.

mod build;
mod raw_result;
mod source;
mod typed;

#[cfg(test)]
mod tests;

use ay_bindings::Expr;
use ay_chc::fp_adapter::FpClauseData;
use ay_chc::{ChcProblem, ChcVar, ClauseBody};
use ay_core::original_query::WorkBudget;

pub use ay_chc::fp_adapter::FpAdapterError;
pub use raw_result::{
    lower_fp_raw_result_clause, FpRawOperation, FpRawResultRelation, RustFpArithmetic,
    RustNanPolicy,
};

/// Stable original Expr input linked to an original Bool/BV clause variable.
///
/// Only an original free Var is accepted. Name and sort must match exactly;
/// FP32/64 use BV32/64 raw words. Exact direct extracts retain the whole original
/// BV32/64 leaf link. Compound BV aliases, numeric conversions and
/// arbitrary NaN payload extraction are not silently treated as raw inputs.
#[derive(Clone, Copy, Debug)]
pub struct FpExprInputBinding<'a> {
    /// Original immutable expression; no temporary TermId escapes.
    pub source: &'a Expr,
    /// Original raw word/Bool clause variable.
    pub target: &'a ChcVar,
}

/// Borrowed whole source descriptor, not text/IR authentication or proof.
pub struct FpExprClauseSource<'a> {
    roots: &'a [Expr],
    bindings: &'a [FpExprInputBinding<'a>],
    namespace: &'a ChcProblem,
    raw_results: &'a [FpRawResultRelation<'a>],
}

impl<'a> FpExprClauseSource<'a> {
    /// Ordered original roots, including repeated occurrences.
    pub fn roots(&self) -> &'a [Expr] {
        self.roots
    }
    /// Original typed free-input identities and exact raw-word links.
    pub fn bindings(&self) -> &'a [FpExprInputBinding<'a>] {
        self.bindings
    }
    /// Original operation-local raw output descriptors; empty for the legacy API.
    pub fn raw_results(&self) -> &'a [FpRawResultRelation<'a>] {
        self.raw_results
    }
    /// Entire live/pruned original CHC namespace, not a projected clause.
    pub fn namespace(&self) -> &'a ChcProblem {
        self.namespace
    }
}

/// Complete source-bound DATA retaining the SAME mutable ledger until consumption.
/// No replacement ledger can be passed to attachment or final publication.
pub struct FpExprClauseEncoding<'a, 'budget, 'owner> {
    data: FpClauseData,
    source: FpExprClauseSource<'a>,
    budget: &'budget mut WorkBudget<'owner>,
}

impl<'a, 'budget, 'owner> FpExprClauseEncoding<'a, 'budget, 'owner> {
    /// Stable original source retained for later consumer checks.
    pub fn source(&self) -> &FpExprClauseSource<'a> {
        &self.source
    }

    /// Consume the whole relation into one original body. Predicate arguments
    /// and the old constraint are moved unchanged, never projected or copied.
    /// The caller retains accounting responsibility for that pre-existing body,
    /// including spare capacities and disposal if attachment refuses.
    pub fn into_body(
        self,
        body: ClauseBody,
    ) -> Result<FpExprClauseBody<'a, 'budget, 'owner>, FpAdapterError> {
        let Self {
            data,
            source,
            budget,
        } = self;
        let body = data.conjoin_body(body, budget)?;
        budget.charge(0)?;
        Ok(FpExprClauseBody {
            body,
            source,
            budget,
        })
    }
}

/// Genuine CHC body DATA plus its stable original typed source.
pub struct FpExprClauseBody<'a, 'budget, 'owner> {
    body: ClauseBody,
    source: FpExprClauseSource<'a>,
    budget: &'budget mut WorkBudget<'owner>,
}

impl<'a, 'budget, 'owner> FpExprClauseBody<'a, 'budget, 'owner> {
    /// Borrow the entire body, not a selected FP root.
    pub fn body(&self) -> &ClauseBody {
        &self.body
    }
    /// Original Expr references remain live after arena cleanup.
    pub fn source(&self) -> &FpExprClauseSource<'a> {
        &self.source
    }

    /// Move the body and complete source descriptor together for a HornClause.
    /// Retain the original head/action/query provenance and later owner checks.
    pub fn into_parts(self) -> Result<(ClauseBody, FpExprClauseSource<'a>), FpAdapterError> {
        let Self {
            body,
            source,
            budget,
        } = self;
        budget.charge(0)?;
        Ok((body, source))
    }
}

/// Encode all typed FP/Bool roots for ONE clause using ONE borrowed ledger.
///
/// FP32/64 operations include literal-RM square root and fused multiply-add,
/// with the native whole-source gate's distinct independent fees. Both ITE arms are fully
/// checked even under a constant condition. Direct indexed BV field extracts
/// from original BV32/64 free leaves or canonical constants are retained as
/// separate nodes, never collapsed into an FP alias. Rust truncating remainder
/// is distinct from IEEE `fp.rem`. Literal-RNE signed/unsigned BV8..64 numeric
/// casts to FP32/64 accept original leaves/constants or direct extracts retaining
/// a complete BV32/64 base. UF, other compound BV operations, other numeric
/// rounding modes, partial FP conversions and unsupported sorts refuse.
/// Translator traversal/maps/records/names/copies/disposal have separate checked
/// fees; native planning/build/transfer retain their original independent fees.
/// Use WorkBudget::with_admission for cumulative work AND logical storage.
/// No new end, timer, grant, public TermStore or source credential is created.
pub fn lower_fp_expr_clause<'a, 'budget, 'owner>(
    roots: &'a [Expr],
    bindings: &'a [FpExprInputBinding<'a>],
    namespace: &'a ChcProblem,
    budget: &'budget mut WorkBudget<'owner>,
) -> Result<FpExprClauseEncoding<'a, 'budget, 'owner>, FpAdapterError> {
    budget.charge(0)?;
    let result = build::lower(roots, bindings, namespace, budget);
    // build::lower destroys the positional arena, entry payloads and maps
    // before returning. Original owner may veto AFTER their cleanup.
    budget.charge(0)?;
    let data = result?;
    Ok(FpExprClauseEncoding {
        data,
        source: FpExprClauseSource {
            roots,
            bindings,
            namespace,
            raw_results: &[],
        },
        budget,
    })
}
