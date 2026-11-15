// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Source-bound, fixed-format SMT floating-point relations in Bool/BV CHCs.
//!
//! This additive adapter does not enable FP in the HORN parser, change its
//! over-approximation policy, or mint a SAT/Safe/Unsafe/proof credential. It
//! encodes the supplied original typed Bool roots using AY's FP circuits and
//! explicitly links every reachable free input to its supplied Bool/BV word.
//! In particular, SMT `=` and `fp.eq` are different, and an arithmetic NaN is
//! related as an SMT FP value, not as a promised Rust/host NaN payload.

mod data;
mod encoding;
mod namespace;
mod source;
mod transfer;
mod typed;

#[cfg(test)]
mod tests;

use ay_core::original_query::{QueryError, WorkBudget};
use ay_core::term::{TermId, TermStore};

use crate::{ChcExpr, ChcProblem, ChcVar};

pub use data::FpClauseData;

/// Exact original free-term to Bool/BV variable link.
///
/// The source must be a live `TermData::Var`. Its name must equal the target's
/// name. FP(8,24)/FP(11,53) link to BV32/BV64; Bool and BV1..64 retain their
/// original sort. This is a typed relation, not evidence of Rust provenance.
#[derive(Clone, Copy, Debug)]
pub struct FpInputBinding<'a> {
    /// Original immutable source term identity.
    pub source: TermId,
    /// Original Bool/BV clause variable, borrowed without cloning its name.
    pub target: &'a ChcVar,
}

/// Refusal of the complete adapter; no partial constraint is returned.
#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum FpAdapterError {
    /// Original owner refused work, storage, cancellation or deadline.
    #[error(transparent)]
    Owner(#[from] QueryError),
    /// Unsupported syntax is explicit, never an unconstrained FP replacement.
    #[error("unsupported FP clause source: {0}")]
    Unsupported(&'static str),
    /// A malformed, incomplete or colliding source descriptor was refused.
    #[error("invalid FP clause source: {0}")]
    Invalid(&'static str),
    /// An internal complete-circuit invariant did not match the prepaid plan.
    #[error("incomplete FP clause encoding: {0}")]
    Encoding(&'static str),
}

/// Complete Bool/BV DATA relation, still bound to its borrowed source inputs.
///
/// All auxiliary variables are local universal CHC variables occurring ONLY
/// in the body constraint. Existentially eliminating those definitional CNF
/// variables recovers the conjunction of the supplied FP roots. Moving them
/// into a predicate signature, dropping clauses/links, or choosing one NaN
/// payload is not licensed by this carrier. Later solve/replay/result admission
/// must retain the original owner; receiving DATA does not do those checks.
pub struct FpClauseEncoding<'a> {
    constraint: ChcExpr,
    auxiliary_variables: Vec<ChcVar>,
    roots: &'a [TermId],
    bindings: &'a [FpInputBinding<'a>],
    terms: &'a TermStore,
    namespace: &'a ChcProblem,
}

impl<'a> FpClauseEncoding<'a> {
    /// Move the WHOLE relation into owned DATA before the temporary source
    /// arena is destroyed. This does not grant source or solver authority.
    /// The consumer must retain its stable original source descriptor.
    pub fn into_data(self, budget: &mut WorkBudget<'_>) -> Result<FpClauseData, FpAdapterError> {
        let Self {
            constraint,
            auxiliary_variables,
            ..
        } = self;
        drop(auxiliary_variables);
        budget.charge(0)?;
        Ok(FpClauseData::new(constraint))
    }

    /// Borrow the whole constraint; there is no partial-circuit accessor.
    pub fn constraint(&self) -> &ChcExpr {
        &self.constraint
    }

    /// Auxiliary Bool variables, excluded from predicate arguments.
    pub fn auxiliary_variables(&self) -> &[ChcVar] {
        &self.auxiliary_variables
    }

    /// Original ordered root identities, including repeated occurrences.
    pub fn source_roots(&self) -> &'a [TermId] {
        self.roots
    }

    /// Original typed free-input links.
    pub fn input_bindings(&self) -> &'a [FpInputBinding<'a>] {
        self.bindings
    }

    /// The immutable source arena borrowed throughout encoding.
    pub fn source_terms(&self) -> &'a TermStore {
        self.terms
    }

    /// Entire original typed CHC namespace checked for auxiliary collisions.
    pub fn source_namespace(&self) -> &'a ChcProblem {
        self.namespace
    }
}

/// Lower a complete, narrow FP predicate relation into Bool/BV clause DATA.
///
/// Accepted FP formats are IEEE binary32/binary64. The supported fragment is
/// Bool constants/free inputs/not/and/or/xor/implication/binary Bool equality,
/// FP structural equality, IEEE equality/order/classification, neg/abs,
/// add/sub/mul/div/sqrt/fma with one of the FIVE literal SMT rounding modes, fixed-format
/// special constants and exact one-argument `to_fp` bit reinterpretation.
/// Bool/FP ITE admits a live Bool condition and two same-sort arms, in direct
/// or name form. All THREE descendants, including constant-condition and
/// unchosen/repeated arms, are authenticated and prepaid before native entry.
/// IEEE fp.rem takes exactly two same-format operands and no rounding mode.
/// It keeps nearest-even quotient semantics, NOT Rust remainder/fmod semantics.
/// Sqrt and fused multiply-add each have a separate complete 262,144-unit
/// adapter class; FMA keeps ONE final rounding, never separate mul+add.
/// Direct indexed BV extracts from a canonical BV32/BV64 constant or original
/// free input retain their exact range, child and complete word link. Each is
/// priced as OTHER; nested extracts and arithmetic raw aliases still refuse.
/// Signed/unsigned two-argument numeric `to_fp` admits literal RNE and BV8..64
/// original leaves/constants or those direct extracts, with a distinct 18,432
/// prepaid class. UF, BV ITE, symbolic rounding, other numeric rounding modes
/// and partial FP conversions refuse.
/// Division has its own conservative prepaid envelope, including successful
/// normal-power-of-two shortcuts. Remainder has a separate 917,504-unit fee
/// bound to the narrow native modular kernel and its complete source cost.
/// Neither grants new work/storage or promises a physical/RSS/4 GiB admission.
///
/// `namespace` must be the complete original typed problem, not a projected
/// clause. Every declaration and every live/pruned clause is scanned before
/// choosing a reserved auxiliary name. Its clauses are not rewritten here.
/// Caller-supplied source terms do not by themselves authenticate a text query
/// or an original compiler IR. No parser, solver or proof defaults change.
///
/// One borrowed budget owns planning, prepaid legacy circuits, transfer and
/// final admission. `with_admission` is needed for cumulative logical storage;
/// the compatibility budget cannot claim an aggregate storage cap. Legacy FP
/// gate allocations and destruction are not hard preemptible or allocator/RSS
/// bounded. A process memory cap remains an independent requirement.
pub fn lower_fp_clause<'a>(
    terms: &'a TermStore,
    roots: &'a [TermId],
    bindings: &'a [FpInputBinding<'a>],
    namespace: &'a ChcProblem,
    budget: &mut WorkBudget<'_>,
) -> Result<FpClauseEncoding<'a>, FpAdapterError> {
    budget.charge(0)?;
    namespace::validate(namespace, bindings, budget)?;
    let plan = source::plan(terms, roots, bindings, budget)?;
    plan.prepay(budget)?;
    let built = encoding::build(terms, roots, &plan, budget)?;
    let (constraint, auxiliary_variables) = transfer::run(built, bindings, &plan, budget)?;
    budget.charge(0)?;
    Ok(FpClauseEncoding {
        constraint,
        auxiliary_variables,
        roots,
        bindings,
        terms,
        namespace,
    })
}
