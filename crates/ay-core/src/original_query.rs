// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Portable, unfurled authored-query structure, not solver terms or proof authority.
//!
//! Locators name entries only inside this descriptor. Validation establishes
//! structural consistency and lexical scope, NOT semantic typing, equivalence,
//! authenticity, or a source-to-proof bridge. A caller must independently bind
//! this structure to the original bytes and check every semantic transformation.
//! No canonical `TermId`, renderer, digest, or legacy proof grants that authority.
//!
//! Comparison is ordered structural alpha-equivalence: nominal declarations,
//! literal token kinds, options, and unused definitions remain significant;
//! bound names alone may differ. Lexical positions follow de Bruijn's treatment
//! of alpha-conversion (N. G. de Bruijn, *Lambda calculus notation with nameless
//! dummies, a tool for automatic formula manipulation*, Indagationes Mathematicae
//! (Proceedings) 75(5), 1972, pp. 381–392, DOI: 10.1016/1385-7258(72)90034-0).
//! This reference motivates the binding model; it does not prove this implementation.

mod admission;
mod budget;
mod catalog;
mod compare;
mod compare_catalog;
mod compare_nodes;
mod compare_syntax;
mod environments;
mod failure;
mod scopes;
mod syntax;
mod validate;
mod validate_catalog;
mod validate_headers;
mod validate_nodes;

pub use admission::{
    AdmissionUsage, CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant,
    OriginalAdmission, OriginalAdmissionError, COUNTED_ADMISSION_USAGE_VERSION,
};
pub use budget::{QueryError, StopReason, WorkBudget};
pub use catalog::*;
pub use failure::ValidationFailure;
pub use syntax::*;

/// Caller-supplied arenas and complete ordered query history, before validation.
#[derive(Clone, Debug, Default)]
pub struct QueryDraft {
    /// Independently captured host declaration lifetime at the start of history.
    pub initial_lifetime: DeclarationLifetime,
    /// Host reset-assertions scope policy; never inferred from a renderer.
    pub reset_assertions: ResetAssertionsPolicy,
    /// Host lifetime policy for a full reset, independently authenticated by caller.
    pub reset_lifetime: ResetLifetimePolicy,
    /// All sort syntax, children preceding parents.
    pub sorts: Vec<SortNode>,
    /// All authored term syntax, children preceding parents.
    pub nodes: Vec<TypedNode>,
    /// Structured annotation/option payloads, children preceding parents.
    pub data: Vec<DataNode>,
    /// Declaration history, including unused and subsequently popped entries.
    pub declarations: Vec<Declaration>,
    /// Every command in authored order, including repeated occurrences.
    pub commands: Vec<QueryCommand>,
    /// Complete language/host typing identity, independently captured by caller.
    pub typing: Vec<Attribute>,
}

/// Immutable, structurally validated descriptor; never a proof capability.
pub struct AuthoredQuery {
    draft: QueryDraft,
}

impl std::fmt::Debug for AuthoredQuery {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("AuthoredQuery")
            .field("nodes", &self.draft.nodes.len())
            .field("declarations", &self.draft.declarations.len())
            .field("commands", &self.draft.commands.len())
            .finish_non_exhaustive()
    }
}

impl AuthoredQuery {
    /// Validate structure and lexical scope with a finite, interruptible ledger.
    ///
    /// This does not check theory semantics or authenticate the supplied draft.
    /// Refusal returns the exact draft in [`ValidationFailure`]; its disposal
    /// remains caller-owned and is not claimed to have bounded total latency.
    #[expect(
        clippy::result_large_err,
        reason = "refusal must return the exact caller-owned draft without allocating after the original grant refuses"
    )]
    pub fn validate(
        draft: QueryDraft,
        work: &mut WorkBudget<'_>,
    ) -> Result<Self, ValidationFailure> {
        match validate::validate(&draft, work) {
            Ok(()) => Ok(Self { draft }),
            Err(error) => Err(ValidationFailure::new(error, draft)),
        }
    }

    /// Borrow all retained structure without allowing mutation.
    pub fn structure(&self) -> &QueryDraft {
        &self.draft
    }

    /// Compare complete ordered structure across independent arenas.
    ///
    /// Bound names may be alpha-renamed; nominal names and token kinds may not.
    /// An equality result is not logical equivalence or source/proof authority.
    pub fn structurally_matches(
        &self,
        other: &Self,
        work: &mut WorkBudget<'_>,
    ) -> Result<bool, QueryError> {
        compare::matches(&self.draft, &other.draft, work)
    }
}

#[cfg(test)]
mod tests;
