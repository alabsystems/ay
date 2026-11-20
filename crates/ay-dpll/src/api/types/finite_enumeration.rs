// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked finite Bool/Int scalar projections, without fabricating a Model.

use num_bigint::BigInt;

use super::bool_enumeration::{
    BoolEnumerationOutcome, BoolEnumerationSearchWork, BoolEnumerationStatistics, EnumerationCommon,
};
use super::Term;
use crate::api::UnsatProofArtifact;

/// Scalar data. Only an AY-constructed row/report gives it checked witness
/// meaning; constructing an enum value alone grants no model authority.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum FiniteEnumerationValue {
    /// Original Boolean value.
    Bool(bool),
    /// Original mathematical integer, with no machine-width narrowing.
    Int(BigInt),
}

/// Completion has the same source-proof authority as Boolean enumeration.
pub type FiniteEnumerationOutcome = BoolEnumerationOutcome;
/// Work counters retain the same schema and partial-meter qualifications.
pub type FiniteEnumerationStatistics = BoolEnumerationStatistics;

/// One distinct scalar projection and its independently checked original witness.
#[derive(Debug, Clone)]
pub struct FiniteEnumerationRow {
    pub(crate) values: Vec<FiniteEnumerationValue>,
    pub(crate) witness: Vec<(Term, FiniteEnumerationValue)>,
    pub(crate) search: BoolEnumerationSearchWork,
    pub(crate) validation_work: u64,
    pub(crate) materialization_work: u64,
}

impl FiniteEnumerationRow {
    /// Values in requested source projection order.
    #[must_use]
    pub fn values(&self) -> &[FiniteEnumerationValue] {
        &self.values
    }

    /// Complete original Bool/Int leaf assignment used by the independent gate.
    #[must_use]
    pub fn witness(&self) -> &[(Term, FiniteEnumerationValue)] {
        &self.witness
    }

    /// SAT work that produced this row.
    #[must_use]
    pub fn search_work(&self) -> BoolEnumerationSearchWork {
        self.search
    }

    /// Logical witness construction and original evaluation work.
    #[must_use]
    pub fn original_validation_work(&self) -> u64 {
        self.validation_work
    }

    /// Logical DATA-only assignment materialization work.
    #[must_use]
    pub fn candidate_materialization_work(&self) -> u64 {
        self.materialization_work
    }
}

/// Checked rows of one immutable original query. Only `Exhaustive` establishes
/// completeness, using one strict original-source-plus-blockers proof. A report
/// is constructed only by AY, and an outcome enum alone grants no authority.
#[derive(Debug)]
#[must_use]
pub struct FiniteEnumerationReport {
    pub(crate) common: EnumerationCommon,
    pub(crate) rows: Vec<FiniteEnumerationRow>,
}

impl FiniteEnumerationReport {
    /// End condition, including explicit incomplete source-proof refusals.
    #[must_use]
    pub fn outcome(&self) -> FiniteEnumerationOutcome {
        self.common.outcome
    }

    /// Exact authenticated source handles, in requested order.
    #[must_use]
    pub fn projection(&self) -> &[Term] {
        &self.common.projection
    }

    /// Distinct, independently checked original scalar projections.
    #[must_use]
    pub fn rows(&self) -> &[FiniteEnumerationRow] {
        &self.rows
    }

    /// Compilation/search/source proof split; not a complete CPU or memory meter.
    #[must_use]
    pub fn statistics(&self) -> FiniteEnumerationStatistics {
        self.common.statistics
    }

    /// Strict native proof of the composite original source and blockers,
    /// present only for `Exhaustive`. This is not the caller's original UNSAT
    /// decision and does not imply portable Alethe acceptance.
    #[must_use]
    pub fn completeness_proof(&self) -> Option<&UnsatProofArtifact> {
        self.common.completeness_proof.as_ref()
    }

    /// Detail of a declined witness or source proof.
    #[must_use]
    pub fn diagnostic(&self) -> Option<&str> {
        self.common.diagnostic.as_deref()
    }
}
