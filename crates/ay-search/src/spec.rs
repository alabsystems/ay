// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![deny(missing_docs)]

//! Versioned JSON schema and execution boundary for declarative AY Search.
//!
//! The public wire types remain defined in this module. Implementation and test
//! fragments are textually included so decomposition does not change their Rust
//! item paths or the names of existing tests.

use std::collections::BTreeMap;
use std::time::Duration;

use serde::{Deserialize, Serialize, Serializer};

use crate::{
    Domain, EnumerationResult, LinearExpr, Model, OptimizationResult, SearchError, SolveOptions,
    SolveResult,
};

/// Maximum UTF-8 byte length of one restricted SearchSpec equation.
pub const MAX_EXPRESSION_BYTES: usize = 65_536;
/// Maximum number of non-EOF tokens in one restricted SearchSpec equation.
pub const MAX_EXPRESSION_TOKENS: usize = 4_096;
/// Maximum number of solutions retained by untrusted SearchSpec execution.
/// Direct typed-Rust [`Model::enumerate_all`] remains an explicit trusted API.
pub const MAX_SEARCH_SPEC_SOLUTIONS: u64 = 10_000;
/// Maximum `solutions * variables` assignment cells retained and serialized by
/// one SearchSpec enumeration run.
pub const MAX_SEARCH_SPEC_RESULT_CELLS: u64 = 1_000_000;
/// Maximum conservative JSON byte size of a retained SearchSpec enumeration
/// result. The estimate accounts for every repeated assignment name and the
/// longest selectable label for each variable, including JSON escaping.
pub const MAX_SEARCH_SPEC_RESULT_BYTES: u64 = 16 * 1024 * 1024;
/// Maximum SMT-LIB bytes rendered by a SearchSpec compile request.
///
/// Table and element lowerings repeat variable names, so a compact JSON
/// document can otherwise amplify into a much larger output. Typed Rust
/// callers that intentionally need a larger rendering can use
/// [`Model::to_smt2`] directly.
pub const MAX_SEARCH_SPEC_SMT_BYTES: u64 = 16 * 1024 * 1024;

/// Portable version-1 JSON description of a finite-domain search problem.
///
/// Unknown fields are rejected at every schema level. [`SearchSpec::from_json`]
/// checks only the JSON shape; call [`SearchSpec::build`] to validate semantic
/// invariants and resolve all named references.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SearchSpec {
    /// Wire-format version. Version 1 is the only supported value.
    pub version: u32,
    /// Optional diagnostic name carried into the built problem.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,
    /// Variables, created and validated in declaration order.
    pub variables: Vec<VariableSpec>,
    /// Constraints, applied in declaration order after every variable exists.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub constraints: Vec<ConstraintSpec>,
    /// Optional linear objective. Its presence selects optimization mode.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub objective: Option<ObjectiveSpec>,
    /// Optional execution limits and capped-enumeration selection.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub limits: Option<LimitsSpec>,
}

/// A named finite-domain variable in a [`SearchSpec`].
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct VariableSpec {
    /// Identifier matching `[A-Za-z_][A-Za-z0-9_]*`, unique in the spec.
    pub name: String,
    /// Finite set of integer values admitted for the variable.
    pub domain: DomainSpec,
    /// Optional display labels keyed by in-domain integer values.
    ///
    /// Labels are result metadata; they do not add constraints.
    #[serde(default, skip_serializing_if = "BTreeMap::is_empty")]
    pub labels: BTreeMap<i64, String>,
}

/// JSON syntax for a finite integer domain.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum DomainSpec {
    /// Inclusive interval from `min` through `max`.
    Interval {
        /// Smallest admitted value.
        min: i64,
        /// Largest admitted value.
        max: i64,
    },
    /// Explicit finite values, sorted and deduplicated while building.
    Values {
        /// Values admitted by the domain.
        values: Vec<i64>,
    },
}

/// Supported version-1 high-level constraint objects.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum ConstraintSpec {
    /// One restricted affine relation using `==`, `!=`, `<=`, or `>=`.
    Expression {
        /// Relation text parsed as data by AY's restricted expression parser.
        expression: String,
    },
    /// Require all named variables to take pairwise-distinct values.
    AllDifferent {
        /// Non-empty variable-name list.
        all_different: Vec<String>,
    },
    /// Allow only the rows listed in a table constraint.
    Table {
        /// Table columns and allowed tuples.
        table: TableSpec,
    },
    /// Constrain a result variable to equal an indexed array variable.
    Element {
        /// Zero-based element selection description.
        element: ElementSpec,
    },
}

/// Allowed rows for an ordered list of variable columns.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TableSpec {
    /// Variable names in the same column order used by every tuple.
    pub variables: Vec<String>,
    /// Non-empty allowed rows; each row must match `variables` in arity.
    pub tuples: Vec<Vec<i64>>,
}

/// Zero-based selection of one variable from an array of variables.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ElementSpec {
    /// Integer variable whose value is the zero-based array position.
    pub index: String,
    /// Non-empty ordered variable-name array.
    pub array: Vec<String>,
    /// Variable constrained to equal the selected array entry.
    pub result: String,
}

/// Direction of a linear optimization objective.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ObjectiveSense {
    /// Select the smallest feasible objective value.
    Minimize,
    /// Select the largest feasible objective value.
    Maximize,
}

/// Linear objective that selects optimization execution mode.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ObjectiveSpec {
    /// Whether to minimize or maximize the expression.
    pub sense: ObjectiveSense,
    /// Restricted affine expression over declared variables.
    pub expression: String,
}

/// Optional wall-clock and result-retention limits.
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LimitsSpec {
    /// Positive wall-clock budget in milliseconds; `None` means no deadline.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub timeout_ms: Option<u64>,
    /// Select capped enumeration for satisfaction models.
    ///
    /// This cannot be combined with [`SearchSpec::objective`], which selects
    /// optimization. SearchSpec runs are capped by
    /// [`MAX_SEARCH_SPEC_SOLUTIONS`], [`MAX_SEARCH_SPEC_RESULT_CELLS`], and
    /// [`MAX_SEARCH_SPEC_RESULT_BYTES`]; trusted Rust callers can use the
    /// explicit [`Model`] enumeration methods directly.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub max_solutions: Option<u64>,
}

/// A structurally validated search plan ready for execution or SMT lowering.
///
/// Building resolves names, domains, constraints, limits, and restricted
/// expressions. Backend preparation and execution remain fallible and are
/// reported by [`SearchProblem::run`] or [`SearchProblem::to_smt2`].
#[derive(Debug)]
pub struct SearchProblem {
    name: Option<String>,
    model: Model,
    objective: Option<(ObjectiveSense, LinearExpr)>,
    limits: LimitsSpec,
}

/// Result selected by the specification's execution mode.
///
/// Serialization delegates directly to the selected result, without an enum
/// wrapper: optimization is selected by an objective, enumeration by
/// `max_solutions`, and otherwise a single solve is performed.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SearchRunResult {
    /// One satisfaction solve.
    Solve(SolveResult),
    /// Complete, capped, or interrupted solution enumeration.
    Enumeration(EnumerationResult),
    /// Linear optimization, including infeasible or interrupted outcomes.
    Optimization(OptimizationResult),
}

impl Serialize for SearchRunResult {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Solve(result) => result.serialize(serializer),
            Self::Enumeration(result) => result.serialize(serializer),
            Self::Optimization(result) => result.serialize(serializer),
        }
    }
}

// Textual inclusion preserves the established ay_search::spec item paths.
include!("spec/build.rs");
include!("spec/problem.rs");
include!("spec/expression.rs");

#[cfg(test)]
mod tests {
    use super::*;

    // Existing test FQNs remain `spec::tests::*` after decomposition.
    include!("spec/tests.rs");
    include!("spec/contract_tests.rs");
}
