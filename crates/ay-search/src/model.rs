// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use ay_cp::engine::CpSolveResult;
use ay_cp::propagator::Constraint as CpConstraint;
use ay_cp::{CpSatEngine, IntVarId};
use serde::ser::SerializeMap;
use serde::{Serialize, Serializer};

use crate::{BoolVar, IntVar, LinearExpr, SearchError};

static NEXT_MODEL_ID: AtomicU64 = AtomicU64::new(1);

/// Maximum inclusive interval width accepted by the dense AY CP order encoder.
///
/// AY CP currently allocates one order literal for each value in the bounding
/// interval, including holes in an explicit domain. The fixed cap makes model
/// construction safe for untrusted [`SearchSpec`](crate::SearchSpec) input.
pub const MAX_ENCODED_DOMAIN_SPAN: u64 = 65_536;
/// Maximum sum of dense order-encoding slots across all public variables.
pub const MAX_TOTAL_ENCODED_VALUES: u64 = 1_000_000;
/// Maximum number of variables in one high-level search model.
pub const MAX_MODEL_VARIABLES: u64 = 100_000;
/// Maximum number of non-trivial constraints in one search model.
pub const MAX_MODEL_CONSTRAINTS: u64 = 100_000;
/// Maximum number of scalar cells in an allowed-tuples table.
pub const MAX_TABLE_CELLS: u64 = 1_000_000;
/// Largest absolute domain bound, coefficient, constraint RHS, or expression
/// constant accepted for AY CP-SAT lowering.
///
/// AY CP uses `i64` internally and some established propagators compute
/// negated bounds, strict `value +/- 1` bounds, and intermediate slack values.
/// Restricting public inputs to one quarter of the signed range, together with
/// aggregate expression checks, reserves enough headroom for those operations.
pub const MAX_CP_SAFE_MAGNITUDE: i64 = i64::MAX / 4;
/// Maximum conservative estimate of scalar backend-lowering and explanation
/// work accumulated by one model.
///
/// The estimate deliberately reflects expansions hidden by high-level
/// primitives (for example pairwise all-different clauses and quadratic linear
/// explanations). It is a security/resource boundary, not a performance hint.
pub const MAX_BACKEND_WORK: u64 = 1_000_000;

/// A finite integer domain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Domain {
    kind: DomainKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum DomainKind {
    /// Every integer in the inclusive interval `min..=max`.
    Interval { min: i64, max: i64 },
    /// An explicit, non-empty set of integer values.
    Values(Vec<i64>),
}

impl Domain {
    /// Construct an inclusive interval domain.
    pub fn interval(min: i64, max: i64) -> Result<Self, SearchError> {
        if min > max {
            return Err(SearchError::InvalidDomain {
                name: "<anonymous>".to_owned(),
                reason: format!("minimum {min} exceeds maximum {max}"),
            });
        }
        validate_domain_span("<anonymous>", min, max)?;
        Ok(Self {
            kind: DomainKind::Interval { min, max },
        })
    }

    /// Construct an explicit-value domain. Values are sorted and deduplicated.
    pub fn values(values: impl IntoIterator<Item = i64>) -> Result<Self, SearchError> {
        let mut values: Vec<_> = values.into_iter().collect();
        values.sort_unstable();
        values.dedup();
        if values.is_empty() {
            return Err(SearchError::InvalidDomain {
                name: "<anonymous>".to_owned(),
                reason: "explicit domains cannot be empty".to_owned(),
            });
        }
        validate_domain_span("<anonymous>", values[0], values[values.len() - 1])?;
        Ok(Self {
            kind: DomainKind::Values(values),
        })
    }

    /// Return true when `value` is in this domain.
    pub fn contains(&self, value: i64) -> bool {
        match &self.kind {
            DomainKind::Interval { min, max } => (*min..=*max).contains(&value),
            DomainKind::Values(values) => values.binary_search(&value).is_ok(),
        }
    }

    /// Smallest value in the domain.
    pub fn min(&self) -> i64 {
        match &self.kind {
            DomainKind::Interval { min, .. } => *min,
            DomainKind::Values(values) => values[0],
        }
    }

    /// Largest value in the domain.
    pub fn max(&self) -> i64 {
        match &self.kind {
            DomainKind::Interval { max, .. } => *max,
            DomainKind::Values(values) => values[values.len() - 1],
        }
    }

    fn cardinality(&self) -> u128 {
        match &self.kind {
            DomainKind::Interval { min, max } => domain_span(*min, *max),
            DomainKind::Values(values) => values.len() as u128,
        }
    }

    fn has_holes(&self) -> bool {
        match &self.kind {
            DomainKind::Interval { .. } => false,
            DomainKind::Values(values) => {
                (values.len() as u128) < domain_span(values[0], values[values.len() - 1])
            }
        }
    }

    fn validate_for(&self, name: &str) -> Result<(), SearchError> {
        match &self.kind {
            DomainKind::Interval { min, max } if min > max => Err(SearchError::InvalidDomain {
                name: name.to_owned(),
                reason: format!("minimum {min} exceeds maximum {max}"),
            }),
            DomainKind::Values(values) if values.is_empty() => Err(SearchError::InvalidDomain {
                name: name.to_owned(),
                reason: "explicit domains cannot be empty".to_owned(),
            }),
            DomainKind::Values(values) if values.windows(2).any(|pair| pair[0] >= pair[1]) => {
                Err(SearchError::InvalidDomain {
                    name: name.to_owned(),
                    reason: "explicit values must be sorted and unique".to_owned(),
                })
            }
            DomainKind::Interval { min, max } => validate_domain_span(name, *min, *max),
            DomainKind::Values(values) => {
                validate_domain_span(name, values[0], values[values.len() - 1])
            }
        }
    }

    fn to_cp(&self) -> ay_cp::Domain {
        match &self.kind {
            DomainKind::Interval { min, max } => ay_cp::Domain::new(*min, *max),
            DomainKind::Values(values) => ay_cp::Domain::from_values(values),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VariableKind {
    Int,
    Bool,
}

#[derive(Debug, Clone)]
struct Variable {
    name: String,
    domain: Domain,
    kind: VariableKind,
    labels: BTreeMap<i64, String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Relation {
    Eq,
    Le,
    Ge,
    Ne,
}

impl Relation {
    fn holds(self, lhs: i128, rhs: i128) -> bool {
        match self {
            Self::Eq => lhs == rhs,
            Self::Le => lhs <= rhs,
            Self::Ge => lhs >= rhs,
            Self::Ne => lhs != rhs,
        }
    }

    fn smt(self) -> &'static str {
        match self {
            Self::Eq => "=",
            Self::Le => "<=",
            Self::Ge => ">=",
            Self::Ne => "distinct",
        }
    }
}

#[derive(Debug, Clone)]
enum Constraint {
    Linear {
        terms: Vec<(u32, i64)>,
        relation: Relation,
        rhs: i64,
    },
    AllDifferent(Vec<u32>),
    Table {
        variables: Vec<u32>,
        tuples: Vec<Vec<i64>>,
    },
    Element {
        index: u32,
        array: Vec<u32>,
        result: u32,
    },
}

/// Options shared by satisfaction and optimization calls.
#[derive(Debug, Clone, Copy, Default)]
pub struct SolveOptions {
    /// Wall-clock budget for CP-SAT search. `None` means no deadline.
    pub timeout: Option<Duration>,
}

#[derive(Debug)]
struct SolutionMetadata {
    names: Vec<String>,
    kinds: Vec<VariableKind>,
    labels: Vec<BTreeMap<i64, String>>,
    name_to_index: BTreeMap<String, usize>,
}

/// A validated satisfying assignment.
///
/// Values can only be obtained from the `Sat`, `Optimal`, or feasible-incumbent
/// variants, preventing accidental reads after `Unsat` or `Unknown`.
#[derive(Debug, Clone)]
pub struct Solution {
    model_id: u64,
    values: Vec<i64>,
    metadata: Arc<SolutionMetadata>,
}

impl Solution {
    /// Read an integer variable from this assignment.
    pub fn int_value(&self, variable: IntVar) -> Result<i64, SearchError> {
        self.check_handle(variable)?;
        Ok(self.values[variable.index as usize])
    }

    /// Read a Boolean variable from this assignment.
    pub fn bool_value(&self, variable: BoolVar) -> Result<bool, SearchError> {
        let value = self.int_value(variable.as_int())?;
        match value {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(SearchError::InvalidSolverAssignment),
        }
    }

    /// Read a value by its variable name.
    pub fn value(&self, name: &str) -> Option<i64> {
        self.metadata
            .name_to_index
            .get(name)
            .map(|&index| self.values[index])
    }

    /// Return the optional human-readable label for an integer choice.
    pub fn choice_label(&self, variable: IntVar) -> Result<Option<&str>, SearchError> {
        let value = self.int_value(variable)?;
        Ok(self.metadata.labels[variable.index as usize]
            .get(&value)
            .map(String::as_str))
    }

    /// Return the optional human-readable label for a named choice.
    pub fn label(&self, name: &str) -> Option<&str> {
        let index = *self.metadata.name_to_index.get(name)?;
        self.metadata.labels[index]
            .get(&self.values[index])
            .map(String::as_str)
    }

    /// Iterate over `(name, value)` pairs in declaration order.
    pub fn assignments(&self) -> impl ExactSizeIterator<Item = (&str, i64)> {
        self.metadata
            .names
            .iter()
            .map(String::as_str)
            .zip(self.values.iter().copied())
    }

    /// Whether a named variable was declared as a Boolean.
    pub fn is_bool(&self, name: &str) -> Option<bool> {
        let index = *self.metadata.name_to_index.get(name)?;
        Some(self.metadata.kinds[index] == VariableKind::Bool)
    }

    fn check_handle(&self, variable: IntVar) -> Result<(), SearchError> {
        if variable.model_id != self.model_id || variable.index as usize >= self.values.len() {
            return Err(SearchError::ForeignVariable);
        }
        Ok(())
    }

    fn assignment_map(&self) -> BTreeMap<&str, i64> {
        self.assignments().collect()
    }

    fn label_map(&self) -> BTreeMap<&str, &str> {
        self.metadata
            .names
            .iter()
            .enumerate()
            .filter_map(|(index, name)| {
                self.metadata.labels[index]
                    .get(&self.values[index])
                    .map(|label| (name.as_str(), label.as_str()))
            })
            .collect()
    }
}

impl Serialize for Solution {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let labels = self.label_map();
        let mut map = serializer.serialize_map(Some(if labels.is_empty() { 1 } else { 2 }))?;
        map.serialize_entry("assignments", &self.assignment_map())?;
        if !labels.is_empty() {
            map.serialize_entry("labels", &labels)?;
        }
        map.end()
    }
}

/// Result of one satisfaction solve.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum SolveResult {
    Sat(Solution),
    Unsat,
    Unknown,
}

impl Serialize for SolveResult {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Sat(solution) => {
                let labels = solution.label_map();
                let mut map =
                    serializer.serialize_map(Some(if labels.is_empty() { 2 } else { 3 }))?;
                map.serialize_entry("status", "sat")?;
                map.serialize_entry("assignments", &solution.assignment_map())?;
                if !labels.is_empty() {
                    map.serialize_entry("labels", &labels)?;
                }
                map.end()
            }
            Self::Unsat => serialize_status(serializer, "unsat"),
            Self::Unknown => serialize_status(serializer, "unknown"),
        }
    }
}

/// Result of complete or capped model enumeration.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum EnumerationResult {
    /// Every solution was enumerated and the final blocking problem was UNSAT.
    Complete(Vec<Solution>),
    /// The requested solution cap was reached; more solutions may exist.
    Capped(Vec<Solution>),
    /// CP-SAT returned Unknown; the listed prefix remains validated and sound.
    Unknown(Vec<Solution>),
}

impl EnumerationResult {
    pub fn solutions(&self) -> &[Solution] {
        match self {
            Self::Complete(solutions) | Self::Capped(solutions) | Self::Unknown(solutions) => {
                solutions
            }
        }
    }
}

impl Serialize for EnumerationResult {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        let (status, solutions) = match self {
            Self::Complete(solutions) => ("complete", solutions),
            Self::Capped(solutions) => ("capped", solutions),
            Self::Unknown(solutions) => ("unknown", solutions),
        };
        let mut map = serializer.serialize_map(Some(2))?;
        map.serialize_entry("status", status)?;
        map.serialize_entry("solutions", solutions)?;
        map.end()
    }
}

/// Result of a sound manual bound-tightening optimization loop.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum OptimizationResult {
    /// The incumbent is optimal because the next strict bound was UNSAT (or
    /// the objective's proven finite bound was reached).
    Optimal {
        solution: Solution,
        value: i64,
    },
    /// A validated incumbent exists, but a later solve returned Unknown before
    /// optimality could be proved.
    FeasibleOnUnknown {
        solution: Solution,
        value: i64,
    },
    Unsat,
    /// No incumbent was found before CP-SAT returned Unknown.
    Unknown,
}

impl Serialize for OptimizationResult {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        match self {
            Self::Optimal { solution, value } => {
                serialize_optimization(serializer, "optimal", solution, *value)
            }
            Self::FeasibleOnUnknown { solution, value } => {
                serialize_optimization(serializer, "feasible", solution, *value)
            }
            Self::Unsat => serialize_status(serializer, "unsat"),
            Self::Unknown => serialize_status(serializer, "unknown"),
        }
    }
}

/// A typed finite-domain search model.
#[derive(Debug)]
pub struct Model {
    id: u64,
    variables: Vec<Variable>,
    names: BTreeMap<String, u32>,
    constraints: Vec<Constraint>,
    forced_unsat: bool,
    encoded_values: u64,
    backend_work: u64,
}

impl Model {
    pub fn new() -> Self {
        Self {
            id: NEXT_MODEL_ID.fetch_add(1, Ordering::Relaxed),
            variables: Vec::new(),
            names: BTreeMap::new(),
            constraints: Vec::new(),
            forced_unsat: false,
            encoded_values: 0,
            backend_work: 0,
        }
    }

    /// Declare a finite-domain integer variable.
    pub fn int_var(
        &mut self,
        name: impl Into<String>,
        domain: Domain,
    ) -> Result<IntVar, SearchError> {
        self.add_variable(name.into(), domain, VariableKind::Int)
    }

    /// Declare a Boolean variable with the exact domain `{0, 1}`.
    pub fn bool_var(&mut self, name: impl Into<String>) -> Result<BoolVar, SearchError> {
        let variable = self.add_variable(
            name.into(),
            Domain {
                kind: DomainKind::Interval { min: 0, max: 1 },
            },
            VariableKind::Bool,
        )?;
        Ok(BoolVar(variable))
    }

    /// Find a previously declared variable by name.
    pub fn variable(&self, name: &str) -> Option<IntVar> {
        self.names.get(name).map(|&index| IntVar {
            model_id: self.id,
            index,
        })
    }

    /// Associate a domain value with a display label (for example `1 -> gpu`).
    pub fn set_choice_label(
        &mut self,
        variable: IntVar,
        value: i64,
        label: impl Into<String>,
    ) -> Result<(), SearchError> {
        self.validate_var(variable)?;
        let metadata = &mut self.variables[variable.index as usize];
        if !metadata.domain.contains(value) {
            return Err(SearchError::LabelOutsideDomain {
                variable: metadata.name.clone(),
                value,
            });
        }
        metadata.labels.insert(value, label.into());
        Ok(())
    }

    pub fn eq<L: Into<LinearExpr>, R: Into<LinearExpr>>(
        &mut self,
        lhs: L,
        rhs: R,
    ) -> Result<(), SearchError> {
        self.add_linear(lhs.into(), Relation::Eq, rhs.into())
    }

    pub fn le<L: Into<LinearExpr>, R: Into<LinearExpr>>(
        &mut self,
        lhs: L,
        rhs: R,
    ) -> Result<(), SearchError> {
        self.add_linear(lhs.into(), Relation::Le, rhs.into())
    }

    pub fn ge<L: Into<LinearExpr>, R: Into<LinearExpr>>(
        &mut self,
        lhs: L,
        rhs: R,
    ) -> Result<(), SearchError> {
        self.add_linear(lhs.into(), Relation::Ge, rhs.into())
    }

    pub fn ne<L: Into<LinearExpr>, R: Into<LinearExpr>>(
        &mut self,
        lhs: L,
        rhs: R,
    ) -> Result<(), SearchError> {
        self.add_linear(lhs.into(), Relation::Ne, rhs.into())
    }

    /// Require every listed variable to take a distinct value.
    pub fn all_different(&mut self, variables: &[IntVar]) -> Result<(), SearchError> {
        if variables.is_empty() {
            return Err(SearchError::EmptyAllDifferent);
        }
        if variables.len() as u64 > MAX_MODEL_VARIABLES {
            return Err(SearchError::ModelTooLarge {
                resource: "all_different arity",
                limit: MAX_MODEL_VARIABLES,
            });
        }
        let indices = variables
            .iter()
            .map(|&variable| {
                self.validate_var(variable)?;
                Ok(variable.index)
            })
            .collect::<Result<Vec<_>, SearchError>>()?;
        let work = self.all_different_backend_work(&indices);
        self.push_constraint(Constraint::AllDifferent(indices), work)?;
        Ok(())
    }

    /// Restrict a tuple of variables to the explicitly allowed rows.
    pub fn table(&mut self, variables: &[IntVar], tuples: &[Vec<i64>]) -> Result<(), SearchError> {
        if variables.is_empty() {
            return Err(SearchError::EmptyTableVariables);
        }
        if tuples.is_empty() {
            return Err(SearchError::EmptyTableTuples);
        }
        if variables.len() as u64 > MAX_MODEL_VARIABLES {
            return Err(SearchError::ModelTooLarge {
                resource: "table arity",
                limit: MAX_MODEL_VARIABLES,
            });
        }
        let cells = (variables.len() as u128) * (tuples.len() as u128);
        if cells > u128::from(MAX_TABLE_CELLS) {
            return Err(SearchError::TableTooLarge {
                cells,
                limit: MAX_TABLE_CELLS,
            });
        }
        for &variable in variables {
            self.validate_var(variable)?;
        }
        for (tuple_index, tuple) in tuples.iter().enumerate() {
            if tuple.len() != variables.len() {
                return Err(SearchError::TableArity {
                    tuple: tuple_index,
                    actual: tuple.len(),
                    expected: variables.len(),
                });
            }
            for (&variable, &value) in variables.iter().zip(tuple) {
                let metadata = &self.variables[variable.index as usize];
                if !metadata.domain.contains(value) {
                    return Err(SearchError::TableValueOutsideDomain {
                        tuple: tuple_index,
                        variable: metadata.name.clone(),
                        value,
                    });
                }
            }
        }
        let indices = variables
            .iter()
            .map(|variable| variable.index)
            .collect::<Vec<_>>();
        let work = self.table_backend_work(&indices, cells);
        // Check before cloning the tuple matrix into the stored constraint.
        self.ensure_constraint_capacity()?;
        self.checked_backend_work(work)?;
        self.push_constraint(
            Constraint::Table {
                variables: indices,
                tuples: tuples.to_vec(),
            },
            work,
        )?;
        Ok(())
    }

    /// Add `result = array[index]`, with a zero-based index.
    pub fn element(
        &mut self,
        index: IntVar,
        array: &[IntVar],
        result: IntVar,
    ) -> Result<(), SearchError> {
        if array.is_empty() {
            return Err(SearchError::EmptyElementArray);
        }
        if array.len() as u64 > MAX_MODEL_VARIABLES {
            return Err(SearchError::ModelTooLarge {
                resource: "element array length",
                limit: MAX_MODEL_VARIABLES,
            });
        }
        self.validate_var(index)?;
        self.validate_var(result)?;
        for &variable in array {
            self.validate_var(variable)?;
        }
        let index_metadata = &self.variables[index.index as usize];
        let largest_index = array.len() - 1;
        let largest_index_i64 =
            i64::try_from(largest_index).map_err(|_| SearchError::ModelTooLarge {
                resource: "element array length",
                limit: MAX_MODEL_VARIABLES,
            })?;
        if index_metadata.domain.min() < 0 || index_metadata.domain.max() > largest_index_i64 {
            return Err(SearchError::InvalidElementIndexDomain {
                variable: index_metadata.name.clone(),
                min: index_metadata.domain.min(),
                max: index_metadata.domain.max(),
                largest_index,
            });
        }
        let work = square_work(array.len());
        self.push_constraint(
            Constraint::Element {
                index: index.index,
                array: array.iter().map(|variable| variable.index).collect(),
                result: result.index,
            },
            work,
        )?;
        Ok(())
    }

    /// Solve once with no timeout.
    pub fn solve(&self) -> Result<SolveResult, SearchError> {
        self.solve_with_options(SolveOptions::default())
    }

    /// Solve once while preserving SAT/UNSAT/UNKNOWN exactly.
    pub fn solve_with_options(&self, options: SolveOptions) -> Result<SolveResult, SearchError> {
        if self.forced_unsat {
            return Ok(SolveResult::Unsat);
        }
        let mut compiled = self.compile(None)?;
        set_deadline(&mut compiled.engine, options)?;
        match compiled.engine.solve() {
            CpSolveResult::Sat(assignment) => {
                let solution = self.solution_from_cp(
                    &assignment,
                    &compiled.public_cp_vars,
                    Arc::clone(&compiled.metadata),
                )?;
                Ok(SolveResult::Sat(solution))
            }
            CpSolveResult::Unsat => Ok(SolveResult::Unsat),
            CpSolveResult::Unknown => Ok(SolveResult::Unknown),
            _ => Ok(SolveResult::Unknown),
        }
    }

    /// Exhaustively enumerate all satisfying assignments.
    ///
    /// This trusted, explicit Rust API retains every solution and can therefore
    /// consume unbounded result memory. Untrusted JSON/binding execution uses
    /// the fixed SearchSpec solution and assignment-cell caps instead.
    pub fn enumerate_all(&self) -> Result<EnumerationResult, SearchError> {
        self.enumerate(None, SolveOptions::default())
    }

    /// Enumerate at most `limit` satisfying assignments.
    ///
    /// The caller is responsible for choosing a result-memory-safe limit.
    pub fn enumerate_up_to(&self, limit: usize) -> Result<EnumerationResult, SearchError> {
        self.enumerate(Some(limit), SolveOptions::default())
    }

    /// Enumerate with an optional cap and global search deadline.
    ///
    /// `None` is an explicit trusted call: all solutions are retained in memory.
    pub fn enumerate(
        &self,
        limit: Option<usize>,
        options: SolveOptions,
    ) -> Result<EnumerationResult, SearchError> {
        if limit == Some(0) {
            return Ok(EnumerationResult::Capped(Vec::new()));
        }
        if self.forced_unsat {
            return Ok(EnumerationResult::Complete(Vec::new()));
        }
        let deadline = absolute_deadline(options)?;
        let mut compiled = self.compile(None)?;
        let mut solutions = Vec::new();
        loop {
            if let Some(deadline) = deadline {
                compiled.engine.set_deadline(deadline);
            }
            match compiled.engine.solve() {
                CpSolveResult::Sat(assignment) => {
                    let solution = self.solution_from_cp(
                        &assignment,
                        &compiled.public_cp_vars,
                        Arc::clone(&compiled.metadata),
                    )?;
                    let blocking: Vec<_> = compiled
                        .public_cp_vars
                        .iter()
                        .copied()
                        .zip(solution.values.iter().copied())
                        .collect();
                    solutions.push(solution);
                    if limit.is_some_and(|cap| solutions.len() >= cap) {
                        return Ok(EnumerationResult::Capped(solutions));
                    }
                    if blocking.is_empty() {
                        return Ok(EnumerationResult::Complete(solutions));
                    }
                    compiled.engine.block_assignment(&blocking);
                }
                CpSolveResult::Unsat => return Ok(EnumerationResult::Complete(solutions)),
                CpSolveResult::Unknown => return Ok(EnumerationResult::Unknown(solutions)),
                _ => return Ok(EnumerationResult::Unknown(solutions)),
            }
        }
    }

    pub fn minimize(
        &self,
        objective: impl Into<LinearExpr>,
    ) -> Result<OptimizationResult, SearchError> {
        self.optimize(objective.into(), true, SolveOptions::default())
    }

    pub fn maximize(
        &self,
        objective: impl Into<LinearExpr>,
    ) -> Result<OptimizationResult, SearchError> {
        self.optimize(objective.into(), false, SolveOptions::default())
    }

    pub fn minimize_with_options(
        &self,
        objective: impl Into<LinearExpr>,
        options: SolveOptions,
    ) -> Result<OptimizationResult, SearchError> {
        self.optimize(objective.into(), true, options)
    }

    pub fn maximize_with_options(
        &self,
        objective: impl Into<LinearExpr>,
        options: SolveOptions,
    ) -> Result<OptimizationResult, SearchError> {
        self.optimize(objective.into(), false, options)
    }

    /// Produce a standalone, exact QF_LIA lowering for all supported primitives.
    pub fn to_smt2(&self) -> Result<String, SearchError> {
        let mut output = String::from("(set-logic QF_LIA)\n");
        for variable in &self.variables {
            let name = smt_symbol(&variable.name);
            output.push_str(&format!("(declare-const {name} Int)\n"));
            match &variable.domain.kind {
                DomainKind::Interval { min, max } if min == max => {
                    output.push_str(&format!("(assert (= {} {}))\n", name, smt_integer(*min)));
                }
                DomainKind::Interval { min, max } => {
                    output.push_str(&format!(
                        "(assert (<= {} {}))\n(assert (<= {} {}))\n",
                        smt_integer(*min),
                        name,
                        name,
                        smt_integer(*max)
                    ));
                }
                DomainKind::Values(values) if values.len() == 1 => {
                    output.push_str(&format!(
                        "(assert (= {} {}))\n",
                        name,
                        smt_integer(values[0])
                    ));
                }
                DomainKind::Values(values) => {
                    let choices = values
                        .iter()
                        .map(|value| format!("(= {name} {})", smt_integer(*value)))
                        .collect::<Vec<_>>()
                        .join(" ");
                    output.push_str(&format!("(assert (or {choices}))\n"));
                }
            }
        }
        if self.forced_unsat {
            output.push_str("(assert false)\n");
        }
        for constraint in &self.constraints {
            output.push_str("(assert ");
            output.push_str(&self.constraint_to_smt(constraint));
            output.push_str(")\n");
        }
        output.push_str("(check-sat)\n(get-model)\n");
        Ok(output)
    }

    /// Exact byte count for [`Self::to_smt2`].
    ///
    /// This walks the normalized model without materializing repeated table
    /// cells. SearchSpec uses the count as a pre-allocation boundary before
    /// exposing SMT rendering through the untrusted one-shot C ABI.
    pub(crate) fn smt2_size_upper_bound(&self) -> u128 {
        let mut size = "(set-logic QF_LIA)\n".len() as u128;
        for variable in &self.variables {
            let symbol_size = smt_symbol_size(&variable.name);
            size = size
                .saturating_add("(declare-const ".len() as u128)
                .saturating_add(symbol_size)
                .saturating_add(" Int)\n".len() as u128);
            match &variable.domain.kind {
                DomainKind::Interval { min, max } if min == max => {
                    size = size
                        .saturating_add("(assert (= ".len() as u128)
                        .saturating_add(symbol_size)
                        .saturating_add(1)
                        .saturating_add(smt_integer_size(*min))
                        .saturating_add("))\n".len() as u128);
                }
                DomainKind::Interval { min, max } => {
                    size = size
                        .saturating_add("(assert (<= ".len() as u128)
                        .saturating_add(smt_integer_size(*min))
                        .saturating_add(1)
                        .saturating_add(symbol_size)
                        .saturating_add("))\n".len() as u128)
                        .saturating_add("(assert (<= ".len() as u128)
                        .saturating_add(symbol_size)
                        .saturating_add(1)
                        .saturating_add(smt_integer_size(*max))
                        .saturating_add("))\n".len() as u128);
                }
                DomainKind::Values(values) if values.len() == 1 => {
                    size = size
                        .saturating_add("(assert (= ".len() as u128)
                        .saturating_add(symbol_size)
                        .saturating_add(1)
                        .saturating_add(smt_integer_size(values[0]))
                        .saturating_add("))\n".len() as u128);
                }
                DomainKind::Values(values) => {
                    let choices = values.iter().fold(0u128, |total, value| {
                        total.saturating_add(
                            "(= ".len() as u128
                                + symbol_size
                                + 1
                                + smt_integer_size(*value)
                                + ")".len() as u128,
                        )
                    });
                    size = size
                        .saturating_add("(assert (or ".len() as u128)
                        .saturating_add(joined_smt_size(choices, values.len()))
                        .saturating_add("))\n".len() as u128);
                }
            }
        }
        if self.forced_unsat {
            size = size.saturating_add("(assert false)\n".len() as u128);
        }
        for constraint in &self.constraints {
            size = size
                .saturating_add("(assert ".len() as u128)
                .saturating_add(self.constraint_smt_size(constraint))
                .saturating_add(")\n".len() as u128);
        }
        size.saturating_add("(check-sat)\n(get-model)\n".len() as u128)
    }

    pub(crate) fn expression_smt_size_upper_bound(
        &self,
        expression: &LinearExpr,
    ) -> Result<u128, SearchError> {
        self.validate_expression(expression)?;
        let terms = expression
            .terms
            .iter()
            .map(|(variable, coefficient)| {
                let coefficient =
                    i64::try_from(*coefficient).map_err(|_| SearchError::ExpressionOverflow)?;
                if coefficient == i64::MIN {
                    return Err(SearchError::ExpressionOverflow);
                }
                Ok((variable.index, coefficient))
            })
            .collect::<Result<Vec<_>, SearchError>>()?;
        let rendered_terms = linear_terms_smt_size(&terms, &self.variables);
        if expression.constant == 0 {
            return Ok(rendered_terms);
        }
        let constant =
            i64::try_from(expression.constant).map_err(|_| SearchError::ExpressionOverflow)?;
        if terms.is_empty() {
            return Ok(smt_integer_size(constant));
        }
        Ok(("(+ ".len() as u128)
            .saturating_add(rendered_terms)
            .saturating_add(1)
            .saturating_add(smt_integer_size(constant))
            .saturating_add(")".len() as u128))
    }

    pub(crate) fn expression_to_smt(&self, expression: &LinearExpr) -> Result<String, SearchError> {
        self.validate_expression(expression)?;
        let mut terms = expression
            .terms
            .iter()
            .map(|(variable, coefficient)| {
                let coefficient =
                    i64::try_from(*coefficient).map_err(|_| SearchError::ExpressionOverflow)?;
                if coefficient == i64::MIN {
                    return Err(SearchError::ExpressionOverflow);
                }
                Ok((variable.index, coefficient))
            })
            .collect::<Result<Vec<_>, SearchError>>()?;
        if expression.constant != 0 {
            let constant =
                i64::try_from(expression.constant).map_err(|_| SearchError::ExpressionOverflow)?;
            let rendered = linear_terms_to_smt(&terms, &self.variables);
            if terms.is_empty() {
                return Ok(smt_integer(constant));
            }
            return Ok(format!("(+ {rendered} {})", smt_integer(constant)));
        }
        // Keep deterministic variable order inherited from the BTreeMap.
        terms.shrink_to_fit();
        Ok(linear_terms_to_smt(&terms, &self.variables))
    }

    fn add_variable(
        &mut self,
        name: String,
        domain: Domain,
        kind: VariableKind,
    ) -> Result<IntVar, SearchError> {
        if !valid_identifier(&name) {
            return Err(SearchError::InvalidVariableName(name));
        }
        if self.names.contains_key(&name) {
            return Err(SearchError::DuplicateVariable(name));
        }
        domain.validate_for(&name)?;
        if self.variables.len() as u64 >= MAX_MODEL_VARIABLES {
            return Err(SearchError::ModelTooLarge {
                resource: "variable count",
                limit: MAX_MODEL_VARIABLES,
            });
        }
        let encoded_width = encoded_width(&domain)?;
        let new_total =
            self.encoded_values
                .checked_add(encoded_width)
                .ok_or(SearchError::ModelTooLarge {
                    resource: "total encoded domain values",
                    limit: MAX_TOTAL_ENCODED_VALUES,
                })?;
        if new_total > MAX_TOTAL_ENCODED_VALUES {
            return Err(SearchError::ModelTooLarge {
                resource: "total encoded domain values",
                limit: MAX_TOTAL_ENCODED_VALUES,
            });
        }
        let index =
            u32::try_from(self.variables.len()).map_err(|_| SearchError::ExpressionTooWide)?;
        self.names.insert(name.clone(), index);
        self.variables.push(Variable {
            name,
            domain,
            kind,
            labels: BTreeMap::new(),
        });
        self.encoded_values = new_total;
        Ok(IntVar {
            model_id: self.id,
            index,
        })
    }

    fn add_linear(
        &mut self,
        lhs: LinearExpr,
        relation: Relation,
        rhs: LinearExpr,
    ) -> Result<(), SearchError> {
        let expression = lhs.add_expr(rhs, true);
        self.validate_expression(&expression)?;
        let rhs = expression
            .constant
            .checked_neg()
            .and_then(|value| i64::try_from(value).ok())
            .ok_or(SearchError::ExpressionOverflow)?;
        let terms = expression
            .terms
            .iter()
            .map(|(variable, coefficient)| {
                let coefficient =
                    i64::try_from(*coefficient).map_err(|_| SearchError::ExpressionOverflow)?;
                if coefficient == i64::MIN {
                    return Err(SearchError::ExpressionOverflow);
                }
                Ok((variable.index, coefficient))
            })
            .collect::<Result<Vec<_>, SearchError>>()?;
        self.validate_cp_envelope(&terms)?;
        validate_safe_numeric("linear constraint right-hand side", i128::from(rhs))?;
        if terms.is_empty() {
            if !relation.holds(0, i128::from(rhs)) {
                self.forced_unsat = true;
            }
            return Ok(());
        }
        // AY's equality/greater-than compiler negates the RHS internally.
        if matches!(relation, Relation::Eq | Relation::Ge) && rhs == i64::MIN {
            return Err(SearchError::ExpressionOverflow);
        }
        let work = linear_backend_work(terms.len(), relation);
        self.push_constraint(
            Constraint::Linear {
                terms,
                relation,
                rhs,
            },
            work,
        )?;
        Ok(())
    }

    fn push_constraint(
        &mut self,
        constraint: Constraint,
        estimated_backend_work: u128,
    ) -> Result<(), SearchError> {
        self.ensure_constraint_capacity()?;
        let new_work = self.checked_backend_work(estimated_backend_work)?;
        self.constraints.push(constraint);
        self.backend_work = new_work;
        Ok(())
    }

    fn ensure_constraint_capacity(&self) -> Result<(), SearchError> {
        if self.constraints.len() as u64 >= MAX_MODEL_CONSTRAINTS {
            return Err(SearchError::ModelTooLarge {
                resource: "constraint count",
                limit: MAX_MODEL_CONSTRAINTS,
            });
        }
        Ok(())
    }

    fn checked_backend_work(&self, additional: u128) -> Result<u64, SearchError> {
        let new_work = u128::from(self.backend_work)
            .checked_add(additional.max(1))
            .ok_or(SearchError::BackendWorkLimit {
                limit: MAX_BACKEND_WORK,
            })?;
        if new_work > u128::from(MAX_BACKEND_WORK) {
            return Err(SearchError::BackendWorkLimit {
                limit: MAX_BACKEND_WORK,
            });
        }
        u64::try_from(new_work).map_err(|_| SearchError::BackendWorkLimit {
            limit: MAX_BACKEND_WORK,
        })
    }

    fn validate_expression(&self, expression: &LinearExpr) -> Result<(), SearchError> {
        if expression.overflowed {
            return Err(SearchError::ExpressionOverflow);
        }
        validate_safe_numeric("linear expression constant", expression.constant)?;
        for (variable, coefficient) in &expression.terms {
            self.validate_var(*variable)?;
            validate_safe_numeric("linear expression coefficient", *coefficient)?;
        }
        Ok(())
    }

    fn validate_cp_envelope(&self, terms: &[(u32, i64)]) -> Result<(), SearchError> {
        let mut magnitude = 0u128;
        for &(index, coefficient) in terms {
            let domain = &self.variables[index as usize].domain;
            let low = i128::from(coefficient) * i128::from(domain.min());
            let high = i128::from(coefficient) * i128::from(domain.max());
            let contribution = low.unsigned_abs().max(high.unsigned_abs());
            magnitude = magnitude
                .checked_add(contribution)
                .ok_or(SearchError::ExpressionTooWide)?;
            if magnitude > MAX_CP_SAFE_MAGNITUDE as u128 {
                return Err(SearchError::NumericEnvelopeExceeded {
                    resource: "aggregate linear term bounds".to_owned(),
                    magnitude,
                    limit: MAX_CP_SAFE_MAGNITUDE as u64,
                });
            }
        }
        Ok(())
    }

    fn all_different_backend_work(&self, variables: &[u32]) -> u128 {
        let arity = variables.len() as u128;
        // Bounds propagation and the possible n-over-n pigeon-hole encoding.
        let mut work = arity.saturating_mul(arity);

        // Below AY CP's threshold, every pair is eagerly encoded once for each
        // value in the domains' bounding-interval intersection.
        if variables.len() < 20 {
            for (position, &left) in variables.iter().enumerate() {
                let left = &self.variables[left as usize].domain;
                for &right in &variables[position + 1..] {
                    let right = &self.variables[right as usize].domain;
                    let lower = left.min().max(right.min());
                    let upper = left.max().min(right.max());
                    if lower <= upper {
                        work = work.saturating_add(domain_span(lower, upper));
                    }
                }
            }
        }

        // Sparse small domains enroll in the AC propagator, whose current
        // workspace can be proportional to variables x union(values). The sum
        // of cardinalities is a conservative, allocation-safe union bound.
        let ac_eligible = variables
            .iter()
            .all(|&index| self.variables[index as usize].domain.cardinality() <= 128)
            && variables
                .iter()
                .any(|&index| self.variables[index as usize].domain.has_holes());
        if ac_eligible {
            let cardinality_sum = variables.iter().fold(0u128, |sum, &index| {
                sum.saturating_add(self.variables[index as usize].domain.cardinality())
            });
            work = work.saturating_add(arity.saturating_mul(cardinality_sum));
        }
        work
    }

    fn table_backend_work(&self, variables: &[u32], cells: u128) -> u128 {
        let arity = variables.len() as u128;
        let domain_span_sum = variables.iter().fold(0u128, |sum, &index| {
            let domain = &self.variables[index as usize].domain;
            sum.saturating_add(domain_span(domain.min(), domain.max()))
        });
        // Tuple filtering costs `cells`. In the worst propagation round each
        // variable gets two bounds, each explained by every other variable's
        // bounds and holes.
        cells.saturating_add(arity.saturating_mul(domain_span_sum).saturating_mul(2))
    }

    fn validate_var(&self, variable: IntVar) -> Result<(), SearchError> {
        if variable.model_id != self.id || variable.index as usize >= self.variables.len() {
            return Err(SearchError::ForeignVariable);
        }
        Ok(())
    }

    fn expression_bounds(&self, expression: &LinearExpr) -> Result<(i64, i64), SearchError> {
        self.validate_expression(expression)?;
        let mut lower = expression.constant;
        let mut upper = expression.constant;
        let mut raw_terms = Vec::with_capacity(expression.terms.len());
        for (variable, coefficient) in &expression.terms {
            let coefficient_i64 =
                i64::try_from(*coefficient).map_err(|_| SearchError::ExpressionOverflow)?;
            if coefficient_i64 == i64::MIN {
                return Err(SearchError::ExpressionOverflow);
            }
            raw_terms.push((variable.index, coefficient_i64));
            let domain = &self.variables[variable.index as usize].domain;
            let a = coefficient * i128::from(domain.min());
            let b = coefficient * i128::from(domain.max());
            lower = lower
                .checked_add(a.min(b))
                .ok_or(SearchError::ExpressionOverflow)?;
            upper = upper
                .checked_add(a.max(b))
                .ok_or(SearchError::ExpressionOverflow)?;
        }
        self.validate_cp_envelope(&raw_terms)?;
        Ok((
            i64::try_from(lower).map_err(|_| SearchError::ExpressionOverflow)?,
            i64::try_from(upper).map_err(|_| SearchError::ExpressionOverflow)?,
        ))
    }

    fn optimize(
        &self,
        objective: LinearExpr,
        minimize: bool,
        options: SolveOptions,
    ) -> Result<OptimizationResult, SearchError> {
        self.validate_expression(&objective)?;
        let (objective_lower, objective_upper) = self.expression_bounds(&objective)?;
        if self.forced_unsat {
            return Ok(OptimizationResult::Unsat);
        }
        if let Some(value) = objective.constant_value() {
            let value = i64::try_from(value).map_err(|_| SearchError::ExpressionOverflow)?;
            return Ok(match self.solve_with_options(options)? {
                SolveResult::Sat(solution) => OptimizationResult::Optimal { solution, value },
                SolveResult::Unsat => OptimizationResult::Unsat,
                SolveResult::Unknown => OptimizationResult::Unknown,
            });
        }

        let deadline = absolute_deadline(options)?;
        let mut compiled = self.compile(Some((&objective, minimize)))?;
        let objective_var = compiled
            .objective_var
            .ok_or(SearchError::IncompleteAssignment)?;
        let mut incumbent: Option<(Solution, i64)> = None;
        loop {
            if let Some(deadline) = deadline {
                compiled.engine.set_deadline(deadline);
            }
            match compiled.engine.solve() {
                CpSolveResult::Sat(assignment) => {
                    let solution = self.solution_from_cp(
                        &assignment,
                        &compiled.public_cp_vars,
                        Arc::clone(&compiled.metadata),
                    )?;
                    let value = evaluate_expression(&objective, &solution.values)?;
                    let raw_objective = assignment
                        .iter()
                        .find_map(|(variable, value)| {
                            (*variable == objective_var).then_some(*value)
                        })
                        .ok_or(SearchError::IncompleteAssignment)?;
                    let expected_raw = i128::from(value) - objective.constant;
                    if i128::from(raw_objective) != expected_raw {
                        return Err(SearchError::InvalidSolverAssignment);
                    }
                    incumbent = Some((solution, value));
                    let theoretical = if minimize {
                        objective_lower
                    } else {
                        objective_upper
                    };
                    if value == theoretical {
                        if let Some((solution, value)) = incumbent {
                            return Ok(OptimizationResult::Optimal { solution, value });
                        }
                        return Err(SearchError::IncompleteAssignment);
                    }
                    compiled.engine.set_solution_phases(&assignment);
                    if minimize {
                        compiled
                            .engine
                            .add_upper_bound(objective_var, raw_objective - 1);
                    } else {
                        compiled
                            .engine
                            .add_lower_bound(objective_var, raw_objective + 1);
                    }
                }
                CpSolveResult::Unsat => {
                    return Ok(match incumbent {
                        Some((solution, value)) => OptimizationResult::Optimal { solution, value },
                        None => OptimizationResult::Unsat,
                    });
                }
                CpSolveResult::Unknown => {
                    return Ok(match incumbent {
                        Some((solution, value)) => {
                            OptimizationResult::FeasibleOnUnknown { solution, value }
                        }
                        None => OptimizationResult::Unknown,
                    });
                }
                _ => {
                    return Ok(match incumbent {
                        Some((solution, value)) => {
                            OptimizationResult::FeasibleOnUnknown { solution, value }
                        }
                        None => OptimizationResult::Unknown,
                    });
                }
            }
        }
    }

    fn compile(&self, objective: Option<(&LinearExpr, bool)>) -> Result<Compiled, SearchError> {
        if let Some((expression, _)) = objective {
            self.checked_backend_work(linear_backend_work(
                expression.terms.len().saturating_add(1),
                Relation::Eq,
            ))?;
        }
        let mut engine = CpSatEngine::new();
        let public_cp_vars: Vec<_> = self
            .variables
            .iter()
            .map(|variable| engine.new_int_var(variable.domain.to_cp(), Some(&variable.name)))
            .collect();
        for constraint in &self.constraints {
            engine.add_constraint(lower_constraint(constraint, &public_cp_vars));
        }
        let mut objective_var = None;
        if let Some((expression, minimize)) = objective {
            let mut raw = expression.clone();
            raw.constant = 0;
            let (raw_lower, raw_upper) = self.expression_bounds(&raw)?;
            let objective_domain = Domain::interval(raw_lower, raw_upper)?;
            let objective_width = encoded_width(&objective_domain)?;
            if self.encoded_values.saturating_add(objective_width) > MAX_TOTAL_ENCODED_VALUES {
                return Err(SearchError::ModelTooLarge {
                    resource: "total encoded domain values including objective",
                    limit: MAX_TOTAL_ENCODED_VALUES,
                });
            }
            let cp_objective =
                engine.new_int_var(objective_domain.to_cp(), Some("_ay_search_objective"));
            let mut coeffs = Vec::with_capacity(raw.terms.len() + 1);
            let mut vars = Vec::with_capacity(raw.terms.len() + 1);
            for (variable, coefficient) in &raw.terms {
                coeffs.push(
                    i64::try_from(*coefficient).map_err(|_| SearchError::ExpressionOverflow)?,
                );
                vars.push(public_cp_vars[variable.index as usize]);
            }
            coeffs.push(-1);
            vars.push(cp_objective);
            engine.add_constraint(CpConstraint::LinearEq {
                coeffs,
                vars,
                rhs: 0,
            });
            engine.set_objective(cp_objective, minimize);
            objective_var = Some(cp_objective);
        }
        Ok(Compiled {
            engine,
            public_cp_vars,
            metadata: self.solution_metadata(),
            objective_var,
        })
    }

    fn solution_metadata(&self) -> Arc<SolutionMetadata> {
        Arc::new(SolutionMetadata {
            names: self
                .variables
                .iter()
                .map(|variable| variable.name.clone())
                .collect(),
            kinds: self
                .variables
                .iter()
                .map(|variable| variable.kind)
                .collect(),
            labels: self
                .variables
                .iter()
                .map(|variable| variable.labels.clone())
                .collect(),
            name_to_index: self
                .variables
                .iter()
                .enumerate()
                .map(|(index, variable)| (variable.name.clone(), index))
                .collect(),
        })
    }

    fn solution_from_cp(
        &self,
        assignment: &[(IntVarId, i64)],
        public_cp_vars: &[IntVarId],
        metadata: Arc<SolutionMetadata>,
    ) -> Result<Solution, SearchError> {
        let assignment: BTreeMap<_, _> = assignment.iter().copied().collect();
        let values = public_cp_vars
            .iter()
            .map(|variable| {
                assignment
                    .get(variable)
                    .copied()
                    .ok_or(SearchError::IncompleteAssignment)
            })
            .collect::<Result<Vec<_>, _>>()?;
        if !self.validate_values(&values) {
            return Err(SearchError::InvalidSolverAssignment);
        }
        Ok(Solution {
            model_id: self.id,
            values,
            metadata,
        })
    }

    fn validate_values(&self, values: &[i64]) -> bool {
        if values.len() != self.variables.len()
            || self
                .variables
                .iter()
                .zip(values)
                .any(|(variable, &value)| !variable.domain.contains(value))
        {
            return false;
        }
        self.constraints.iter().all(|constraint| match constraint {
            Constraint::Linear {
                terms,
                relation,
                rhs,
            } => {
                let lhs: i128 = terms
                    .iter()
                    .map(|&(index, coefficient)| {
                        i128::from(coefficient) * i128::from(values[index as usize])
                    })
                    .sum();
                relation.holds(lhs, i128::from(*rhs))
            }
            Constraint::AllDifferent(variables) => {
                let distinct: BTreeSet<_> = variables
                    .iter()
                    .map(|&index| values[index as usize])
                    .collect();
                distinct.len() == variables.len()
            }
            Constraint::Table { variables, tuples } => tuples.iter().any(|tuple| {
                variables
                    .iter()
                    .zip(tuple)
                    .all(|(&index, &expected)| values[index as usize] == expected)
            }),
            Constraint::Element {
                index,
                array,
                result,
            } => usize::try_from(values[*index as usize])
                .ok()
                .and_then(|position| array.get(position))
                .is_some_and(|&selected| values[*result as usize] == values[selected as usize]),
        })
    }

    fn constraint_to_smt(&self, constraint: &Constraint) -> String {
        match constraint {
            Constraint::Linear {
                terms,
                relation,
                rhs,
            } => format!(
                "({} {} {})",
                relation.smt(),
                linear_terms_to_smt(terms, &self.variables),
                smt_integer(*rhs)
            ),
            Constraint::AllDifferent(variables) => format!(
                "(distinct {})",
                variables
                    .iter()
                    .map(|&index| smt_symbol(&self.variables[index as usize].name))
                    .collect::<Vec<_>>()
                    .join(" ")
            ),
            Constraint::Table { variables, tuples } => {
                if tuples.is_empty() {
                    return "false".to_owned();
                }
                let rows = tuples
                    .iter()
                    .map(|tuple| {
                        let cells = variables
                            .iter()
                            .zip(tuple)
                            .map(|(&index, &value)| {
                                format!(
                                    "(= {} {})",
                                    smt_symbol(&self.variables[index as usize].name),
                                    smt_integer(value)
                                )
                            })
                            .collect::<Vec<_>>()
                            .join(" ");
                        format!("(and {cells})")
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(or {rows})")
            }
            Constraint::Element {
                index,
                array,
                result,
            } => {
                let index_name = smt_symbol(&self.variables[*index as usize].name);
                let result_name = smt_symbol(&self.variables[*result as usize].name);
                let choices = array
                    .iter()
                    .enumerate()
                    .map(|(position, &selected)| {
                        format!(
                            "(and (= {index_name} {position}) (= {result_name} {}))",
                            smt_symbol(&self.variables[selected as usize].name)
                        )
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(or {choices})")
            }
        }
    }

    fn constraint_smt_size(&self, constraint: &Constraint) -> u128 {
        match constraint {
            Constraint::Linear {
                terms,
                relation,
                rhs,
            } => {
                "(".len() as u128
                    + relation.smt().len() as u128
                    + 1
                    + linear_terms_smt_size(terms, &self.variables)
                    + 1
                    + smt_integer_size(*rhs)
                    + ")".len() as u128
            }
            Constraint::AllDifferent(variables) => {
                let symbols = variables.iter().fold(0u128, |total, &index| {
                    total.saturating_add(smt_symbol_size(&self.variables[index as usize].name))
                });
                "(distinct ".len() as u128
                    + joined_smt_size(symbols, variables.len())
                    + ")".len() as u128
            }
            Constraint::Table { variables, tuples } => {
                if tuples.is_empty() {
                    return "false".len() as u128;
                }
                let rows = tuples.iter().fold(0u128, |rows, tuple| {
                    let cells =
                        variables
                            .iter()
                            .zip(tuple)
                            .fold(0u128, |cells, (&index, &value)| {
                                cells.saturating_add(
                                    "(= ".len() as u128
                                        + smt_symbol_size(&self.variables[index as usize].name)
                                        + 1
                                        + smt_integer_size(value)
                                        + ")".len() as u128,
                                )
                            });
                    rows.saturating_add(
                        "(and ".len() as u128
                            + joined_smt_size(cells, variables.len())
                            + ")".len() as u128,
                    )
                });
                "(or ".len() as u128 + joined_smt_size(rows, tuples.len()) + ")".len() as u128
            }
            Constraint::Element {
                index,
                array,
                result,
            } => {
                let index_size = smt_symbol_size(&self.variables[*index as usize].name);
                let result_size = smt_symbol_size(&self.variables[*result as usize].name);
                let choices =
                    array
                        .iter()
                        .enumerate()
                        .fold(0u128, |total, (position, &selected)| {
                            total.saturating_add(
                                "(and (= ".len() as u128
                                    + index_size
                                    + 1
                                    + decimal_digits(position as u128)
                                    + ") (= ".len() as u128
                                    + result_size
                                    + 1
                                    + smt_symbol_size(&self.variables[selected as usize].name)
                                    + "))".len() as u128,
                            )
                        });
                "(or ".len() as u128 + joined_smt_size(choices, array.len()) + ")".len() as u128
            }
        }
    }
}

impl Default for Model {
    fn default() -> Self {
        Self::new()
    }
}

struct Compiled {
    engine: CpSatEngine,
    public_cp_vars: Vec<IntVarId>,
    metadata: Arc<SolutionMetadata>,
    objective_var: Option<IntVarId>,
}

fn lower_constraint(constraint: &Constraint, variables: &[IntVarId]) -> CpConstraint {
    match constraint {
        Constraint::Linear {
            terms,
            relation,
            rhs,
        } => {
            let coeffs = terms.iter().map(|(_, coefficient)| *coefficient).collect();
            let vars = terms
                .iter()
                .map(|(index, _)| variables[*index as usize])
                .collect();
            match relation {
                Relation::Eq => CpConstraint::LinearEq {
                    coeffs,
                    vars,
                    rhs: *rhs,
                },
                Relation::Le => CpConstraint::LinearLe {
                    coeffs,
                    vars,
                    rhs: *rhs,
                },
                Relation::Ge => CpConstraint::LinearGe {
                    coeffs,
                    vars,
                    rhs: *rhs,
                },
                Relation::Ne => CpConstraint::LinearNotEqual {
                    coeffs,
                    vars,
                    rhs: *rhs,
                },
            }
        }
        Constraint::AllDifferent(indices) => CpConstraint::AllDifferent(
            indices
                .iter()
                .map(|&index| variables[index as usize])
                .collect(),
        ),
        Constraint::Table {
            variables: indices,
            tuples,
        } => CpConstraint::Table {
            vars: indices
                .iter()
                .map(|&index| variables[index as usize])
                .collect(),
            tuples: tuples.clone(),
        },
        Constraint::Element {
            index,
            array,
            result,
        } => CpConstraint::Element {
            index: variables[*index as usize],
            array: array.iter().map(|&item| variables[item as usize]).collect(),
            result: variables[*result as usize],
        },
    }
}

fn absolute_deadline(options: SolveOptions) -> Result<Option<Instant>, SearchError> {
    options
        .timeout
        .map(|timeout| {
            Instant::now()
                .checked_add(timeout)
                .ok_or(SearchError::InvalidLimit {
                    name: "timeout",
                    value: timeout.as_millis().min(u128::from(u64::MAX)) as u64,
                })
        })
        .transpose()
}

fn set_deadline(engine: &mut CpSatEngine, options: SolveOptions) -> Result<(), SearchError> {
    if let Some(deadline) = absolute_deadline(options)? {
        engine.set_deadline(deadline);
    }
    Ok(())
}

fn evaluate_expression(expression: &LinearExpr, values: &[i64]) -> Result<i64, SearchError> {
    let mut value = expression.constant;
    for (variable, coefficient) in &expression.terms {
        value = value
            .checked_add(coefficient * i128::from(values[variable.index as usize]))
            .ok_or(SearchError::ExpressionOverflow)?;
    }
    i64::try_from(value).map_err(|_| SearchError::ExpressionOverflow)
}

fn valid_identifier(name: &str) -> bool {
    let mut chars = name.chars();
    matches!(chars.next(), Some(first) if first == '_' || first.is_ascii_alphabetic())
        && chars.all(|character| character == '_' || character.is_ascii_alphanumeric())
}

fn validate_domain_span(name: &str, min: i64, max: i64) -> Result<(), SearchError> {
    validate_safe_numeric(format!("domain `{name}` lower bound"), i128::from(min))?;
    validate_safe_numeric(format!("domain `{name}` upper bound"), i128::from(max))?;
    let span = domain_span(min, max);
    if span > u128::from(MAX_ENCODED_DOMAIN_SPAN) {
        return Err(SearchError::DomainTooLarge {
            name: name.to_owned(),
            span,
            limit: MAX_ENCODED_DOMAIN_SPAN,
        });
    }
    Ok(())
}

fn validate_safe_numeric(resource: impl Into<String>, value: i128) -> Result<(), SearchError> {
    let magnitude = value.unsigned_abs();
    if magnitude > MAX_CP_SAFE_MAGNITUDE as u128 {
        return Err(SearchError::NumericEnvelopeExceeded {
            resource: resource.into(),
            magnitude,
            limit: MAX_CP_SAFE_MAGNITUDE as u64,
        });
    }
    Ok(())
}

fn domain_span(min: i64, max: i64) -> u128 {
    debug_assert!(min <= max);
    (i128::from(max) - i128::from(min) + 1) as u128
}

fn square_work(arity: usize) -> u128 {
    let arity = arity as u128;
    arity.saturating_mul(arity)
}

fn linear_backend_work(arity: usize, relation: Relation) -> u128 {
    let factor = if relation == Relation::Eq { 2 } else { 1 };
    square_work(arity).max(1).saturating_mul(factor)
}

fn encoded_width(domain: &Domain) -> Result<u64, SearchError> {
    let span = domain_span(domain.min(), domain.max());
    // CP allocates the sentinel `[x >= ub + 1]` except at i64::MAX.
    let sentinel = u128::from(domain.max() != i64::MAX);
    u64::try_from(span + sentinel).map_err(|_| SearchError::ExpressionTooWide)
}

fn smt_integer(value: i64) -> String {
    if value < 0 {
        format!("(- {})", -i128::from(value))
    } else {
        value.to_string()
    }
}

fn smt_integer_size(value: i64) -> u128 {
    let digits = decimal_digits(i128::from(value).unsigned_abs());
    if value < 0 {
        "(- ".len() as u128 + digits + ")".len() as u128
    } else {
        digits
    }
}

fn decimal_digits(mut value: u128) -> u128 {
    let mut digits = 1;
    while value >= 10 {
        value /= 10;
        digits += 1;
    }
    digits
}

fn smt_symbol(name: &str) -> String {
    // Model identifiers are restricted to ASCII alphanumeric/underscore, so
    // neither SMT's `|` delimiter nor backslash can occur here. Quoting every
    // name avoids collisions with both current and future SMT-LIB reserved or
    // theory-provided identifiers (`let`, `and`, `div`, ...).
    format!("|{name}|")
}

fn smt_symbol_size(name: &str) -> u128 {
    name.len() as u128 + 2
}

fn linear_terms_to_smt(terms: &[(u32, i64)], variables: &[Variable]) -> String {
    let rendered = terms
        .iter()
        .map(|&(index, coefficient)| {
            let name = smt_symbol(&variables[index as usize].name);
            match coefficient {
                1 => name,
                -1 => format!("(- {name})"),
                _ => format!("(* {} {name})", smt_integer(coefficient)),
            }
        })
        .collect::<Vec<_>>();
    match rendered.as_slice() {
        [] => "0".to_owned(),
        [term] => term.clone(),
        _ => format!("(+ {})", rendered.join(" ")),
    }
}

fn linear_terms_smt_size(terms: &[(u32, i64)], variables: &[Variable]) -> u128 {
    let terms_size = terms.iter().fold(0u128, |total, &(index, coefficient)| {
        let symbol_size = smt_symbol_size(&variables[index as usize].name);
        let term_size = match coefficient {
            1 => symbol_size,
            -1 => "(- ".len() as u128 + symbol_size + ")".len() as u128,
            _ => {
                "(* ".len() as u128
                    + smt_integer_size(coefficient)
                    + 1
                    + symbol_size
                    + ")".len() as u128
            }
        };
        total.saturating_add(term_size)
    });
    match terms.len() {
        0 => "0".len() as u128,
        1 => terms_size,
        count => "(+ ".len() as u128 + joined_smt_size(terms_size, count) + ")".len() as u128,
    }
}

fn joined_smt_size(items_size: u128, item_count: usize) -> u128 {
    items_size.saturating_add(item_count.saturating_sub(1) as u128)
}

fn serialize_status<S: Serializer>(serializer: S, status: &str) -> Result<S::Ok, S::Error> {
    let mut map = serializer.serialize_map(Some(1))?;
    map.serialize_entry("status", status)?;
    map.end()
}

fn serialize_optimization<S: Serializer>(
    serializer: S,
    status: &str,
    solution: &Solution,
    value: i64,
) -> Result<S::Ok, S::Error> {
    let labels = solution.label_map();
    let mut map = serializer.serialize_map(Some(if labels.is_empty() { 3 } else { 4 }))?;
    map.serialize_entry("status", status)?;
    map.serialize_entry("objective", &value)?;
    map.serialize_entry("assignments", &solution.assignment_map())?;
    if !labels.is_empty() {
        map.serialize_entry("labels", &labels)?;
    }
    map.end()
}
