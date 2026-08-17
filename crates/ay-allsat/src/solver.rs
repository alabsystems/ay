// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ALL-SAT Solver Implementation
//!
//! This module implements solution enumeration using iterative SAT solving
//! with blocking clauses. Supports two backends:
//!
//! - **Internal**: Clauses accumulated in memory; a fresh SAT solver is built
//!   for each enumeration call (backwards-compatible default).
//! - **External**: An existing `ay_sat::Solver` is passed in; blocking clauses
//!   are added incrementally, preserving learned clauses between iterations.

use std::collections::HashSet;

#[cfg(test)]
use ay_sat::Variable;
use ay_sat::{Literal, SignedClause, Solver as SatSolver};

use crate::outcome::{AllSatIncomplete, AllSatInputError, AllSatOutcome, AllSatStats};

mod backend;
mod iterator;
mod solution;

pub use iterator::AllSatIterator;
pub use solution::{Solution, SolutionIndexing, SolutionLiteralError};

/// Default safety limit for model enumeration (#8625).
///
/// The `enumerate()` and `iter()` convenience methods apply this cap to
/// prevent accidental OOM on problems with exponentially many models. Use
/// `enumerate_with_config()` or `iter_with_config()` with an explicit
/// `max_solutions` to override.
const DEFAULT_MAX_SOLUTIONS: usize = 1_000_000;

/// The internal backend allocates every 1-based identifier through `max_var`,
/// including gaps. Reject larger identifiers before constructing ay-sat's
/// dense variable state instead of risking a multi-gigabyte allocation.
const MAX_INTERNAL_VARIABLE_INDEX: u32 = 1_000_000;

/// Collected solutions together with their explicit termination status.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct EnumerationReport {
    /// Solutions found before enumeration terminated.
    pub solutions: Vec<Solution>,
    /// Per-run statistics and the reason enumeration terminated.
    pub stats: AllSatStats,
}

/// Configuration for ALL-SAT enumeration.
#[derive(Debug, Clone, Default)]
pub struct AllSatConfig {
    /// Maximum number of solutions to enumerate (None = unlimited).
    pub max_solutions: Option<usize>,

    /// Variables to project onto (None = all variables).
    /// When set, blocking clauses only reference these variables,
    /// effectively finding all distinct assignments to projected vars.
    /// Indices are 1-based for [`AllSatSolver::new`] and 0-based for
    /// [`AllSatSolver::from_solver`], matching the selected backend.
    pub projection: Option<Vec<u32>>,
}

/// Backend for the ALL-SAT solver.
///
/// Internal mode stores clauses and rebuilds a fresh solver per iteration.
/// External mode wraps a caller-provided solver and adds blocking clauses
/// incrementally, preserving learned clauses.
///
/// Indexing convention: the internal backend uses 1-indexed variables
/// (matching the `SignedClause` convention where variable 0 is unused).
/// The external backend uses 0-indexed variables (matching ay-sat's
/// native `Variable::new(idx)` convention).
enum SolverBackend {
    /// Clauses accumulated internally; fresh solver built per call.
    /// Variables are 1-indexed: variable indices go from 1 to max_var.
    Internal {
        clauses: Vec<Vec<Literal>>,
        max_var: u32,
    },
    /// External solver; blocking clauses added incrementally.
    /// Variables are 0-indexed: variable indices go from 0 to num_vars-1.
    External(Box<SatSolver>),
}

/// ALL-SAT Solver
///
/// Enumerates all satisfying assignments to a Boolean formula.
///
/// Two construction modes:
/// - [`AllSatSolver::new()`]: Internal mode — accumulate clauses, rebuild solver
///   each iteration. Simple and correct.
/// - [`AllSatSolver::from_solver()`]: External mode — wrap an existing SAT solver,
///   add blocking clauses incrementally. Preserves learned clauses between
///   iterations for better performance on large formulas.
pub struct AllSatSolver {
    backend: SolverBackend,
    stats: AllSatStats,
    invalid_input: Option<AllSatInputError>,
}

impl AllSatSolver {
    /// Create a new ALL-SAT solver (internal backend).
    ///
    /// Clauses are accumulated via [`add_clause`](Self::add_clause) and a fresh
    /// SAT solver is constructed for each enumeration call.
    pub fn new() -> Self {
        Self {
            backend: SolverBackend::Internal {
                clauses: Vec::new(),
                max_var: 0,
            },
            stats: AllSatStats::default(),
            invalid_input: None,
        }
    }

    /// Create an ALL-SAT solver wrapping an existing SAT solver (external backend).
    ///
    /// The solver should already have clauses loaded. Blocking clauses are added
    /// incrementally to the same solver instance, preserving learned clauses
    /// between iterations. This is more efficient for large formulas and useful
    /// when the caller wants to share learned clauses with other solving tasks.
    pub fn from_solver(solver: SatSolver) -> Self {
        Self {
            backend: SolverBackend::External(Box::new(solver)),
            stats: AllSatStats::default(),
            invalid_input: None,
        }
    }

    /// Recover an owned external SAT solver.
    ///
    /// All enumeration blockers are scoped and retracted before an enumeration
    /// method or iterator completes, so the returned solver retains its base
    /// formula. Returns the unchanged `AllSatSolver` for the internal backend
    /// or when a previously latched backend error makes safe recovery
    /// impossible.
    pub fn try_into_solver(self) -> Result<SatSolver, Self> {
        if self.invalid_input.is_some() {
            return Err(self);
        }
        match self {
            Self {
                backend: SolverBackend::External(solver),
                ..
            } => Ok(*solver),
            internal => Err(internal),
        }
    }

    /// Add a clause to the formula.
    ///
    /// Literals use signed integer encoding: positive = positive literal,
    /// negative = negated literal. E.g., `vec![1, -2]` means x1 OR NOT x2.
    /// This compatibility method is supported only by the internal backend.
    /// Invalid input is latched so every later enumeration fails closed with
    /// [`AllSatOutcome::InvalidInput`]. Use [`try_add_clause`](Self::try_add_clause)
    /// when the caller can handle the error immediately.
    pub fn add_clause(&mut self, clause: SignedClause) {
        if let Err(error) = self.try_add_clause(clause) {
            self.invalid_input.get_or_insert(error);
            self.set_last_outcome(AllSatOutcome::InvalidInput, Some(error));
        }
    }

    /// Try to add an internal-backend signed clause.
    ///
    /// Literal zero and `i32::MIN` are rejected before conversion. External
    /// backends are also rejected because their formula is natively 0-based
    /// and must be loaded into the SAT solver before [`from_solver`](Self::from_solver).
    pub fn try_add_clause(&mut self, clause: SignedClause) -> Result<(), AllSatInputError> {
        let SolverBackend::Internal { clauses, max_var } = &mut self.backend else {
            return Err(AllSatInputError::ClauseAdditionUnsupportedBackend);
        };

        for &literal in &clause {
            if literal == 0 || literal == i32::MIN {
                return Err(AllSatInputError::InvalidClauseLiteral(literal));
            }
            let variable = literal.unsigned_abs();
            if variable > MAX_INTERNAL_VARIABLE_INDEX {
                return Err(AllSatInputError::InternalVariableIndexExceedsLimit {
                    variable,
                    max_variable: MAX_INTERNAL_VARIABLE_INDEX,
                });
            }
        }

        let lits: Vec<Literal> = clause
            .iter()
            .map(|&literal| Literal::from(literal))
            .collect();
        for literal in clause {
            *max_var = (*max_var).max(literal.unsigned_abs());
        }
        clauses.push(lits);
        Ok(())
    }

    /// Ensure that the internal formula contains at least `variable_count`
    /// 1-based variables, including variables that do not occur in a clause.
    ///
    /// DIMACS headers and other formula containers can declare free variables;
    /// those variables are semantically part of full model enumeration and
    /// must not be inferred only from the largest clause literal.
    pub fn try_ensure_num_vars(&mut self, variable_count: usize) -> Result<(), AllSatInputError> {
        let SolverBackend::Internal { max_var, .. } = &mut self.backend else {
            return Err(AllSatInputError::VariableRegistrationUnsupportedBackend);
        };
        if variable_count > MAX_INTERNAL_VARIABLE_INDEX as usize {
            return Err(AllSatInputError::InternalVariableCountExceedsLimit {
                variable_count,
                max_variable: MAX_INTERNAL_VARIABLE_INDEX,
            });
        }
        let declared = u32::try_from(variable_count).map_err(|_| {
            AllSatInputError::InternalVariableCountExceedsLimit {
                variable_count,
                max_variable: MAX_INTERNAL_VARIABLE_INDEX,
            }
        })?;
        *max_var = (*max_var).max(declared);
        Ok(())
    }

    /// Get the number of variables.
    ///
    /// For the internal backend this is the maximum variable index seen.
    /// For the external backend this is the solver's user variable count.
    pub fn num_vars(&self) -> usize {
        match &self.backend {
            SolverBackend::Internal { max_var, .. } => *max_var as usize,
            SolverBackend::External(solver) => solver.user_num_vars(),
        }
    }

    /// Get solver statistics.
    pub fn stats(&self) -> &AllSatStats {
        &self.stats
    }

    pub(crate) fn set_last_outcome(
        &mut self,
        outcome: AllSatOutcome,
        input_error: Option<AllSatInputError>,
    ) {
        self.stats.outcome = outcome;
        self.stats.input_error = input_error;
    }

    fn validate_config(&self, config: &AllSatConfig) -> Result<(), AllSatInputError> {
        if let Some(error) = self.invalid_input {
            return Err(error);
        }

        let Some(projection) = &config.projection else {
            return self.validate_backend_size();
        };

        self.validate_backend_size()?;
        let mut seen = HashSet::with_capacity(projection.len());
        for &variable in projection {
            if !seen.insert(variable) {
                return Err(AllSatInputError::DuplicateProjectionVariable(variable));
            }
            match &self.backend {
                SolverBackend::Internal { max_var, .. } => {
                    if variable == 0 || variable > *max_var {
                        return Err(AllSatInputError::InternalProjectionVariableOutOfRange {
                            variable,
                            max_variable: *max_var,
                        });
                    }
                }
                SolverBackend::External(solver) => {
                    let variable_count = u32::try_from(solver.user_num_vars()).map_err(|_| {
                        AllSatInputError::BackendVariableCountOutOfRange(solver.user_num_vars())
                    })?;
                    if variable >= variable_count {
                        return Err(AllSatInputError::ExternalProjectionVariableOutOfRange {
                            variable,
                            variable_count,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    fn validate_backend_size(&self) -> Result<(), AllSatInputError> {
        match &self.backend {
            SolverBackend::Internal { max_var, .. } => {
                usize::try_from(*max_var)
                    .ok()
                    .and_then(|max| max.checked_add(1))
                    .ok_or(AllSatInputError::BackendVariableCountOutOfRange(
                        *max_var as usize,
                    ))?;
            }
            SolverBackend::External(solver) => {
                let count = solver.user_num_vars();
                let largest_encodable_count = (i32::MAX as usize).saturating_add(1);
                if count > largest_encodable_count || u32::try_from(count).is_err() {
                    return Err(AllSatInputError::BackendVariableCountOutOfRange(count));
                }
            }
        }
        Ok(())
    }

    /// Create an iterator over all solutions.
    ///
    /// Applies `DEFAULT_MAX_SOLUTIONS` as a safety cap to prevent OOM on
    /// problems with exponentially many models. Use [`iter_with_config`](Self::iter_with_config)
    /// with an explicit `max_solutions` to override (#8625).
    pub fn iter(&mut self) -> AllSatIterator<'_> {
        let config = AllSatConfig {
            max_solutions: Some(DEFAULT_MAX_SOLUTIONS),
            ..Default::default()
        };
        self.iter_with_config(config)
    }

    /// Create an iterator with custom configuration.
    pub fn iter_with_config(&mut self, config: AllSatConfig) -> AllSatIterator<'_> {
        AllSatIterator::new(self, config)
    }

    /// Enumerate solutions into a vector (partial-result convenience method).
    ///
    /// Applies `DEFAULT_MAX_SOLUTIONS` as a safety cap. A cap, invalid input,
    /// or backend `Unknown` can therefore return a partial vector; inspect
    /// [`stats`](Self::stats), use [`enumerate_report`](Self::enumerate_report),
    /// or use [`try_enumerate`](Self::try_enumerate) when exhaustiveness matters.
    pub fn enumerate(&mut self) -> Vec<Solution> {
        self.enumerate_report().solutions
    }

    /// Enumerate solutions with custom configuration, returning any partial
    /// vector produced before termination.
    ///
    /// Use [`enumerate_report_with_config`](Self::enumerate_report_with_config)
    /// to receive termination status alongside the solutions.
    pub fn enumerate_with_config(&mut self, config: AllSatConfig) -> Vec<Solution> {
        self.enumerate_report_with_config(config).solutions
    }

    /// Enumerate with the default safety cap and return an explicit report.
    pub fn enumerate_report(&mut self) -> EnumerationReport {
        let config = AllSatConfig {
            max_solutions: Some(DEFAULT_MAX_SOLUTIONS),
            ..Default::default()
        };
        self.enumerate_report_with_config(config)
    }

    /// Enumerate with custom configuration and return solutions plus the
    /// explicit termination status.
    pub fn enumerate_report_with_config(&mut self, config: AllSatConfig) -> EnumerationReport {
        let mut solutions = Vec::new();
        let stats = self.enumerate_with_callback(config, |solution| {
            solutions.push(solution.clone());
            true
        });
        EnumerationReport { solutions, stats }
    }

    /// Collect solutions only when enumeration proves exhaustion.
    pub fn try_enumerate(&mut self) -> Result<Vec<Solution>, AllSatIncomplete> {
        let config = AllSatConfig {
            max_solutions: Some(DEFAULT_MAX_SOLUTIONS),
            ..Default::default()
        };
        self.try_enumerate_with_config(config)
    }

    /// Collect solutions with custom configuration, failing if enumeration
    /// does not prove exhaustion.
    pub fn try_enumerate_with_config(
        &mut self,
        config: AllSatConfig,
    ) -> Result<Vec<Solution>, AllSatIncomplete> {
        let report = self.enumerate_report_with_config(config);
        if report.stats.outcome == AllSatOutcome::Exhaustive {
            Ok(report.solutions)
        } else {
            Err(AllSatIncomplete {
                outcome: report.stats.outcome,
                solutions_found: report.stats.solutions_found,
                input_error: report.stats.input_error,
            })
        }
    }

    /// Enumerate solutions via callback without collecting them.
    ///
    /// The callback receives each solution as it is found. Return `true` to
    /// continue enumeration, `false` to stop early. Returns statistics for
    /// the enumeration run.
    ///
    /// This is useful for large state spaces where collecting all solutions
    /// into a `Vec` would be prohibitively expensive.
    pub fn enumerate_with_callback<F>(
        &mut self,
        config: AllSatConfig,
        mut callback: F,
    ) -> AllSatStats
    where
        F: FnMut(&Solution) -> bool,
    {
        // The iterator is the single enumeration engine. In particular, its
        // Drop implementation retracts an external solver scope even if the
        // user callback panics and unwinds through this method.
        let mut iterator = self.iter_with_config(config);
        while let Some(solution) = iterator.next() {
            if !callback(&solution) {
                iterator.finish(AllSatOutcome::CallbackStopped);
                break;
            }
        }
        iterator.run_stats.clone()
    }
}

impl Default for AllSatSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
#[path = "solver_tests.rs"]
mod tests;
